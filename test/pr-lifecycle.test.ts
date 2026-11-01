import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, generateKeyPairSync, randomUUID } from 'node:crypto';
import { Pool } from 'pg';
import { processPullEvent, pullAction } from '../src/pull-events.ts';
import { processRerunEvent, type RerunRequest } from '../src/rerun-events.ts';
import { resolvePullDelivery } from '../src/pull-delivery.ts';
import { GitHubApp } from '../src/github-app.ts';
import { RunStore, type Candidate, type PullLease } from '../src/run-store.ts';
import { executeNext } from '../src/run-worker.ts';
import { publishNext } from '../src/publication-worker.ts';

const sign = (body: Buffer) => `sha256=${createHmac('sha256', 'secret').update(body).digest('hex')}`;

test('pull request actions follow the documented run behavior', async () => {
  assert.equal(pullAction('opened', undefined), 'invalidate');
  assert.equal(pullAction('reopened', undefined), 'invalidate');
  assert.equal(pullAction('synchronize', undefined), 'invalidate');
  assert.equal(pullAction('closed', undefined), 'invalidate');
  assert.equal(pullAction('edited', { base: { ref: { from: 'main' } } }), 'invalidate');
  assert.equal(pullAction('edited', { title: { from: 'old' } }), 'ignore');
  assert.equal(pullAction('ready_for_review', undefined), 'resolve');
  assert.equal(pullAction('converted_to_draft', undefined), 'resolve');
  assert.equal(pullAction('labeled', undefined), 'ignore');

  const accepted: Array<[number, boolean]> = [];
  const store = { acceptPullDelivery: async (item: { number: number }, invalidate: boolean) => { accepted.push([item.number, invalidate]); return true; } };
  for (const [action, changes] of [['edited', { body: { from: '' } }], ['edited', { base: { sha: { from: 'a' } } }], ['ready_for_review', undefined]] as const) {
    const body = Buffer.from(JSON.stringify({ action, changes, number: 5, installation: { id: 1 }, repository: { id: 2 }, pull_request: { number: 5, base: { repo: { id: 2 } } } }));
    assert.equal(await processPullEvent({ body, signature: sign(body), event: 'pull_request', deliveryId: randomUUID(), secret: 'secret', store }), true);
  }
  assert.deepEqual(accepted, [[5, true], [5, false]]);
});

test('only signed reruns of this App\'s own checks are queued, with the requesting actor', async () => {
  const requests: RerunRequest[] = [];
  const store = { acceptRerun: async (request: RerunRequest) => { requests.push(request); return true; } };
  const runId = randomUUID(), sha = 'd'.repeat(40);
  const base = { action: 'rerequested', installation: { id: 1 }, repository: { id: 2 }, sender: { id: 77, login: 'contributor' } };
  const send = async (event: string, payload: unknown, signature?: string) => {
    const body = Buffer.from(JSON.stringify(payload));
    return processRerunEvent({ body, signature: signature ?? sign(body), event, deliveryId: randomUUID(), secret: 'secret', appId: 7, store });
  };
  assert.equal(await send('check_run', { ...base, check_run: { external_id: runId, head_sha: sha, app: { id: 7 } } }), true);
  assert.equal(await send('check_suite', { ...base, check_suite: { head_sha: sha, app: { id: 7 } } }), true);
  assert.equal(await send('check_run', { ...base, check_run: { external_id: runId, head_sha: sha, app: { id: 8 } } }), true);
  assert.equal(await send('check_run', { ...base, check_run: { external_id: 'not-a-run', head_sha: sha, app: { id: 7 } } }), true);
  assert.equal(await send('check_run', { ...base, action: 'completed', check_run: { external_id: runId, head_sha: sha, app: { id: 7 } } }), true);
  assert.equal(await send('check_run', { ...base, check_run: { external_id: runId, head_sha: sha, app: { id: 7 } } }, 'sha256=' + '0'.repeat(64)), false);
  assert.deepEqual(requests.map(({ deliveryId: _, ...rest }) => rest), [
    { installationId: 1, repositoryId: 2, actorId: 77, actorLogin: 'contributor', sha, runId },
    { installationId: 1, repositoryId: 2, actorId: 77, actorLogin: 'contributor', sha, runId: null },
  ]);
});

test('rerun authority requires current write access for the same numeric user', async () => {
  const { privateKey } = generateKeyPairSync('rsa', { modulusLength: 2048 });
  let answer: () => Response = () => Response.json({ permission: 'write', user: { id: 77 } });
  const request: typeof fetch = async (input) => {
    const path = new URL(String(input)).pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, suspended_at: null });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 't', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === '/repos/owner/repo/collaborators/contributor/permission') return answer();
    throw new Error(`unexpected request ${path}`);
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  const scope = { installationId: 12, repositoryId: 34 }, actor = { id: 77, login: 'contributor' };
  assert.equal(await app.rerunAuthority(scope, actor), 'allowed');
  answer = () => Response.json({ permission: 'admin', user: { id: 77 } });
  assert.equal(await app.rerunAuthority(scope, actor), 'allowed');
  answer = () => Response.json({ permission: 'read', user: { id: 77 } });
  assert.equal(await app.rerunAuthority(scope, actor), 'denied');
  answer = () => Response.json({ permission: 'write', user: { id: 78 } });
  assert.equal(await app.rerunAuthority(scope, actor), 'denied');
  answer = () => new Response('', { status: 404 });
  assert.equal(await app.rerunAuthority(scope, actor), 'denied');
  answer = () => new Response('', { status: 502 });
  await assert.rejects(app.rerunAuthority(scope, actor));
  assert.equal(await app.rerunAuthority(scope, { id: 77, login: '../x' }), 'denied');
});

test('a denied rerun does not resolve the pull request', async () => {
  const delivery: PullLease = { deliveryId: 'd', installationId: 1, repositoryId: 2, number: 3, generation: 1, selectionGeneration: 'v1', rerunActor: { id: 77, login: 'reader' } };
  let resolved = false;
  const github = { installationAccess: async () => 'allowed' as const, rerunAuthority: async () => 'denied' as const,
    resolvePullRequest: async () => { resolved = true; return null; }, resolvePullMerge: async () => { resolved = true; return { kind: 'blocked' as const, reason: 'merge_unresolved' as const }; } };
  const selections = { readVersion: async () => 'v1', removeIfVersion: async () => {} };
  assert.equal(await resolvePullDelivery({ delivery, selections, github, baselines: { active: async () => 'c'.repeat(64) } }), 'rerun-denied');
  assert.equal(resolved, false);
});

const url = process.env.PROOFCI_TEST_DATABASE_URL;
async function withStore(run: (context: { pool: Pool; runs: RunStore; select(scope: { installationId: number; repositoryId: number }): Promise<void> }) => Promise<void>): Promise<void> {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const selections = new EnrollmentStore(pool), runs = new RunStore(pool);
    await selections.initialize(); await runs.initialize();
    await run({ pool, runs, select: scope => selections.select(scope) });
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
}
const pull = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/5', number: 5, sourceRepositoryId: 3, head: 'a'.repeat(40), mergeHead: 'd'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
async function admitPull(runs: RunStore, candidate: Candidate, invalidate = true): Promise<void> {
  await runs.acceptPullDelivery({ deliveryId: randomUUID(), installationId: candidate.installationId, repositoryId: candidate.repositoryId, number: 5 }, invalidate);
  const delivery = await runs.claimPullDelivery(60_000); assert.ok(delivery);
  assert.equal(await runs.processPullDelivery(delivery, async () => candidate), true);
}

test('reruns verify authority and repository ownership before creating a fresh attempt', { skip: !url }, () => withStore(async ({ pool, runs, select }) => {
  await select(pull); await select({ installationId: 1, repositoryId: 9 });
  await admitPull(runs, pull);
  const lease = await runs.claim(60_000); assert.ok(lease);
  assert.equal(await runs.fail(lease, 'worker_unavailable'), true);
  const failed = lease.id;
  const request = { installationId: 1, repositoryId: 2, actorId: 77, actorLogin: 'contributor', sha: pull.mergeHead, runId: failed };

  // Another repository cannot name this run, and an unknown check is ignored.
  assert.equal(await runs.acceptRerun({ ...request, deliveryId: randomUUID(), repositoryId: 9 }), false);
  assert.equal(await runs.acceptRerun({ ...request, deliveryId: randomUUID(), runId: randomUUID() }), false);
  assert.equal(await runs.claimPullDelivery(60_000), null);

  // An unauthorized actor changes nothing: no cancellation, no new attempt.
  const deliveryId = randomUUID();
  assert.equal(await runs.acceptRerun({ ...request, deliveryId }), true);
  assert.equal(await runs.acceptRerun({ ...request, deliveryId }), true);
  assert.equal(await runs.acceptRerun({ ...request, deliveryId, actorId: 78 }), false);
  const denied = await runs.claimPullDelivery(60_000); assert.ok(denied);
  assert.deepEqual(denied.rerunActor, { id: 77, login: 'contributor' });
  assert.equal(await runs.processPullDelivery(denied, async () => 'rerun-denied'), true);
  assert.equal((await runs.inspectPull(pull, 5))?.lastError, 'rerun_denied');
  assert.deepEqual((await runs.list(pull)).map(run => [run.id, run.state, run.applicable]), [[failed, 'failed', true]]);

  // An authorized rerun creates a new attempt for the current inputs and retires the old one.
  assert.equal(await runs.acceptRerun({ ...request, deliveryId: randomUUID() }), true);
  const allowed = await runs.claimPullDelivery(60_000); assert.ok(allowed);
  assert.equal(await runs.processPullDelivery(allowed, async () => pull), true);
  const attempt = await runs.claim(60_000); assert.ok(attempt);
  assert.notEqual(attempt.id, failed);
  assert.equal((await runs.inspect(pull, failed))?.applicable, false);

  // A rerun while that attempt is still active does not duplicate work.
  assert.equal(await runs.acceptRerun({ ...request, runId: null, deliveryId: randomUUID() }), true);
  const duplicate = await runs.claimPullDelivery(60_000); assert.ok(duplicate);
  assert.equal(await runs.processPullDelivery(duplicate, async () => pull), true);
  assert.equal(await runs.renew(attempt, 60_000), true);
  const rows = await pool.query("SELECT count(*)::int AS count FROM proofci_runs WHERE applicable");
  assert.equal(rows.rows[0].count, 1);
}));

test('a base advance during proof search cannot satisfy the changed candidate', { skip: !url }, () => withStore(async ({ runs, select }) => {
  await select(pull);
  await admitPull(runs, pull);
  const old = await runs.claim(60_000); assert.ok(old);
  assert.deepEqual(await runs.startDispatch(old, async () => ({ started: true }), () => {}), { started: true });
  const oldPublication = await runs.claimPublication(60_000); assert.ok(oldPublication);
  await runs.finishPublication(oldPublication);

  // The target branch advances while the old proof search is still running.
  await runs.acceptDelivery({ deliveryId: randomUUID(), installationId: 1, repositoryId: 2, ref: 'refs/heads/main', head: 'e'.repeat(40), deleted: false }, false);
  assert.equal(await runs.renew(old, 60_000), false);
  assert.equal(await runs.complete(old, { version: 1, status: 'passed' }, Buffer.from('late')), false);
  assert.equal((await runs.inspect(pull, old.id))?.applicable, false);

  const advanced = { ...pull, base: 'e'.repeat(40), mergeHead: 'f'.repeat(40) };
  const delivery = await runs.claimPullDelivery(60_000); assert.ok(delivery);
  assert.equal(await runs.processPullDelivery(delivery, async () => advanced), true);
  const fresh = await runs.claim(60_000); assert.ok(fresh);
  assert.equal(fresh.candidate.base, advanced.base);

  // The old check is marked stale; only the new merge candidate can publish success.
  const invalidated: string[] = [], published: string[] = [];
  const github = {
    resolvePullMerge: async () => ({ kind: 'resolved' as const, head: advanced.head, base: advanced.base, merge: advanced.mergeHead }),
    invalidateCheck: async (_scope: unknown, input: { runId: string }) => { invalidated.push(input.runId); },
    publishCheck: async (_scope: unknown, input: { runId: string; output: { conclusion: string } | null; fresh(): Promise<boolean> }) => {
      if (await input.fresh()) published.push(`${input.runId}:${input.output?.conclusion ?? 'pending'}`);
    },
  };
  const options = { store: runs, github, baselines: { active: async () => pull.baseline }, origin: 'https://example.com' };
  while (await publishNext(options)) { /* drain */ }
  assert.ok(invalidated.includes(old.id));
  assert.ok(!published.some(entry => entry.startsWith(old.id)));
  assert.equal(await runs.complete(fresh, { version: 1, status: 'passed' }, Buffer.from('evidence')), true);
  while (await publishNext(options)) { /* drain */ }
  // Only the fresh run publishes; the stub report is not a validated report, so it blocks.
  assert.deepEqual(published, [`${fresh.id}:pending`, `${fresh.id}:failure`]);
}));

test('a force-push terminates active execution through the worker and readiness changes keep current work', { skip: !url }, () => withStore(async ({ runs, select }) => {
  await select(pull);
  await admitPull(runs, pull);
  let entered: () => void = () => {};
  const started = new Promise<void>(resolve => { entered = resolve; });
  let aborted = false, completed = false;
  const working = executeNext({ store: runs, leaseMs: 300, authorize: async () => 'allowed',
    execute: async (_candidate, signal, _ensureActive, dispatch) => dispatch(async () => {
      entered();
      await new Promise<void>(resolve => {
        if (signal.aborted) return resolve();
        signal.addEventListener('abort', () => resolve(), { once: true });
        setTimeout(() => { completed = true; resolve(); }, 5_000);
      });
      aborted = signal.aborted;
      return { version: 1, status: 'passed' };
    }).then(report => ({ report, evidence: null })),
  });
  await started;

  // Readiness changes re-resolve without disturbing the active run.
  await runs.acceptPullDelivery({ deliveryId: randomUUID(), installationId: 1, repositoryId: 2, number: 5 }, false);
  const ready = await runs.claimPullDelivery(60_000); assert.ok(ready);
  assert.equal(await runs.processPullDelivery(ready, async () => pull), true);
  const [active] = await runs.list(pull);
  assert.equal(active.state, 'running');

  // A force-push supersedes the run durably; the worker loses its lease and aborts.
  await runs.acceptPullDelivery({ deliveryId: randomUUID(), installationId: 1, repositoryId: 2, number: 5 }, true);
  await working;
  assert.equal(aborted, true);
  assert.equal(completed, false);
  const [cancelled] = await runs.list(pull);
  assert.equal(cancelled.state, 'cancelled');
  assert.equal(cancelled.applicable, false);
  assert.equal(await runs.claim(60_000), null);
  const pushed = await runs.claimPullDelivery(60_000); assert.ok(pushed);
  await runs.processPullDelivery(pushed, async () => ({ ...pull, head: '1'.repeat(40), mergeHead: '2'.repeat(40) }));
  assert.equal((await runs.claim(60_000))?.candidate.head, '1'.repeat(40));
}));
