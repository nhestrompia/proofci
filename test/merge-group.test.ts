import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, generateKeyPairSync, randomUUID } from 'node:crypto';
import { Pool } from 'pg';
import { processMergeGroupEvent, type MergeGroupDelivery, type MergeGroupRetirement } from '../src/merge-group-events.ts';
import { resolveMergeGroupDelivery } from '../src/merge-group-delivery.ts';
import { GitHubApp } from '../src/github-app.ts';
import { RunStore, type Candidate, type Lease, type MergeGroupLease } from '../src/run-store.ts';
import { publishNext } from '../src/publication-worker.ts';
import { checkReport } from '../src/check-report.ts';

const sign = (body: Buffer) => `sha256=${createHmac('sha256', 'secret').update(body).digest('hex')}`;
const sha = (char: string) => char.repeat(40);
const ref = (n: number, char: string) => `refs/heads/gh-readonly-queue/main/pr-${n}-${sha(char)}`;

test('only signed merge-group events for the target branch queue or retire exact groups', async () => {
  const accepted: MergeGroupDelivery[] = [], retired: MergeGroupRetirement[] = [];
  const store = { acceptMergeGroup: async (item: MergeGroupDelivery) => { accepted.push(item); return true; }, retireMergeGroup: async (item: MergeGroupRetirement) => { retired.push(item); return true; } };
  const group = { head_sha: sha('a'), head_ref: ref(5, '1'), base_sha: sha('b'), base_ref: 'refs/heads/main' };
  const deliveryId = randomUUID();
  const send = async (payload: unknown, signature?: string, event = 'merge_group') => {
    const body = Buffer.from(JSON.stringify(payload));
    return processMergeGroupEvent({ body, signature: signature ?? sign(body), event, deliveryId, secret: 'secret', store });
  };
  const base = { installation: { id: 1 }, repository: { id: 2 }, merge_group: group };
  assert.equal(await send({ ...base, action: 'checks_requested' }), true);
  assert.equal(await send({ ...base, action: 'destroyed', reason: 'dequeued' }), true);
  assert.equal(await send({ ...base, action: 'destroyed', reason: 'merged' }), true);
  assert.equal(await send({ ...base, action: 'destroyed', reason: 'something-new' }), true);
  assert.equal(await send({ ...base, action: 'checks_requested' }, 'sha256=' + '0'.repeat(64)), false);
  // A group branch must belong to the named target branch.
  assert.equal(await send({ ...base, action: 'checks_requested', merge_group: { ...group, head_ref: 'refs/heads/feature' } }), false);
  assert.equal(await send({ ...base, action: 'checks_requested', merge_group: { ...group, base_ref: 'refs/heads/release' } }), false);
  assert.equal(await send({ ...base, action: 'checks_requested', merge_group: { ...group, head_sha: 'short' } }), false);
  assert.equal(await send({ ...base, action: 'checks_requested' }, undefined, 'pull_request'), true);
  assert.deepEqual(accepted, [{ installationId: 1, repositoryId: 2, deliveryId, headRef: group.head_ref, headSha: group.head_sha, baseRef: 'refs/heads/main', baseSha: group.base_sha }]);
  assert.deepEqual(retired.map(item => item.reason), ['dequeued', 'merged', 'invalidated']);
});

test('GitHub resolves the merge group only when its branch and first parent still match', async () => {
  const { privateKey } = generateKeyPairSync('rsa', { modulusLength: 2048 });
  let refAnswer: () => Response = () => Response.json({ ref: ref(5, '1'), object: { type: 'commit', sha: sha('a') } });
  let commitAnswer: () => Response = () => Response.json({ sha: sha('a'), parents: [{ sha: sha('b') }, { sha: sha('c') }] });
  const request: typeof fetch = async (input) => {
    const path = new URL(String(input)).pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read', merge_queues: 'read' }, suspended_at: null });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 't', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === `/repos/owner/repo/git/ref/heads/gh-readonly-queue/main/pr-5-${sha('1')}`) return refAnswer();
    if (path === `/repos/owner/repo/git/commits/${sha('a')}`) return commitAnswer();
    throw new Error(`unexpected request ${path}`);
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  const scope = { installationId: 12, repositoryId: 34 }, group = { headRef: ref(5, '1'), headSha: sha('a'), baseSha: sha('b') };
  assert.deepEqual(await app.resolveMergeGroup(scope, group), { kind: 'resolved', head: sha('a'), base: sha('b') });
  commitAnswer = () => Response.json({ sha: sha('a'), parents: [{ sha: sha('e') }] });
  assert.deepEqual(await app.resolveMergeGroup(scope, group), { kind: 'blocked', reason: 'merge_group_parents_mismatch' });
  refAnswer = () => Response.json({ ref: ref(5, '1'), object: { type: 'commit', sha: sha('f') } });
  assert.deepEqual(await app.resolveMergeGroup(scope, group), { kind: 'blocked', reason: 'merge_group_ref_mismatch' });
  refAnswer = () => new Response('', { status: 404 });
  assert.deepEqual(await app.resolveMergeGroup(scope, group), { kind: 'blocked', reason: 'merge_group_ref_missing' });
  refAnswer = () => new Response('', { status: 502 });
  await assert.rejects(app.resolveMergeGroup(scope, group));
  await assert.rejects(app.resolveMergeGroup(scope, { ...group, headRef: 'refs/heads/main' }));
});

test('merge-group resolution binds the protected target and trusted baseline, never a PR result', async () => {
  const delivery: MergeGroupLease = { deliveryId: 'd', installationId: 1, repositoryId: 2, headRef: ref(5, '1'), headSha: sha('a'), baseRef: 'refs/heads/main', baseSha: sha('b'), generation: 1, selectionGeneration: 'v1' };
  let version: string | null = 'v1';
  const selections = { readVersion: async () => version, removeIfVersion: async () => { version = null; } };
  const github = { installationAccess: async () => 'allowed' as const, resolveMergeGroup: async () => ({ kind: 'resolved' as const, head: sha('a'), base: sha('b') }) };
  const baselines = { active: async () => 'c'.repeat(64) };
  const options = { delivery, protectedRef: 'refs/heads/main', selections, github, baselines };
  assert.deepEqual(await resolveMergeGroupDelivery(options), { kind: 'merge-group', installationId: 1, repositoryId: 2, lane: delivery.headRef, head: sha('a'), base: sha('b'), mergeHead: sha('a'), baseline: 'c'.repeat(64) });
  assert.deepEqual(await resolveMergeGroupDelivery({ ...options, protectedRef: 'refs/heads/release' }), { unavailable: 'merge_group_target_unprotected' });
  assert.deepEqual(await resolveMergeGroupDelivery({ ...options, baselines: { active: async () => null } }), { unavailable: 'baseline_unavailable' });
  assert.deepEqual(await resolveMergeGroupDelivery({ ...options, github: { ...github, resolveMergeGroup: async () => ({ kind: 'blocked' as const, reason: 'merge_group_ref_missing' as const }) } }), { unavailable: 'merge_group_ref_missing' });
  await assert.rejects(resolveMergeGroupDelivery({ ...options, github: { ...github, installationAccess: async () => 'unavailable' as const } }));
  assert.equal(await resolveMergeGroupDelivery({ ...options, github: { ...github, installationAccess: async () => 'revoked' as const } }), null);
  assert.equal(version, null);
});

test('an unresolved group explains the execution reason in its blocking check', () => {
  const candidate = { kind: 'merge-group' as const, installationId: 1, repositoryId: 2, lane: ref(5, '1'), head: sha('a'), mergeHead: sha('a'), base: sha('b'), baseline: '0'.repeat(64) };
  const output = checkReport(candidate, { version: 1, status: 'error', reason: 'merge_group_ref_missing' }, null);
  assert.equal(output.conclusion, 'failure');
  assert.match(output.summary, /Execution reason: merge_group_ref_missing/);
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

const scope = { installationId: 1, repositoryId: 2 };
const baseline = 'c'.repeat(64);
const groupOne = { headRef: ref(5, '1'), headSha: sha('a'), baseRef: 'refs/heads/main', baseSha: sha('b') };
const candidateFor = (group: typeof groupOne): Candidate => ({ ...scope, kind: 'merge-group', lane: group.headRef, head: group.headSha, mergeHead: group.headSha, base: group.baseSha, baseline });
async function deliver(runs: RunStore, group: typeof groupOne, resolve: (delivery: MergeGroupLease) => Promise<Candidate | { unavailable: string } | null> = async () => candidateFor(group)): Promise<MergeGroupLease> {
  assert.equal(await runs.acceptMergeGroup({ ...scope, ...group, deliveryId: randomUUID() }), true);
  const delivery = await runs.claimMergeGroupDelivery(60_000); assert.ok(delivery);
  assert.equal(await runs.processMergeGroupDelivery(delivery, resolve), true);
  return delivery;
}
function report(candidate: { head: string; base: string; baseline: string }, decision: 'verified' | 'violated') {
  const digest = 'e'.repeat(64);
  return { version: 1, status: decision === 'verified' ? 'passed' : 'blocked', envelope: { head: candidate.head, base: candidate.base, baseline_sha256: candidate.baseline, candidate_sha256: digest }, dispatch: { final_status: decision === 'verified' ? 0 : 1 },
    support: { admitted_candidate: 'candidate.lean', guarantee: 'Approved target', assumptions: [], exclusions: [] },
    results: [{ id: 'increment', policy: 'required', decision, reason: decision === 'verified' ? 'accepted' : 'counterexample', validation: { decision, candidate_sha256: digest, contract_sha256: 'f'.repeat(64) } }] };
}
function recorder(groups: Map<string, { head: string; base: string }>) {
  const published: Array<{ runId: string; sha: string; conclusion: string; summary: string }> = [], invalidated: Array<{ runId: string; sha: string }> = [];
  const github = {
    resolvePullMerge: async () => ({ kind: 'blocked' as const, reason: 'merge_unresolved' as const }),
    resolveMergeGroup: async (_scope: unknown, group: { headRef: string; headSha: string }) => {
      const current = groups.get(group.headRef);
      return current && current.head === group.headSha ? { kind: 'resolved' as const, ...current } : { kind: 'blocked' as const, reason: 'merge_group_ref_missing' as const };
    },
    invalidateCheck: async (_scope: unknown, input: { runId: string; sha: string }) => { invalidated.push(input); },
    publishCheck: async (_scope: unknown, input: { runId: string; sha: string; output: { conclusion: string; summary: string } | null; fresh(): Promise<boolean> }) => {
      if (!await input.fresh()) throw new Error('Check is stale');
      published.push({ runId: input.runId, sha: input.sha, conclusion: input.output?.conclusion ?? 'pending', summary: input.output?.summary ?? '' });
    },
  };
  return { github, published, invalidated };
}
async function drain(runs: RunStore, github: ReturnType<typeof recorder>['github']): Promise<void> {
  const options = { store: runs, github, baselines: { active: async () => baseline }, origin: 'https://example.com' };
  for (let i = 0; i < 20; i++) { try { if (!await publishNext(options)) return; } catch { /* retried later */ } }
}

test('a passing PR check cannot satisfy a merge group; each group publishes its own result', { skip: !url }, () => withStore(async ({ pool, runs, select }) => {
  await select(scope);
  // A PR whose test merge commit happens to equal the group commit has already passed.
  const pull = { ...scope, kind: 'pull-request' as const, lane: 'pull/5', number: 5, sourceRepositoryId: 2, head: sha('1'), mergeHead: groupOne.headSha, base: groupOne.baseSha, baseline };
  await runs.acceptPullDelivery({ ...scope, deliveryId: randomUUID(), number: 5 });
  const pullDelivery = await runs.claimPullDelivery(60_000); assert.ok(pullDelivery);
  assert.equal(await runs.processPullDelivery(pullDelivery, async () => pull), true);
  const pullLease = await runs.claim(60_000); assert.ok(pullLease);
  assert.equal(await runs.complete(pullLease, report({ ...pull, head: pull.mergeHead }, 'verified'), Buffer.from('pr')), true);

  // The group gets an independent run generation even with identical commit inputs.
  await deliver(runs, groupOne);
  const groupLease = await runs.claim(60_000); assert.ok(groupLease);
  assert.notEqual(groupLease.id, pullLease.id);
  assert.equal(groupLease.candidate.kind, 'merge-group');
  assert.equal(groupLease.candidate.lane, groupOne.headRef);
  assert.equal((await runs.inspect(scope, pullLease.id))?.applicable, true);

  // A second, stacked group in the same queue is independent and stays valid alongside the first.
  const groupTwo = { headRef: ref(6, '2'), headSha: sha('d'), baseRef: 'refs/heads/main', baseSha: groupOne.headSha };
  await deliver(runs, groupTwo);
  const defective = await runs.claim(60_000); assert.ok(defective);
  assert.equal(defective.candidate.head, groupTwo.headSha);
  assert.equal((await runs.inspect(scope, groupLease.id))?.state, 'running');

  assert.equal(await runs.complete(groupLease, report(groupLease.candidate, 'verified'), Buffer.from('group')), true);
  assert.equal(await runs.complete(defective, report(defective.candidate, 'violated'), Buffer.from('defective')), true);
  const scopes = await pool.query<{ id: string; scope: string }>("SELECT id, report->'scheduler'->>'scope' AS scope FROM proofci_runs");
  const byId = new Map(scopes.rows.map(row => [row.id, row.scope]));
  assert.equal(byId.get(pullLease.id), 'pull-request-test-merge');
  assert.equal(byId.get(groupLease.id), 'merge-group');

  const { github, published } = recorder(new Map([[groupOne.headRef, { head: groupOne.headSha, base: groupOne.baseSha }], [groupTwo.headRef, { head: groupTwo.headSha, base: groupTwo.baseSha }]]));
  await drain(runs, github);
  const final = (id: string) => published.filter(entry => entry.runId === id).at(-1);
  assert.equal(final(groupLease.id)?.sha, groupOne.headSha);
  assert.equal(final(groupLease.id)?.conclusion, 'success');
  assert.match(final(groupLease.id)?.summary ?? '', /Candidate scope: merge group/);
  assert.equal(final(defective.id)?.sha, groupTwo.headSha);
  assert.equal(final(defective.id)?.conclusion, 'failure');
  // The PR's own success is never published on the group's behalf.
  assert.ok(!published.some(entry => entry.runId === pullLease.id && entry.conclusion === 'success'));
}));

test('replacement, dequeueing, and late completions cannot satisfy the current group', { skip: !url }, () => withStore(async ({ runs, select }) => {
  await select(scope);
  await deliver(runs, groupOne);
  const replaced: Lease | null = await runs.claim(60_000); assert.ok(replaced);

  // GitHub rebuilds the group on the same queue branch with a new commit.
  const rebuilt = { ...groupOne, headSha: sha('9'), baseSha: sha('8') };
  await deliver(runs, rebuilt);
  assert.equal(await runs.renew(replaced, 60_000), false);
  assert.equal(await runs.complete(replaced, report(replaced.candidate, 'verified'), Buffer.from('late')), false);
  assert.equal((await runs.inspect(scope, replaced.id))?.applicable, false);
  const current = await runs.claim(60_000); assert.ok(current);
  assert.equal(current.candidate.head, rebuilt.headSha);

  // Dequeueing cancels the active run; a redelivered request for that group admits nothing.
  assert.equal(await runs.retireMergeGroup({ ...scope, headRef: rebuilt.headRef, headSha: rebuilt.headSha, reason: 'dequeued' }), true);
  assert.equal(await runs.complete(current, report(current.candidate, 'verified'), Buffer.from('late')), false);
  const redelivered = await deliver(runs, rebuilt);
  assert.equal((await runs.inspectMergeGroup(scope, redelivered.headRef))?.lastError, 'merge_group_retired');
  assert.equal(await runs.claim(60_000), null);

  // A resolution that raced with retirement is fenced at admission.
  assert.equal(await runs.acceptMergeGroup({ ...scope, ...groupOne, headSha: sha('7'), deliveryId: randomUUID() }), true);
  const racing = await runs.claimMergeGroupDelivery(60_000); assert.ok(racing);
  assert.equal(await runs.processMergeGroupDelivery(racing, async item => {
    await runs.retireMergeGroup({ ...scope, headRef: item.headRef, headSha: item.headSha, reason: 'invalidated' });
    return candidateFor({ ...groupOne, headSha: sha('7') });
  }), true);
  assert.equal(await runs.claim(60_000), null);

  // Stale checks for retired groups are marked failed, never published as success.
  const { github, published, invalidated } = recorder(new Map());
  await drain(runs, github);
  assert.ok(!published.some(entry => entry.conclusion === 'success'));
  assert.ok(invalidated.some(entry => entry.runId === current.id && entry.sha === rebuilt.headSha));
}));

test('a missing candidate publishes an explicit failure, and a merged group keeps its final check', { skip: !url }, () => withStore(async ({ runs, select }) => {
  await select(scope);
  // GitHub no longer has the queue branch when ProofCI resolves the notification.
  await deliver(runs, groupOne, async () => ({ unavailable: 'merge_group_ref_missing' }));
  assert.equal(await runs.claim(60_000), null);
  const { github, published } = recorder(new Map());
  await drain(runs, github);
  assert.deepEqual(published.map(entry => [entry.sha, entry.conclusion]), [[groupOne.headSha, 'failure']]);
  assert.match(published[0].summary, /Execution reason: merge_group_ref_missing/);

  // A target-branch push does not invalidate queued groups: each one is bound to its own base.
  const merged = { headRef: ref(7, '3'), headSha: sha('5'), baseRef: 'refs/heads/main', baseSha: sha('6') };
  await deliver(runs, merged);
  await runs.acceptDelivery({ ...scope, deliveryId: randomUUID(), ref: 'refs/heads/main', head: sha('4'), deleted: false }, false);
  const lease = await runs.claim(60_000); assert.ok(lease);
  assert.equal(await runs.complete(lease, report(lease.candidate, 'verified'), Buffer.from('ok')), true);
  const live = recorder(new Map([[merged.headRef, { head: merged.headSha, base: merged.baseSha }]]));
  await drain(runs, live.github);
  assert.equal(live.published.at(-1)?.conclusion, 'success');

  // After GitHub merges the group, its passing check stays as published.
  assert.equal(await runs.retireMergeGroup({ ...scope, headRef: merged.headRef, headSha: merged.headSha, reason: 'merged' }), true);
  const after = recorder(new Map());
  await drain(runs, after.github);
  assert.deepEqual(after.invalidated, []);
  assert.deepEqual(after.published, []);
}));
