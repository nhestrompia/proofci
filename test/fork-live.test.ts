import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash, createHmac, randomUUID } from 'node:crypto';
import { Pool } from 'pg';
import { ActiveBaselines } from '../src/active-baselines.ts';
import { executeRun } from '../src/run-executor.ts';
import { fetchSnapshot } from '../src/snapshot-fetch.ts';
import { EnrollmentStore } from '../src/enrollment-store.ts';
import { RunStore } from '../src/run-store.ts';
import { processPullEvent } from '../src/pull-events.ts';
import { resolvePullDelivery } from '../src/pull-delivery.ts';
import { executeNext } from '../src/run-worker.ts';

test('a public GitHub fork snapshot reaches the real isolated verifier without model access', { skip: !process.env.PROOFCI_TEST_LIVE_FORK, timeout: 300_000 }, async t => {
  const owner = 'typicode', name = 'json-server', number = 1781;
  const repository = `https://github.com/${owner}/${name}.git`;
  const databaseUrl = process.env.PROOFCI_TEST_DATABASE_URL;
  if (!databaseUrl) throw new Error('PROOFCI_TEST_DATABASE_URL is required for live fork admission');
  const token = execFileSync('gh', ['auth', 'token'], { encoding: 'utf8' }).trim();
  const resolvePullRequest = async () => {
    const response = await fetch(`https://api.github.com/repos/${owner}/${name}/pulls/${number}`, { headers: { accept: 'application/vnd.github+json' } });
    if (!response.ok) throw new Error(`GitHub pull request returned ${response.status}`);
    const data: unknown = await response.json();
    if (typeof data !== 'object' || !data || !('state' in data) || data.state !== 'open' || !('head' in data) || typeof data.head !== 'object' || !data.head || !('base' in data) || typeof data.base !== 'object' || !data.base ||
        !('sha' in data.head) || typeof data.head.sha !== 'string' || !('repo' in data.head) || typeof data.head.repo !== 'object' || !data.head.repo || !('id' in data.head.repo) || typeof data.head.repo.id !== 'number' ||
        !('sha' in data.base) || typeof data.base.sha !== 'string' || !('repo' in data.base) || typeof data.base.repo !== 'object' || !data.base.repo || !('id' in data.base.repo) || typeof data.base.repo.id !== 'number') throw new Error('Invalid live fork response');
    return { number, sourceRepositoryId: data.head.repo.id, destinationRepositoryId: data.base.repo.id, head: data.head.sha, base: data.base.sha };
  };
  const pr = await resolvePullRequest();
  assert.notEqual(pr.sourceRepositoryId, pr.destinationRepositoryId);
  const root = await mkdtemp(join(tmpdir(), 'proofci-live-fork-'));
  try {
    const manifest = { version: 1, candidate: 'package.json', contracts: [{ id: 'increment', explanation: 'Fixture contract', owner: 'test', formal_statement: 'x + 1', assumptions: [], specification_closure: [], implementation_bindings: ['target'], policy: 'required', evidence: 'proofci-absent-evidence' }] };
    const manifestPath = join(root, 'manifest.json'); await writeFile(manifestPath, JSON.stringify(manifest));
    const baselineOutput = join(root, 'baseline'); await mkdir(baselineOutput);
    const store = join(root, 'baseline.db');
    const helper = `import hashlib, pathlib, sys\nsys.path.insert(0, 'portable')\nimport baselines\nstore, path, repo, head, output = sys.argv[1:]\ndata = pathlib.Path(path).read_bytes()\nmanifest = baselines.parse_manifest(data)\nbaseline = baselines.materialize(manifest, pathlib.Path(output))\ndigest = hashlib.sha256(data).hexdigest()\nwith baselines.open_store(store) as db:\n db.execute('INSERT INTO baselines (digest, manifest, manifest_path, baseline_sha256, repository, initial_head, approval_identity, approval_source, report) VALUES (?,?,?,?,?,?,?,?,?)', (digest, data, 'proofci-absent-manifest.json', baseline, repo, head, 'test-reviewer', 'fixture', b'{}'))\n db.execute('INSERT INTO active (id, digest) VALUES (1, ?)', (digest,))\n`;
    execFileSync('python3', ['-c', helper, store, manifestPath, repository, pr.head, baselineOutput]);
    const baseline = createHash('sha256').update(await readFile(join(baselineOutput, 'baseline.json'))).digest('hex');
    const resolvePullMerge = async () => {
      const response = await fetch(`https://api.github.com/repos/${owner}/${name}/pulls/${number}`, { headers: { accept: 'application/vnd.github+json' } });
      if (!response.ok) throw new Error(`GitHub pull request returned ${response.status}`);
      const data: unknown = await response.json();
      if (typeof data !== 'object' || !data || !('mergeable' in data) || data.mergeable !== true || !('merge_commit_sha' in data) || typeof data.merge_commit_sha !== 'string' || !/^[a-f0-9]{40}$/.test(data.merge_commit_sha)) throw new Error('Live pull merge unavailable');
      const current = await resolvePullRequest();
      const commitResponse = await fetch(`https://api.github.com/repos/${owner}/${name}/git/commits/${data.merge_commit_sha}`);
      if (!commitResponse.ok) throw new Error('Live merge commit unavailable');
      const commit: unknown = await commitResponse.json();
      if (typeof commit !== 'object' || !commit || !('parents' in commit) || !Array.isArray(commit.parents) || commit.parents.length !== 2 || commit.parents[0]?.sha !== current.base || commit.parents[1]?.sha !== current.head) throw new Error('Live merge parents changed');
      return { kind: 'resolved' as const, merge: data.merge_commit_sha, head: current.head, base: current.base };
    };
    const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: pr.destinationRepositoryId, lane: `pull/${number}`, number, sourceRepositoryId: pr.sourceRepositoryId, head: pr.head, base: pr.base, baseline };
    const github = { installationAccess: async () => 'allowed' as const, resolveHead: async () => null, resolvePullRequest, resolvePullMerge, stageSnapshot: async (_scope: unknown, input: { head: string; base: string; root: string; signal: AbortSignal }) => fetchSnapshot({ ...input, owner, name, token }) };
    const baselines = new ActiveBaselines([{ ...candidate, store, repository }]);
    const schema = `fork_live_${randomUUID().replaceAll('-', '')}`;
    const admin = new Pool({ connectionString: databaseUrl });
    await admin.query(`CREATE SCHEMA ${schema}`);
    const pool = new Pool({ connectionString: databaseUrl, options: `-c search_path=${schema}` });
    let report: unknown;
    try {
      const selections = new EnrollmentStore(pool), runs = new RunStore(pool);
      await selections.initialize(); await runs.initialize(); await selections.select(candidate);
      const body = Buffer.from(JSON.stringify({ action: 'opened', number, installation: { id: candidate.installationId }, repository: { id: candidate.repositoryId }, pull_request: { number, base: { repo: { id: candidate.repositoryId } } } }));
      const secret = 'local-test-webhook-secret';
      const signature = `sha256=${createHmac('sha256', secret).update(body).digest('hex')}`;
      assert.equal(await processPullEvent({ body, signature, event: 'pull_request', deliveryId: randomUUID(), secret, store: runs }), true);
      const delivery = await runs.claimPullDelivery(60_000); assert.ok(delivery);
      await runs.processPullDelivery(delivery, item => resolvePullDelivery({ delivery: item, selections, github, baselines }));
      assert.equal(await executeNext({ store: runs, leaseMs: 30_000, authorize: async () => 'allowed', execute: (input, signal, ensureActive, dispatch) => executeRun({ candidate: input, signal, github, baselines, ensureActive, dispatch }) }), true);
      const stored = await runs.list(candidate);
      assert.equal(stored.length, 1);
      report = stored[0]?.report;
    } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
    assert.ok(typeof report === 'object' && report !== null);
    assert.ok('status' in report && 'results' in report && 'usage' in report);
    assert.equal(report.status, 'blocked', JSON.stringify(report));
    assert.ok(Array.isArray(report.results));
    assert.equal(report.results[0]?.reason, 'unsupported_semantics');
    assert.ok(typeof report.usage === 'object' && report.usage !== null && 'model_calls' in report.usage);
    assert.equal(report.usage.model_calls, 0);
    t.diagnostic(`PR ${owner}/${name}#${number}, source repository ${pr.sourceRepositoryId}, destination repository ${pr.destinationRepositoryId}, head ${pr.head}, base ${pr.base}; blocked: unsupported_semantics; model calls: 0`);
  } finally { await rm(root, { recursive: true, force: true }); }
});
