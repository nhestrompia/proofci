import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { cp, mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { ActiveBaselines } from '../src/active-baselines.ts';
import { executeRun } from '../src/run-executor.ts';

test('the executor uses an approved baseline and the real isolated verifier', { skip: !process.env.PROOFCI_TEST_VM, timeout: 300_000 }, async () => {
  const root = await mkdtemp(join(tmpdir(), 'proofci-executor-test-'));
  try {
    const snapshot = join(root, 'snapshot'); await mkdir(snapshot);
    await cp('experiments/source-binding/fixtures/candidate.lean', join(snapshot, 'candidate.lean'));
    await cp('experiments/source-binding/fixtures/verified', join(snapshot, 'evidence'), { recursive: true });
    const manifest = { version: 1, candidate: 'candidate.lean', contracts: [{ id: 'increment', explanation: 'Adds one', owner: 'maintainer', formal_statement: 'x + 1', assumptions: [], specification_closure: [], implementation_bindings: ['target'], policy: 'required', evidence: 'evidence' }] };
    await writeFile(join(snapshot, 'contracts.json'), JSON.stringify(manifest));
    const git = (...args: string[]) => execFileSync('git', ['-C', snapshot, ...args], { encoding: 'utf8' }).trim();
    git('init', '-q'); git('config', 'user.name', 'ProofCI'); git('config', 'user.email', 'proofci@example.invalid');
    const repository = 'https://github.com/example/fixture.git';
    git('remote', 'add', 'origin', repository); git('add', '.'); git('commit', '-qm', 'fixture');
    const head = git('rev-parse', 'HEAD');
    const store = join(root, 'baseline.db');
    const helper = `import hashlib, pathlib, sys\nsys.path.insert(0, 'portable')\nimport baselines\nstore, path, repo, head, output = sys.argv[1:]\ndata = pathlib.Path(path).read_bytes()\nmanifest = baselines.parse_manifest(data)\nbaseline = baselines.materialize(manifest, pathlib.Path(output))\ndigest = hashlib.sha256(data).hexdigest()\nwith baselines.open_store(store) as db:\n db.execute('INSERT INTO baselines (digest, manifest, manifest_path, baseline_sha256, repository, initial_head, approval_identity, approval_source, report) VALUES (?,?,?,?,?,?,?,?,?)', (digest, data, 'contracts.json', baseline, repo, head, 'reviewer', 'fixture', b'{}'))\n db.execute('INSERT INTO active (id, digest) VALUES (1, ?)', (digest,))\n`;
    const baselineOutput = join(root, 'baseline'); await mkdir(baselineOutput);
    execFileSync('python3', ['-c', helper, store, join(snapshot, 'contracts.json'), repository, head, baselineOutput]);
    const { createHash } = await import('node:crypto');
    const digest = createHash('sha256').update(await readFile(join(baselineOutput, 'baseline.json'))).digest('hex');
    const candidate = { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: 'refs/heads/main', head, base: head, baseline: digest };
    const github = { resolveHead: async () => head, stageSnapshot: async (_scope: unknown, input: { root: string }) => {
      const target = join(input.root, 'snapshot'); await cp(snapshot, target, { recursive: true }); return { snapshot: target, repository };
    } };
    const result = await executeRun({ candidate, signal: new AbortController().signal, github, baselines: new ActiveBaselines([{ installationId: 1, repositoryId: 2, store, repository }]) });
    assert.equal(result.status, 'passed', JSON.stringify(result));
  } finally { await rm(root, { recursive: true, force: true }); }
});
