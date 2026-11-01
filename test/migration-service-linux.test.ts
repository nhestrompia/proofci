import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { cp, mkdir, mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { MigrationService } from '../src/migration-service.ts';

const sha = (value: Buffer | string) => createHash('sha256').update(value).digest('hex');

for (const reason of ['revocation', 'head change'] as const) test(`${reason} observed after verification blocks activation`, { skip: !process.env.PROOFCI_TEST_VM, timeout: 600_000 }, async () => {
  const root = await mkdtemp(join(tmpdir(), 'proofci-migration-integration-'));
  try {
    const snapshot = join(root, 'source'); await mkdir(snapshot);
    await cp('experiments/source-binding/fixtures/candidate.lean', join(snapshot, 'candidate.lean'));
    await cp('experiments/source-binding/fixtures/verified', join(snapshot, 'evidence'), { recursive: true });
    const item = { id: 'increment', explanation: 'Adds one', owner: 'maintainer', formal_statement: 'x + 1', assumptions: [], specification_closure: [], implementation_bindings: ['target'], policy: 'required', evidence: 'evidence' };
    const old = JSON.stringify({ version: 1, candidate: 'candidate.lean', contracts: [item] });
    const replacement = JSON.stringify({ version: 1, candidate: 'candidate.lean', contracts: [{ ...item, id: 'replacement' }] });
    await writeFile(join(snapshot, 'contracts.json'), replacement);
    const git = (...args: string[]) => execFileSync('git', ['-C', snapshot, ...args], { encoding: 'utf8' }).trim();
    git('init', '-q'); git('config', 'user.name', 'ProofCI'); git('config', 'user.email', 'proofci@example.invalid');
    const repository = 'https://github.com/example/fixture.git';
    git('remote', 'add', 'origin', repository); git('add', '.'); git('commit', '-qm', 'candidate');
    const head = git('rev-parse', 'HEAD');
    const store = join(root, 'baselines.db');
    const oldPath = join(root, 'old.json'); await writeFile(oldPath, old);
    const baselineDir = join(root, 'baseline'); await mkdir(baselineDir);
    const pythonEnv = { ...process.env, PYTHONDONTWRITEBYTECODE: '1' };
    const seed = `import pathlib,sys\nsys.path.insert(0,'portable')\nimport baselines\nstore,path,repo,head,out=sys.argv[1:]\ndata=pathlib.Path(path).read_bytes()\ndigest=baselines.sha(data)\nbaseline=baselines.materialize(baselines.parse_manifest(data),pathlib.Path(out))\nwith baselines.open_store(store) as db:\n db.execute('INSERT INTO baselines(digest,manifest,manifest_path,baseline_sha256,repository,initial_head,approval_identity,approval_source,report) VALUES(?,?,?,?,?,?,?,?,?)',(digest,data,'contracts.json',baseline,repo,head,'1','fixture',b'{}'))\n db.execute('INSERT INTO active VALUES(1,?)',(digest,))\n`;
    execFileSync('python3', ['-c', seed, store, oldPath, repository, head, baselineDir], { env: pythonEnv });
    let checks = 0, headChecks = 0;
    const scope = { installationId: 1, repositoryId: 2 };
    const service = new MigrationService({
      repositories: [{ ...scope, store, repository, ref: 'refs/heads/main' }],
      selections: { readVersion: async () => 'selected', removeIfVersion: async () => {} },
      sessions: { checkMaintainer: async () => ++checks === 1 || reason === 'head change' ? 42 : null },
      github: {
        checkMaintainerAccess: async () => 42,
        installationAccess: async () => 'allowed',
        resolveHead: async () => ++headChecks >= 3 && reason === 'head change' ? (head === 'a'.repeat(40) ? 'b'.repeat(40) : 'a'.repeat(40)) : head,
        stageSnapshot: async (_scope, input) => { const staged = join(input.root, 'snapshot'); await cp(snapshot, staged, { recursive: true }); return { snapshot: staged, repository }; },
      },
    });
    const outcome = await service.migrate({ session: 'fixture', scope, head, previous: sha(old), replacement: sha(replacement) })
      .then(report => ({ kind: 'report' as const, report }), error => ({ kind: 'error' as const, error }));
    assert.equal(outcome.kind, 'error', `Verification did not reach the authorization check: ${JSON.stringify(outcome)}`);
    if (outcome.kind !== 'error') throw new Error('Expected a rejected migration');
    assert.match(String(outcome.error), /authorization is stale/);
    assert.equal(checks, 2);
    assert.equal(headChecks, reason === 'head change' ? 3 : 2);
    const result = JSON.parse(execFileSync('python3', ['portable/service_baseline.py', '--store', store, '--repository', repository], { encoding: 'utf8', env: pythonEnv }));
    assert.equal(result.reviewed_sha256, sha(old));
  } finally { await rm(root, { recursive: true, force: true }); }
});
