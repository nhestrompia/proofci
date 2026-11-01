import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { cp, mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash, randomUUID } from 'node:crypto';
import { createConnection } from 'node:net';
import { ActiveBaselines } from '../src/active-baselines.ts';
import { executeRun } from '../src/run-executor.ts';

test('a fork proof cannot access the test sentinels or a public network endpoint', { skip: !process.env.PROOFCI_TEST_FORK_ISOLATION, timeout: 360_000 }, async t => {
  await new Promise<void>((resolve, reject) => {
    const socket = createConnection({ host: '1.1.1.1', port: 443 });
    socket.setTimeout(5000);
    socket.once('connect', () => { socket.destroy(); resolve(); });
    socket.once('error', reject);
    socket.once('timeout', () => { socket.destroy(); reject(new Error('Network positive control timed out')); });
  });
  const probe = JSON.parse(execFileSync('docker', ['run', '--rm', '--network', 'none', (process.env.PROOFCI_TEST_PROBE_IMAGE ?? 'proofci-ticket16-probe'), '--job', 'probe', '--challenge', 'fork-isolation'], { encoding: 'utf8', timeout: 180_000 }));
  assert.equal(probe.status, 'passed');
  for (const name of ['host-home', 'credentials', 'other-workspace', 'other-repository-cache', 'container_socket', 'network']) {
    assert.equal(probe.results.find((item: { probe: string }) => item.probe === name)?.status, 'denied');
  }
  const root = await mkdtemp(join(tmpdir(), 'proofci-fork-isolation-'));
  const priorProviderKey = process.env.OPENAI_API_KEY, priorInstallationToken = process.env.GITHUB_TOKEN;
  try {
    process.env.OPENAI_API_KEY = 'proofci-test-provider-canary';
    process.env.GITHUB_TOKEN = 'proofci-test-installation-canary';
    const baseSnapshot = join(root, 'base'); await mkdir(baseSnapshot);
    await cp('experiments/source-binding/fixtures/candidate.lean', join(baseSnapshot, 'candidate.lean'));
    await cp('experiments/source-binding/fixtures/verified', join(baseSnapshot, 'evidence'), { recursive: true });
    const manifest = { version: 1, candidate: 'candidate.lean', contracts: [{ id: 'increment', explanation: 'Adds one', owner: 'reviewer', formal_statement: 'x + 1', assumptions: [], specification_closure: [], implementation_bindings: ['target'], policy: 'required', evidence: 'evidence' }] };
    await writeFile(join(baseSnapshot, 'contracts.json'), JSON.stringify(manifest));
    const git = (dir: string, ...args: string[]) => execFileSync('git', ['-C', dir, ...args], { encoding: 'utf8' }).trim();
    git(baseSnapshot, 'init', '-q'); git(baseSnapshot, 'config', 'user.name', 'ProofCI'); git(baseSnapshot, 'config', 'user.email', 'proofci@example.invalid');
    git(baseSnapshot, 'add', '.'); git(baseSnapshot, 'commit', '-qm', 'reviewed baseline');
    const base = git(baseSnapshot, 'rev-parse', 'HEAD');
    const snapshot = join(root, 'fork'); execFileSync('git', ['clone', '-q', '--no-hardlinks', baseSnapshot, snapshot]);
    git(snapshot, 'config', 'user.name', 'fork contributor'); git(snapshot, 'config', 'user.email', 'fork@example.invalid');
    const repository = 'https://github.com/example/fixture.git'; git(snapshot, 'remote', 'set-url', 'origin', repository);
    const host = join(root, 'host-home'), credential = join(root, 'credential'), cache = join(root, 'other-repository-cache');
    await mkdir(host); await mkdir(cache);
    await writeFile(join(host, 'sentinel'), 'host-only');
    await writeFile(credential, 'credential-only');
    await writeFile(join(cache, 'sentinel'), 'other-repository-only');
    const markerSuffix = randomUUID().replaceAll('-', '');
    const marker = `PROOFCI_TEST_${markerSuffix}`;
    const proof = `import CandidateCheck\ndef readGuard (path : String) : IO Unit := do\n  let value ← try pure (some (← IO.FS.readFile path)) catch _ => pure none\n  if value.isSome then throw (IO.userError "unexpected host access")\n#eval do\n  readGuard ${JSON.stringify(join(host, 'sentinel'))}\n  readGuard ${JSON.stringify(credential)}\n  readGuard ${JSON.stringify(join(cache, 'sentinel'))}\n  if (← IO.getEnv "OPENAI_API_KEY").isSome then throw (IO.userError "provider credential exposed")\n  if (← IO.getEnv "GITHUB_TOKEN").isSome then throw (IO.userError "installation credential exposed")\n  let applets ← IO.Process.output { cmd := "/bin/busybox.static", args := #["--list"] }\n  if applets.exitCode != 0 || !(applets.stdout.splitOn "\\n").contains "nc" then throw (IO.userError "network test client missing")\n  let probe ← IO.Process.output { cmd := "/bin/busybox.static", args := #["nc", "-w", "1", "1.1.1.1", "443"] }\n  if probe.exitCode == 0 then throw (IO.userError "network access succeeded")\n  (throw (IO.userError ("PROOFCI_TEST_" ++ "${markerSuffix}")) : IO Unit)\ntheorem contract (x : Nat) : target x = x + 1 := by rfl\n`;
    const solution = join(snapshot, 'evidence', 'solution.lean');
    await writeFile(solution, proof);
    const manifestPath = join(snapshot, 'evidence', 'manifest.json');
    const evidenceManifest = JSON.parse(await readFile(manifestPath, 'utf8'));
    evidenceManifest.solution_sha256 = createHash('sha256').update(proof).digest('hex');
    await writeFile(manifestPath, JSON.stringify(evidenceManifest));
    git(snapshot, 'add', 'evidence'); git(snapshot, 'commit', '-qm', 'exercise proof isolation');
    const head = git(snapshot, 'rev-parse', 'HEAD');
    const store = join(root, 'baseline.db'), baselineOutput = join(root, 'baseline'); await mkdir(baselineOutput);
    const helper = `import hashlib, pathlib, sys\nsys.path.insert(0, 'portable')\nimport baselines\nstore, path, repo, head, output = sys.argv[1:]\ndata = pathlib.Path(path).read_bytes()\nmanifest = baselines.parse_manifest(data)\nbaseline = baselines.materialize(manifest, pathlib.Path(output))\ndigest = hashlib.sha256(data).hexdigest()\nwith baselines.open_store(store) as db:\n db.execute('INSERT INTO baselines (digest, manifest, manifest_path, baseline_sha256, repository, initial_head, approval_identity, approval_source, report) VALUES (?,?,?,?,?,?,?,?,?)', (digest, data, 'contracts.json', baseline, repo, head, 'reviewer', 'fixture', b'{}'))\n db.execute('INSERT INTO active (id, digest) VALUES (1, ?)', (digest,))\n`;
    execFileSync('python3', ['-c', helper, store, join(baseSnapshot, 'contracts.json'), repository, base, baselineOutput]);
    const baseline = createHash('sha256').update(await readFile(join(baselineOutput, 'baseline.json'))).digest('hex');
    const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/1', number: 1, sourceRepositoryId: 3, head, base, baseline };
    const github = { resolveHead: async () => null, resolvePullRequest: async () => ({ number: 1, sourceRepositoryId: 3, destinationRepositoryId: 2, head, base }), stageSnapshot: async (_scope: unknown, input: { root: string }) => { const target = join(input.root, 'snapshot'); await cp(snapshot, target, { recursive: true }); return { snapshot: target, repository }; } };
    const report = await executeRun({ candidate, signal: new AbortController().signal, github, baselines: new ActiveBaselines([{ ...candidate, store, repository }]) });
    assert.ok(typeof report.dispatch === 'object' && report.dispatch !== null && 'worker_status' in report.dispatch, JSON.stringify(report));
    assert.equal(report.dispatch.worker_status, 1, JSON.stringify(report));
    assert.equal(report.status, 'blocked', JSON.stringify(report));
    assert.ok(Array.isArray(report.results) && report.results[0]?.reason === 'proof_failed', JSON.stringify(report));
    const validation = report.results[0]?.validation;
    assert.ok(typeof validation === 'object' && validation !== null && 'detail' in validation && typeof validation.detail === 'string');
    assert.match(validation.detail, /error/i);
    assert.ok(validation.detail.includes(marker), JSON.stringify(report));
    assert.equal(await readFile(join(host, 'sentinel'), 'utf8'), 'host-only');
    assert.equal(await readFile(credential, 'utf8'), 'credential-only');
    assert.equal(await readFile(join(cache, 'sentinel'), 'utf8'), 'other-repository-only');
    t.diagnostic('The construction sandbox reached the fixture completion marker after checking three sentinel paths, two credential variables and one TCP endpoint. The independent fixed probe reported denials for those classes, the container socket and another workspace.');

  } finally {
    if (priorProviderKey === undefined) delete process.env.OPENAI_API_KEY; else process.env.OPENAI_API_KEY = priorProviderKey;
    if (priorInstallationToken === undefined) delete process.env.GITHUB_TOKEN; else process.env.GITHUB_TOKEN = priorInstallationToken;
    await rm(root, { recursive: true, force: true });
  }
});
