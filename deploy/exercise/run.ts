/**
 * Operational exercise for the self-hosted pilot. See deploy/exercise/README.md.
 *
 * Deploys the pinned compose stack on the local Docker host with a GitHub simulator,
 * verifies real pull requests with the pinned Lean VM verifier, and exercises evidence
 * retrieval, crash recovery, backup and restoration, credential rotation, upgrade, and
 * diagnostics. Results are written to OUTPUT_DIR/exercise.json and exercise.md.
 *
 * Usage: node deploy/exercise/run.ts OUTPUT_DIR
 */
import { createHash, createHmac, generateKeyPairSync, randomBytes, randomUUID } from 'node:crypto';
import { execFileSync, spawn } from 'node:child_process';
import { chmodSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { Pool } from 'pg';
import { ModelLedger } from '../../src/model-ledger.ts';
import type { Lease } from '../../src/run-store.ts';

const repo = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const output = resolve(process.argv[2] ?? join(repo, 'docs/evidence/ticket-23'));
const stamp = new Date().toISOString().replace(/[-:]/g, '').slice(0, 15).toLowerCase();
const root = join(realpathSync(process.env.PROOFCI_EXERCISE_ROOT ?? tmpdir()), `proofci-exercise-${stamp}`);
const image = process.env.PROOFCI_EXERCISE_IMAGE ?? 'proofci-control:exercise';
const ports = { pg: 25432, s3: 27070, control: 23000, sim: 28080, pg2: 25433, s3b: 27071, control2: 23001 };
const network = `proofci-exercise-${stamp}`;
const simName = `proofci-exercise-github-${stamp}`;
const app = { id: 4242, clientId: 'Iv1.exercise' };
const maintainer = { id: 5151, login: 'pilot-maintainer' };
const ledgerRepo = { installationId: 701, repositoryId: 9001, name: 'proofci-pilot/ledger' };
const otherRepo = { installationId: 701, repositoryId: 9002, name: 'proofci-pilot/registry' };
const scope = { installationId: ledgerRepo.installationId, repositoryId: ledgerRepo.repositoryId };

type Step = { phase: string; name: string; ok: boolean; detail: unknown; at: string };
const log: Step[] = [];
const started = Date.now();
function record(phase: string, name: string, ok: boolean, detail: unknown = null): void {
  log.push({ phase, name, ok, detail, at: new Date().toISOString() });
  process.stdout.write(`${ok ? 'PASS' : 'FAIL'} [${phase}] ${name}${detail && typeof detail !== 'object' ? `: ${String(detail)}` : ''}\n`);
}
function expect(phase: string, name: string, condition: boolean, detail: unknown = null): void {
  record(phase, name, condition, detail);
  if (!condition) throw new Error(`${phase}: ${name} failed: ${JSON.stringify(detail)}`);
}
function sh(command: string, args: string[], options: { env?: NodeJS.ProcessEnv; allowFailure?: boolean; input?: string; timeout?: number } = {}): { code: number; stdout: string; stderr: string } {
  try {
    const stdout = execFileSync(command, args, { cwd: repo, env: { ...process.env, ...options.env }, encoding: 'utf8', stdio: ['pipe', 'pipe', 'pipe'], input: options.input, timeout: options.timeout ?? 900_000, maxBuffer: 64 * 1024 * 1024 });
    return { code: 0, stdout, stderr: '' };
  } catch (error) {
    const failure = error as { status?: number; stdout?: string; stderr?: string };
    if (!options.allowFailure) throw new Error(`${command} ${args.join(' ')} failed (${failure.status}): ${failure.stderr ?? ''}${failure.stdout ?? ''}`);
    return { code: failure.status ?? 1, stdout: failure.stdout ?? '', stderr: failure.stderr ?? '' };
  }
}
const sleep = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));
async function waitFor<T>(label: string, probe: () => Promise<T | null | undefined | false>, timeoutMs: number, intervalMs = 2000): Promise<T> {
  const deadline = Date.now() + timeoutMs;
  for (;;) {
    let value: T | null | undefined | false = null;
    try { value = await probe(); } catch { value = null; }
    if (value) return value;
    if (Date.now() > deadline) throw new Error(`Timed out waiting for ${label}`);
    await sleep(intervalMs);
  }
}
const digest = (bytes: Uint8Array | string) => createHash('sha256').update(bytes).digest('hex');

// ---------- Deployment layout ----------
type Deployment = { project: string; envFile: string; state: string; pool: Pool; controlPort: number; origin: string; secrets: string };
const dirs = { secrets: join(root, 'secrets'), state: join(root, 'state'), state2: join(root, 'state-restored'), work: join(root, 'work'), git: join(root, 'git'), backups: join(root, 'backups'), legacy: join(root, 'legacy') };
const secrets = {
  webhook1: randomBytes(32).toString('hex'), webhook2: randomBytes(32).toString('hex'),
  client1: randomBytes(20).toString('hex'), client2: randomBytes(20).toString('hex'),
  postgres: randomBytes(24).toString('hex'), s3Key: `ex${randomBytes(6).toString('hex')}`, s3Secret: randomBytes(24).toString('hex'),
  keyA: generateKeyPairSync('rsa', { modulusLength: 2048 }), keyB: generateKeyPairSync('rsa', { modulusLength: 2048 }),
};
const pem = (pair: typeof secrets.keyA, kind: 'private' | 'public') => kind === 'private'
  ? pair.privateKey.export({ type: 'pkcs1', format: 'pem' }).toString() : pair.publicKey.export({ type: 'spki', format: 'pem' }).toString();
function writeSecret(name: string, value: string): void {
  // Replace atomically, as an operator should, so a reader never sees a partial file.
  const path = join(dirs.secrets, name), next = `${path}.next`;
  writeFileSync(next, value, { mode: 0o600 }); chmodSync(next, 0o600);
  execFileSync('mv', ['-f', next, path]);
}

function envFile(name: string, values: { state: string; controlPort: number; pgPort: number; s3Port: number }): string {
  const path = join(root, `${name}.env`);
  writeFileSync(path, [
    `PROOFCI_CONTROL_IMAGE=${image}`, `PROOFCI_ORIGIN=http://127.0.0.1:${values.controlPort}`, `PROOFCI_PORT=${values.controlPort}`,
    `GITHUB_APP_ID=${app.id}`, `GITHUB_CLIENT_ID=${app.clientId}`, `PROOFCI_SECRETS_DIR=${dirs.secrets}`, `PROOFCI_STATE_DIR=${values.state}`,
    `PROOFCI_WORK_DIR=${dirs.work}`, `PROOFCI_DOCKER_GID=0`, `PROOFCI_S3_ACCESS_KEY=${secrets.s3Key}`, `PROOFCI_S3_SECRET_KEY=${secrets.s3Secret}`,
    `PROOFCI_EVIDENCE_RETENTION_DAYS=30`, `EX_PG_PORT=${values.pgPort}`, `EX_S3_PORT=${values.s3Port}`, `EX_GIT_DIR=${dirs.git}`,
    `EX_BACKUP_DIR=${dirs.backups}`, `EX_GITHUB_NETWORK=${network}`, `EX_GITHUB_URL=http://${simName}:8080`,
  ].join('\n') + '\n', { mode: 0o600 });
  return path;
}
function compose(deployment: Pick<Deployment, 'project' | 'envFile'>, args: string[], options: { allowFailure?: boolean; timeout?: number } = {}) {
  return sh('docker', ['compose', '-p', deployment.project, '--env-file', deployment.envFile, '-f', 'deploy/compose.yaml', '-f', 'deploy/exercise/compose.exercise.yaml', ...args], options);
}
function operator(deployment: Pick<Deployment, 'project' | 'envFile'>, command: string[], options: { allowFailure?: boolean; env?: Record<string, string> } = {}) {
  const extra = Object.entries(options.env ?? {}).flatMap(([key, value]) => ['-e', `${key}=${value}`]);
  return compose(deployment, ['run', '--rm', '--no-deps', ...extra, 'control', ...command], { allowFailure: options.allowFailure });
}

// ---------- GitHub simulator ----------
const sim = `http://127.0.0.1:${ports.sim}`;
async function simPost(path: string, body: unknown): Promise<void> {
  const response = await fetch(new URL(path, sim), { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(body) });
  if (!response.ok) throw new Error(`Simulator ${path} failed: ${response.status}`);
}
async function simState(): Promise<{ checks: Array<{ id: number; head_sha: string; external_id: string; status: string; conclusion: string | null; details_url: string; output: { title?: string; summary?: string } }>; rejectedJwts: number }> {
  return (await fetch(new URL('/admin/state', sim))).json() as never;
}
async function registerApp(keys: string[], clientSecrets: string[]): Promise<void> {
  await simPost('/admin/app', { appId: app.id, clientId: app.clientId, publicKeys: keys, clientSecrets, user: maintainer });
}
type Prepared = { repository: string; main: string; reviewed_sha256: string; pulls: Record<string, { head: string; base: string; merge: string; parents: string[]; pushed: boolean }> };
async function registerRepository(target: typeof ledgerRepo, prepared: Prepared): Promise<void> {
  const [owner, name] = target.name.split('/');
  await simPost('/admin/repo', { id: target.repositoryId, installationId: target.installationId, owner, name, defaultBranch: 'main' });
  await simPost('/admin/ref', { repoId: target.repositoryId, ref: 'refs/heads/main', sha: prepared.main });
  await simPost('/admin/commit', { repoId: target.repositoryId, sha: prepared.main, parents: [] });
  for (const [number, pull] of Object.entries(prepared.pulls)) {
    await simPost('/admin/commit', { repoId: target.repositoryId, sha: pull.merge, parents: pull.parents });
    await simPost('/admin/ref', { repoId: target.repositoryId, ref: `refs/pull/${number}/merge`, sha: pull.merge });
  }
}
async function openPull(target: typeof ledgerRepo, prepared: Prepared, number: number, state: 'open' | 'closed' = 'open'): Promise<void> {
  const pull = prepared.pulls[String(number)]!;
  await simPost('/admin/pull', { repoId: target.repositoryId, number, pull: { number, state, head: pull.head, headRepoId: target.repositoryId, base: pull.base, merge: pull.merge, mergeable: true } });
}

// ---------- Service interaction ----------
function signature(body: string, secret: string): string { return `sha256=${createHmac('sha256', secret).update(body).digest('hex')}`; }
async function webhook(deployment: Deployment, event: string, payload: unknown, secret: string): Promise<number> {
  const body = JSON.stringify(payload);
  const response = await fetch(`${deployment.origin}/webhooks/github`, { method: 'POST', body, headers: {
    'content-type': 'application/json', 'x-github-event': event, 'x-github-delivery': randomUUID(), 'x-hub-signature-256': signature(body, secret) } });
  return response.status;
}
function pullPayload(target: typeof ledgerRepo, number: number, action: string) {
  return { action, number, installation: { id: target.installationId }, repository: { id: target.repositoryId },
    pull_request: { number, base: { repo: { id: target.repositoryId } } } };
}
async function signIn(deployment: Deployment): Promise<string | null> {
  const login = await fetch(`${deployment.origin}/login`, { redirect: 'manual' });
  const binding = /proofci_login=([^;]+)/.exec(login.headers.get('set-cookie') ?? '')?.[1];
  const state = new URL(login.headers.get('location') ?? 'https://invalid').searchParams.get('state');
  if (!binding || !state) return null;
  const callback = await fetch(`${deployment.origin}/oauth/callback?state=${encodeURIComponent(state)}&code=exercise`, { redirect: 'manual', headers: { cookie: `proofci_login=${binding}` } });
  return /proofci_session=([^;]+)/.exec(callback.headers.get('set-cookie') ?? '')?.[1] || null;
}
async function enroll(deployment: Deployment, session: string, target: typeof ledgerRepo): Promise<number> {
  const response = await fetch(`${deployment.origin}/enroll`, { method: 'POST', body: `repository=${target.installationId}:${target.repositoryId}`,
    headers: { 'content-type': 'application/x-www-form-urlencoded', origin: deployment.origin, cookie: `proofci_session=${session}` } });
  return response.status;
}
type RunRow = { id: string; state: string; generation: number; applicable: boolean; report: Record<string, unknown> | null; first_started_at: Date | null; completed_at: Date | null; evidence_sha256: string | null; merge_head: string | null };
async function latestRun(deployment: Deployment, lane: string): Promise<RunRow | null> {
  const result = await deployment.pool.query<RunRow>(`SELECT r.id, r.state, r.generation, r.applicable, r.report, r.first_started_at, r.completed_at, coalesce(e.sha256, r.evidence_sha256) AS evidence_sha256, r.merge_head
    FROM proofci_runs r LEFT JOIN proofci_evidence e ON e.run_id=r.id AND e.state='ready' WHERE r.installation_id=$1 AND r.repository_id=$2 AND r.lane=$3 ORDER BY r.applicable DESC, r.created_at DESC LIMIT 1`, [scope.installationId, scope.repositoryId, lane]);
  return result.rows[0] ?? null;
}
async function publication(deployment: Deployment, runId: string) {
  return (await deployment.pool.query<{ pending: boolean; last_error: string | null; published_at: Date | null; revision: number }>('SELECT pending, last_error, published_at, revision FROM proofci_publications WHERE run_id=$1', [runId])).rows[0] ?? null;
}
async function waitForHttp(deployment: Deployment): Promise<void> {
  await waitFor('control service', async () => (await fetch(`${deployment.origin}/`)).ok, 180_000, 1000);
}
function vmContainers(): string[] {
  return sh('docker', ['ps', '--filter', 'name=proofci-vm-', '--format', '{{.Names}}']).stdout.split('\n').filter(Boolean);
}
function controlContainer(deployment: Deployment): string {
  return compose(deployment, ['ps', '-q', 'control']).stdout.trim();
}

/** Inspect the dispatcher process and the verifier VM container while a run is executing. */
function credentialIsolation(deployment: Deployment): Record<string, unknown> {
  const container = controlContainer(deployment);
  // Match only the Python dispatcher (argv[1] is service_execute.py), not this probe's own shell.
  const script = 'for p in /proc/[0-9]*; do if tr "\\0" "\\n" < $p/cmdline 2>/dev/null | sed -n 2p | grep -q "service_execute.py$"; then echo "PID ${p#/proc/}"; tr "\\0" "\\n" < $p/environ; fi; done';
  const processes = sh('docker', ['exec', container, 'sh', '-c', script]).stdout;
  const vm = vmContainers()[0];
  const vmInspect = vm ? JSON.parse(sh('docker', ['inspect', vm]).stdout)[0] : null;
  const values = [secrets.webhook1, secrets.webhook2, secrets.client1, secrets.client2, secrets.postgres, secrets.s3Secret, 'BEGIN RSA PRIVATE KEY', '/run/proofci-secrets'];
  const names = ['GITHUB_', 'DATABASE_URL', 'AWS_', 'PROOFCI_S3', 'PROOFCI_OPENAI'];
  const dispatcherEnv = processes.split('\n').filter(line => line.includes('='));
  const vmEnv: string[] = vmInspect?.Config?.Env ?? [];
  const vmMounts: string[] = (vmInspect?.Mounts ?? []).map((mount: { Source: string; Destination: string; RW: boolean }) => `${mount.Source}:${mount.Destination}:${mount.RW ? 'rw' : 'ro'}`);
  const leaked = [...dispatcherEnv, ...vmEnv, ...vmMounts].filter(line => values.some(value => line.includes(value)) || names.some(name => line.startsWith(name)));
  return { dispatcherFound: processes.includes('PID '), dispatcherEnvironment: dispatcherEnv.map(line => line.split('=')[0]), vmContainer: vm ?? null,
    vmNetwork: vmInspect?.HostConfig?.NetworkMode ?? null, vmEnvironment: vmEnv.map(line => line.split('=')[0]), vmMounts, vmReadOnlyMounts: (vmInspect?.Mounts ?? []).every((mount: { RW: boolean }) => !mount.RW), leaked };
}

async function waitForTerminal(deployment: Deployment, lane: string, minutes: number, cancelled = false): Promise<RunRow> {
  return waitFor(`${lane} to finish`, async () => {
    const run = await latestRun(deployment, lane);
    if (!run) return null;
    // Closing a pull request cancels or fails its run, and either way the run stops being applicable.
    if (cancelled) return ['cancelled', 'failed'].includes(run.state) && !run.applicable ? run : null;
    return run.applicable && ['completed', 'failed'].includes(run.state) ? run : null;
  }, minutes * 60_000, 5000);
}

/**
 * Wait for an applicable run that is executing in a verifier VM and stays the applicable run
 * across two baseline reconciliation intervals. See the README for the cancellation race this avoids.
 */
async function stableRunning(deployment: Deployment, lane: string): Promise<RunRow> {
  for (;;) {
    const run = await waitFor(`${lane} verifier VM`, async () => {
      const row = await latestRun(deployment, lane);
      return row?.applicable && row.state === 'running' && vmContainers().length > 0 ? row : null;
    }, 10 * 60_000, 2000);
    await sleep(12_000);
    const again = await latestRun(deployment, lane);
    if (again?.id === run.id && again.applicable && again.state === 'running') return again;
  }
}

/** Runs for one pull request that were cancelled although a later run verified the same inputs. */
async function spuriousCancellations(deployment: Deployment): Promise<number> {
  const result = await deployment.pool.query<{ count: string }>(`SELECT count(*) FROM proofci_runs a WHERE a.state='cancelled' AND a.kind='pull-request'
    AND EXISTS (SELECT 1 FROM proofci_runs b WHERE b.lane=a.lane AND b.repository_id=a.repository_id AND b.created_at > a.created_at
      AND b.head=a.head AND b.base=a.base AND b.merge_head IS NOT DISTINCT FROM a.merge_head AND b.baseline=a.baseline AND b.state <> 'cancelled')`);
  return Number(result.rows[0]?.count ?? 0);
}

/** Report identity, excluding the publication latency that publication itself records. */
function reportDigest(report: Record<string, unknown> | null): string {
  const scheduler = report?.scheduler && typeof report.scheduler === 'object' ? { ...(report.scheduler as Record<string, unknown>), publication_seconds: undefined } : undefined;
  return digest(JSON.stringify(report ? { ...report, scheduler } : null));
}

function properties(report: Record<string, unknown> | null): unknown {
  return Array.isArray(report?.results) ? (report!.results as Array<Record<string, unknown>>).map(item => ({ id: item.id, decision: item.decision, reason: item.reason })) : null;
}

async function main(): Promise<void> {
  for (const dir of Object.values(dirs)) mkdirSync(dir, { recursive: true, mode: 0o700 });
  mkdirSync(output, { recursive: true });
  const primary: Deployment = { project: `proofci-ex-${stamp}`, envFile: envFile('primary', { state: dirs.state, controlPort: ports.control, pgPort: ports.pg, s3Port: ports.s3 }),
    state: dirs.state, pool: new Pool({ host: '127.0.0.1', port: ports.pg, user: 'proofci', password: secrets.postgres, database: 'proofci', max: 4 }),
    controlPort: ports.control, origin: `http://127.0.0.1:${ports.control}`, secrets: dirs.secrets };
  const restored: Deployment = { project: `proofci-ex-${stamp}-restored`, envFile: envFile('restored', { state: dirs.state2, controlPort: ports.control2, pgPort: ports.pg2, s3Port: ports.s3b }),
    state: dirs.state2, pool: new Pool({ host: '127.0.0.1', port: ports.pg2, user: 'proofci', password: secrets.postgres, database: 'proofci', max: 4 }),
    controlPort: ports.control2, origin: `http://127.0.0.1:${ports.control2}`, secrets: dirs.secrets };
  // Teardown terminates server connections; idle pool clients must not crash the driver.
  for (const pool of [primary.pool, restored.pool]) pool.on('error', () => {});
  const environment: Record<string, unknown> = {
    host: sh('uname', ['-srm']).stdout.trim(), docker: sh('docker', ['version', '--format', '{{.Server.Os}}/{{.Server.Arch}} {{.Server.Version}}']).stdout.trim(),
    kvm: sh('docker', ['run', '--rm', '--device', '/dev/kvm', 'alpine:3.22', 'true'], { allowFailure: true }).code === 0,
    commit: sh('git', ['rev-parse', 'HEAD']).stdout.trim(), dirty: sh('git', ['status', '--porcelain']).stdout.trim().length > 0,
  };
  try {
    // ---------- Phase 1: clean deployment ----------
    const P1 = 'deploy';
    sh('docker', ['build', '-f', 'deploy/Dockerfile', '-t', image, '.'], { timeout: 1_800_000 });
    environment.controlImage = sh('docker', ['image', 'inspect', '--format', '{{.Id}}', image]).stdout.trim();
    environment.verifierImage = sh('docker', ['image', 'inspect', '--format', '{{.Id}}', 'proofci-vm-verifier']).stdout.trim();
    writeSecret('github-app.pem', pem(secrets.keyA, 'private'));
    writeSecret('github-client-secret', `${secrets.client1}\n`);
    writeSecret('github-webhook-secret', `${secrets.webhook1}\n`);
    writeSecret('postgres-password', `${secrets.postgres}\n`);
    writeSecret('database-url', `postgres://proofci:${secrets.postgres}@postgres:5432/proofci\n`);
    writeSecret('s3-credentials', `[default]\naws_access_key_id = ${secrets.s3Key}\naws_secret_access_key = ${secrets.s3Secret}\n`);
    sh('docker', ['network', 'create', network]);
    sh('docker', ['run', '-d', '--name', simName, '--network', network, '--read-only', '--user', '1000:1000', '-p', `127.0.0.1:${ports.sim}:8080`, image, 'node', 'deploy/exercise/github-sim.ts']);
    await waitFor('GitHub simulator', async () => (await fetch(new URL('/admin/state', sim))).ok, 60_000, 500);
    await registerApp([pem(secrets.keyA, 'public')], [secrets.client1]);

    const ledger = JSON.parse(sh('python3', ['deploy/exercise/prepare_repository.py', '--root', root, '--name', ledgerRepo.name, '--store', join(dirs.state, 'ledger.db'),
      '--actor', String(maintainer.id), '--pulls', '4', '--unpushed', '4']).stdout) as Prepared;
    const other = JSON.parse(sh('python3', ['deploy/exercise/prepare_repository.py', '--root', root, '--name', otherRepo.name, '--store', join(dirs.state, 'registry.db'),
      '--actor', String(maintainer.id)]).stdout) as Prepared;
    expect(P1, 'reviewed baselines activated through the pinned verifier', true, { ledger: ledger.reviewed_sha256, registry: other.reviewed_sha256 });
    const pilot = (state: string) => JSON.stringify([
      { installationId: ledgerRepo.installationId, repositoryId: ledgerRepo.repositoryId, store: join(state, 'ledger.db'), repository: ledger.repository, ref: 'refs/heads/main' },
      { installationId: otherRepo.installationId, repositoryId: otherRepo.repositoryId, store: join(state, 'registry.db'), repository: other.repository, ref: 'refs/heads/main' },
    ], null, 2);
    writeFileSync(join(dirs.state, 'pilot.json'), pilot(dirs.state), { mode: 0o644 });
    await registerRepository(ledgerRepo, ledger);
    await registerRepository(otherRepo, other);

    compose(primary, ['up', '-d', 'postgres', 'objects']);
    compose(primary, ['up', '--exit-code-from', 'bucket-init', 'bucket-init']);
    const preflight = operator(primary, ['node', 'src/preflight.ts'], { allowFailure: true });
    expect(P1, 'preflight reports no failures', preflight.code === 0, preflight.stdout.trim().split('\n'));
    compose(primary, ['up', '-d', 'control']);
    await waitForHttp(primary);
    const deployment = await primary.pool.query('SELECT schema_version, release, upgraded_from FROM proofci_deployment');
    expect(P1, 'fresh deployment records its schema', deployment.rows[0]?.schema_version === 2 && deployment.rows[0]?.upgraded_from === null, deployment.rows[0]);

    // ---------- Phase 2: maintainer enrollment over the real HTTP and OAuth path ----------
    const P2 = 'enroll';
    const session = await signIn(primary);
    expect(P2, 'maintainer signs in through OAuth', Boolean(session));
    expect(P2, 'ledger repository enrolled', await enroll(primary, session!, ledgerRepo) === 200);
    expect(P2, 'registry repository enrolled', await enroll(primary, session!, otherRepo) === 200);

    // ---------- Phase 3: real Lean-backed pull request run ----------
    const P3 = 'pull-request';
    await openPull(ledgerRepo, ledger, 1);
    expect(P3, 'signed pull_request webhook accepted', await webhook(primary, 'pull_request', pullPayload(ledgerRepo, 1, 'opened'), secrets.webhook1) === 204);
    await stableRunning(primary, 'pull/1');
    const isolation = credentialIsolation(primary);
    expect(P3, 'no credential reaches the dispatcher or the verifier VM', (isolation.leaked as string[]).length === 0 && isolation.dispatcherFound === true && isolation.vmNetwork === 'none' && isolation.vmReadOnlyMounts === true, isolation);
    const run1 = await waitForTerminal(primary, 'pull/1', 25);
    record(P3, 'real Lean run finished', run1.state === 'completed', { id: run1.id, state: run1.state, status: run1.report?.status, properties: properties(run1.report),
      elapsedSeconds: (run1.report?.dispatch as { elapsed_seconds?: number } | undefined)?.elapsed_seconds, virtualization: (run1.report?.execution as { virtualization?: string } | undefined)?.virtualization });
    expect(P3, 'run binds the GitHub test merge commit', run1.merge_head === ledger.pulls['1']!.merge && (run1.report?.envelope as { head?: string })?.head === ledger.pulls['1']!.merge);
    const published1 = await waitFor('PR 1 check', async () => (await simState()).checks.find(check => check.external_id === run1.id && check.status === 'completed'), 120_000);
    expect(P3, 'check published on the merge commit', published1.head_sha === ledger.pulls['1']!.merge, { conclusion: published1.conclusion, title: published1.output?.title, details: published1.details_url });
    const evidenceResponse = await fetch(`${primary.origin}/runs/${scope.installationId}/${scope.repositoryId}/${run1.id}/evidence`, { headers: { cookie: `proofci_session=${session}` } });
    const bundle = Buffer.from(await evidenceResponse.arrayBuffer());
    expect(P3, 'maintainer downloads hosted evidence', evidenceResponse.status === 200 && digest(bundle) === run1.evidence_sha256 && evidenceResponse.headers.get('x-proofci-sha256') === run1.evidence_sha256, { bytes: bundle.length, sha256: digest(bundle) });
    writeFileSync(join(root, 'run1-evidence.tar'), bundle);
    const crossRepository = await fetch(`${primary.origin}/runs/${otherRepo.installationId}/${otherRepo.repositoryId}/${run1.id}/evidence`, { headers: { cookie: `proofci_session=${session}` } });
    const anonymous = await fetch(`${primary.origin}/runs/${scope.installationId}/${scope.repositoryId}/${run1.id}/evidence`);
    expect(P3, 'evidence is not reachable through another repository or without a session', crossRepository.status === 404 && anonymous.status === 404);
    const replayOutput = join(root, 'run1-replay.json');
    const replay = sh('python3', ['portable/replay.py', 'replay', '--bundle', join(root, 'run1-evidence.tar'), '--sha256', digest(bundle), '--output', replayOutput], { allowFailure: true, timeout: 1_800_000 });
    let replayed: { status?: string } = {};
    try { replayed = JSON.parse(readFileSync(replayOutput, 'utf8')); } catch { replayed = { status: `no output: ${replay.stderr.slice(-300)}` }; }
    record(P3, 'downloaded bundle replays in a fresh verifier VM', replayed.status === 'reproduced', { exit: replay.code, status: replayed.status });

    // ---------- Phase 4: crash with accepted work, a pending publication, and an in-flight model attempt ----------
    const P4 = 'crash';
    await simPost('/admin/faults', { failCheckWrites: true });
    await openPull(ledgerRepo, ledger, 2);
    expect(P4, 'PR 2 webhook accepted', await webhook(primary, 'pull_request', pullPayload(ledgerRepo, 2, 'opened'), secrets.webhook1) === 204);
    const run2 = await waitForTerminal(primary, 'pull/2', 25);
    const pending2 = await waitFor('PR 2 publication failure', async () => { const item = await publication(primary, run2.id); return item?.pending && item.last_error ? item : null; }, 120_000);
    expect(P4, 'completed run with a failing publication stays pending', run2.state === 'completed' && pending2.pending, { run: run2.id, lastError: pending2.last_error });
    await openPull(ledgerRepo, ledger, 3);
    expect(P4, 'PR 3 webhook accepted', await webhook(primary, 'pull_request', pullPayload(ledgerRepo, 3, 'opened'), secrets.webhook1) === 204);
    const run3 = await stableRunning(primary, 'pull/3');
    const modelLedger = new ModelLedger(primary.pool);
    await modelLedger.setPolicy(scope, { enabled: true, private: true, sourceConsent: true, limits: { contextBytes: 65536, maxOutputPerCall: 2048,
      inputMicrosPerMillion: 150000, outputMicrosPerMillion: 600000, maxAttemptsPerObligation: 5,
      run: { inputTokens: 200000, outputTokens: 20000, costMicros: 100000 }, repository: { inputTokens: 2000000, outputTokens: 200000, costMicros: 1000000 } } });
    const leaseRow = (await primary.pool.query<{ generation: number; head: string; base: string; baseline: string; lane: string }>('SELECT generation, head, base, baseline, lane FROM proofci_runs WHERE id=$1', [run3.id])).rows[0]!;
    const lease = { id: run3.id, generation: leaseRow.generation, candidate: { kind: 'resolved', ...scope, lane: leaseRow.lane, head: leaseRow.head, base: leaseRow.base, baseline: leaseRow.baseline } } as Lease;
    const payload = digest('exercise model request');
    const sent = await modelLedger.reserve(lease, { obligation: 'increment', attempt: 1, payloadSha256: payload, requestBytes: 2048 });
    const begin = sent.kind === 'attempt' ? await modelLedger.beginSend(lease, sent.attempt.requestId) : null;
    const reserved = await modelLedger.reserve(lease, { obligation: 'increment', attempt: 2, payloadSha256: digest('second request'), requestBytes: 2048 });
    expect(P4, 'model attempt recorded as sending before the crash', begin?.kind === 'sending' && reserved.kind === 'attempt', { sending: begin?.kind === 'sending' ? begin.attempt.requestId : null });
    const before = { run2: { generation: run2.generation, started: run2.first_started_at?.toISOString(), completed: run2.completed_at?.toISOString(), report: reportDigest(run2.report), evidence: run2.evidence_sha256 },
      run3: { generation: run3.generation } };
    const victim = controlContainer(primary);
    sh('docker', ['update', '--restart', 'no', victim]);
    sh('docker', ['kill', '--signal', 'KILL', victim]);
    compose(primary, ['stop', 'control']);
    const orphans = vmContainers();
    record(P4, 'control process killed during verification', true, { orphanedVerifierContainers: orphans.length });

    // ---------- Phase 5: consistent backup of the stopped deployment ----------
    const P5 = 'backup';
    const full = join(dirs.backups, 'full'), scoped = join(dirs.backups, 'ledger-only');
    const fullResult = operator(primary, ['node', 'src/backup.ts', 'create', '--output', full]);
    const scopedResult = operator(primary, ['node', 'src/backup.ts', 'create', '--output', scoped, '--scope', `${scope.installationId}:${scope.repositoryId}`]);
    const fullManifest = JSON.parse(readFileSync(join(full, 'manifest.json'), 'utf8'));
    const scopedManifest = JSON.parse(readFileSync(join(scoped, 'manifest.json'), 'utf8'));
    expect(P5, 'full backup captures baselines, approvals, runs, evidence, reservations and pending publications', fullManifest.summary.active_baselines.length === 2 &&
      fullManifest.summary.evidence_references >= 2 && fullManifest.summary.pending_publications >= 1 && fullManifest.summary.reservations.model === 2, JSON.parse(fullResult.stdout));
    const scopedRows = readFileSync(join(scoped, 'database/proofci_repository_selections.jsonl'), 'utf8');
    expect(P5, 'scoped backup excludes the other repository', scopedManifest.stores.length === 1 && !scopedRows.includes(`"repository_id":${otherRepo.repositoryId}`) && scopedManifest.tables.proofci_installation_deliveries === 0, JSON.parse(scopedResult.stdout));
    const lockedOut = operator(primary, ['node', 'src/backup.ts', 'verify', '--input', full]);
    expect(P5, 'backup verifies offline', JSON.parse(lockedOut.stdout).verified === true);
    // Tampering with a copied row must be detected before any restore step.
    const tampered = join(dirs.backups, 'tampered');
    sh('cp', ['-R', full, tampered]);
    const runsFile = join(tampered, 'database/proofci_runs.jsonl');
    writeFileSync(runsFile, readFileSync(runsFile, 'utf8').replace(`"repository_id":${scope.repositoryId}`, `"repository_id":${otherRepo.repositoryId}`));
    const rejected = operator(primary, ['node', 'src/backup.ts', 'verify', '--input', tampered], { allowFailure: true });
    expect(P5, 'tampered backup is rejected', rejected.code !== 0, rejected.stderr.trim().split('\n').slice(-1)[0]);
    compose(primary, ['up', '-d', 'control']);
    await waitForHttp(primary);
    const busy = operator(primary, ['node', 'src/backup.ts', 'create', '--output', join(dirs.backups, 'while-running')], { allowFailure: true });
    expect(P5, 'backup refuses to run while the service is running', busy.code !== 0 && busy.stderr.includes('Stop every control process'), busy.stderr.trim().split('\n').slice(-2));

    // ---------- Phase 6: restart recovery on the original deployment ----------
    const P6 = 'recovery';
    await simPost('/admin/faults', { failCheckWrites: false });
    const published2 = await waitFor('PR 2 publication retry', async () => (await simState()).checks.find(check => check.external_id === run2.id && check.status === 'completed'), 180_000);
    const after2 = (await latestRun(primary, 'pull/2'))!;
    expect(P6, 'publication retried from the database without repeating proof construction', after2.id === run2.id && after2.generation === before.run2.generation &&
      after2.completed_at?.toISOString() === before.run2.completed && after2.first_started_at?.toISOString() === before.run2.started && reportDigest(after2.report) === before.run2.report && after2.evidence_sha256 === before.run2.evidence,
      { conclusion: published2.conclusion, generation: after2.generation });
    const recovered = await waitFor('PR 3 reclaim', async () => {
      const attempts = await modelLedger.attempts(run3.id);
      const row = await latestRun(primary, 'pull/3');
      return row && row.generation > before.run3.generation && attempts.find(item => item.attempt === 1)?.state === 'uncertain' ? { row, attempts } : null;
    }, 180_000);
    const first = recovered.attempts.find(item => item.attempt === 1)!;
    const second = recovered.attempts.find(item => item.attempt === 2)!;
    expect(P6, 'in-flight model attempt became uncertain and was not resent', first.state === 'uncertain' && first.sendCount === 1, { requestId: first.requestId, reason: first.reason });
    expect(P6, 'unsent reservation was preserved, not sent', second.state === 'reserved' && second.sendCount === 0);
    expect(P6, 'interrupted verification was reclaimed by a new generation', recovered.row.generation === before.run3.generation + 1);
    const diagnosis = JSON.parse(operator(primary, ['node', 'src/run-diagnose.ts', String(scope.installationId), String(scope.repositoryId)]).stdout);
    const d3 = diagnosis.runs.find((item: { run: string }) => item.run === run3.id);
    expect(P6, 'diagnostics report the uncertain attempt with reconciliation instructions', d3?.model?.uncertain?.[0] === first.requestId && typeof d3?.model?.action === 'string');
    // Close PR 3: the running reclaimed generation is cancelled; attempts close without a send.
    await openPull(ledgerRepo, ledger, 3, 'closed');
    expect(P6, 'PR 3 close webhook accepted', await webhook(primary, 'pull_request', pullPayload(ledgerRepo, 3, 'closed'), secrets.webhook1) === 204);
    const cancelled3 = await waitForTerminal(primary, 'pull/3', 5, true);
    const closedAttempts = await waitFor('PR 3 attempts to close', async () => {
      const attempts = await modelLedger.attempts(run3.id);
      return attempts.every(item => item.state !== 'reserved' && item.state !== 'sending') ? attempts : null;
    }, 180_000);
    expect(P6, 'cancelled run released its reservation without contacting the provider', cancelled3.state === 'cancelled' && closedAttempts.every(item => item.sendCount <= 1) && closedAttempts.find(item => item.attempt === 2)?.state === 'released',
      closedAttempts.map(item => ({ attempt: item.attempt, state: item.state, sendCount: item.sendCount })));
    const reconcile = operator(primary, ['node', 'src/model-attempts.ts', 'reconcile', String(scope.installationId), String(scope.repositoryId), first.requestId, 'not-processed']);
    expect(P6, 'operator reconciled the uncertain attempt from provider records', reconcile.stdout.includes('reconciled'));
    for (const name of orphans) sh('docker', ['rm', '-f', name], { allowFailure: true });

    // ---------- Phase 7: credential rotation ----------
    const P7 = 'rotation';
    // A file change can take a moment to reach the container through Docker Desktop file sharing; wait for it, bounded.
    const labeled = (secret: string) => webhook(primary, 'pull_request', pullPayload(ledgerRepo, 1, 'labeled'), secret);
    let rotationStarted = Date.now();
    writeSecret('github-webhook-secret', `${secrets.webhook2}\n${secrets.webhook1}\n`);
    await waitFor('new webhook secret', async () => await labeled(secrets.webhook2) === 204, 30_000, 250);
    const addSeconds = (Date.now() - rotationStarted) / 1000;
    const both = [await labeled(secrets.webhook2), await labeled(secrets.webhook1)];
    rotationStarted = Date.now();
    writeSecret('github-webhook-secret', `${secrets.webhook2}\n`);
    await waitFor('old webhook secret removal', async () => await labeled(secrets.webhook1) === 401, 30_000, 250);
    const removeSeconds = (Date.now() - rotationStarted) / 1000;
    const onlyNew = [await labeled(secrets.webhook2), await labeled(secrets.webhook1)];
    expect(P7, 'webhook secret rotates without a restart', both.join() === '204,204' && onlyNew.join() === '204,401', { duringRotation: both, afterRotation: onlyNew, secondsToAccept: addSeconds, secondsToReject: removeSeconds });
    // The App key and OAuth client secret were rotated at GitHub first: only the new ones are accepted.
    await registerApp([pem(secrets.keyB, 'public')], [secrets.client2]);
    const jwtBefore = (await simState()).rejectedJwts;
    await openPull(ledgerRepo, ledger, 4);
    expect(P7, 'PR 4 webhook accepted with the new secret', await webhook(primary, 'pull_request', pullPayload(ledgerRepo, 4, 'opened'), secrets.webhook2) === 204);
    await waitFor('rejected App JWTs', async () => (await simState()).rejectedJwts > jwtBefore, 60_000);
    const staleLogin = await signIn(primary);
    const stuck = await primary.pool.query<{ state: string; last_error: string | null }>("SELECT state, last_error FROM proofci_pull_deliveries WHERE installation_id=$1 AND repository_id=$2 AND pull_number=4", [scope.installationId, scope.repositoryId]);
    expect(P7, 'old App key and client secret stop working', staleLogin === null && (await latestRun(primary, 'pull/4')) === null, { delivery: stuck.rows[0] });
    writeSecret('github-app.pem', pem(secrets.keyB, 'private'));
    writeSecret('github-client-secret', `${secrets.client2}\n`);
    compose(primary, ['restart', 'control']);
    await waitForHttp(primary);
    const freshSession = await signIn(primary);
    expect(P7, 'OAuth works after rotating the client secret', Boolean(freshSession));
    const run4 = await waitForTerminal(primary, 'pull/4', 10);
    const published4 = await waitFor('PR 4 check', async () => (await simState()).checks.find(check => check.external_id === run4.id && check.status === 'completed'), 180_000);
    expect(P7, 'App publishing resumes with the new key', published4.conclusion === 'failure', { run: run4.id, state: run4.state, reason: run4.report?.reason });

    // ---------- Phase 8: operator diagnostics ----------
    const P8 = 'diagnostics';
    record(P8, 'known defect: runs cancelled and re-admitted with identical inputs (publication freshness race)', true, { count: await spuriousCancellations(primary) });
    const diagnostics = JSON.parse(operator(primary, ['node', 'src/run-diagnose.ts', String(scope.installationId), String(scope.repositoryId)]).stdout);
    const byRun = (id: string) => diagnostics.runs.find((item: { run: string }) => item.run === id);
    expect(P8, 'diagnostics distinguish proof failure, infrastructure failure and superseded runs',
      byRun(run1.id)?.outcome === (run1.report?.status === 'passed' ? 'passed' : 'proof_failure') && byRun(run4.id)?.outcome === 'infrastructure_failure' && byRun(run3.id)?.outcome === 'superseded',
      diagnostics.totals);
    writeFileSync(join(output, 'diagnostics.json'), JSON.stringify(diagnostics, null, 2) + '\n');

    // ---------- Phase 9: restore the crash-time backup into a new deployment ----------
    const P9 = 'restore';
    compose(primary, ['stop', 'control']);
    mkdirSync(dirs.state2, { recursive: true, mode: 0o700 });
    writeFileSync(join(dirs.state2, 'pilot.json'), pilot(dirs.state2), { mode: 0o644 });
    // The restored deployment has new, empty database and object volumes. GitHub still uses the rotated credentials.
    compose(restored, ['up', '-d', 'postgres', 'objects']);
    compose(restored, ['up', '--exit-code-from', 'bucket-init', 'bucket-init']);
    await waitFor('restored database', async () => (await restored.pool.query('SELECT 1')).rowCount === 1, 60_000);
    const restore = operator(restored, ['node', 'src/backup.ts', 'restore', '--input', full]);
    const compare = operator(restored, ['node', 'src/backup.ts', 'compare', '--input', full], { allowFailure: true });
    expect(P9, 'restored database matches the backup row for row', JSON.parse(compare.stdout).identical === true, JSON.parse(restore.stdout).summary);
    const describe = (store: string) => JSON.parse(sh('python3', ['deploy/store_snapshot.py', 'describe', store]).stdout);
    expect(P9, 'restored baseline and authority stores match the backup', JSON.stringify(describe(join(dirs.state2, 'ledger.db'))) === JSON.stringify(fullManifest.stores[0].description) &&
      JSON.stringify(describe(join(dirs.state2, 'registry.db'))) === JSON.stringify(fullManifest.stores[1].description));
    const again = operator(restored, ['node', 'src/backup.ts', 'restore', '--input', full], { allowFailure: true });
    expect(P9, 'restore refuses a non-empty database', again.code !== 0, again.stderr.trim().split('\n').slice(-1)[0]);
    compose(restored, ['up', '-d', 'control']);
    await waitForHttp(restored);
    const restoredSession = await signIn(restored);
    const restoredEvidence = await fetch(`${restored.origin}/runs/${scope.installationId}/${scope.repositoryId}/${run1.id}/evidence`, { headers: { cookie: `proofci_session=${restoredSession}` } });
    const restoredBytes = Buffer.from(await restoredEvidence.arrayBuffer());
    expect(P9, 'restored evidence downloads with the original digest', restoredEvidence.status === 200 && digest(restoredBytes) === digest(bundle));
    const restoredCross = await fetch(`${restored.origin}/runs/${otherRepo.installationId}/${otherRepo.repositoryId}/${run1.id}/evidence`, { headers: { cookie: `proofci_session=${restoredSession}` } });
    expect(P9, 'restored evidence stays repository scoped', restoredCross.status === 404);
    const restored2 = await waitFor('restored PR 2 publication', async () => { const item = await publication(restored, run2.id); return item && !item.pending ? item : null; }, 180_000);
    const restoredRun2 = (await latestRun(restored, 'pull/2'))!;
    expect(P9, 'restored pending publication completes without re-running proof construction', restoredRun2.generation === before.run2.generation && reportDigest(restoredRun2.report) === before.run2.report, { publishedAt: restored2.published_at });
    const restoredAttempts = await waitFor('restored PR 3 recovery', async () => {
      const attempts = await new ModelLedger(restored.pool).attempts(run3.id);
      return attempts.find(item => item.attempt === 1)?.state === 'uncertain' ? attempts : null;
    }, 180_000);
    expect(P9, 'restored in-flight attempt is uncertain, never resent', restoredAttempts.find(item => item.attempt === 1)!.sendCount === 1);
    await webhook(restored, 'pull_request', pullPayload(ledgerRepo, 3, 'closed'), secrets.webhook2);
    await waitForTerminal(restored, 'pull/3', 5, true);
    compose(restored, ['stop', 'control']);
    for (const name of vmContainers()) sh('docker', ['rm', '-f', name], { allowFailure: true });

    // ---------- Phase 10: upgrade compatibility ----------
    const P10 = 'upgrade';
    const previous = sh('git', ['merge-base', 'HEAD', 'origin/main']).stdout.trim();
    sh('sh', ['-c', `git archive ${previous} src package.json | tar -x -C ${dirs.legacy}`]);
    const admin = new Pool({ host: '127.0.0.1', port: ports.pg, user: 'proofci', password: secrets.postgres, database: 'proofci', max: 1 });
    for (const name of ['proofci_legacy', 'proofci_newer', 'proofci_report']) await admin.query(`CREATE DATABASE ${name}`);
    await admin.end();
    const legacyScript = `
      import { Pool } from 'pg';
      import { EnrollmentStore } from './src/enrollment-store.ts';
      import { RunStore } from './src/run-store.ts';
      import { ModelLedger } from './src/model-ledger.ts';
      const pool = new Pool({ connectionString: process.argv[2] });
      const selections = new EnrollmentStore(pool); await selections.initialize();
      const runs = new RunStore(pool); await runs.initialize(); await new ModelLedger(pool).initialize();
      const scope = { installationId: ${scope.installationId}, repositoryId: ${scope.repositoryId} };
      await selections.select(scope);
      const id = await runs.admit({ ...scope, kind: 'resolved', lane: 'legacy', head: '${ledger.main}', base: '${ledger.main}', baseline: '${'a'.repeat(64)}' });
      const lease = await runs.claim(60000);
      await runs.complete(lease, { version: 1, status: 'blocked', results: [{ id: 'increment', policy: 'required', decision: 'unproven', reason: 'legacy' }] });
      console.log(id); await pool.end();`;
    writeFileSync(join(dirs.legacy, 'make-legacy.ts'), legacyScript);
    const legacyUrl = (database: string) => `postgres://proofci:${secrets.postgres}@postgres:5432/${database}`;
    const runLegacy = (database: string) => sh('docker', ['run', '--rm', '--network', `${primary.project}_default`, '-v', `${dirs.legacy}:/legacy`, '-w', '/legacy', '--entrypoint', 'sh', image,
      '-c', `ln -sfn /opt/proofci/node_modules node_modules && node make-legacy.ts ${legacyUrl(database)}`]).stdout.trim();
    const legacyRun = runLegacy('proofci_legacy');
    runLegacy('proofci_newer'); runLegacy('proofci_report');
    const upgradeEnv = (database: string): Record<string, string> => ({ DATABASE_URL_FILE: '', DATABASE_URL: legacyUrl(database) });
    const preUpgrade = operator(primary, ['node', 'src/preflight.ts'], { allowFailure: true, env: upgradeEnv('proofci_legacy') });
    expect(P10, 'preflight announces the pending upgrade', preUpgrade.stdout.includes('will be upgraded'), preUpgrade.stdout.split('\n').find(line => line.includes('database')));
    // Start this release against the previous release's database, then stop it.
    // GitHub is unreachable during these checks, so the temporary service cannot schedule work.
    await simPost('/admin/faults', { unavailable: true });
    const upgradeProcess = startTemporary(primary, upgradeEnv('proofci_legacy'));
    await waitFor('upgraded service', async () => upgradeProcess.output().includes('listening'), 120_000, 1000);
    upgradeProcess.stop();
    await waitFor('upgraded service to stop', async () => upgradeProcess.exited(), 60_000, 500);
    const legacyPool = new Pool({ host: '127.0.0.1', port: ports.pg, user: 'proofci', password: secrets.postgres, database: 'proofci_legacy', max: 1 });
    const upgraded = (await legacyPool.query('SELECT schema_version, upgraded_from, release FROM proofci_deployment')).rows[0];
    const legacyReport = (await legacyPool.query('SELECT state, report FROM proofci_runs WHERE id=$1', [legacyRun])).rows[0];
    await legacyPool.end();
    expect(P10, 'previous-release database upgrades in place and keeps its reports', upgraded?.schema_version === 2 && upgraded?.upgraded_from === 1 && legacyReport?.state === 'completed' && legacyReport?.report?.results?.[0]?.reason === 'legacy', upgraded);
    const newerPool = new Pool({ host: '127.0.0.1', port: ports.pg, user: 'proofci', password: secrets.postgres, database: 'proofci_newer', max: 1 });
    await newerPool.query("CREATE TABLE proofci_deployment (id INTEGER PRIMARY KEY CHECK (id = 1), schema_version INTEGER NOT NULL, release TEXT NOT NULL, upgraded_from INTEGER, updated_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp())");
    await newerPool.query("INSERT INTO proofci_deployment (id, schema_version, release) VALUES (1, 3, '0.24.0')");
    await newerPool.end();
    const refusedNewer = startTemporary(primary, upgradeEnv('proofci_newer'));
    const newerOutput = await waitFor('refusal', async () => refusedNewer.exited() ? refusedNewer.output() : null, 120_000, 1000);
    expect(P10, 'a database from a newer release is refused with instructions', newerOutput.includes('Downgrades are not supported') && newerOutput.includes('Roll back an upgrade'), newerOutput.split('\n').filter(line => line.includes('schema') || line.includes('Downgrades')).slice(0, 2));
    const reportPool = new Pool({ host: '127.0.0.1', port: ports.pg, user: 'proofci', password: secrets.postgres, database: 'proofci_report', max: 1 });
    await reportPool.query(`UPDATE proofci_runs SET report = jsonb_set(report, '{version}', '2')`);
    await reportPool.end();
    const refusedReport = startTemporary(primary, upgradeEnv('proofci_report'));
    const reportOutput = await waitFor('report refusal', async () => refusedReport.exited() ? refusedReport.output() : null, 120_000, 1000);
    expect(P10, 'an unsupported report format is refused with instructions', reportOutput.includes('report format other than version 1') && reportOutput.includes('Do not edit stored reports'));
  } finally {
    const summary = { exercise: 'ticket-23 self-hosted pilot', environment, started: new Date(started).toISOString(), minutes: Math.round((Date.now() - started) / 600) / 100,
      passed: log.filter(step => step.ok).length, failed: log.filter(step => !step.ok).length, steps: log };
    writeFileSync(join(output, 'exercise.json'), JSON.stringify(summary, null, 2) + '\n');
    writeFileSync(join(output, 'exercise.md'), markdown(summary));
    await Promise.all([primary.pool.end(), restored.pool.end()].map(item => item.catch(() => {})));
    await primary_cleanup();
  }
}

let cleanupProjects: Array<Pick<Deployment, 'project' | 'envFile'>> = [];
async function primary_cleanup(): Promise<void> {
  if (process.env.PROOFCI_EXERCISE_KEEP) { process.stdout.write(`Kept deployment state in ${root}\n`); return; }
  for (const deployment of cleanupProjects) compose(deployment, ['down', '-v', '--remove-orphans'], { allowFailure: true });
  sh('docker', ['rm', '-f', simName], { allowFailure: true });
  sh('docker', ['network', 'rm', network], { allowFailure: true });
  for (const name of vmContainers()) sh('docker', ['rm', '-f', name], { allowFailure: true });
  rmSync(root, { recursive: true, force: true });
}

/** Run the control service in the foreground with extra environment, for upgrade checks. */
function startTemporary(deployment: Pick<Deployment, 'project' | 'envFile'>, env: Record<string, string>) {
  const name = `${deployment.project}-upgrade-${randomUUID().slice(0, 8)}`;
  const args = ['compose', '-p', deployment.project, '--env-file', deployment.envFile, '-f', 'deploy/compose.yaml', '-f', 'deploy/exercise/compose.exercise.yaml',
    'run', '--rm', '--no-deps', '--name', name, ...Object.entries(env).flatMap(([key, value]) => ['-e', `${key}=${value}`]), '-e', 'PORT=3999', 'control', 'node', 'deploy/exercise/control-sim.ts'];
  const child = spawn('docker', args, { cwd: repo, stdio: ['ignore', 'pipe', 'pipe'] });
  let text = '', done = false;
  child.stdout.on('data', chunk => { text += chunk; });
  child.stderr.on('data', chunk => { text += chunk; });
  child.once('close', () => { done = true; });
  return { output: () => text, exited: () => done, stop: () => { sh('docker', ['stop', '-t', '20', name], { allowFailure: true }); } };
}

function markdown(summary: { environment: Record<string, unknown>; minutes: number; passed: number; failed: number; steps: Step[] }): string {
  const lines = ['# Ticket 23 operational exercise', '', `Duration: ${summary.minutes} minutes. Steps passed: ${summary.passed}. Failed: ${summary.failed}.`, '',
    '## Environment', '', ...Object.entries(summary.environment).map(([key, value]) => `- ${key}: \`${String(value)}\``), '', '## Steps', '',
    '| Phase | Step | Result |', '| --- | --- | --- |', ...summary.steps.map(step => `| ${step.phase} | ${step.name} | ${step.ok ? 'pass' : '**fail**'} |`), ''];
  return lines.join('\n');
}

process.on('unhandledRejection', error => { process.stderr.write(`${String(error)}\n`); });
cleanupProjects = [];
const projects = () => [`proofci-ex-${stamp}`, `proofci-ex-${stamp}-restored`].map((project, index) => ({ project, envFile: join(root, index === 0 ? 'primary.env' : 'restored.env') }));
cleanupProjects = projects();
await main().then(() => { process.stdout.write(`Exercise passed. Evidence: ${output}\n`); }, error => {
  process.stderr.write(`Exercise failed: ${error instanceof Error ? error.stack : String(error)}\n`);
  process.exitCode = 1;
});
