import { createPrivateKey } from 'node:crypto';
import { execFile } from 'node:child_process';
import { existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { GetBucketVersioningCommand, HeadBucketCommand, S3Client } from '@aws-sdk/client-s3';
import { Pool } from 'pg';
import { WebhookSecrets, credential, privateKeyPath, readCredentialFile } from './credentials.ts';
import { RELEASE, SCHEMA_VERSION, checkStoredReports, refusal, schemaState } from './deployment.ts';
import { readPilotConfiguration } from './pilot-configuration.ts';

const run = promisify(execFile);
const root = fileURLToPath(new URL('..', import.meta.url));
type Check = { name: string; status: 'ok' | 'warn' | 'fail'; detail: string };

/** Check a deployment without starting the service or changing any state. */
export async function preflight(env: NodeJS.ProcessEnv): Promise<Check[]> {
  const checks: Check[] = [];
  const check = async (name: string, work: () => Promise<string | { warn: string }>) => {
    try {
      const result = await work();
      checks.push(typeof result === 'string' ? { name, status: 'ok', detail: result } : { name, status: 'warn', detail: result.warn });
    } catch (error) { checks.push({ name, status: 'fail', detail: error instanceof Error ? error.message : String(error) }); }
  };
  const pythonEnv = { PATH: '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', PYTHONDONTWRITEBYTECODE: '1' };

  await check('release', async () => `ProofCI ${RELEASE}, schema ${SCHEMA_VERSION}, Node.js ${process.versions.node}`);
  await check('unprivileged user', async () => {
    if (process.getuid?.() === 0) throw new Error('The control service must not run as root; the VM launcher refuses root.');
    return `uid ${process.getuid?.() ?? 'unknown'}`;
  });
  await check('origin', async () => {
    const origin = new URL(env.PROOFCI_ORIGIN ?? '');
    const loopback = origin.protocol === 'http:' && ['127.0.0.1', 'localhost'].includes(origin.hostname);
    if (origin.protocol !== 'https:' && !loopback) throw new Error('PROOFCI_ORIGIN must be HTTPS or loopback HTTP');
    return origin.origin;
  });
  await check('GitHub App key', async () => {
    const key = createPrivateKey(readCredentialFile(privateKeyPath(env)));
    if (key.asymmetricKeyType !== 'rsa') throw new Error('The App private key must be an RSA key');
    if (!Number.isSafeInteger(Number(env.GITHUB_APP_ID)) || Number(env.GITHUB_APP_ID) < 1) throw new Error('Invalid GITHUB_APP_ID');
    return `App ${env.GITHUB_APP_ID}, ${key.asymmetricKeyDetails?.modulusLength ?? '?'}-bit key`;
  });
  await check('OAuth client', async () => {
    if (!env.GITHUB_CLIENT_ID || !credential(env, 'GITHUB_CLIENT_SECRET')) throw new Error('Set GITHUB_CLIENT_ID and GITHUB_CLIENT_SECRET_FILE');
    return env.GITHUB_CLIENT_ID;
  });
  await check('webhook secrets', async () => {
    const count = new WebhookSecrets(env).current().length;
    if (count === 0) throw new Error('Set GITHUB_WEBHOOK_SECRET_FILE');
    return count === 2 ? { warn: 'A previous webhook secret is still accepted. Remove it once GitHub uses the new secret.' } : 'one current secret';
  });
  await check('database', async () => {
    const url = credential(env, 'DATABASE_URL');
    if (!url) throw new Error('Set DATABASE_URL or DATABASE_URL_FILE');
    const pool = new Pool({ connectionString: url, max: 1 });
    try {
      const state = await schemaState(pool);
      const refused = refusal(state);
      if (refused) throw refused;
      await checkStoredReports(pool);
      if (state.kind === 'fresh') return 'empty database; the service will create schema version ' + SCHEMA_VERSION;
      if (state.kind === 'upgrade') return { warn: `schema ${state.from} will be upgraded to ${SCHEMA_VERSION} on start. Take a backup first (deploy/README.md).` };
      return `schema ${SCHEMA_VERSION}, last migrated by ${state.release}`;
    } finally { await pool.end(); }
  });
  const pilot = env.PROOFCI_LOCAL_PILOT_CONFIG;
  if (!pilot) checks.push({ name: 'pilot configuration', status: 'warn', detail: 'PROOFCI_LOCAL_PILOT_CONFIG is unset; only enrollment is served.' });
  else {
    let repositories: ReturnType<typeof readPilotConfiguration> = [];
    await check('pilot configuration', async () => { repositories = readPilotConfiguration(pilot); return `${repositories.length} repositories`; });
    for (const repository of repositories) {
      await check(`baseline store ${repository.installationId}:${repository.repositoryId}`, async () => {
        const { stdout } = await run('python3', [`${root}deploy/store_snapshot.py`, 'describe', repository.store], { env: pythonEnv, timeout: 30_000 });
        const description = JSON.parse(stdout);
        if (description.repositories.some((item: string) => item !== repository.repository)) throw new Error('The store contains another repository');
        if (!description.active) return { warn: 'no active baseline; runs cannot be scheduled' };
        if (description.authority?.pending) return { warn: 'a gateway head change is pending; managed runs are blocked until `authority_gateway.py recover`' };
        if (description.authority && !description.authority.enabled) return { warn: 'authority enrollment is disabled' };
        return `active ${description.active.reviewed_sha256.slice(0, 12)}, revision ${description.active_revision}, authority ${description.authority ? `epoch ${description.authority.epoch}` : 'not initialized'}`;
      });
    }
    await check('evidence bucket', async () => {
      const region = env.PROOFCI_S3_REGION, bucket = env.PROOFCI_S3_BUCKET, endpoint = env.PROOFCI_S3_ENDPOINT;
      if (!region || !bucket) throw new Error('Set PROOFCI_S3_REGION and PROOFCI_S3_BUCKET');
      const s3 = new S3Client({ region, endpoint, forcePathStyle: Boolean(endpoint) });
      try {
        await s3.send(new HeadBucketCommand({ Bucket: bucket }));
        const versioning = await s3.send(new GetBucketVersioningCommand({ Bucket: bucket }));
        if (versioning.Status) throw new Error('Bucket versioning must never have been enabled');
        return bucket;
      } finally { s3.destroy(); }
    });
    await check('retention', async () => {
      const days = Number(env.PROOFCI_EVIDENCE_RETENTION_DAYS ?? '30');
      if (!Number.isInteger(days) || days < 1 || days > 3650) throw new Error('PROOFCI_EVIDENCE_RETENTION_DAYS must be 1 to 3650');
      return `${days} days`;
    });
  }
  await check('python', async () => {
    const { stdout } = await run('python3', ['-c', 'import sys; print("%d.%d" % sys.version_info[:2])'], { env: pythonEnv, timeout: 10_000 });
    const [major, minor] = stdout.trim().split('.').map(Number);
    if (major !== 3 || minor! < 11) throw new Error(`Python 3.11 or later is required, found ${stdout.trim()}`);
    return stdout.trim();
  });
  await check('git', async () => (await run('git', ['--version'], { env: pythonEnv, timeout: 10_000 })).stdout.trim());
  await check('verifier image', async () => {
    const { stdout: pinned } = await run('python3', ['-c', 'import sys; sys.path.insert(0, sys.argv[1]); import vm_container; print(vm_container.VM_IMAGE_ID)', `${root}portable`], { env: pythonEnv, timeout: 10_000 });
    if (env.PROOFCI_APPLE_RUNTIME) return { warn: `Apple container runtime configured; the launcher checks image ${pinned.trim()} and the kernel digest at each run` };
    const dockerEnv = { ...pythonEnv, ...(env.DOCKER_HOST ? { DOCKER_HOST: env.DOCKER_HOST } : {}) };
    const { stdout } = await run('docker', ['image', 'inspect', '--format', '{{.Id}}', 'proofci-vm-verifier'], { env: dockerEnv, timeout: 20_000 });
    if (stdout.trim() !== pinned.trim()) throw new Error(`proofci-vm-verifier is ${stdout.trim()}, but this release pins ${pinned.trim()}`);
    return pinned.trim();
  });
  await check('hardware virtualization', async () => {
    if (env.PROOFCI_APPLE_RUNTIME) return 'Apple virtualization';
    if (existsSync('/dev/kvm')) return '/dev/kvm available';
    return { warn: '/dev/kvm is unavailable. The verifier VM falls back to software emulation, which can exceed the fixed obligation budget and report blocked results.' };
  });
  return checks;
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const checks = await preflight(process.env);
  for (const item of checks) process.stdout.write(`${item.status.toUpperCase().padEnd(4)} ${item.name}: ${item.detail}\n`);
  if (checks.some(item => item.status === 'fail')) process.exitCode = 1;
}
