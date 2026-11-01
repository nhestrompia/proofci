import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, generateKeyPairSync, randomUUID } from 'node:crypto';
import { spawn } from 'node:child_process';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { createServer } from 'node:net';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { Pool } from 'pg';
import { EnrollmentStore } from '../src/enrollment-store.ts';
import { RunStore } from '../src/run-store.ts';
import { CreateBucketCommand, DeleteBucketCommand, S3Client } from '@aws-sdk/client-s3';

const database = process.env.PROOFCI_TEST_DATABASE_URL;
const endpoint = process.env.PROOFCI_TEST_S3_ENDPOINT;
test('the webhook persists a signed selected push before acknowledging it', { skip: !database || !endpoint, timeout: 30_000 }, async () => {
  if (!database || !endpoint) return;
  const bucket = `proofci-${randomUUID()}`;
  const s3 = new S3Client({ endpoint, region: 'us-east-1', forcePathStyle: true, credentials: { accessKeyId: 'test', secretAccessKey: 'test' } });
  await s3.send(new CreateBucketCommand({ Bucket: bucket }));
  const schema = `webhook_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: database });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const db = new URL(database); db.searchParams.set('options', `-c search_path=${schema}`);
  const pool = new Pool({ connectionString: db.toString() });
  const root = await mkdtemp(join(tmpdir(), 'proofci-http-test-'));
  let child: ReturnType<typeof spawn> | undefined;
  try {
    const enrollment = new EnrollmentStore(pool); await enrollment.initialize();
    const scope = { installationId: 1001, repositoryId: 1002 }; await enrollment.select(scope);
    const key = join(root, 'app.pem');
    const { privateKey } = generateKeyPairSync('rsa', { modulusLength: 2048 });
    await writeFile(key, privateKey.export({ type: 'pkcs8', format: 'pem' }), { mode: 0o600 });
    const config = join(root, 'pilot.json');
    await writeFile(config, JSON.stringify([{ ...scope, ref: 'refs/heads/main', store: join(root, 'baseline.db'), repository: 'https://github.com/example/fixture.git' }]), { mode: 0o600 });
    const listener = createServer(); await new Promise<void>(resolve => listener.listen(0, '127.0.0.1', resolve));
    const address = listener.address(); assert.ok(address && typeof address !== 'string');
    const port = address.port; await new Promise<void>((resolve, reject) => listener.close(error => error ? reject(error) : resolve()));
    child = spawn(process.execPath, ['src/server.ts'], { stdio: 'ignore', env: { ...process.env, DATABASE_URL: db.toString(), GITHUB_APP_ID: '1', GITHUB_PRIVATE_KEY_FILE: key, GITHUB_CLIENT_ID: 'test', GITHUB_CLIENT_SECRET: 'test', GITHUB_WEBHOOK_SECRET: 'test-secret', PROOFCI_ORIGIN: `http://127.0.0.1:${port}`, PROOFCI_LOCAL_PILOT_CONFIG: config, PROOFCI_S3_BUCKET: bucket, PROOFCI_S3_REGION: 'us-east-1', PROOFCI_S3_ENDPOINT: endpoint, AWS_ACCESS_KEY_ID: 'test', AWS_SECRET_ACCESS_KEY: 'test', PORT: String(port) } });
    const url = `http://127.0.0.1:${port}`;
    let ready = false;
    for (let attempt = 0; attempt < 100 && !ready; attempt++) {
      try { ready = (await fetch(url)).ok; } catch { await new Promise(resolve => setTimeout(resolve, 50)); }
    }
    assert.equal(ready, true);
    const body = JSON.stringify({ installation: { id: 1001 }, repository: { id: 1002 }, ref: 'refs/heads/main', deleted: false, after: 'a'.repeat(40) });
    const deliveryId = randomUUID();
    const signature = `sha256=${createHmac('sha256', 'test-secret').update(body).digest('hex')}`;
    const headers = { 'x-github-event': 'push', 'x-github-delivery': deliveryId, 'x-hub-signature-256': signature };
    assert.equal((await fetch(`${url}/webhooks/github`, { method: 'POST', headers: { ...headers, 'x-hub-signature-256': `sha256=${'0'.repeat(64)}` }, body })).status, 401);
    assert.equal((await fetch(`${url}/webhooks/github`, { method: 'POST', headers, body })).status, 204);
    assert.equal((await fetch(`${url}/webhooks/github`, { method: 'POST', headers, body })).status, 204);
    const deliveries = await new RunStore(pool).listDeliveries(scope);
    assert.equal(deliveries.filter(item => item.deliveryId === deliveryId).length, 1);
    const pullBody = JSON.stringify({ action: 'opened', installation: { id: 1001 }, repository: { id: 1002 }, number: 7, pull_request: { number: 7, base: { repo: { id: 1002 } } } });
    const pullHeaders = { 'x-github-event': 'pull_request', 'x-github-delivery': randomUUID(), 'x-hub-signature-256': `sha256=${createHmac('sha256', 'test-secret').update(pullBody).digest('hex')}` };
    assert.equal((await fetch(`${url}/webhooks/github`, { method: 'POST', headers: pullHeaders, body: pullBody })).status, 204);
    assert.ok(await new RunStore(pool).inspectPull(scope, 7));
    assert.equal((await fetch(`${url}/pulls/1001/1002/7`)).status, 404);
    assert.equal((await fetch(`${url}/runs/1001/1002/${randomUUID()}`)).status, 404);
  } finally {
    child?.kill('SIGKILL'); await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end();
    await s3.send(new DeleteBucketCommand({ Bucket: bucket })); s3.destroy();
    await rm(root, { recursive: true, force: true });
  }
});
