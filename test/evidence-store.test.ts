import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash, randomUUID } from 'node:crypto';
import { CreateBucketCommand, DeleteBucketCommand, S3Client } from '@aws-sdk/client-s3';
import { Pool } from 'pg';
import { EnrollmentStore } from '../src/enrollment-store.ts';
import { RunStore } from '../src/run-store.ts';
import { EvidenceStore } from '../src/evidence-store.ts';
import { downloadEvidence } from '../src/evidence-access.ts';

const database = process.env.PROOFCI_TEST_DATABASE_URL;
const endpoint = process.env.PROOFCI_TEST_S3_ENDPOINT;

test('persisted evidence is scoped, immutable, and expires without changing the report', { skip: !database || !endpoint, timeout: 300_000 }, async () => {
  const schema = `evidence_${randomUUID().replaceAll('-', '')}`;
  const bucket = `proofci-${randomUUID()}`;
  const admin = new Pool({ connectionString: database });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: database, options: `-c search_path=${schema}` });
  const s3 = new S3Client({ endpoint, region: 'us-east-1', forcePathStyle: true, credentials: { accessKeyId: 'test', secretAccessKey: 'test' } });
  const root = await mkdtemp(join(tmpdir(), 'proofci-evidence-test-'));
  try {
    await s3.send(new CreateBucketCommand({ Bucket: bucket }));
    const archive = join(root, 'evidence.tar');
    const realBundle = process.env.PROOFCI_TEST_HOSTED_BUNDLE;
    let fixture;
    if (realBundle) {
      const original = await readFile(realBundle);
      const digest = createHash('sha256').update(original).digest('hex');
      const checked = JSON.parse(execFileSync('python3', ['portable/check_hosted_bundle.py', realBundle, digest], { encoding: 'utf8' }));
      fixture = { ...checked, digest };
      await writeFile(archive, original);
    } else fixture = JSON.parse(execFileSync('python3', ['test/create-evidence.py', archive], { encoding: 'utf8' }));
    const bytes = await readFile(archive);
    const selections = new EnrollmentStore(pool); const runs = new RunStore(pool);
    await selections.initialize(); await runs.initialize();
    const scope = { installationId: 11, repositoryId: 22 };
    await selections.select(scope);
    const candidate = { ...scope, kind: 'resolved' as const, lane: 'test', head: fixture.envelope.head, base: fixture.envelope.base, baseline: fixture.envelope.baseline_sha256 };
    const id = await runs.admit(candidate); const lease = await runs.claim(60_000); assert.ok(lease);
    const evidence = new EvidenceStore(runs, s3, bucket, 86400);
    const changed = Buffer.from(bytes); changed[512] ^= 1;
    const allowed = async () => true;
    await assert.rejects(evidence.complete(lease, fixture.report, changed, new AbortController().signal, allowed));
    await assert.rejects(evidence.complete(lease, { ...fixture.report, status: fixture.report.status === 'passed' ? 'blocked' : 'passed' }, bytes, new AbortController().signal, allowed));
    let checks = 0;
    assert.equal(await evidence.complete(lease, fixture.report, bytes, new AbortController().signal, async () => ++checks === 1), false);
    assert.deepEqual(await evidence.download(scope, id), { kind: 'missing' });
    await pool.query("UPDATE proofci_evidence SET created_at=clock_timestamp()-interval '3 hours' WHERE run_id=$1", [id]);
    await evidence.expire();
    assert.equal(await evidence.complete(lease, fixture.report, bytes, new AbortController().signal, allowed), true);
    assert.equal(await evidence.complete(lease, fixture.report, bytes, new AbortController().signal, allowed), false);
    assert.deepEqual(await evidence.download({ ...scope, repositoryId: 23 }, id), { kind: 'missing' });
    const downloaded = await evidence.download(scope, id); assert.equal(downloaded.kind, 'available');
    if (downloaded.kind !== 'available') throw new Error('Missing evidence');
    assert.deepEqual(Buffer.from(downloaded.bytes), bytes);
    assert.equal(downloaded.sha256, fixture.digest);
    if (realBundle) {
      const downloadedPath = join(root, 'downloaded.tar');
      await writeFile(downloadedPath, downloaded.bytes);
      const output = join(root, 'replay.json');
      execFileSync('python3', ['portable/replay.py', 'replay', '--bundle', downloadedPath, '--sha256', downloaded.sha256, '--output', output], { timeout: 240_000 });
      assert.equal(JSON.parse(await readFile(output, 'utf8')).status, 'reproduced');
    }
    const github = { checkMaintainerAccess: async () => 123, installationAccess: async () => 'allowed' as const };
    let actorAllowed = true;
    const sessions = { checkMaintainer: async () => actorAllowed ? 123 : null };
    const request = { scope, runId: id, session: 'session', github, sessions, selections, evidence };
    assert.equal((await downloadEvidence(request)).kind, 'available');
    actorAllowed = false;
    assert.deepEqual(await downloadEvidence(request), { kind: 'missing' });
    actorAllowed = true;
    assert.deepEqual(await downloadEvidence({ ...request, scope: { ...scope, repositoryId: 23 } }), { kind: 'missing' });
    const revokeDuringDownload = { download: async () => { actorAllowed = false; return downloaded; } };
    assert.deepEqual(await downloadEvidence({ ...request, evidence: revokeDuringDownload }), { kind: 'missing' });
    actorAllowed = true;
    const historical = await runs.inspect(scope, id);
    await pool.query("UPDATE proofci_evidence SET expires_at=clock_timestamp()-interval '1 second' WHERE run_id=$1", [id]);
    assert.deepEqual(await evidence.download(scope, id), { kind: 'expired' });
    await evidence.expire();
    assert.deepEqual(await evidence.download(scope, id), { kind: 'expired' });
    assert.deepEqual(await runs.inspect(scope, id), historical);
    await selections.remove(scope);
    assert.deepEqual(await evidence.download(scope, id), { kind: 'missing' });
  } finally {
    await s3.send(new DeleteBucketCommand({ Bucket: bucket })).catch(() => {}); s3.destroy();
    await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end();
    await rm(root, { recursive: true, force: true });
  }
});
