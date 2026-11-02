import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, randomUUID } from 'node:crypto';
import { chmodSync, mkdtempSync, renameSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { Pool } from 'pg';
import { WebhookSecrets, credential, parseWebhookSecrets, readCredentialFile } from '../src/credentials.ts';
import { diagnose } from '../src/diagnostics.ts';
import { TABLES, checkIsolation, compareDatabase, createBackup, restoreBackup, verifyBackup } from '../src/backup.ts';
import { SCHEMA_VERSION, checkStoredReports, checkUpgrade, holdExclusiveLock, holdServiceLock, recordSchema, schemaState } from '../src/deployment.ts';
import { EnrollmentStore } from '../src/enrollment-store.ts';
import { RunStore } from '../src/run-store.ts';
import { ModelLedger } from '../src/model-ledger.ts';

const sign = (body: string, secret: string) => `sha256=${createHmac('sha256', secret).update(body).digest('hex')}`;

test('webhook secrets rotate through the secret file without a restart', () => {
  const dir = mkdtempSync(join(tmpdir(), 'proofci-secrets-'));
  try {
    const path = join(dir, 'webhook');
    const [current, previous] = ['c'.repeat(40), 'p'.repeat(40)];
    writeFileSync(path, `${previous}\n`, { mode: 0o600 });
    const secrets = new WebhookSecrets({ GITHUB_WEBHOOK_SECRET_FILE: path });
    const body = Buffer.from('{"action":"opened"}');
    assert.equal(secrets.match(body, sign(body.toString(), previous)), previous);
    assert.equal(secrets.match(body, sign(body.toString(), current)), null);
    // Rotation: write a new file and rename it into place, as an operator should.
    writeFileSync(`${path}.next`, `${current}\n${previous}\n`, { mode: 0o600 }); renameSync(`${path}.next`, path);
    assert.equal(secrets.match(body, sign(body.toString(), current)), current);
    assert.equal(secrets.match(body, sign(body.toString(), previous)), previous);
    writeFileSync(`${path}.next`, `${current}\n`, { mode: 0o600 }); renameSync(`${path}.next`, path);
    assert.equal(secrets.match(body, sign(body.toString(), previous)), null);
    assert.equal(secrets.match(body, sign(body.toString(), current)), current);
    assert.equal(secrets.match(body, 'sha256=zz'), null);
    assert.deepEqual(new WebhookSecrets({ GITHUB_WEBHOOK_SECRET: 'legacy' }).current(), ['legacy']);
    assert.deepEqual(new WebhookSecrets({}).current(), []);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test('credential files are validated and preferred over plain settings', () => {
  const dir = mkdtempSync(join(tmpdir(), 'proofci-credential-'));
  try {
    const path = join(dir, 'secret');
    writeFileSync(path, 'from-file\n', { mode: 0o600 });
    assert.equal(credential({ NAME_FILE: path, NAME: 'plain' }, 'NAME'), 'from-file');
    assert.equal(credential({ NAME: 'plain' }, 'NAME'), 'plain');
    assert.equal(credential({}, 'NAME'), undefined);
    chmodSync(path, 0o666);
    assert.throws(() => readCredentialFile(path), /Invalid credential file/);
    assert.throws(() => readCredentialFile('relative'), /absolute/);
    assert.throws(() => parseWebhookSecrets('short\n'), /20 to 512/);
    assert.throws(() => parseWebhookSecrets(`${'a'.repeat(20)}\n${'a'.repeat(20)}\n`), /repeats/);
    assert.throws(() => parseWebhookSecrets(`${'a'.repeat(20)}\n${'b'.repeat(20)}\n${'c'.repeat(20)}\n`), /at most one previous/);
  } finally { rmSync(dir, { recursive: true, force: true }); }
});

test('diagnostics separate proof failures, infrastructure failures, and uncertain model attempts', () => {
  const scope = { installationId: 1, repositoryId: 2 };
  const blocked = { version: 1, status: 'blocked', results: [{ id: 'increment', policy: 'required', decision: 'unproven', reason: 'proof_failed' }] };
  assert.equal(diagnose({ id: 'a', state: 'completed', applicable: true, report: blocked }, null, null, scope).outcome, 'proof_failure');
  assert.equal(diagnose({ id: 'b', state: 'completed', applicable: true, report: { version: 1, status: 'passed', results: [] } }, null, null, scope).outcome, 'passed');
  assert.equal(diagnose({ id: 'c', state: 'failed', applicable: true, report: { version: 1, status: 'error', reason: 'worker_execution_failed' } }, null, null, scope).outcome, 'infrastructure_failure');
  assert.equal(diagnose({ id: 'd', state: 'failed', applicable: true, report: { version: 1, status: 'error', reason: 'candidate_superseded' } }, null, null, scope).outcome, 'superseded');
  assert.equal(diagnose({ id: 'e', state: 'cancelled', applicable: false, report: null }, null, null, scope).outcome, 'superseded');
  assert.equal(diagnose({ id: 'f', state: 'running', applicable: true, report: null }, null, null, scope).outcome, 'in_progress');
  // A blocked report without property results is not a proof judgment.
  assert.equal(diagnose({ id: 'g', state: 'completed', applicable: true, report: { version: 1, status: 'blocked' } }, null, null, scope).outcome, 'infrastructure_failure');
  const usage = { model_calls: 1, attempts: [{ request_id: 'r'.repeat(64), obligation: 'increment', attempt: 1, state: 'uncertain' as const, exact: null,
    charged_upper_bound: { inputTokens: 1, outputTokens: 1, costMicros: 1 }, validation: null, late: false, reason: 'response_not_recorded' }],
    exact: { inputTokens: 0, outputTokens: 0, costMicros: 0 }, upper_bound: { inputTokens: 1, outputTokens: 1, costMicros: 1 }, unknown_usage_attempts: 1, uncertain_attempts: 1, failed_attempts: 0 };
  const flagged = diagnose({ id: 'h', state: 'completed', applicable: true, report: blocked }, usage, null, scope);
  assert.equal(flagged.outcome, 'proof_failure');
  assert.deepEqual(flagged.model?.uncertain, ['r'.repeat(64)]);
  assert.match(flagged.model?.action ?? '', /model-attempts\.ts reconcile 1 2/);
});

test('backup isolation rejects rows, objects, and stores from another repository', () => {
  const run = { id: '00000000-0000-4000-8000-000000000001', installation_id: 1, repository_id: 2 };
  const evidence = { id: '00000000-0000-4000-8000-000000000002', run_id: run.id, object_key: `evidence/1/2/${run.id}/x.tar`, sha256: 'a'.repeat(64), state: 'ready' };
  const rows = { proofci_runs: [run], proofci_evidence: [evidence] };
  const item = { id: evidence.id, run_id: run.id, key: evidence.object_key, sha256: evidence.sha256, bytes: 1, state: 'ready', file: null };
  const description = { tables: [], repositories: ['https://github.com/o/r.git'], baselines: 1, active_revision: 1, active: null, authority: null, migrations: [] };
  const store = { installationId: 1, repositoryId: 2, repository: 'https://github.com/o/r.git', file: 'stores/1-2.db', description };
  checkIsolation({ scopes: [{ installationId: 1, repositoryId: 2 }], rows, evidence: [item], stores: [store] });
  assert.throws(() => checkIsolation({ scopes: [{ installationId: 1, repositoryId: 3 }], rows, evidence: [item], stores: [] }), /outside the backup scope/);
  assert.throws(() => checkIsolation({ scopes: 'all', rows, evidence: [{ ...item, key: `evidence/1/3/${run.id}/x.tar` }], stores: [] }), /does not match|outside its run/);
  const moved = { ...evidence, object_key: `evidence/1/3/${run.id}/x.tar` };
  assert.throws(() => checkIsolation({ scopes: 'all', rows: { ...rows, proofci_evidence: [moved] }, evidence: [{ ...item, key: moved.object_key }], stores: [] }), /outside its run repository/);
  assert.throws(() => checkIsolation({ scopes: 'all', rows, evidence: [], stores: [{ ...store, description: { ...description, repositories: ['https://github.com/o/other.git'] } }] }), /another repository/);
  assert.throws(() => checkIsolation({ scopes: 'all', rows: { ...rows, proofci_model_attempts: [{ run_id: run.id, installation_id: 1, repository_id: 3 }] }, evidence: [], stores: [] }), /another repository/);
  assert.throws(() => checkIsolation({ scopes: 'all', rows, evidence: [], stores: [store], repositories: [{ installationId: 1, repositoryId: 2, store: '/s', repository: 'https://github.com/o/x.git', ref: 'refs/heads/main', assistanceQuotaMicros: 0 }] }), /not configured for the same repository/);
  assert.ok(TABLES.some(table => table.name === 'proofci_model_attempts'));
});

const database = process.env.PROOFCI_TEST_DATABASE_URL;

async function schema(): Promise<{ pool: Pool; url: string; drop: () => Promise<void> }> {
  const name = `deploy_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: database });
  await admin.query(`CREATE SCHEMA ${name}`);
  const url = new URL(database!);
  url.searchParams.set('options', `-c search_path=${name}`);
  const pool = new Pool({ connectionString: url.toString() });
  return { pool, url: url.toString(), drop: async () => { await pool.end(); await admin.query(`DROP SCHEMA ${name} CASCADE`); await admin.end(); } };
}

test('schema versions upgrade legacy databases and refuse newer or incompatible ones', { skip: !database }, async () => {
  const { pool, drop } = await schema();
  try {
    assert.deepEqual(await schemaState(pool), { kind: 'fresh' });
    await new EnrollmentStore(pool).initialize();
    await new RunStore(pool).initialize();
    assert.deepEqual(await checkUpgrade(pool), { kind: 'upgrade', from: 1, release: null });
    await recordSchema(pool);
    assert.equal((await schemaState(pool)).kind, 'current');
    assert.equal((await pool.query('SELECT upgraded_from FROM proofci_deployment')).rows[0].upgraded_from, 1);
    const fresh = await schema();
    try {
      const initial = await checkUpgrade(fresh.pool);
      await new EnrollmentStore(fresh.pool).initialize();
      await recordSchema(fresh.pool, initial);
      assert.equal((await fresh.pool.query('SELECT upgraded_from FROM proofci_deployment')).rows[0].upgraded_from, null);
    } finally { await fresh.drop(); }
    await pool.query('UPDATE proofci_deployment SET schema_version=$1', [SCHEMA_VERSION + 1]);
    await assert.rejects(checkUpgrade(pool), /Downgrades are not supported/);
    await assert.rejects(recordSchema(pool), /Downgrades are not supported/);
    await pool.query('UPDATE proofci_deployment SET schema_version=0');
    await assert.rejects(checkUpgrade(pool), /cannot upgrade directly/);
    await pool.query('UPDATE proofci_deployment SET schema_version=$1', [SCHEMA_VERSION]);
    const selections = new EnrollmentStore(pool); const runs = new RunStore(pool);
    const scope = { installationId: 1, repositoryId: 2 };
    await selections.select(scope);
    await runs.admit({ ...scope, kind: 'resolved', lane: 'x', head: 'a'.repeat(40), base: 'a'.repeat(40), baseline: 'b'.repeat(64) });
    const lease = await runs.claim(60_000); assert.ok(lease);
    await runs.complete(lease, { version: 2, status: 'passed' });
    await assert.rejects(checkStoredReports(pool), /report format other than version 1/);
  } finally { await drop(); }
});

test('the service lock excludes backup while any control process runs', { skip: !database }, async () => {
  const { pool, drop } = await schema();
  try {
    const release = await holdServiceLock(pool);
    const second = await holdServiceLock(pool);
    const client = await pool.connect();
    try {
      await assert.rejects(holdExclusiveLock(client), /control service is running/);
      await release(); await second();
      await holdExclusiveLock(client);
      await assert.rejects(holdServiceLock(pool), /backup or restore holds/);
    } finally { client.release(); }
  } finally { await drop(); }
});

test('a database backup restores row for row into an empty schema', { skip: !database }, async () => {
  const source = await schema(), target = await schema();
  const dir = mkdtempSync(join(tmpdir(), 'proofci-backup-'));
  try {
    const selections = new EnrollmentStore(source.pool); const runs = new RunStore(source.pool); const ledger = new ModelLedger(source.pool);
    await selections.initialize(); await runs.initialize(); await ledger.initialize(); await recordSchema(source.pool);
    const scope = { installationId: 1, repositoryId: 2 };
    await selections.select(scope);
    const id = await runs.admit({ ...scope, kind: 'resolved', lane: 'pull/7', head: 'a'.repeat(40), base: 'c'.repeat(40), baseline: 'b'.repeat(64), pullHead: 'd'.repeat(40) });
    const lease = await runs.claim(60_000); assert.ok(lease);
    await ledger.setPolicy(scope, { enabled: true, private: false, sourceConsent: false, limits: { contextBytes: 65536, maxOutputPerCall: 100, inputMicrosPerMillion: 1, outputMicrosPerMillion: 1, maxAttemptsPerObligation: 5,
      run: { inputTokens: 100000, outputTokens: 1000, costMicros: 1000 }, repository: { inputTokens: 100000, outputTokens: 1000, costMicros: 1000 } } });
    const reserved = await ledger.reserve(lease, { obligation: 'increment', attempt: 1, payloadSha256: 'e'.repeat(64), requestBytes: 10 });
    assert.equal(reserved.kind, 'attempt');
    const output = join(dir, 'backup');
    const manifest = await createBackup({ DATABASE_URL: source.url }, output, 'all');
    assert.equal(manifest.summary.reservations.model, 1);
    assert.equal(manifest.summary.pending_publications, 1);
    await verifyBackup(output);
    await restoreBackup({ DATABASE_URL: target.url, PROOFCI_LOCAL_PILOT_CONFIG: '' }, output).then(() => assert.fail('runs without configured repository must be refused'), error => assert.match(String(error), /no configured repository/));
    const config = join(dir, 'pilot.json');
    writeFileSync(config, JSON.stringify([{ installationId: 1, repositoryId: 2, store: join(dir, 'unused.db'), repository: 'https://github.com/o/r.git', ref: 'refs/heads/main' }]), { mode: 0o644 });
    await restoreBackup({ DATABASE_URL: target.url, PROOFCI_LOCAL_PILOT_CONFIG: config }, output);
    assert.deepEqual(await compareDatabase({ DATABASE_URL: target.url }, output), []);
    assert.equal((await target.pool.query('SELECT state FROM proofci_runs WHERE id=$1', [id])).rows[0].state, 'running');
    await assert.rejects(restoreBackup({ DATABASE_URL: target.url, PROOFCI_LOCAL_PILOT_CONFIG: config }, output), /empty database/);
  } finally { rmSync(dir, { recursive: true, force: true }); await source.drop(); await target.drop(); }
});
