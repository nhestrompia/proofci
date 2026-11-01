import { test } from 'node:test';
import assert from 'node:assert/strict';
import { Pool } from 'pg';
import { randomUUID } from 'node:crypto';
import { RunStore } from '../src/run-store.ts';

const url = process.env.PROOFCI_TEST_DATABASE_URL;
test('durable runs deduplicate, recover leases, fence stale completions, and persist cancellation', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  const store = new RunStore(pool);
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const enrollment = new EnrollmentStore(pool);
    await enrollment.initialize(); await store.initialize();
    await enrollment.select({ installationId: 1, repositoryId: 2 });
    const candidate = { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: 'refs/heads/main', head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    const first = await store.admit(candidate);
    assert.equal(await store.admit(candidate), first);
    const lease = await store.claim(10);
    assert.ok(lease);
    await pool.query("UPDATE proofci_runs SET lease_until = now() - interval '1 second' WHERE id = $1", [first]);
    const recovered = await new RunStore(pool).claim(60_000);
    assert.ok(recovered);
    assert.equal(recovered.id, first);
    assert.equal(recovered.candidate.head, candidate.head);
    assert.equal(await store.renew(lease, 60_000), false);
    assert.equal(await store.renew(recovered, 60_000), true);
    assert.ok(recovered.generation > lease.generation);
    assert.equal(await store.complete(lease, { version: 1, status: 'completed' }, Buffer.from('stale')), false);
    assert.equal(await store.complete(recovered, { version: 1, status: 'completed' }, Buffer.from('evidence')), true);
    assert.deepEqual(await new RunStore(pool).evidence(candidate, first), { bytes: Buffer.from('evidence'), sha256: 'ee8250fb76e094b34b471f13a73dbbe51d1ae142e9df59d7c0d31ec20f0a0a8e' });
    assert.equal(await store.evidence({ installationId: 1, repositoryId: 3 }, first), null);
    assert.equal((await store.inspect(candidate, first))?.state, 'completed');
    const second = await store.admit({ ...candidate, head: 'd'.repeat(40) });
    assert.notEqual(second, first);
    assert.equal(await store.cancel(candidate, second), true);
    assert.equal(await new RunStore(pool).claim(1000), null);
    assert.equal((await store.inspect(candidate, second))?.state, 'cancelled');
    const third = await store.admit({ ...candidate, head: 'e'.repeat(40) });
    const active = await store.claim(60_000);
    assert.ok(active);
    assert.equal(active.id, third);
    const fourth = await store.admit({ ...candidate, head: 'f'.repeat(40) });
    assert.equal((await store.inspect(candidate, third))?.state, 'cancelled');
    assert.equal(await store.complete(active, { version: 1, status: 'completed' }), false);
    const failed = await store.claim(60_000);
    assert.equal(failed?.id, fourth);
    assert.ok(failed);
    assert.equal(await store.fail(failed, 'worker_unavailable'), true);
    const failedReport = (await store.inspect(candidate, fourth))?.report;
    assert.ok(typeof failedReport === 'object' && failedReport !== null && 'reason' in failedReport);
    assert.equal(failedReport.reason, 'worker_unavailable');
    assert.ok('scheduler' in failedReport);
    const returned = await store.admit(candidate);
    assert.notEqual(returned, first);
    assert.equal(await store.admit(candidate), returned);
    const revoked = await store.claim(60_000);
    assert.ok(revoked);
    await enrollment.remove(candidate);
    assert.equal(await store.renew(revoked, 60_000), false);
    assert.equal(await store.complete(revoked, { status: 'passed' }), false);
    await assert.rejects(store.admit({ ...candidate, head: '1'.repeat(40) }));
    assert.equal(await store.claim(60_000), null);
    assert.equal((await store.inspect(candidate, returned))?.state, 'cancelled');
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('signed deliveries are stored only for a selected repository and retries are idempotent', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const enrollment = new EnrollmentStore(pool);
    const runs = new RunStore(pool);
    await enrollment.initialize(); await runs.initialize();
    const event = { deliveryId: randomUUID(), installationId: 41, repositoryId: 42, ref: 'refs/heads/main', head: 'a'.repeat(40), deleted: false };
    assert.equal(await runs.acceptDelivery(event), false);
    await enrollment.select(event);
    assert.equal(await runs.acceptDelivery(event), true);
    assert.equal(await runs.acceptDelivery(event), true);
    const delivery = await runs.claimDelivery(60_000);
    assert.equal(delivery?.deliveryId, event.deliveryId);
    assert.equal(await runs.claimDelivery(60_000), null);
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('processing a delivery atomically admits the current candidate and finishes the delivery', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const enrollment = new EnrollmentStore(pool);
    const runs = new RunStore(pool);
    await enrollment.initialize(); await runs.initialize();
    const event = { deliveryId: randomUUID(), installationId: 71, repositoryId: 72, ref: 'refs/heads/main', head: 'a'.repeat(40), deleted: false };
    await enrollment.select(event);
    await runs.acceptDelivery(event);
    const delivery = await runs.claimDelivery(60_000);
    assert.ok(delivery);
    const candidate = { kind: 'head-snapshot' as const, installationId: 71, repositoryId: 72, lane: event.ref, head: event.head, base: event.head, baseline: 'b'.repeat(64) };
    assert.equal(await runs.processDelivery(delivery, async () => candidate), true);
    assert.equal(await runs.claimDelivery(60_000), null);
    assert.deepEqual((await runs.claim(60_000))?.candidate, candidate);
    const staleEvent = { ...event, deliveryId: randomUUID() };
    assert.equal(await runs.acceptDelivery(staleEvent), true);
    const stale = await runs.claimDelivery(60_000);
    assert.ok(stale);
    await pool.query("UPDATE proofci_push_deliveries SET lease_until=clock_timestamp() - interval '1 second' WHERE delivery_id=$1", [stale.deliveryId]);
    assert.equal(await runs.processDelivery(stale, async () => candidate), false);
    const recovered = await runs.claimDelivery(60_000);
    assert.ok(recovered);
    assert.ok(recovered.generation > stale.generation);
    assert.equal(await runs.processDelivery(recovered, async () => candidate), true);
    const deletion = { ...event, deliveryId: randomUUID(), head: '0'.repeat(40), deleted: true };
    assert.equal(await runs.acceptDelivery(deletion), true);
    const deleted = await runs.claimDelivery(60_000);
    assert.ok(deleted);
    assert.equal(await runs.processDelivery(deleted, async () => 'deleted'), true);
    const prior = await runs.list(candidate);
    assert.equal(prior[0]?.state, 'cancelled');
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('a signed delivery survives restart and reaches the authorized executor once', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const { processPushEvent } = await import('../src/push-events.ts');
    const { resolveDelivery } = await import('../src/delivery-worker.ts');
    const { executeNext } = await import('../src/run-worker.ts');
    const { createHmac } = await import('node:crypto');
    const enrollment = new EnrollmentStore(pool);
    const store = new RunStore(pool);
    await enrollment.initialize(); await store.initialize();
    const scope = { installationId: 101, repositoryId: 102 };
    await enrollment.select(scope);
    const body = Buffer.from(JSON.stringify({ installation: { id: 101 }, repository: { id: 102 }, ref: 'refs/heads/main', deleted: false, after: 'a'.repeat(40) }));
    const signature = `sha256=${createHmac('sha256', 'secret').update(body).digest('hex')}`;
    const notification = { body, signature, secret: 'secret', event: 'push', deliveryId: randomUUID(), store };
    assert.equal(await processPushEvent(notification), true);
    assert.equal(await processPushEvent(notification), true);
    const restarted = new RunStore(pool);
    const delivery = await restarted.claimDelivery(60_000);
    assert.ok(delivery);
    const github = { installationAccess: async () => 'allowed' as const, resolveHead: async () => 'a'.repeat(40) };
    const baselines = { active: async () => 'b'.repeat(64) };
    await restarted.processDelivery(delivery, item => resolveDelivery({ delivery: item, selections: enrollment, github, baselines }));
    let executions = 0;
    await executeNext({ store: restarted, authorize: async () => 'allowed', leaseMs: 60_000, execute: async () => { executions++; return { report: { version: 1, status: 'blocked' }, evidence: null }; } });
    assert.equal(executions, 1);
    assert.equal(await executeNext({ store: restarted, authorize: async () => 'allowed', leaseMs: 60_000, execute: async () => { executions++; return { report: {}, evidence: null }; } }), false);
    assert.equal(await restarted.claimDelivery(60_000), null);
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('pull deliveries admit only current selected merge candidates and fence stale leases', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const enrollment = new EnrollmentStore(pool), runs = new RunStore(pool);
    await enrollment.initialize(); await runs.initialize();
    const scope = { installationId: 51, repositoryId: 52 };
    const event = { ...scope, deliveryId: randomUUID(), number: 7 };
    assert.equal(await runs.acceptPullDelivery(event), false);
    await enrollment.select(scope);
    assert.equal(await runs.acceptPullDelivery(event), true);
    assert.equal(await runs.acceptPullDelivery(event), true);
    assert.equal(await runs.acceptPullDelivery({ ...event, number: 8 }), false);
    const lease = await runs.claimPullDelivery(10);
    assert.ok(lease);
    await pool.query("UPDATE proofci_pull_deliveries SET lease_until=now()-interval '1 second'");
    const recovered = await runs.claimPullDelivery(60_000);
    assert.ok(recovered);
    const candidate = { ...scope, kind: 'resolved' as const, lane: 'pull/7', pullHead: '1'.repeat(40), head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    assert.equal(await runs.processPullDelivery(lease, async () => candidate), false);
    assert.equal(await runs.processPullDelivery(recovered, async () => candidate), true);
    assert.equal((await runs.list(scope)).length, 1);
    assert.equal(await runs.acceptPullDelivery({ ...event, deliveryId: randomUUID() }), true);
    const conflict = await runs.claimPullDelivery(60_000);
    assert.ok(conflict);
    assert.equal(await runs.processPullDelivery(conflict, async () => 'merge_conflict'), true);
    assert.equal((await runs.list(scope))[0].applicable, false);
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('publication outbox survives restart and fences an older run generation', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url }); await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const enrollment = new EnrollmentStore(pool), runs = new RunStore(pool);
    await enrollment.initialize(); await runs.initialize();
    const candidate = { kind: 'resolved' as const, installationId: 61, repositoryId: 62, lane: 'pull/3', pullHead: '1'.repeat(40), head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    await enrollment.select(candidate); const id = await runs.admit(candidate);
    let releaseLock: () => void = () => {};
    let acquired: () => void = () => {};
    const locked = new Promise<void>(resolve => { acquired = resolve; });
    const held = runs.withPublicationLock(id, async () => { acquired(); await new Promise<void>(resolve => { releaseLock = resolve; }); });
    await locked;
    assert.equal(await new RunStore(pool).withPublicationLock(id, async () => {}), false);
    releaseLock(); assert.equal(await held, true);
    const pending = await runs.claimPublication(60_000); assert.ok(pending);
    assert.equal(await runs.publicationCurrent(pending), true);
    const lease = await runs.claim(60_000); assert.ok(lease);
    assert.equal(await runs.publicationCurrent(pending), false);
    assert.equal(await runs.complete(lease, { version: 1, status: 'passed' }, Buffer.from('evidence')), true);
    assert.equal(await runs.finishPublication(pending), false);
    await runs.retryPublication(pending);
    await pool.query("UPDATE proofci_publications SET lease_until=now()-interval '1 second'");
    const final = await new RunStore(pool).claimPublication(60_000); assert.ok(final);
    assert.equal(final.id, id); assert.equal(final.state, 'completed');
    assert.equal(await runs.publicationCurrent(final), true);
    assert.equal(await runs.finishPublication(final), true);
    assert.equal(await new RunStore(pool).claimPublication(60_000), null);
    const report = (await runs.inspect(candidate, id))?.report;
    assert.ok(typeof report === 'object' && report !== null && 'scheduler' in report);
    assert.ok(typeof report.scheduler === 'object' && report.scheduler !== null && 'publication_seconds' in report.scheduler);
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('a failed publication retries the completed report without dispatching work again', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url }); await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const { publishNext } = await import('../src/publication-worker.ts');
    const enrollment = new EnrollmentStore(pool), runs = new RunStore(pool);
    await enrollment.initialize(); await runs.initialize();
    const candidate = { kind: 'resolved' as const, installationId: 81, repositoryId: 82, lane: 'pull/4', pullHead: '1'.repeat(40), head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    await enrollment.select(candidate); const id = await runs.admit(candidate);
    const lease = await runs.claim(60_000); assert.ok(lease);
    const report = { version: 1, status: 'passed', envelope: { head: candidate.head, base: candidate.base, baseline_sha256: candidate.baseline, candidate_sha256: 'd'.repeat(64) }, dispatch: { final_status: 0 }, support: { guarantee: 'Target', assumptions: [], exclusions: [], admitted_candidate: 'candidate.lean' }, results: [{ id: 'one', policy: 'required', decision: 'verified', reason: 'accepted', validation: { decision: 'verified', candidate_sha256: 'd'.repeat(64), contract_sha256: 'e'.repeat(64) } }] };
    assert.equal(await runs.complete(lease, report, Buffer.from('evidence')), true);
    let attempts = 0;
    const github = { resolvePullMerge: async () => ({ kind: 'resolved' as const, merge: candidate.head, base: candidate.base, head: candidate.pullHead }), invalidateCheck: async () => {}, publishCheck: async (_scope: unknown, input: { output: { conclusion: string } | null; fresh(): Promise<boolean> }) => {
      attempts++; assert.equal(input.output?.conclusion, 'success'); assert.equal(await input.fresh(), true);
      if (attempts === 1) throw new Error('transient');
    } };
    const options = { store: runs, github, baselines: { active: async () => candidate.baseline }, origin: 'https://example.com' };
    await assert.rejects(publishNext(options));
    await pool.query("UPDATE proofci_publications SET lease_until=now()-interval '1 second' WHERE run_id=$1", [id]);
    assert.equal(await publishNext(options), true);
    assert.equal(attempts, 2); assert.equal(await runs.claim(1000), null);
    assert.equal((await runs.inspect(candidate, id))?.state, 'completed');
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});
