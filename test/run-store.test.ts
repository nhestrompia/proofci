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
    await enrollment.initialize(); await Promise.all([store.initialize(), new RunStore(pool).initialize()]);
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
    assert.equal(await store.complete(lease, { version: 1, status: 'completed' }), false);
    assert.equal(await store.complete(recovered, { version: 1, status: 'completed' }), true);
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
    const failedRun = await store.inspect(candidate, fourth);
    assert.equal(failedRun?.state, 'failed');
    const failedReport = failedRun?.report;
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
    await executeNext({ store: restarted, authorize: async () => 'allowed', leaseMs: 60_000, execute: async () => { executions++; return { report: { version: 1, status: 'blocked' } }; } });
    assert.equal(executions, 1);
    assert.equal(await executeNext({ store: restarted, authorize: async () => 'allowed', leaseMs: 60_000, execute: async () => { executions++; return { report: {} }; } }), false);
    assert.equal(await restarted.claimDelivery(60_000), null);
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('pull observations survive restart and fence superseded and closed fork runs', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const enrollment = new EnrollmentStore(pool), runs = new RunStore(pool);
    await enrollment.initialize(); await runs.initialize();
    const event = { deliveryId: randomUUID(), installationId: 1, repositoryId: 2, number: 5 };
    await enrollment.select(event);
    assert.equal(await runs.acceptPullDelivery(event), true);
    assert.equal(await runs.acceptPullDelivery(event), true);
    const delivery = await new RunStore(pool).claimPullDelivery(60_000);
    assert.ok(delivery);
    const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/5', number: 5, sourceRepositoryId: 3, head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    assert.equal(await runs.processPullDelivery(delivery, async () => candidate), true);
    const lease = await runs.claim(60_000);
    assert.ok(lease);
    assert.deepEqual(lease.candidate, candidate);
    assert.deepEqual(await runs.startDispatch(lease, async () => ({ started: true }), () => {}), { started: true });
    assert.equal(await runs.acceptPullDelivery({ ...event, deliveryId: randomUUID() }, false), true);
    const missingBaseline = await runs.claimPullDelivery(60_000);
    assert.ok(missingBaseline);
    await runs.processPullDelivery(missingBaseline, async () => 'baseline-unavailable');
    assert.equal(await runs.renew(lease, 60_000), false);
    assert.equal(await runs.findPull(event, 5), null);
    await runs.reconcilePulls(event, [5]);
    await runs.reconcilePulls(event, [5]);
    const pending = await pool.query("SELECT count(*)::int AS count FROM proofci_pull_deliveries WHERE pull_number=5 AND state IN ('queued','processing')");
    assert.equal(pending.rows[0].count, 1);
    const restored = await runs.claimPullDelivery(60_000);
    assert.ok(restored);
    await runs.processPullDelivery(restored, async () => candidate);
    const restoredLease = await runs.claim(60_000);
    assert.ok(restoredLease);
    assert.equal(await runs.acceptPullDelivery({ ...event, deliveryId: randomUUID() }), true);
    assert.equal(await runs.renew(restoredLease, 60_000), false);
    let oldStarted = false;
    await assert.rejects(runs.startDispatch(restoredLease, async () => { oldStarted = true; return {}; }, () => {}));
    assert.equal(oldStarted, false);
    const updated = await runs.claimPullDelivery(60_000);
    assert.ok(updated);
    assert.equal(await runs.processPullDelivery(updated, async () => ({ ...candidate, head: 'd'.repeat(40) })), true);
    assert.equal(await runs.renew(lease, 60_000), false);
    const next = await runs.claim(60_000);
    assert.ok(next);
    assert.equal(next.candidate.head, 'd'.repeat(40));
    assert.equal(await runs.acceptPullDelivery({ ...event, deliveryId: randomUUID() }), true);
    const closed = await runs.claimPullDelivery(60_000);
    assert.ok(closed);
    await runs.processPullDelivery(closed, async () => 'closed');
    assert.equal(await runs.renew(next, 60_000), false);
    let started = false;
    await assert.rejects(runs.startDispatch(next, async () => { started = true; return {}; }, () => {}));
    assert.equal(started, false);
    assert.equal(await runs.claim(60_000), null);
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('a close observed during PR resolution cannot resurrect the older candidate', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const selections = new EnrollmentStore(pool), runs = new RunStore(pool);
    await selections.initialize(); await runs.initialize();
    const event = { deliveryId: randomUUID(), installationId: 1, repositoryId: 2, number: 3 };
    await selections.select(event); await runs.acceptPullDelivery(event);
    const delivery = await runs.claimPullDelivery(60_000); assert.ok(delivery);
    const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/3', number: 3, sourceRepositoryId: 4, head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    let resume: () => void = () => {}, resolved: () => void = () => {};
    const waiting = new Promise<void>(resolve => { resume = resolve; });
    const entered = new Promise<void>(resolve => { resolved = resolve; });
    const processing = runs.processPullDelivery(delivery, async () => { resolved(); await waiting; return candidate; });
    await entered;
    await runs.acceptPullDelivery({ ...event, deliveryId: randomUUID() });
    resume();
    await processing;
    assert.equal(await runs.claim(60_000), null);
    const close = await runs.claimPullDelivery(60_000); assert.ok(close);
    assert.equal(close.deliveryId, delivery.deliveryId);
    await runs.processPullDelivery(close, async () => 'closed');
    assert.equal(await runs.claim(60_000), null);
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});


test('a destination push during the first PR lookup forces a fresh resolution', { skip: !url }, async () => {
  const schema = `run_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const { EnrollmentStore } = await import('../src/enrollment-store.ts');
    const selections = new EnrollmentStore(pool), runs = new RunStore(pool);
    await selections.initialize(); await runs.initialize();
    const event = { deliveryId: randomUUID(), installationId: 1, repositoryId: 2, number: 3 };
    await selections.select(event); await runs.acceptPullDelivery(event);
    const delivery = await runs.claimPullDelivery(60_000); assert.ok(delivery);
    const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/3', number: 3, sourceRepositoryId: 4, head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    let resume: () => void = () => {}, entered: () => void = () => {};
    const waiting = new Promise<void>(resolve => { resume = resolve; });
    const resolving = new Promise<void>(resolve => { entered = resolve; });
    const processing = runs.processPullDelivery(delivery, async () => { entered(); await waiting; return candidate; });
    await resolving;
    await runs.acceptDelivery({ deliveryId: randomUUID(), installationId: 1, repositoryId: 2, ref: 'refs/heads/main', head: 'd'.repeat(40), deleted: false }, false);
    resume(); await processing;
    assert.equal(await runs.claim(60_000), null);
    const retry = await runs.claimPullDelivery(60_000); assert.ok(retry);
    await runs.processPullDelivery(retry, async () => ({ ...candidate, base: 'd'.repeat(40) }));
    assert.equal((await runs.claim(60_000))?.candidate.base, 'd'.repeat(40));
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});
