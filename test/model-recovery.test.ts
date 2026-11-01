import { test } from 'node:test';
import assert from 'node:assert/strict';
import { randomUUID } from 'node:crypto';
import { Pool } from 'pg';
import { RunStore, type Candidate, type Lease } from '../src/run-store.ts';
import { EnrollmentStore } from '../src/enrollment-store.ts';
import { ModelLedger, requestId, type ModelLimits } from '../src/model-ledger.ts';
import { ProviderRejected, repairObligation, requestModel, type ModelProvider } from '../src/model-broker.ts';
import { executeNext } from '../src/run-worker.ts';

const url = process.env.PROOFCI_TEST_DATABASE_URL;
const scope = { installationId: 1, repositoryId: 2 };
const request = { candidate: 'def increment (n : Nat) : Nat := n + 1', contract: 'theorem increment_gt (n : Nat) : increment n > n', diagnostic: 'proof_failed' };
const requestBytes = Buffer.byteLength(JSON.stringify(request));
const reservedIn = requestBytes + 4096;
const reservedCost = reservedIn + 100;
const limits = (runAttempts: number, repositoryAttempts = 100): ModelLimits => ({
  contextBytes: 8192, maxOutputPerCall: 100, inputMicrosPerMillion: 1_000_000, outputMicrosPerMillion: 1_000_000, maxAttemptsPerObligation: 5,
  run: { inputTokens: reservedIn * runAttempts, outputTokens: 100 * runAttempts, costMicros: reservedCost * runAttempts },
  repository: { inputTokens: reservedIn * repositoryAttempts, outputTokens: 100 * repositoryAttempts, costMicros: reservedCost * repositoryAttempts },
});

/** A deterministic model stub. Each call is recorded so tests can prove that no duplicate request was sent. */
function stub(options: { idempotent?: boolean; respond?: (call: number, requestId: string) => Promise<{ body: string; inputTokens: number; outputTokens: number }> } = {}) {
  const calls: string[] = [];
  const provider: ModelProvider = {
    idempotent: options.idempotent ?? false,
    available: () => true,
    send: async ({ requestId }) => { calls.push(requestId); return options.respond ? options.respond(calls.length, requestId) : { body: 'by omega', inputTokens: 10, outputTokens: 1 }; },
  };
  return { provider, calls };
}

async function setup(candidate: Candidate = { kind: 'head-snapshot', ...scope, lane: 'refs/heads/main', head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) }) {
  const schema = `model_test_${randomUUID().replaceAll('-', '')}`;
  const admin = new Pool({ connectionString: url });
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  const enrollment = new EnrollmentStore(pool);
  await enrollment.initialize();
  const store = new RunStore(pool);
  await store.initialize();
  await new ModelLedger(pool).initialize();
  await enrollment.select(scope);
  const runId = await store.admit(candidate);
  const lease = await store.claim(60_000);
  assert.ok(lease);
  /** Simulate a service restart: the lease lapses and a fresh process claims a new generation. */
  const restart = async (): Promise<{ lease: Lease; ledger: ModelLedger; store: RunStore }> => {
    await pool.query("UPDATE proofci_runs SET lease_until=clock_timestamp()-interval '1 second' WHERE id=$1", [runId]);
    const freshStore = new RunStore(pool);
    const next = await freshStore.claim(60_000);
    assert.ok(next);
    const ledger = new ModelLedger(pool);
    await ledger.recover(next);
    return { lease: next, ledger, store: freshStore };
  };
  const cleanup = async () => { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); };
  return { pool, store, enrollment, lease, runId, restart, cleanup, candidate };
}

const active = async () => true;

/** Wrap a ledger so one transition fails before it runs, or after it has committed. */
function crash(ledger: ModelLedger, method: 'reserve' | 'beginSend' | 'settle', after: boolean): ModelLedger {
  return new Proxy(ledger, { get(target, key) {
    const value = Reflect.get(target, key);
    if (key !== method) return typeof value === 'function' ? value.bind(target) : value;
    return async (...args: unknown[]) => {
      if (!after) throw new Error(`crash before ${method}`);
      await (value as (...args: unknown[]) => Promise<unknown>).apply(target, args);
      throw new Error(`crash after ${method}`);
    };
  } });
}

test('reservations, request IDs, usage, and completion persist across restart without resetting budgets', { skip: !url }, async () => {
  const { pool, lease, runId, restart, cleanup } = await setup();
  try {
    const ledger = new ModelLedger(pool);
    await ledger.setPolicy(scope, { enabled: true, private: false, sourceConsent: false, limits: limits(3) });
    const { provider, calls } = stub();
    const first = await requestModel({ ledger, provider, lease, obligation: 'increment', attempt: 1, request, ensureActive: active });
    assert.equal(first.kind, 'response');
    assert.equal(calls.length, 1);
    assert.deepEqual(calls, [requestId(runId, 'increment', 1)]);

    // Duplicate dispatch of the same logical attempt, including concurrent duplicates, converges on one record.
    const duplicate = await requestModel({ ledger: new ModelLedger(pool), provider, lease, obligation: 'increment', attempt: 1, request, ensureActive: active });
    assert.deepEqual(duplicate.kind === 'response' && [duplicate.reused, duplicate.body], [true, 'by omega']);
    const concurrent = await Promise.all([1, 2, 3].map(() => requestModel({ ledger: new ModelLedger(pool), provider, lease, obligation: 'increment', attempt: 2, request, ensureActive: active })));
    assert.equal(calls.length, 2);
    assert.ok(concurrent.every(item => item.kind === 'response' || item.kind === 'in_flight'));
    await assert.rejects(ledger.reserve(lease, { obligation: 'increment', attempt: 2, payloadSha256: 'f'.repeat(64), requestBytes }), /different request/);

    // The response for attempt 3 is lost before it is recorded.
    await assert.rejects(requestModel({ ledger: crash(ledger, 'settle', false), provider, lease, obligation: 'increment', attempt: 3, request, ensureActive: active }), /crash before settle/);
    assert.equal(calls.length, 3);

    const after = await restart();
    const attempts = await after.ledger.attempts(runId);
    assert.deepEqual(attempts.map(item => [item.attempt, item.state, item.requestId]), [
      [1, 'settled', requestId(runId, 'increment', 1)], [2, 'settled', requestId(runId, 'increment', 2)], [3, 'uncertain', requestId(runId, 'increment', 3)]]);
    assert.deepEqual(attempts[0]!.exact, { inputTokens: 10, outputTokens: 1, costMicros: 11 });
    assert.equal(attempts[2]!.exact, null);

    // The uncertain attempt is not resent, and its reservation keeps the run at its ceiling after recovery.
    const retried = await requestModel({ ledger: after.ledger, provider, lease: after.lease, obligation: 'increment', attempt: 3, request, ensureActive: active });
    assert.deepEqual([retried.kind, calls.length], ['uncertain', 3]);
    await after.ledger.setPolicy(scope, { enabled: true, private: false, sourceConsent: false, limits: limits(2) });
    const blocked = await requestModel({ ledger: after.ledger, provider, lease: after.lease, obligation: 'increment', attempt: 4, request, ensureActive: active });
    assert.deepEqual(blocked, { kind: 'exhausted', reason: 'run_budget' });
    assert.equal(calls.length, 3);

    const usage = await after.ledger.usage(runId);
    assert.ok(usage);
    assert.equal(usage.model_calls, 3);
    assert.equal(usage.uncertain_attempts, 1);
    assert.equal(usage.unknown_usage_attempts, 1);
    assert.deepEqual(usage.exact, { inputTokens: 20, outputTokens: 2, costMicros: 22 });
    assert.deepEqual(usage.upper_bound, { inputTokens: 20 + reservedIn, outputTokens: 102, costMicros: 22 + reservedCost });

    // Operator reconciliation records the provider's exact outcome without importing a response.
    assert.equal(await after.ledger.reconcile({ installationId: 1, repositoryId: 3 }, requestId(runId, 'increment', 3), { kind: 'not_processed' }), false);
    assert.equal(await after.ledger.reconcile(scope, requestId(runId, 'increment', 3), { kind: 'charged', inputTokens: 12, outputTokens: 3 }), true);
    const reconciled = await after.ledger.usage(runId);
    assert.deepEqual([reconciled?.unknown_usage_attempts, reconciled?.upper_bound], [0, { inputTokens: 32, outputTokens: 5, costMicros: 37 }]);
    const again = await requestModel({ ledger: after.ledger, provider, lease: after.lease, obligation: 'increment', attempt: 3, request, ensureActive: active });
    assert.deepEqual([again.kind, calls.length], ['failed', 3]);
  } finally { await cleanup(); }
});

test('repository ceilings span runs, and provider idempotency is used only when declared', { skip: !url }, async () => {
  const { pool, store, lease, runId, restart, cleanup, candidate } = await setup();
  try {
    const ledger = new ModelLedger(pool);
    await ledger.setPolicy(scope, { enabled: true, private: false, sourceConsent: false, limits: limits(5, 2) });
    let fail = true;
    const idempotent = stub({ idempotent: true, respond: async () => { if (fail) { fail = false; throw new Error('connection reset'); } return { body: 'by simp', inputTokens: 9, outputTokens: 2 }; } });
    const first = await requestModel({ ledger, provider: idempotent.provider, lease, obligation: 'increment', attempt: 1, request, ensureActive: active });
    assert.equal(first.kind, 'uncertain');
    const resent = await requestModel({ ledger, provider: idempotent.provider, lease, obligation: 'increment', attempt: 1, request, ensureActive: active });
    assert.equal(resent.kind, 'response');
    assert.deepEqual(idempotent.calls, [requestId(runId, 'increment', 1), requestId(runId, 'increment', 1)]);
    assert.deepEqual((await ledger.attempts(runId))[0]?.exact, { inputTokens: 9, outputTokens: 2, costMicros: 11 });

    const rejected = stub({ respond: async () => { throw new ProviderRejected('rate limited'); } });
    assert.equal((await requestModel({ ledger, provider: rejected.provider, lease, obligation: 'increment', attempt: 2, request, ensureActive: active })).kind, 'failed');
    assert.deepEqual((await ledger.attempts(runId))[1]?.exact, { inputTokens: 0, outputTokens: 0, costMicros: 0 });
    const timeout = stub({ respond: () => new Promise(() => {}) });
    const slow = await requestModel({ ledger, provider: timeout.provider, lease, obligation: 'increment', attempt: 3, request, ensureActive: active, timeoutMs: 20 });
    assert.deepEqual(slow.kind === 'uncertain' && slow.reason, 'provider_timeout');

    // A new run for the same repository cannot reset the repository ceiling.
    await store.admit({ ...candidate, head: 'd'.repeat(40) });
    const next = await restart();
    assert.notEqual(next.lease.id, runId);
    const denied = await requestModel({ ledger: next.ledger, provider: stub().provider, lease: next.lease, obligation: 'increment', attempt: 1, request, ensureActive: active });
    assert.deepEqual(denied, { kind: 'exhausted', reason: 'repository_budget' });
    assert.equal((await next.ledger.repositorySpending(scope)).costMicros, 11 + reservedCost);
  } finally { await cleanup(); }
});

test('cancellation, supersession, consent revocation, and removed access survive restart and fence late results', { skip: !url }, async () => {
  const { pool, store, enrollment, lease, runId, restart, cleanup, candidate } = await setup();
  try {
    const ledger = new ModelLedger(pool);
    await ledger.setPolicy(scope, { enabled: true, private: true, sourceConsent: false, limits: limits(5) });
    const { provider, calls } = stub();
    assert.deepEqual(await requestModel({ ledger, provider, lease, obligation: 'increment', attempt: 1, request, ensureActive: active }), { kind: 'denied', reason: 'consent_required' });
    await ledger.setPolicy(scope, { enabled: true, private: true, sourceConsent: true, limits: limits(5) });

    // A late response from an interrupted generation is accounted for but cannot be used by the newer generation.
    let release!: () => void;
    const held = stub({ respond: () => new Promise(resolve => { release = () => resolve({ body: 'by decide', inputTokens: 7, outputTokens: 1 }); }) });
    const pending = requestModel({ ledger, provider: held.provider, lease, obligation: 'increment', attempt: 1, request, ensureActive: active });
    while (held.calls.length === 0) await new Promise(resolve => setTimeout(resolve, 5));
    const next = await restart();
    assert.equal((await next.ledger.attempts(runId))[0]?.state, 'uncertain');
    release();
    assert.equal((await pending).kind, 'stale');
    const [late] = await next.ledger.attempts(runId);
    assert.deepEqual([late?.state, late?.late, late?.exact], ['settled', true, { inputTokens: 7, outputTokens: 1, costMicros: 8 }]);
    assert.equal((await requestModel({ ledger: next.ledger, provider, lease: next.lease, obligation: 'increment', attempt: 1, request, ensureActive: active })).kind, 'stale');
    assert.equal(await next.ledger.recordValidation(next.lease, late!.requestId, 'accepted'), false);
    assert.equal(calls.length, 0);

    // Consent revocation is durable and blocks a reserved attempt from being sent.
    const reserved = await next.ledger.reserve(next.lease, { obligation: 'increment', attempt: 2, payloadSha256: (await import('node:crypto')).createHash('sha256').update(JSON.stringify(request)).digest('hex'), requestBytes });
    assert.equal(reserved.kind, 'attempt');
    assert.equal(await new ModelLedger(pool).revokeConsent(scope), true);
    assert.deepEqual(await requestModel({ ledger: new ModelLedger(pool), provider, lease: next.lease, obligation: 'increment', attempt: 2, request, ensureActive: active }), { kind: 'denied', reason: 'consent_required' });
    await ledger.setPolicy(scope, { enabled: true, private: true, sourceConsent: true, limits: limits(5) });
    assert.equal(await ledger.disable(scope), true);
    assert.deepEqual(await requestModel({ ledger, provider, lease: next.lease, obligation: 'increment', attempt: 2, request, ensureActive: active }), { kind: 'denied', reason: 'disabled' });
    await ledger.setPolicy(scope, { enabled: true, private: true, sourceConsent: true, limits: limits(5) });

    // Cancellation persists across restart.
    assert.equal(await store.cancel(scope, runId), true);
    assert.deepEqual(await requestModel({ ledger: new ModelLedger(pool), provider, lease: next.lease, obligation: 'increment', attempt: 2, request, ensureActive: active }), { kind: 'denied', reason: 'inactive' });
    assert.equal(await new ModelLedger(pool).sweep(), 1);
    assert.equal((await ledger.attempts(runId))[1]?.state, 'released');

    // Supersession: a newer candidate on the lane fences the older run.
    await store.admit({ ...candidate, head: 'd'.repeat(40) });
    const superseded = await new RunStore(pool).claim(60_000);
    assert.ok(superseded);
    await store.admit({ ...candidate, head: 'e'.repeat(40) });
    assert.deepEqual(await requestModel({ ledger, provider, lease: superseded, obligation: 'increment', attempt: 1, request, ensureActive: active }), { kind: 'denied', reason: 'inactive' });

    // Removed repository access fences the newest run as well.
    const current = await new RunStore(pool).claim(60_000);
    assert.ok(current);
    await enrollment.remove(scope);
    assert.deepEqual(await requestModel({ ledger, provider, lease: current, obligation: 'increment', attempt: 1, request, ensureActive: active }), { kind: 'denied', reason: 'inactive' });
    assert.equal(calls.length, 0);
  } finally { await cleanup(); }
});

test('fault injection covers reservation, send, response persistence, validation, and publication handoff', { skip: !url }, async () => {
  const candidate: Candidate = { kind: 'resolved', ...scope, lane: 'pull/3', pullHead: '1'.repeat(40), head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
  const { pool, lease, runId, restart, cleanup } = await setup(candidate);
  try {
    const ledger = new ModelLedger(pool);
    await ledger.setPolicy(scope, { enabled: true, private: false, sourceConsent: false, limits: limits(5) });
    const { provider, calls } = stub({ respond: async call => ({ body: `candidate ${call}`, inputTokens: 10, outputTokens: 1 }) });
    const attempt = (target: typeof ledger, current: Lease, number: number) => requestModel({ ledger: target, provider, lease: current, obligation: 'increment', attempt: number, request, ensureActive: active });

    await assert.rejects(attempt(crash(ledger, 'reserve', false), lease, 1), /crash before reserve/);
    assert.deepEqual([await ledger.attempts(runId), calls.length], [[], 0]);
    await assert.rejects(attempt(crash(ledger, 'reserve', true), lease, 1), /crash after reserve/);
    let recovered = await restart();
    assert.equal((await recovered.ledger.attempts(runId))[0]?.state, 'reserved');
    assert.equal((await attempt(recovered.ledger, recovered.lease, 1)).kind, 'response');
    assert.equal(calls.length, 1);

    // The send marker commits but the process stops before the provider is reached: the outcome is uncertain.
    await assert.rejects(attempt(crash(ledger, 'beginSend', true), recovered.lease, 2), /crash after beginSend/);
    // The provider accepts the request but its response is never persisted.
    recovered = await restart();
    await assert.rejects(attempt(crash(ledger, 'settle', false), recovered.lease, 3), /crash before settle/);
    assert.equal(calls.length, 2);
    recovered = await restart();
    assert.deepEqual((await recovered.ledger.attempts(runId)).map(item => item.state), ['settled', 'uncertain', 'uncertain']);
    assert.deepEqual([(await attempt(recovered.ledger, recovered.lease, 2)).kind, (await attempt(recovered.ledger, recovered.lease, 3)).kind, calls.length], ['uncertain', 'uncertain', 2]);

    // Validation crashes after a paid response; the next generation validates the stored response instead of paying again.
    let validations = 0;
    await assert.rejects(repairObligation({ ledger: recovered.ledger, provider, lease: recovered.lease, obligation: 'increment', request, ensureActive: active,
      validate: async body => { validations++; if (body === 'candidate 1') return 'rejected'; throw new Error('validator crashed'); } }), /validator crashed/);
    assert.equal(calls.length, 3);
    const validated: string[] = [];
    recovered = await restart();
    const repaired = await repairObligation({ ledger: recovered.ledger, provider, lease: recovered.lease, obligation: 'increment', request, ensureActive: active,
      validate: async body => { validated.push(body); return body === 'candidate 3' ? 'accepted' : 'rejected'; } });
    assert.deepEqual([repaired.decision, repaired.reason, calls.length, validations], ['verified', 'verified', 3, 2]);
    assert.deepEqual(validated, ['candidate 3']);

    // Publication handoff: the final report carries the durable usage, and publication retries never call the model.
    await pool.query("UPDATE proofci_runs SET lease_until=clock_timestamp()-interval '1 second' WHERE id=$1", [runId]);
    const store = new RunStore(pool);
    assert.equal(await executeNext({ store, ledger: new ModelLedger(pool), authorize: async () => 'allowed', leaseMs: 60_000,
      execute: async (_candidate, _signal, ensureActive, _dispatch, current) => {
        const outcome = await repairObligation({ ledger: new ModelLedger(pool), provider, lease: current, obligation: 'increment', request, ensureActive,
          validate: async body => body === 'candidate 3' ? 'accepted' : 'rejected' });
        return { report: { version: 1, status: outcome.decision === 'verified' ? 'passed' : 'blocked', usage: { model_calls: 0 } }, evidence: null };
      } }), true);
    assert.equal(calls.length, 3);
    const first = await store.claimPublication(60_000);
    assert.ok(first);
    assert.equal(first.state, 'completed');
    const model = (first.report as { usage: { model: { model_calls: number; uncertain_attempts: number; unknown_usage_attempts: number; attempts: unknown[] } } }).usage.model;
    assert.deepEqual([model.model_calls, model.uncertain_attempts, model.unknown_usage_attempts, model.attempts.length], [4, 2, 2, 4]);
    // The publisher stops before finishing; a later claim reuses the persisted report.
    await pool.query("UPDATE proofci_publications SET lease_until=clock_timestamp()-interval '1 second' WHERE run_id=$1", [runId]);
    const second = await store.claimPublication(60_000);
    assert.deepEqual(second?.report, first.report);
    assert.equal(await store.finishPublication(second!), true);
    assert.equal(calls.length, 3);
  } finally { await cleanup(); }
});
