import { test } from 'node:test';
import assert from 'node:assert/strict';
import { executeNext } from '../src/run-worker.ts';

test('a run denied at dispatch never invokes the executor', async () => {
  let invoked = false;
  let cancelled = false;
  const lease = { id: 'run', generation: 1, candidate: { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: 'main', head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) } };
  const store = { startDispatch: async (_lease: unknown, start: () => Promise<Record<string, unknown>>) => start(), claim: async () => lease, renew: async () => true, fail: async () => true, cancelLease: async () => { cancelled = true; return true; }, retry: async () => true, complete: async () => true };
  assert.equal(await executeNext({ store, authorize: async () => 'revoked', execute: async () => { invoked = true; return { report: {} }; }, leaseMs: 1000 }), true);
  assert.equal(invoked, false);
  assert.equal(cancelled, true);
});

test('a lost lease aborts the executor and cannot publish its late report', async () => {
  const lease = { id: 'run', generation: 1, candidate: { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: 'main', head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) } };
  let completed = false;
  let aborted = false;
  const store = { startDispatch: async (_lease: unknown, start: () => Promise<Record<string, unknown>>) => start(), claim: async () => lease, renew: async () => false, fail: async () => true, cancelLease: async () => true, retry: async () => true, complete: async () => { completed = true; return true; } };
  await executeNext({ store, authorize: async () => 'allowed', leaseMs: 30, execute: async (_candidate, signal) => {
    await new Promise<void>(resolve => signal.addEventListener('abort', () => { aborted = true; resolve(); }, { once: true }));
    return { report: { status: 'passed' } };
  } });
  assert.equal(aborted, true);
  assert.equal(completed, false);
});

test('transient execution errors are retried before the final failure', async () => {
  const candidate = { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: 'main', head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
  const outcomes: string[] = [];
  for (const generation of [1, 3]) {
    const lease = { id: 'run', generation, candidate };
    const store = { startDispatch: async (_lease: unknown, start: () => Promise<Record<string, unknown>>) => start(), claim: async () => lease, renew: async () => true, cancelLease: async () => true, complete: async () => true,
      retry: async () => { outcomes.push('retry'); return true; }, fail: async () => { outcomes.push('failed'); return true; } };
    await executeNext({ store, authorize: async () => 'allowed', execute: async () => { throw new Error('temporary'); }, leaseMs: 1000 });
  }
  assert.deepEqual(outcomes, ['retry', 'failed']);
});

test('authorized dispatch retains evidence for the leased run', async () => {
  const lease = { id: 'run', generation: 1, candidate: { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: 'main', head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) } };
  const report = { status: 'passed' };
  const bytes = Buffer.from('evidence');
  let dispatched = false;
  let saved = false;
  const store = { claim: async () => lease, renew: async () => true, fail: async () => true, cancelLease: async () => true, retry: async () => true, complete: async () => { throw new Error('evidence must be persisted'); },
    startDispatch: async (_lease: unknown, start: () => Promise<Record<string, unknown>>) => { dispatched = true; return start(); } };
  await executeNext({ store, authorize: async () => 'allowed', leaseMs: 1000,
    execute: async (_candidate, _signal, ensureActive, dispatch) => {
      assert.equal(await ensureActive(), true);
      return { report: await dispatch(async () => report), evidence: bytes };
    },
    evidence: { complete: async (actualLease, actualReport, actualBytes) => {
      assert.equal(actualLease, lease); assert.equal(actualReport, report); assert.equal(actualBytes, bytes); saved = true; return true;
    } },
  });
  assert.equal(dispatched, true);
  assert.equal(saved, true);
});


test('temporary authorization failure during dispatch retries the run', async () => {
  const lease = { id: 'run', generation: 1, candidate: { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: 'main', head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) } };
  let checks = 0;
  let retried = false;
  const store = { claim: async () => lease, renew: async () => true, fail: async () => { throw new Error('unexpected failure'); }, cancelLease: async () => true, retry: async () => { retried = true; return true; }, complete: async () => true,
    startDispatch: async (_lease: unknown, start: () => Promise<Record<string, unknown>>) => start() };
  await executeNext({ store, leaseMs: 1000, authorize: async () => ++checks === 1 ? 'allowed' : 'unavailable',
    execute: async (_candidate, _signal, ensureActive) => { await ensureActive(); return { report: { status: 'passed' } }; } });
  assert.equal(retried, true);
});
