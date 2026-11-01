import { test } from 'node:test';
import assert from 'node:assert/strict';
import { decisionMatches, type ForkDecision } from '../src/fork-policy.ts';

const decision: ForkDecision = { installationId: 1, repositoryId: 2, number: 3, sourceRepositoryId: 4, head: 'a'.repeat(40), mergeHead: 'd'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64), baselineRevision: 1, selectionGeneration: 'selection', policyDigest: 'd'.repeat(64), quotaMicros: 100, maintainerId: 5, consent: true, authorityEpoch: null };
test('fork decisions require exact inputs, consent and available quota', () => {
  assert.equal(decisionMatches(decision, decision, 99), true);
  assert.equal(decisionMatches(decision, decision, 100), false);
  for (const change of [{ head: 'e'.repeat(40) }, { mergeHead: 'e'.repeat(40) }, { base: 'e'.repeat(40) }, { baseline: 'e'.repeat(64) }, { baselineRevision: 2 }, { policyDigest: 'e'.repeat(64) }, { selectionGeneration: 'new' }, { sourceRepositoryId: 8 }, { number: 4 }, { repositoryId: 9 }, { consent: false }]) {
    assert.equal(decisionMatches(decision, { ...decision, ...change }, 0), false);
  }
});

test('maintainer approval is scoped to an active fork and cancellation revokes request eligibility', { skip: !process.env.PROOFCI_TEST_DATABASE_URL }, async () => {
  const { Pool } = await import('pg');
  const { randomUUID } = await import('node:crypto');
  const { EnrollmentStore } = await import('../src/enrollment-store.ts');
  const { RunStore } = await import('../src/run-store.ts');
  const { ForkPolicy } = await import('../src/fork-policy.ts');
  const url = process.env.PROOFCI_TEST_DATABASE_URL;
  const admin = new Pool({ connectionString: url });
  const schema = `fork_test_${randomUUID().replaceAll('-', '')}`;
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: url, options: `-c search_path=${schema}` });
  try {
    const selections = new EnrollmentStore(pool), runs = new RunStore(pool);
    await selections.initialize(); await runs.initialize();
    const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/3', number: 3, sourceRepositoryId: 4, head: 'a'.repeat(40), mergeHead: 'd'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    await selections.select(candidate);
    let maintainer = true, head = candidate.head;
    const github = { checkMaintainerAccess: async () => maintainer ? 5 : null, installationAccess: async () => 'allowed' as const,
      resolvePullRequest: async () => ({ number: 3, sourceRepositoryId: 4, destinationRepositoryId: 2, head, base: candidate.base }) };
    let pause: (() => Promise<void>) | undefined;
    const sessions = { checkMaintainer: async () => { if (pause) await pause(); return maintainer ? 5 : null; } };
    let baselineRevision = 1;
    const policy = new ForkPolicy({ pool, selections, github, sessions, baselines: { activeIdentity: async () => ({ digest: candidate.baseline, revision: baselineRevision }) } });
    await policy.syncPolicy(candidate, 100);
    await runs.admit(candidate);
    const found = await runs.findPull(candidate, candidate.number);
    assert.equal(found?.candidate.mergeHead, candidate.mergeHead);
    const lease = await runs.claim(60_000);
    assert.ok(lease && lease.candidate.kind === 'pull-request');
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'denied');
    assert.equal(await policy.approve({ session: 'session', candidate, quotaMicros: 100, baselineRevision: 1, consent: false }), false);
    maintainer = false;
    assert.equal(await policy.approve({ session: 'candidate', candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), false);
    maintainer = true;
    assert.equal(await policy.approve({ session: 'maintainer', candidate: found!.candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), true);
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'deferred');
    baselineRevision = 3;
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'denied');
    assert.equal(await policy.approve({ session: 'maintainer', candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), false);
    baselineRevision = 1;
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 100), 'denied');
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 101, 0), 'denied');
    let resume: () => void = () => {}, entered: () => void = () => {};
    const waiting = new Promise<void>(resolve => { resume = resolve; });
    const started = new Promise<void>(resolve => { entered = resolve; });
    pause = async () => { entered(); await waiting; };
    const staleApproval = policy.approve({ session: 'maintainer', candidate, quotaMicros: 100, baselineRevision: 1, consent: true });
    await started;
    await policy.syncPolicy(candidate, 101);
    await policy.syncPolicy(candidate, 100);
    resume();
    assert.equal(await staleApproval, false);
    pause = undefined;
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'denied');
    assert.equal(await policy.approve({ session: 'maintainer', candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), true);
    head = 'd'.repeat(40);
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'denied');
    head = candidate.head;
    assert.equal(await policy.revoke({ session: 'maintainer', scope: candidate, number: 3 }), true);
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'denied');
    assert.equal(await policy.approve({ session: 'maintainer', candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), true);
    const event = { deliveryId: randomUUID(), installationId: 1, repositoryId: 2, number: 3 };
    await runs.acceptPullDelivery(event);
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'denied');
    const eventLease = await runs.claimPullDelivery(60_000);
    assert.ok(eventLease);
    await runs.processPullDelivery(eventLease, async () => candidate);
    const next = await runs.claim(60_000);
    assert.ok(next && next.candidate.kind === 'pull-request');
    assert.equal(await policy.requestStatus({ ...next, candidate: next.candidate }, 100, 0), 'denied');
    assert.equal(await policy.approve({ session: 'maintainer', candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), true);
    const push = { deliveryId: randomUUID(), installationId: 1, repositoryId: 2, ref: 'refs/heads/other-base', head: 'f'.repeat(40), deleted: false };
    assert.equal(await runs.acceptDelivery(push, false), true);
    assert.equal(await policy.requestStatus({ ...next, candidate: next.candidate }, 100, 0), 'denied');
    const rediscovery = await runs.claimPullDelivery(60_000);
    assert.ok(rediscovery);
    await runs.processPullDelivery(rediscovery, async () => candidate);
    const fresh = await runs.claim(60_000);
    assert.ok(fresh && fresh.candidate.kind === 'pull-request');
    assert.equal(await policy.approve({ session: 'maintainer', candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), true);
    assert.equal(await runs.acceptDelivery(push, false), true);
    assert.equal(await runs.acceptDelivery({ ...push, deliveryId: randomUUID() }, true, false), true);
    assert.equal(await policy.requestStatus({ ...fresh, candidate: fresh.candidate }, 100, 0), 'deferred');
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});

test('authority revisions fence fork approvals and previously admitted runs', { skip: !process.env.PROOFCI_TEST_DATABASE_URL }, async () => {
  const { Pool } = await import('pg');
  const { randomUUID } = await import('node:crypto');
  const { EnrollmentStore } = await import('../src/enrollment-store.ts');
  const { RunStore } = await import('../src/run-store.ts');
  const { ForkPolicy } = await import('../src/fork-policy.ts');
  const admin = new Pool({ connectionString: process.env.PROOFCI_TEST_DATABASE_URL });
  const schema = `fork_authority_${randomUUID().replaceAll('-', '')}`;
  await admin.query(`CREATE SCHEMA ${schema}`);
  const pool = new Pool({ connectionString: process.env.PROOFCI_TEST_DATABASE_URL, options: `-c search_path=${schema}` });
  try {
    let epoch = 1;
    const authority = { current: async () => epoch, managedRef: () => 'refs/heads/main' };
    const selections = new EnrollmentStore(pool), runs = new RunStore(pool, authority);
    await selections.initialize(); await runs.initialize();
    const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/3', number: 3, sourceRepositoryId: 4, head: 'a'.repeat(40), mergeHead: 'd'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
    await selections.select(candidate);
    const github = { checkMaintainerAccess: async () => 5, installationAccess: async () => 'allowed' as const,
      resolvePullRequest: async () => ({ number: 3, sourceRepositoryId: 4, destinationRepositoryId: 2, head: candidate.head, base: candidate.base, baseRef: 'refs/heads/main' }) };
    const policy = new ForkPolicy({ pool, selections, github, authority, sessions: { checkMaintainer: async () => 5 }, baselines: { activeIdentity: async () => ({ digest: candidate.baseline, revision: 1 }) } });
    await policy.syncPolicy(candidate, 100);
    await runs.admit(candidate);
    const lease = await runs.claim(60_000);
    assert.ok(lease && lease.candidate.kind === 'pull-request');
    assert.equal(await policy.approve({ session: 'session', candidate: lease.candidate, quotaMicros: 100, baselineRevision: 1, consent: true }), true);
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'deferred');
    epoch = 2;
    assert.equal(await runs.findPull(candidate, 3), null);
    assert.equal(await policy.requestStatus({ ...lease, candidate: lease.candidate }, 100, 0), 'denied');
    await runs.admit(candidate);
    const next = await runs.claim(60_000);
    assert.ok(next && next.candidate.kind === 'pull-request');
    assert.equal(await policy.requestStatus({ ...next, candidate: next.candidate }, 100, 0), 'denied');
  } finally { await pool.end(); await admin.query(`DROP SCHEMA ${schema} CASCADE`); await admin.end(); }
});
