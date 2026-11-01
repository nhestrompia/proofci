import { test } from 'node:test';
import assert from 'node:assert/strict';
import { reconcileHead, resolveDelivery } from '../src/delivery-worker.ts';

const delivery = { deliveryId: 'delivery', installationId: 1, repositoryId: 2, ref: 'refs/heads/main', head: 'a'.repeat(40), deleted: false, generation: 1, selectionGeneration: 'selection' };
test('only the current selected head with an active baseline resolves to work', async () => {
  const selections = { readVersion: async () => 'selection', removeIfVersion: async () => {} };
  const github = { installationAccess: async () => 'allowed' as const, resolveHead: async () => delivery.head };
  const baselines = { active: async () => 'b'.repeat(64) };
  assert.deepEqual(await resolveDelivery({ delivery, selections, github, baselines }), { kind: 'head-snapshot' as const, installationId: 1, repositoryId: 2, lane: delivery.ref, head: delivery.head, base: delivery.head, baseline: 'b'.repeat(64) });
  assert.equal(await resolveDelivery({ delivery, selections, github: { ...github, resolveHead: async () => 'c'.repeat(40) }, baselines }), null);
  await assert.rejects(resolveDelivery({ delivery, selections, github: { ...github, installationAccess: async () => 'unavailable' as const }, baselines }));
});


test('reconciliation queues a missing branch as a deletion', async () => {
  const saved: Array<{ deleted: boolean; head: string }> = [];
  const store = { acceptDelivery: async (event: { deleted: boolean; head: string }) => { saved.push(event); return true; } };
  assert.equal(await reconcileHead({ scope: { installationId: 1, repositoryId: 2 }, ref: 'refs/heads/main', github: { resolveHead: async () => null }, store }), true);
  assert.equal(saved[0]?.deleted, true);
  assert.equal(saved[0]?.head, '0'.repeat(40));
});
