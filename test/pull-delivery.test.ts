import { test } from 'node:test';
import assert from 'node:assert/strict';
import { resolvePullDelivery } from '../src/pull-delivery.ts';

const delivery = { deliveryId: 'delivery', installationId: 1, repositoryId: 2, number: 3, generation: 1, selectionGeneration: 'v1' };
const pr = { number: 3, sourceRepositoryId: 4, destinationRepositoryId: 2, head: 'a'.repeat(40), base: 'b'.repeat(40) };
const baselines = { active: async () => 'c'.repeat(64) };
test('fork admission resolves the current destination and requires enrolled access', async () => {
  let version: string | null = 'v1';
  const selections = { readVersion: async () => version, removeIfVersion: async () => { version = null; } };
  const github = { installationAccess: async () => 'allowed' as const, resolvePullRequest: async () => pr, resolvePullMerge: async () => ({ kind: 'resolved' as const, merge: 'd'.repeat(40), head: pr.head, base: pr.base }) };
  assert.deepEqual(await resolvePullDelivery({ delivery, selections, github, baselines }), { kind: 'pull-request', installationId: 1, repositoryId: 2, lane: 'pull/3', number: 3, sourceRepositoryId: 4, head: pr.head, base: pr.base, mergeHead: 'd'.repeat(40), baseline: 'c'.repeat(64) });
  assert.equal(await resolvePullDelivery({ delivery, selections, github, baselines: { active: async () => null } }), 'baseline-unavailable');
  version = 'new';
  assert.equal(await resolvePullDelivery({ delivery, selections, github, baselines }), null);
  version = 'v1';
  assert.equal(await resolvePullDelivery({ delivery, selections, github: { ...github, resolvePullRequest: async () => null }, baselines }), 'closed');
  assert.equal(await resolvePullDelivery({ delivery, selections, github: { ...github, installationAccess: async () => 'revoked' }, baselines }), null);
  assert.equal(version, null);
});
