import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, randomUUID } from 'node:crypto';
import { processInstallationEvent } from '../src/installation-events.ts';

const secret = 'webhook-test-secret';
function signed(value: unknown): { body: Buffer; signature: string } {
  const body = Buffer.from(JSON.stringify(value));
  return { body, signature: `sha256=${createHmac('sha256', secret).update(body).digest('hex')}` };
}

test('signed repository removals and installation deletion invalidate selections', async () => {
  const removed: string[] = [];
  const store = { removeRepositories: async (id: number, repositories: number[]) => { for (const repository of repositories) removed.push(`${id}:${repository}`); }, removeInstallation: async (id: number) => { removed.push(`${id}:all`); } };
  const deliveryId = randomUUID();
  const removal = signed({ action: 'removed', installation: { id: 12 }, repositories_removed: [{ id: 34 }] });
  assert.equal(await processInstallationEvent({ ...removal, event: 'installation_repositories', deliveryId, secret, store }), true);
  assert.deepEqual(removed, ['12:34']);
  const deleted = signed({ action: 'deleted', installation: { id: 12 } });
  assert.equal(await processInstallationEvent({ ...deleted, event: 'installation', deliveryId: randomUUID(), secret, store }), true);
  assert.deepEqual(removed, ['12:34', '12:all']);
  assert.equal(await processInstallationEvent({ ...removal, signature: `sha256=${'0'.repeat(64)}`, event: 'installation_repositories', deliveryId, secret, store }), false);
  assert.deepEqual(removed, ['12:34', '12:all']);
});

test('signed removal persists across store instances and leaves other repositories intact', { skip: !process.env.PROOFCI_TEST_DATABASE_URL }, async () => {
  const { Pool } = await import('pg');
  const { EnrollmentStore } = await import('../src/enrollment-store.ts');
  const pool = new Pool({ connectionString: process.env.PROOFCI_TEST_DATABASE_URL });
  const store = new EnrollmentStore(pool);
  const first = { installationId: 920001, repositoryId: 920002 };
  const second = { installationId: 920001, repositoryId: 920003 };
  try {
    await store.initialize();
    await store.select(first); await store.select(second);
    const revision = await store.beginSelection(first);
    const deliveryId = randomUUID();
  const removal = signed({ action: 'removed', installation: { id: first.installationId }, repositories_removed: [{ id: first.repositoryId }] });
    assert.equal(await processInstallationEvent({ ...removal, event: 'installation_repositories', deliveryId, secret, store }), true);
    assert.equal(await store.selectIfUnchanged(first, revision), false);
    const freshStore = new EnrollmentStore(pool);
    assert.equal(await freshStore.isSelected(first), false);
    assert.equal(await freshStore.isSelected(second), true);
    const { authorizeNewWork } = await import('../src/repository-authorization.ts');
    const github = { installationAccess: async () => 'allowed' as const };
    assert.equal(await authorizeNewWork({ scope: first, selections: freshStore, github }), false);
    await freshStore.select(first);
    assert.equal(await processInstallationEvent({ ...removal, event: 'installation_repositories', deliveryId, secret, store }), true);
    assert.equal(await authorizeNewWork({ scope: first, selections: freshStore, github }), true);
    const deleted = signed({ action: 'deleted', installation: { id: first.installationId } });
    assert.equal(await processInstallationEvent({ ...deleted, event: 'installation', deliveryId: randomUUID(), secret, store }), true);
    assert.equal(await freshStore.isSelected(second), false);
  } finally { await pool.end(); }
});
