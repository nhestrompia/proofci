import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, randomUUID } from 'node:crypto';
import { processPullEvent, type PullDelivery } from '../src/pull-events.ts';

test('only verified, scoped pull request notifications reach durable admission', async () => {
  const secret = 'test-secret', deliveryId = randomUUID();
  const body = Buffer.from(JSON.stringify({ action: 'synchronize', number: 7, installation: { id: 1 }, repository: { id: 2 } }));
  const signature = `sha256=${createHmac('sha256', secret).update(body).digest('hex')}`;
  const events: PullDelivery[] = [];
  const store = { acceptPullDelivery: async (event: PullDelivery) => { events.push(event); return true; } };
  assert.equal(await processPullEvent({ body, signature: `sha256=${'0'.repeat(64)}`, deliveryId, secret, store }), false);
  assert.equal(await processPullEvent({ body, signature, deliveryId, secret, store }), true);
  assert.deepEqual(events, [{ deliveryId, installationId: 1, repositoryId: 2, number: 7 }]);
});
