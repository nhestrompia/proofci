import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, randomUUID } from 'node:crypto';
import { processPullEvent } from '../src/pull-events.ts';

test('only authenticated pull request events for their destination reach the queue', async () => {
  const deliveryId = randomUUID(), secret = 'secret';
  const event = { action: 'synchronize', number: 5, installation: { id: 12 }, repository: { id: 34 }, pull_request: { number: 5, base: { repo: { id: 34 } } } };
  const body = Buffer.from(JSON.stringify(event));
  const signature = 'sha256=' + createHmac('sha256', secret).update(body).digest('hex');
  const accepted: unknown[] = [];
  const store = { acceptPullDelivery: async (item: unknown) => { accepted.push(item); return true; } };
  assert.equal(await processPullEvent({ body, signature, event: 'pull_request', deliveryId, secret, store }), true);
  assert.deepEqual(accepted, [{ deliveryId, installationId: 12, repositoryId: 34, number: 5 }]);
  assert.equal(await processPullEvent({ body, signature: 'sha256=' + '0'.repeat(64), event: 'pull_request', deliveryId, secret, store }), false);
  const bad = Buffer.from(JSON.stringify({ ...event, repository: { id: 35 } }));
  assert.equal(await processPullEvent({ body: bad, signature: 'sha256=' + createHmac('sha256', secret).update(bad).digest('hex'), event: 'pull_request', deliveryId, secret, store }), false);
  assert.equal(accepted.length, 1);

});
