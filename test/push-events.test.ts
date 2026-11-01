import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHmac, randomUUID } from 'node:crypto';
import { processPushEvent } from '../src/push-events.ts';

const secret = 'test-secret';
test('only signed, well-formed branch pushes reach durable admission', async () => {
  const body = Buffer.from(JSON.stringify({ installation: { id: 1 }, repository: { id: 2 }, ref: 'refs/heads/main', deleted: false, after: 'a'.repeat(40) }));
  const signature = `sha256=${createHmac('sha256', secret).update(body).digest('hex')}`;
  const saved: unknown[] = [];
  const store = { acceptDelivery: async (event: unknown) => { saved.push(event); return true; } };
  const event = { body, signature, event: 'push', deliveryId: randomUUID(), secret, store };
  assert.equal(await processPushEvent({ ...event, signature: `sha256=${'0'.repeat(64)}` }), false);
  assert.equal(saved.length, 0);
  assert.equal(await processPushEvent(event), true);
  assert.equal(saved.length, 1);
  assert.deepEqual(saved[0], { deliveryId: event.deliveryId, installationId: 1, repositoryId: 2, ref: 'refs/heads/main', head: 'a'.repeat(40), deleted: false });
});
