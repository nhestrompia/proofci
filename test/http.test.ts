import { test } from 'node:test';
import assert from 'node:assert/strict';

const service = process.env.PROOFCI_TEST_SERVICE_URL;
test('onboarding permits same-origin forms and rejects unsigned enrollment', { skip: !service }, async () => {
  assert.ok(service);
  const page = await fetch(service);
  assert.equal(page.headers.get('referrer-policy'), 'same-origin');
  const response = await fetch(new URL('/enroll', service), {
    method: 'POST',
    headers: { origin: new URL(service).origin, 'content-type': 'application/x-www-form-urlencoded' },
    body: 'repository=12%3A34',
  });
  assert.equal(response.status, 403);
  assert.match(await response.text(), /Enrollment denied/);
});
