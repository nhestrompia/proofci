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

test('webhook endpoint verifies signatures before removing enrollment', { skip: !service || !process.env.PROOFCI_TEST_DATABASE_URL || !process.env.PROOFCI_TEST_WEBHOOK_SECRET }, async () => {
  assert.ok(service);
  const secret = process.env.PROOFCI_TEST_WEBHOOK_SECRET;
  assert.ok(secret);
  const { createHmac, randomUUID } = await import('node:crypto');
  const { Pool } = await import('pg');
  const { EnrollmentStore } = await import('../src/enrollment-store.ts');
  const pool = new Pool({ connectionString: process.env.PROOFCI_TEST_DATABASE_URL });
  const store = new EnrollmentStore(pool);
  const scope = { installationId: 930001, repositoryId: 930002 };
  const body = JSON.stringify({ action: 'removed', installation: { id: scope.installationId }, repositories_removed: [{ id: scope.repositoryId }] });
  try {
    await store.initialize(); await store.select(scope);
    const endpoint = new URL('/webhooks/github', service);
    const headers = { 'content-type': 'application/json', 'x-github-event': 'installation_repositories', 'x-github-delivery': randomUUID(), 'x-hub-signature-256': `sha256=${'0'.repeat(64)}` };
    assert.equal((await fetch(endpoint, { method: 'POST', headers, body })).status, 401);
    assert.equal(await store.isSelected(scope), true);
    headers['x-hub-signature-256'] = `sha256=${createHmac('sha256', secret).update(body).digest('hex')}`;
    assert.equal((await fetch(endpoint, { method: 'POST', headers, body })).status, 204);
    assert.equal(await store.isSelected(scope), false);
  } finally { await store.remove(scope); await pool.end(); }
});
