import { test } from 'node:test';
import assert from 'node:assert/strict';
import { Pool } from 'pg';
import { EnrollmentStore } from '../src/enrollment-store.ts';

const databaseUrl = process.env.PROOFCI_TEST_DATABASE_URL;
test('repository selections persist and are scoped to their installation', { skip: !databaseUrl }, async () => {
  const pool = new Pool({ connectionString: databaseUrl });
  try {
    const store = new EnrollmentStore(pool);
    await store.initialize();
    await store.select({ installationId: 12, repositoryId: 34 });
    assert.equal(await store.isSelected({ installationId: 12, repositoryId: 34 }), true);
    assert.equal(await store.isSelected({ installationId: 13, repositoryId: 34 }), false);
    const oldVersion = await store.readVersion({ installationId: 12, repositoryId: 34 });
    assert.ok(oldVersion);
    await store.select({ installationId: 12, repositoryId: 34 });
    assert.notEqual(await store.readVersion({ installationId: 12, repositoryId: 34 }), oldVersion);
    await store.removeIfVersion({ installationId: 12, repositoryId: 34 }, oldVersion);
    assert.equal(await store.isSelected({ installationId: 12, repositoryId: 34 }), true);
    await store.remove({ installationId: 12, repositoryId: 34 });
    assert.equal(await store.isSelected({ installationId: 12, repositoryId: 34 }), false);
  } finally { await pool.end(); }
});

test('new work requires both an enrolled selection and current installation access', async () => {
  const { authorizeNewWork } = await import('../src/repository-authorization.ts');
  const scope = { installationId: 12, repositoryId: 34 };
  let checked = 0;
  const github = { installationAccess: async () => { checked++; return 'allowed' as const; } };
  assert.equal(await authorizeNewWork({ scope, selections: { readVersion: async () => null, removeIfVersion: async () => {} }, github }), false);
  assert.equal(checked, 0);
  assert.equal(await authorizeNewWork({ scope, selections: { readVersion: async () => 'v1', removeIfVersion: async () => {} }, github }), true);
  assert.equal(await authorizeNewWork({ scope, selections: { readVersion: async () => 'v1', removeIfVersion: async () => {} }, github: { installationAccess: async () => 'revoked' } }), false);
});

test('enrollment requires a trusted maintainer session and rechecks authority', async () => {
  const { EnrollmentService } = await import('../src/enrollment-service.ts');
  const selected: string[] = [];
  let actor: number | null = null;
  const service = new EnrollmentService({
    store: { select: async () => { selected.push('selected'); }, remove: async () => { selected.push('removed'); }, isSelected: async () => true },
    sessions: { checkMaintainer: async () => actor },
    github: { checkMaintainerAccess: async () => null, inspectEnforcement: async () => 'unconfirmed' },
  });
  const input = { session: 'session', scope: { installationId: 12, repositoryId: 34 } };
  assert.equal(await service.enroll(input), false);
  assert.deepEqual(selected, []);
  actor = 56;
  assert.equal(await service.enroll(input), true);
  assert.deepEqual(selected, ['selected']);
  actor = null;
  assert.equal(await service.enroll(input), false);
  assert.deepEqual(selected, ['selected']);
});


test('removal and policy inspection require current maintainer authority', async () => {
  const { EnrollmentService } = await import('../src/enrollment-service.ts');
  let allowed = false, selected = true;
  const service = new EnrollmentService({
    store: { select: async () => {}, remove: async () => { selected = false; }, isSelected: async () => selected },
    sessions: { checkMaintainer: async () => allowed ? 56 : null },
    github: { checkMaintainerAccess: async () => null, inspectEnforcement: async () => 'unconfirmed' },
  });
  const input = { session: 'session', scope: { installationId: 12, repositoryId: 34 } };
  assert.equal(await service.remove(input), false);
  assert.equal(await service.inspect(input), null);
  allowed = true;
  assert.equal(await service.inspect(input), 'unconfirmed');
  assert.equal(await service.remove(input), true);
  assert.equal(await service.inspect(input), null);
});

test('does not authorize if the selection is removed during the GitHub access check', async () => {
  const { authorizeNewWork } = await import('../src/repository-authorization.ts');
  let selected = true;
  const result = await authorizeNewWork({
    scope: { installationId: 12, repositoryId: 34 },
    selections: { readVersion: async () => selected ? 'v1' : null, removeIfVersion: async () => {} },
    github: { installationAccess: async () => { selected = false; return 'allowed'; } },
  });
  assert.equal(result, false);
});

test('observed revocation clears enrollment, while a transient GitHub error does not', async () => {
  const { authorizeNewWork } = await import('../src/repository-authorization.ts');
  let selected = true;
  const selections = { readVersion: async () => selected ? 'v1' : null, removeIfVersion: async () => { selected = false; } };
  const scope = { installationId: 12, repositoryId: 34 };
  assert.equal(await authorizeNewWork({ scope, selections, github: { installationAccess: async () => 'unavailable' } }), false);
  assert.equal(selected, true);
  assert.equal(await authorizeNewWork({ scope, selections, github: { installationAccess: async () => 'revoked' } }), false);
  assert.equal(selected, false);
});


test('an old revocation result cannot delete a newer enrollment', async () => {
  const { authorizeNewWork } = await import('../src/repository-authorization.ts');
  let version: string | null = 'old';
  const selections = { readVersion: async () => version, removeIfVersion: async (_scope: unknown, expected: string) => { if (version === expected) version = null; } };
  const result = await authorizeNewWork({ scope: { installationId: 12, repositoryId: 34 }, selections, github: { installationAccess: async () => { version = 'new'; return 'revoked'; } } });
  assert.equal(result, false);
  assert.equal(version, 'new');
});
