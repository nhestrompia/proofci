import test from 'node:test';
import assert from 'node:assert/strict';
import { MigrationService } from '../src/migration-service.ts';

const scope = { installationId: 1, repositoryId: 2 };
const input = { session: 'session', scope, head: 'a'.repeat(40), previous: 'b'.repeat(64), replacement: 'c'.repeat(64) };
const repository = { ...scope, store: '/tmp/proofci-test.db', repository: 'https://github.com/test/repo.git', ref: 'refs/heads/main' };

test('migration rejects revoked maintainers and stale candidate heads before fetching', async () => {
  let actor: number | null = null;
  let head = input.head;
  let fetches = 0;
  const service = new MigrationService({
    repositories: [repository],
    sessions: { checkMaintainer: async () => actor },
    selections: { readVersion: async () => 'generation', removeIfVersion: async () => {} },
    github: { checkMaintainerAccess: async () => actor, installationAccess: async () => 'allowed', resolveHead: async () => head,
      stageSnapshot: async () => { fetches++; throw new Error('unexpected fetch'); } },
  });
  await assert.rejects(service.migrate(input), /authorization denied or stale/);
  actor = 42;
  head = 'd'.repeat(40);
  await assert.rejects(service.migrate(input), /authorization denied or stale/);
  assert.equal(fetches, 0);
});
