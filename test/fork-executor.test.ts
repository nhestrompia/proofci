import { test } from 'node:test';
import assert from 'node:assert/strict';
import { executeRun } from '../src/run-executor.ts';
import { ActiveBaselines } from '../src/active-baselines.ts';

class Baselines extends ActiveBaselines {
  constructor() { super([{ installationId: 1, repositoryId: 2, store: '/tmp/baseline.db', repository: 'https://github.com/example/repo.git' }]); }
  override async active() { return 'c'.repeat(64); }
}
const candidate = { kind: 'pull-request' as const, installationId: 1, repositoryId: 2, lane: 'pull/3', number: 3, sourceRepositoryId: 4, head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
test('a closed, changed, or cancelled fork cannot enter isolated dispatch', async () => {
  let staged = 0;
  const pr = { number: 3, sourceRepositoryId: 4, destinationRepositoryId: 2, head: candidate.head, base: candidate.base };
  const github = { resolveHead: async () => null, resolvePullRequest: async () => pr, stageSnapshot: async () => { staged++; throw new Error('must not stage'); } };
  for (const changed of [null, { ...pr, sourceRepositoryId: 5 }, { ...pr, head: 'd'.repeat(40) }, { ...pr, base: 'd'.repeat(40) }]) {
    await assert.rejects(executeRun({ candidate, signal: new AbortController().signal, github: { ...github, resolvePullRequest: async () => changed }, baselines: new Baselines(), ensureActive: async () => true }));
  }
  await assert.rejects(executeRun({ candidate, signal: new AbortController().signal, github, baselines: new Baselines(), ensureActive: async () => false }));
  assert.equal(staged, 0);
});
