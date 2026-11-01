import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { isolatedDispatch } from '../src/isolated-dispatch.ts';

test('the real dispatch command returns a nonpassing report for invalid inputs', async () => {
  const root = await mkdtemp(join(tmpdir(), 'proofci-dispatch-control-'));
  try {
    const snapshot = join(root, 'snapshot');
    await mkdir(snapshot);
    const result = await isolatedDispatch({ kind: 'head-snapshot', installationId: 1, repositoryId: 2, lane: 'main', head: 'a'.repeat(40), base: 'a'.repeat(40), baseline: 'b'.repeat(64) }, { snapshot, store: join(root, 'missing.db'), repository: 'https://example.invalid/fixture.git', report: join(root, 'report.json') }, new AbortController().signal);
    assert.equal(result.status, 'error');
  } finally { await rm(root, { recursive: true, force: true }); }
});
