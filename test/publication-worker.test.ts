import { test } from 'node:test';
import assert from 'node:assert/strict';
import { publishNext } from '../src/publication-worker.ts';
import type { Publication } from '../src/run-store.ts';

const candidate = { kind: 'resolved' as const, installationId: 1, repositoryId: 2, lane: 'pull/3', pullHead: '1'.repeat(40), head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
const item: Publication = { id: '12345678-1234-4234-8234-123456789abc', revision: 2, leaseGeneration: 1, runGeneration: 1, candidate, state: 'completed', applicable: true, evidenceSha256: 'd'.repeat(64), report: { version: 1, status: 'passed', envelope: { head: candidate.head, base: candidate.base, baseline_sha256: candidate.baseline, candidate_sha256: 'e'.repeat(64) }, dispatch: { final_status: 0 }, support: { admitted_candidate: 'candidate.lean', guarantee: 'Target', assumptions: [], exclusions: [] }, results: [{ id: 'p', policy: 'required', decision: 'verified', reason: 'accepted', validation: { decision: 'verified', candidate_sha256: 'e'.repeat(64), contract_sha256: 'f'.repeat(64) } }] } };

test('publication rechecks the merge, baseline and generation immediately before completing', async () => {
  let current = true, completed = false, retried = false;
  const store = { claimPublication: async () => item, ownsPublication: async () => true, publicationCurrent: async () => current, finishPublication: async () => { completed = true; return true; }, retryPublication: async () => { retried = true; }, withPublicationLock: async (_id: string, publish: () => Promise<void>) => { await publish(); return true; } };
  const github = { invalidateCheck: async () => {}, resolvePullMerge: async () => ({ kind: 'resolved' as const, merge: candidate.head, base: candidate.base, head: '1'.repeat(40) }), publishCheck: async (_scope: unknown, input: { output: { conclusion: string } | null; fresh(): Promise<boolean>; annotations: unknown[] }) => {
    assert.equal(input.output?.conclusion, 'success'); assert.equal(input.annotations.length, 1);
    current = false;
    assert.equal(await input.fresh(), false);
    throw new Error('stale before completion');
  } };
  await assert.rejects(publishNext({ store, github, baselines: { active: async () => candidate.baseline }, origin: 'https://example.com' }));
  assert.equal(completed, false); assert.equal(retried, true);
});

test('a publisher that lost its lease cannot invalidate a newer check', async () => {
  let calls = 0;
  const store = { claimPublication: async () => item, ownsPublication: async () => false, publicationCurrent: async () => false, finishPublication: async () => { calls++; return true; }, retryPublication: async () => {}, withPublicationLock: async (_id: string, publish: () => Promise<void>) => { await publish(); return true; } };
  const github = { resolvePullMerge: async () => { calls++; return { kind: 'blocked' as const, reason: 'merge_unresolved' as const }; }, publishCheck: async () => { calls++; }, invalidateCheck: async () => { calls++; } };
  await publishNext({ store, github, baselines: { active: async () => candidate.baseline }, origin: 'https://example.com' });
  assert.equal(calls, 0);
});
