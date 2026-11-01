import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkReport } from '../src/check-report.ts';

const candidate = { kind: 'resolved' as const, installationId: 1, repositoryId: 2, lane: 'pull/1', pullHead: '1'.repeat(40), head: 'a'.repeat(40), base: 'b'.repeat(40), baseline: 'c'.repeat(64) };
const valid = { version: 1, status: 'passed', envelope: { head: candidate.head, base: candidate.base, baseline_sha256: candidate.baseline, candidate_sha256: 'f'.repeat(64) }, dispatch: { final_status: 0 }, support: { guarantee: 'Approved target', assumptions: ['Lean'], exclusions: ['Other code'] }, results: [{ id: 'one', policy: 'required', decision: 'verified', reason: 'accepted', validation: { decision: 'verified', candidate_sha256: 'f'.repeat(64), contract_sha256: '1'.repeat(64) } }] };

test('the check gate requires the validated result, exact inputs, and persisted evidence', () => {
  const digest = 'd'.repeat(64);
  assert.equal(checkReport(candidate, valid, digest).conclusion, 'success');
  assert.equal(checkReport(candidate, { ...valid, status: 'blocked' }, digest).conclusion, 'failure');
  assert.equal(checkReport(candidate, { ...valid, dispatch: { final_status: 1 } }, digest).conclusion, 'failure');
  assert.equal(checkReport(candidate, { ...valid, envelope: { ...valid.envelope, head: 'e'.repeat(40) } }, digest).conclusion, 'failure');
  assert.equal(checkReport(candidate, { ...valid, results: [{ ...valid.results[0], decision: 'unproven' }] }, digest).conclusion, 'failure');
  assert.equal(checkReport(candidate, valid, null).conclusion, 'failure');
  assert.match(checkReport(candidate, valid, digest).summary, /Approved target/);
});

test('a truncated summary keeps aggregate counts', () => {
  const results = Array.from({ length: 120 }, (_, index) => ({ ...valid.results[0], id: `property-${index}`, reason: 'x'.repeat(2000) }));
  const output = checkReport(candidate, { ...valid, results }, 'd'.repeat(64));
  assert.equal(output.conclusion, 'success');
  assert.ok(output.summary.length <= 60000);
  assert.match(output.summary, /Properties: verified: 120, violated: 0, unproven: 0/);
});
