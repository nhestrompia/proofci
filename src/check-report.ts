import type { Candidate } from './run-store.ts';

function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }
function lines(value: unknown): string { return Array.isArray(value) ? value.filter(item => typeof item === 'string').join('; ') : ''; }
export function truncateText(value: string, maxBytes: number): string {
  const bytes = Buffer.from(value, 'utf8');
  return bytes.length <= maxBytes ? value : bytes.subarray(0, maxBytes - 3).toString('utf8');
}

export type CheckOutput = { title: string; summary: string; conclusion: 'success' | 'failure' };

/** The dispatcher and final validator establish the result; missing fields always block. */
export function checkReport(candidate: Candidate, report: unknown, evidenceSha256: string | null): CheckOutput {
  const failures: string[] = [];
  if (!object(report)) return { title: 'ProofCI blocked', summary: 'A validated report is unavailable.', conclusion: 'failure' };
  const envelope = object(report.envelope) ? report.envelope : {};
  const dispatch = object(report.dispatch) ? report.dispatch : {};
  const support = object(report.support) ? report.support : {};
  const results = Array.isArray(report.results) ? report.results : [];
  const digest = (value: unknown) => typeof value === 'string' && /^[a-f0-9]{64}$/.test(value);
  const validResults = results.length > 0 && results.every(item => object(item) && typeof item.id === 'string' &&
    (item.policy === 'required' || item.policy === 'advisory') && ['verified', 'violated', 'unproven'].includes(String(item.decision)) &&
    typeof item.reason === 'string' && item.reason.length > 0 &&
    (item.decision !== 'verified' || (object(item.validation) && item.validation.decision === 'verified' &&
      item.validation.candidate_sha256 === envelope.candidate_sha256 && digest(item.validation.contract_sha256))));
  if (report.version !== 1 || report.status !== 'passed' || dispatch.final_status !== 0 ||
      envelope.head !== candidate.head || envelope.base !== candidate.base || envelope.baseline_sha256 !== candidate.baseline ||
      !digest(envelope.candidate_sha256) || !digest(evidenceSha256) || typeof support.guarantee !== 'string' ||
      !Array.isArray(support.assumptions) || !support.assumptions.every(item => typeof item === 'string') ||
      !Array.isArray(support.exclusions) || !support.exclusions.every(item => typeof item === 'string') || !validResults ||
      results.some(item => object(item) && item.policy === 'required' && item.decision !== 'verified')) failures.push('The authoritative report or required evidence is not passing.');
  const outcome = results.filter(object).map(item => `- ${String(item.id)} (${String(item.policy)}): ${String(item.decision)} — ${String(item.reason)}`);
  const counts = ['verified', 'violated', 'unproven'].map(decision => `${decision}: ${results.filter(item => object(item) && item.decision === decision).length}`).join(', ');
  const summary = [
    `Candidate: ${candidate.head}`, `Base: ${candidate.base}`, `Baseline: ${candidate.baseline}`, `Properties: ${counts}`,
    `Scope: ${typeof support.guarantee === 'string' ? support.guarantee : 'unavailable'}`,
    `Assumptions: ${lines(support.assumptions) || 'unavailable'}`,
    `Exclusions: ${lines(support.exclusions) || 'unavailable'}`,
    `Evidence SHA-256: ${evidenceSha256 ?? 'unavailable'}`, ...failures, '', ...outcome,
  ].join('\n');
  const displayed = Buffer.byteLength(summary, 'utf8') > 60000 ? `${truncateText(summary, 59950)}\nFull report available in Details.` : summary;
  return { title: failures.length ? 'ProofCI blocked' : 'ProofCI verified', summary: displayed, conclusion: failures.length ? 'failure' : 'success' };
}
