import type { ModelUsage } from './model-ledger.ts';

/**
 * Operator-facing classification of a run. The categories are disjoint:
 * - `proof_failure`: the verifier completed and judged at least one property violated or unproven.
 * - `infrastructure_failure`: no property judgment was produced (dispatch, VM, snapshot, store, or GitHub failure).
 * - `superseded`: the candidate changed or the run was cancelled; it has no bearing on the code.
 * Uncertain model attempts are reported separately because they can accompany any outcome.
 */
export type Outcome = 'passed' | 'proof_failure' | 'infrastructure_failure' | 'superseded' | 'in_progress';
export type Diagnosis = {
  run: string; state: string; applicable: boolean; outcome: Outcome; reason: string | null;
  properties: Array<{ id: string; policy: string; decision: string; reason: string }>;
  model: { uncertain: string[]; unknown_usage: number; action: string | null } | null;
  publication: { pending: boolean; last_error: string | null; published_at: string | null } | null;
};

const LIFECYCLE = new Set(['cancelled', 'candidate_superseded']);
function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }

export function diagnose(run: { id: string; state: string; applicable: boolean; report: unknown },
  model: ModelUsage | null, publication: Diagnosis['publication'], scope: { installationId: number; repositoryId: number }): Diagnosis {
  const report = object(run.report) ? run.report : null;
  const reason = report && typeof report.reason === 'string' ? report.reason : null;
  const properties = report && Array.isArray(report.results) ? report.results.filter(object).map(item => ({
    id: String(item.id), policy: String(item.policy), decision: String(item.decision), reason: String(item.reason) })) : [];
  let outcome: Outcome;
  if (run.state === 'queued' || run.state === 'running') outcome = 'in_progress';
  else if (run.state === 'cancelled' || (reason !== null && LIFECYCLE.has(reason))) outcome = 'superseded';
  else if (run.state === 'completed' && report?.status === 'passed') outcome = 'passed';
  else if (run.state === 'completed' && report?.status === 'blocked' && properties.length > 0) outcome = 'proof_failure';
  else outcome = 'infrastructure_failure';
  const uncertain = model?.attempts.filter(item => item.state === 'uncertain').map(item => item.request_id) ?? [];
  return {
    run: run.id, state: run.state, applicable: run.applicable, outcome, reason, properties,
    model: model ? { uncertain, unknown_usage: model.unknown_usage_attempts,
      action: uncertain.length ? `Check the provider's usage records, then run: node src/model-attempts.ts reconcile ${scope.installationId} ${scope.repositoryId} REQUEST_ID charged INPUT_TOKENS OUTPUT_TOKENS (or not-processed)` : null } : null,
    publication,
  };
}
