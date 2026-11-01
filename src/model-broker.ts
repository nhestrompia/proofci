import { createHash } from 'node:crypto';
import type { Lease } from './run-store.ts';
import type { Attempt, ModelLedger } from './model-ledger.ts';

export type ModelRequest = { candidate: string; contract: string; diagnostic: string };
export type ProviderResponse = { body: string; inputTokens: number; outputTokens: number };

/** Thrown only when the provider confirms that it did not process the request, so nothing was charged. */
export class ProviderRejected extends Error {}

/**
 * A trusted deployment adapter. Set `idempotent` only when the provider guarantees that resending the same
 * request ID returns the original outcome without a second charge. Without that guarantee, ProofCI never
 * resends an attempt whose outcome is unknown.
 */
export type ModelProvider = {
  readonly idempotent: boolean;
  available(): boolean;
  send(input: { requestId: string; request: ModelRequest; maxOutputTokens: number; signal: AbortSignal }): Promise<ProviderResponse>;
};

type Ledger = Pick<ModelLedger, 'reserve' | 'beginSend' | 'settle' | 'reject' | 'fail' | 'uncertain'>;
export type BrokerOutcome =
  | { kind: 'response'; requestId: string; body: string; reused: boolean; validation: Attempt['validation'] }
  | { kind: 'uncertain' | 'failed' | 'stale' | 'in_flight'; requestId: string; reason: string | null }
  | { kind: 'denied'; reason: 'inactive' | 'disabled' | 'consent_required' | 'provider_unavailable' }
  | { kind: 'exhausted'; reason: 'attempt_limit' | 'context' | 'run_budget' | 'repository_budget' };

function recorded(attempt: Attempt, provider: ModelProvider): BrokerOutcome | null {
  const id = attempt.requestId;
  switch (attempt.state) {
    case 'reserved': return null;
    case 'uncertain': return provider.idempotent ? null : { kind: 'uncertain', requestId: id, reason: attempt.reason };
    case 'settled': return attempt.late || attempt.response === null ? { kind: 'stale', requestId: id, reason: attempt.reason }
      : { kind: 'response', requestId: id, body: attempt.response, reused: true, validation: attempt.validation };
    case 'sending': return { kind: 'in_flight', requestId: id, reason: null };
    default: return { kind: 'failed', requestId: id, reason: attempt.reason };
  }
}

function validResponse(value: unknown, maxOutput: number): value is ProviderResponse {
  if (typeof value !== 'object' || value === null) return false;
  const response = value as ProviderResponse;
  return typeof response.body === 'string' && Buffer.byteLength(response.body) <= 65536 &&
    Number.isSafeInteger(response.inputTokens) && response.inputTokens >= 0 &&
    Number.isSafeInteger(response.outputTokens) && response.outputTokens >= 0 && response.outputTokens <= maxOutput;
}

/**
 * Make at most one provider call for a logical attempt. Every step is persisted before the next begins, so a
 * crash at any point leaves either an unsent reservation, an explicit uncertain attempt, or a recorded result.
 */
export async function requestModel(options: { ledger: Ledger; provider: ModelProvider; lease: Lease; obligation: string; attempt: number; request: ModelRequest; ensureActive(): Promise<boolean>; signal?: AbortSignal; timeoutMs?: number }): Promise<BrokerOutcome> {
  const { ledger, provider, lease } = options;
  if (!await options.ensureActive()) return { kind: 'denied', reason: 'inactive' };
  const raw = JSON.stringify({ candidate: options.request.candidate, contract: options.request.contract, diagnostic: options.request.diagnostic });
  const reservation = await ledger.reserve(lease, { obligation: options.obligation, attempt: options.attempt, payloadSha256: createHash('sha256').update(raw).digest('hex'), requestBytes: Buffer.byteLength(raw) });
  if (reservation.kind !== 'attempt') return reservation;
  const prior = recorded(reservation.attempt, provider);
  if (prior) return prior;
  const id = reservation.attempt.requestId;
  if (!provider.available()) return { kind: 'denied', reason: 'provider_unavailable' };
  if (!await options.ensureActive()) return { kind: 'denied', reason: 'inactive' };
  const started = await ledger.beginSend(lease, id, { idempotentRetry: provider.idempotent });
  if (started.kind === 'denied') return started;
  if (started.kind === 'not_sendable') return (started.attempt && recorded(started.attempt, provider)) ?? { kind: 'in_flight', requestId: id, reason: null };
  const generation = lease.generation;
  const maxOutputTokens = started.attempt.reserved.outputTokens;
  const timeout = AbortSignal.timeout(options.timeoutMs ?? 60_000);
  const signal = options.signal ? AbortSignal.any([options.signal, timeout]) : timeout;
  let response: unknown;
  try {
    // Do not rely on the adapter to honor cancellation; an abandoned call stays uncertain.
    response = await new Promise((resolve, reject) => {
      const stop = () => reject(signal.reason);
      if (signal.aborted) return stop();
      signal.addEventListener('abort', stop, { once: true });
      provider.send({ requestId: id, request: options.request, maxOutputTokens, signal }).then(resolve, reject).finally(() => signal.removeEventListener('abort', stop));
    });
  } catch (error) {
    if (error instanceof ProviderRejected) {
      await ledger.reject(id, generation, 'provider_rejected');
      return { kind: 'failed', requestId: id, reason: 'provider_rejected' };
    }
    const reason = timeout.aborted ? 'provider_timeout' : options.signal?.aborted ? 'cancelled_during_request' : 'provider_error';
    await ledger.uncertain(id, generation, reason);
    return { kind: 'uncertain', requestId: id, reason };
  }
  if (!validResponse(response, maxOutputTokens)) {
    await ledger.fail(id, generation, 'invalid_provider_response');
    return { kind: 'failed', requestId: id, reason: 'invalid_provider_response' };
  }
  const result = await ledger.settle(id, generation, { inputTokens: response.inputTokens, outputTokens: response.outputTokens }, response.body);
  if (result.usable) return { kind: 'response', requestId: id, body: response.body, reused: false, validation: null };
  return result.recorded && !result.late ? { kind: 'failed', requestId: id, reason: 'invalid_provider_response' } : { kind: 'stale', requestId: id, reason: 'late_result' };
}

export type RepairReason = 'verified' | 'attempts_exhausted' | 'budget_or_context_exhausted' | 'not_authorized' | 'source_consent_required' |
  'provider_unavailable' | 'validation_unavailable' | 'cancelled' | 'attempt_in_flight' | 'timeout';

/**
 * Bounded repair of one obligation. Responses already paid for are validated again rather than requested again;
 * uncertain and failed attempts keep counting against the attempt and spending limits.
 */
export async function repairObligation(options: Omit<Parameters<typeof requestModel>[0], 'attempt' | 'ledger'> & {
  ledger: Ledger & Pick<ModelLedger, 'recordValidation'>; deadline?: number;
  validate(body: string, requestId: string): Promise<'accepted' | 'rejected' | 'unavailable'>;
}): Promise<{ decision: 'verified' | 'unproven'; reason: RepairReason; requestIds: string[] }> {
  const requestIds: string[] = [];
  const done = (decision: 'verified' | 'unproven', reason: RepairReason) => ({ decision, reason, requestIds });
  for (let attempt = 1; attempt <= 5; attempt++) {
    if (options.deadline !== undefined && Date.now() >= options.deadline) return done('unproven', 'timeout');
    const outcome = await requestModel({ ...options, attempt });
    if ('requestId' in outcome) requestIds.push(outcome.requestId);
    if (outcome.kind === 'denied') return done('unproven', outcome.reason === 'inactive' ? 'cancelled' : outcome.reason === 'consent_required' ? 'source_consent_required' : outcome.reason === 'disabled' ? 'not_authorized' : 'provider_unavailable');
    if (outcome.kind === 'exhausted') return done('unproven', outcome.reason === 'attempt_limit' ? 'attempts_exhausted' : 'budget_or_context_exhausted');
    if (outcome.kind === 'in_flight') return done('unproven', 'attempt_in_flight');
    if (outcome.kind !== 'response' || outcome.validation === 'rejected') continue;
    const decision = await options.validate(outcome.body, outcome.requestId);
    if (!await options.ledger.recordValidation(options.lease, outcome.requestId, decision)) return done('unproven', 'cancelled');
    if (decision === 'accepted') return done('verified', 'verified');
    if (decision === 'unavailable') return done('unproven', 'validation_unavailable');
  }
  return done('unproven', 'attempts_exhausted');
}
