import { createHash } from 'node:crypto';
import type { Pool, PoolClient } from 'pg';
import type { RepositoryScope } from './enrollment-store.ts';
import type { Lease } from './run-store.ts';

/** Token and microdollar ceilings. Rates use microdollars per million tokens, like the portable broker. */
export type Ceiling = { inputTokens: number; outputTokens: number; costMicros: number };
export type ModelLimits = {
  contextBytes: number; maxOutputPerCall: number; inputMicrosPerMillion: number; outputMicrosPerMillion: number;
  maxAttemptsPerObligation: number; run: Ceiling; repository: Ceiling;
};
export type ModelPolicy = { enabled: boolean; private: boolean; sourceConsent: boolean; limits: ModelLimits };

/**
 * reserved: budget held, provider not contacted. sending: the provider may have received the request.
 * settled: exact usage and response recorded. failed: the call finished without a usable response.
 * uncertain: the provider may have processed the request but no outcome was recorded.
 * reconciled: an operator recorded the provider's outcome for an uncertain attempt. released: never sent.
 */
export type AttemptState = 'reserved' | 'sending' | 'settled' | 'failed' | 'uncertain' | 'reconciled' | 'released';
export type Usage = { inputTokens: number; outputTokens: number; costMicros: number };
export type Attempt = {
  requestId: string; runId: string; obligation: string; attempt: number; state: AttemptState; payloadSha256: string;
  runGeneration: number; sendGeneration: number | null; sendCount: number; reserved: Usage; exact: Usage | null;
  response: string | null; late: boolean; validation: 'accepted' | 'rejected' | 'unavailable' | null; reason: string | null;
};
export type Denial = 'inactive' | 'disabled' | 'consent_required';
export type Exhaustion = 'attempt_limit' | 'context' | 'run_budget' | 'repository_budget';
export type Reservation = { kind: 'attempt'; attempt: Attempt; created: boolean } | { kind: 'denied'; reason: Denial } | { kind: 'exhausted'; reason: Exhaustion };
export type ModelUsage = {
  model_calls: number; attempts: Array<{ request_id: string; obligation: string; attempt: number; state: AttemptState; exact: Usage | null; charged_upper_bound: Usage; validation: string | null; late: boolean; reason: string | null }>;
  exact: Usage; upper_bound: Usage; unknown_usage_attempts: number; uncertain_attempts: number; failed_attempts: number;
};

const MAX_RESPONSE_BYTES = 65536;
const REQUEST_FRAMING_TOKENS = 4096;

function positive(value: unknown, maximum = Number.MAX_SAFE_INTEGER): value is number {
  return typeof value === 'number' && Number.isSafeInteger(value) && value > 0 && value <= maximum;
}
function ceiling(value: unknown): value is Ceiling {
  return typeof value === 'object' && value !== null && positive((value as Ceiling).inputTokens) && positive((value as Ceiling).outputTokens) && positive((value as Ceiling).costMicros);
}
export function validLimits(limits: unknown): limits is ModelLimits {
  if (typeof limits !== 'object' || limits === null) return false;
  const value = limits as ModelLimits;
  return positive(value.contextBytes) && positive(value.maxOutputPerCall) && positive(value.inputMicrosPerMillion) &&
    positive(value.outputMicrosPerMillion) && positive(value.maxAttemptsPerObligation, 5) && ceiling(value.run) && ceiling(value.repository);
}

function cost(tokens: number, rate: number): number { return Math.ceil(tokens * rate / 1_000_000); }

/** The logical attempt identity is stable across run generations, so recovery cannot mint a fresh attempt. */
export function requestId(runId: string, obligation: string, attempt: number): string {
  return createHash('sha256').update(JSON.stringify([runId, obligation, attempt])).digest('hex');
}

const charged = (column: string) => `CASE WHEN state='released' THEN 0 WHEN cost_micros IS NOT NULL THEN ${column} ELSE reserved_${column} END`;
const CHARGED = `coalesce(sum(${charged('input_tokens')}),0)::float8 AS input, coalesce(sum(${charged('output_tokens')}),0)::float8 AS output, coalesce(sum(${charged('cost_micros')}),0)::float8 AS cost`;
const ATTEMPT = `request_id AS "requestId", run_id AS "runId", obligation, attempt, state, payload_sha256 AS "payloadSha256", run_generation AS "runGeneration",
  send_generation AS "sendGeneration", send_count AS "sendCount", json_build_object('inputTokens', reserved_input_tokens::float8, 'outputTokens', reserved_output_tokens::float8, 'costMicros', reserved_cost_micros::float8) AS reserved,
  CASE WHEN cost_micros IS NULL THEN NULL ELSE json_build_object('inputTokens', input_tokens::float8, 'outputTokens', output_tokens::float8, 'costMicros', cost_micros::float8) END AS exact,
  response, late, validation, reason`;
/** The run is still the leased, applicable, selected generation. */
const ACTIVE_RUN = `SELECT r.id FROM proofci_runs r JOIN proofci_repository_selections s ON
  s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
  WHERE r.id=$1 AND r.generation=$2 AND r.state='running' AND r.applicable AND r.lease_until > clock_timestamp()`;

/**
 * Durable model broker accounting. Every reservation, send, outcome, and validation is a transition on one
 * row per logical attempt, fenced by the run generation and current repository selection.
 */
export class ModelLedger {
  private readonly pool: Pool;
  constructor(pool: Pool) { this.pool = pool; }

  async initialize(): Promise<void> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query("SELECT pg_advisory_xact_lock(hashtextextended(current_schema() || ':proofci-model-ledger-migration', 0))");
      await client.query(`CREATE TABLE IF NOT EXISTS proofci_model_policies (
        installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, enabled BOOLEAN NOT NULL DEFAULT false,
        private BOOLEAN NOT NULL DEFAULT true, source_consent BOOLEAN NOT NULL DEFAULT false, limits JSONB NOT NULL,
        revision BIGINT NOT NULL DEFAULT 1, updated_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp(),
        PRIMARY KEY (installation_id, repository_id))`);
      await client.query(`CREATE TABLE IF NOT EXISTS proofci_model_attempts (
        request_id TEXT PRIMARY KEY, run_id UUID NOT NULL REFERENCES proofci_runs(id),
        installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, obligation TEXT NOT NULL, attempt INTEGER NOT NULL CHECK (attempt > 0),
        payload_sha256 TEXT NOT NULL, state TEXT NOT NULL CHECK (state IN ('reserved','sending','settled','failed','uncertain','reconciled','released')),
        run_generation INTEGER NOT NULL, send_generation INTEGER, send_count INTEGER NOT NULL DEFAULT 0,
        reserved_input_tokens BIGINT NOT NULL, reserved_output_tokens BIGINT NOT NULL, reserved_cost_micros BIGINT NOT NULL,
        input_tokens BIGINT, output_tokens BIGINT, cost_micros BIGINT, response TEXT, late BOOLEAN NOT NULL DEFAULT false,
        validation TEXT CHECK (validation IN ('accepted','rejected','unavailable')), reason TEXT,
        created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp(), sent_at TIMESTAMPTZ, finished_at TIMESTAMPTZ,
        UNIQUE (run_id, obligation, attempt))`);
      await client.query('CREATE INDEX IF NOT EXISTS proofci_model_attempts_repository ON proofci_model_attempts (installation_id, repository_id)');
      await client.query('COMMIT');
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  private async transaction<T>(work: (client: PoolClient) => Promise<T>): Promise<T> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query("SET LOCAL lock_timeout='5s'");
      const result = await work(client);
      await client.query('COMMIT');
      return result;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  async setPolicy(scope: RepositoryScope, policy: ModelPolicy): Promise<void> {
    if (typeof policy.enabled !== 'boolean' || typeof policy.private !== 'boolean' || typeof policy.sourceConsent !== 'boolean' || !validLimits(policy.limits)) throw new Error('Invalid model policy');
    const { limits } = policy;
    const stored = { contextBytes: limits.contextBytes, maxOutputPerCall: limits.maxOutputPerCall, inputMicrosPerMillion: limits.inputMicrosPerMillion,
      outputMicrosPerMillion: limits.outputMicrosPerMillion, maxAttemptsPerObligation: limits.maxAttemptsPerObligation,
      run: { inputTokens: limits.run.inputTokens, outputTokens: limits.run.outputTokens, costMicros: limits.run.costMicros },
      repository: { inputTokens: limits.repository.inputTokens, outputTokens: limits.repository.outputTokens, costMicros: limits.repository.costMicros } };
    await this.pool.query(`INSERT INTO proofci_model_policies (installation_id, repository_id, enabled, private, source_consent, limits) VALUES ($1,$2,$3,$4,$5,$6::jsonb)
      ON CONFLICT (installation_id, repository_id) DO UPDATE SET enabled=EXCLUDED.enabled, private=EXCLUDED.private, source_consent=EXCLUDED.source_consent,
      limits=EXCLUDED.limits, revision=proofci_model_policies.revision+1, updated_at=clock_timestamp()`,
    [scope.installationId, scope.repositoryId, policy.enabled, policy.private, policy.sourceConsent, JSON.stringify(stored)]);
  }

  /** Revocation commits only after in-progress send transitions, and blocks every later send. */
  async revokeConsent(scope: RepositoryScope): Promise<boolean> {
    const result = await this.pool.query('UPDATE proofci_model_policies SET source_consent=false, revision=revision+1, updated_at=clock_timestamp() WHERE installation_id=$1 AND repository_id=$2', [scope.installationId, scope.repositoryId]);
    return result.rowCount === 1;
  }

  async disable(scope: RepositoryScope): Promise<boolean> {
    const result = await this.pool.query('UPDATE proofci_model_policies SET enabled=false, revision=revision+1, updated_at=clock_timestamp() WHERE installation_id=$1 AND repository_id=$2', [scope.installationId, scope.repositoryId]);
    return result.rowCount === 1;
  }

  async policy(scope: RepositoryScope): Promise<ModelPolicy | null> {
    const result = await this.pool.query<{ enabled: boolean; private: boolean; source_consent: boolean; limits: unknown }>('SELECT enabled, private, source_consent, limits FROM proofci_model_policies WHERE installation_id=$1 AND repository_id=$2', [scope.installationId, scope.repositoryId]);
    const row = result.rows[0];
    if (!row) return null;
    if (!validLimits(row.limits)) throw new Error('Stored model policy is invalid');
    return { enabled: row.enabled, private: row.private, sourceConsent: row.source_consent, limits: row.limits };
  }

  private async lockPolicy(client: PoolClient, lease: Lease): Promise<{ policy: ModelPolicy } | { denied: Denial }> {
    const result = await client.query<{ enabled: boolean; private: boolean; source_consent: boolean; limits: unknown }>('SELECT enabled, private, source_consent, limits FROM proofci_model_policies WHERE installation_id=$1 AND repository_id=$2 FOR SHARE', [lease.candidate.installationId, lease.candidate.repositoryId]);
    const row = result.rows[0];
    if (!row || !row.enabled) return { denied: 'disabled' };
    // An unreadable ceiling cannot justify further spending.
    if (!validLimits(row.limits)) return { denied: 'disabled' };
    if (row.private && !row.source_consent) return { denied: 'consent_required' };
    return { policy: { enabled: row.enabled, private: row.private, sourceConsent: row.source_consent, limits: row.limits } };
  }

  private async lockActiveRun(client: PoolClient, lease: Lease): Promise<boolean> {
    const result = await client.query(`${ACTIVE_RUN} FOR SHARE OF r, s`, [lease.id, lease.generation]);
    return result.rowCount === 1;
  }

  private async find(client: PoolClient | Pool, id: string, lock = false): Promise<Attempt | null> {
    const result = await client.query<Attempt>(`SELECT ${ATTEMPT} FROM proofci_model_attempts WHERE request_id=$1${lock ? ' FOR UPDATE' : ''}`, [id]);
    return result.rows[0] ?? null;
  }

  /**
   * Reserve the worst-case cost of one logical attempt before any provider contact. A duplicate dispatch of the
   * same attempt converges on the existing record instead of reserving or sending again.
   */
  async reserve(lease: Lease, input: { obligation: string; attempt: number; payloadSha256: string; requestBytes: number }): Promise<Reservation> {
    if (!input.obligation || input.obligation.length > 512 || !positive(input.attempt, 1000) || !/^[a-f0-9]{64}$/.test(input.payloadSha256) || !positive(input.requestBytes)) throw new Error('Invalid model attempt');
    const id = requestId(lease.id, input.obligation, input.attempt);
    return this.transaction(async client => {
      if (!await this.lockActiveRun(client, lease)) return { kind: 'denied', reason: 'inactive' };
      await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`model-budget:${lease.candidate.installationId}:${lease.candidate.repositoryId}`]);
      const existing = await this.find(client, id, true);
      if (existing && existing.payloadSha256 !== input.payloadSha256) throw new Error('Model attempt identity reused for a different request');
      if (existing && existing.state !== 'released') {
        if (existing.state === 'reserved' && existing.runGeneration !== lease.generation) {
          await client.query('UPDATE proofci_model_attempts SET run_generation=$2 WHERE request_id=$1', [id, lease.generation]);
          return { kind: 'attempt', attempt: { ...existing, runGeneration: lease.generation }, created: false };
        }
        return { kind: 'attempt', attempt: existing, created: false };
      }
      const allowed = await this.lockPolicy(client, lease);
      if ('denied' in allowed) return { kind: 'denied', reason: allowed.denied };
      const { limits } = allowed.policy;
      if (input.attempt > limits.maxAttemptsPerObligation) return { kind: 'exhausted', reason: 'attempt_limit' };
      const prior = await client.query<{ count: number }>('SELECT count(*)::int AS count FROM proofci_model_attempts WHERE run_id=$1 AND obligation=$2 AND attempt < $3', [lease.id, input.obligation, input.attempt]);
      if (prior.rows[0]!.count !== input.attempt - 1) throw new Error('Model attempts must be reserved in order');
      const reservedIn = input.requestBytes + REQUEST_FRAMING_TOKENS;
      if (reservedIn > limits.contextBytes) return { kind: 'exhausted', reason: 'context' };
      const reservedOut = limits.maxOutputPerCall;
      const reservedCost = cost(reservedIn, limits.inputMicrosPerMillion) + cost(reservedOut, limits.outputMicrosPerMillion);
      const over = (spent: { input: number; output: number; cost: number }, cap: Ceiling) =>
        spent.input + reservedIn > cap.inputTokens || spent.output + reservedOut > cap.outputTokens || spent.cost + reservedCost > cap.costMicros;
      const run = await client.query<{ input: number; output: number; cost: number }>(`SELECT ${CHARGED} FROM proofci_model_attempts WHERE run_id=$1`, [lease.id]);
      if (over(run.rows[0]!, limits.run)) return { kind: 'exhausted', reason: 'run_budget' };
      const repository = await client.query<{ input: number; output: number; cost: number }>(`SELECT ${CHARGED} FROM proofci_model_attempts WHERE installation_id=$1 AND repository_id=$2`, [lease.candidate.installationId, lease.candidate.repositoryId]);
      if (over(repository.rows[0]!, limits.repository)) return { kind: 'exhausted', reason: 'repository_budget' };
      if (existing) {
        await client.query(`UPDATE proofci_model_attempts SET state='reserved', run_generation=$2, reserved_input_tokens=$3, reserved_output_tokens=$4, reserved_cost_micros=$5, reason=NULL, finished_at=NULL WHERE request_id=$1`,
          [id, lease.generation, reservedIn, reservedOut, reservedCost]);
      } else {
        await client.query(`INSERT INTO proofci_model_attempts (request_id, run_id, installation_id, repository_id, obligation, attempt, payload_sha256, state, run_generation, reserved_input_tokens, reserved_output_tokens, reserved_cost_micros)
          VALUES ($1,$2,$3,$4,$5,$6,$7,'reserved',$8,$9,$10,$11)`, [id, lease.id, lease.candidate.installationId, lease.candidate.repositoryId, input.obligation, input.attempt, input.payloadSha256, lease.generation, reservedIn, reservedOut, reservedCost]);
      }
      return { kind: 'attempt', attempt: (await this.find(client, id))!, created: true };
    });
  }

  /**
   * Durably record that the provider may receive this request, immediately before contacting it. Cancellation,
   * supersession, removed access, disabled assistance, and consent revocation all block this transition.
   * An uncertain attempt is resent only for providers whose idempotency guarantees a single charge.
   */
  async beginSend(lease: Lease, id: string, options: { idempotentRetry?: boolean } = {}): Promise<{ kind: 'sending'; attempt: Attempt } | { kind: 'denied'; reason: Denial } | { kind: 'not_sendable'; attempt: Attempt | null }> {
    return this.transaction(async client => {
      if (!await this.lockActiveRun(client, lease)) return { kind: 'denied', reason: 'inactive' };
      const allowed = await this.lockPolicy(client, lease);
      if ('denied' in allowed) return { kind: 'denied', reason: allowed.denied };
      const attempt = await this.find(client, id, true);
      const resend = options.idempotentRetry === true && attempt?.state === 'uncertain';
      if (!attempt || attempt.runId !== lease.id || (attempt.state !== 'reserved' && !resend)) return { kind: 'not_sendable', attempt };
      await client.query("UPDATE proofci_model_attempts SET state='sending', send_generation=$2, send_count=send_count+1, sent_at=clock_timestamp(), reason=NULL WHERE request_id=$1", [id, lease.generation]);
      return { kind: 'sending', attempt: (await this.find(client, id))! };
    });
  }

  /**
   * Record the provider's exact usage and response. The result is usable only by the generation that sent it while
   * that generation is still current; a late result is accounted for but never replaces newer work.
   */
  async settle(id: string, sendGeneration: number, usage: { inputTokens: number; outputTokens: number }, body: string): Promise<{ recorded: boolean; usable: boolean; late: boolean }> {
    if (!Number.isSafeInteger(usage.inputTokens) || usage.inputTokens < 0 || !Number.isSafeInteger(usage.outputTokens) || usage.outputTokens < 0) throw new Error('Invalid provider usage');
    return this.transaction(async client => {
      const attempt = await this.find(client, id, true);
      if (!attempt || attempt.sendGeneration !== sendGeneration || (attempt.state !== 'sending' && attempt.state !== 'uncertain')) return { recorded: false, usable: false, late: true };
      const policy = await client.query<{ limits: unknown }>('SELECT p.limits FROM proofci_model_policies p JOIN proofci_model_attempts a ON a.installation_id=p.installation_id AND a.repository_id=p.repository_id WHERE a.request_id=$1', [id]);
      const limits = policy.rows[0]?.limits;
      if (!validLimits(limits)) throw new Error('Stored model policy is invalid');
      const exactCost = cost(usage.inputTokens, limits.inputMicrosPerMillion) + cost(usage.outputTokens, limits.outputMicrosPerMillion);
      const current = (await client.query(ACTIVE_RUN, [attempt.runId, sendGeneration])).rowCount === 1;
      const withinReservation = usage.inputTokens <= attempt.reserved.inputTokens && usage.outputTokens <= attempt.reserved.outputTokens && Buffer.byteLength(body) <= MAX_RESPONSE_BYTES;
      const late = attempt.state === 'uncertain' || !current;
      await client.query(`UPDATE proofci_model_attempts SET state=$2, input_tokens=$3, output_tokens=$4, cost_micros=$5, response=$6, late=$7, reason=$8, finished_at=clock_timestamp() WHERE request_id=$1`,
        [id, withinReservation ? 'settled' : 'failed', usage.inputTokens, usage.outputTokens, exactCost, withinReservation ? body : null, late, withinReservation ? (late ? 'late_result' : null) : 'invalid_provider_response']);
      return { recorded: true, usable: withinReservation && !late, late };
    });
  }

  /** The provider definitively did not process the request, so no usage was incurred. */
  async reject(id: string, sendGeneration: number, reason: string): Promise<boolean> {
    const result = await this.pool.query("UPDATE proofci_model_attempts SET state='failed', input_tokens=0, output_tokens=0, cost_micros=0, reason=$3, finished_at=clock_timestamp() WHERE request_id=$1 AND send_generation=$2 AND state='sending'", [id, sendGeneration, reason.slice(0, 128)]);
    return result.rowCount === 1;
  }

  /** The provider answered without usable data or usage. The full reservation stays charged. */
  async fail(id: string, sendGeneration: number, reason: string): Promise<boolean> {
    const result = await this.pool.query("UPDATE proofci_model_attempts SET state='failed', reason=$3, finished_at=clock_timestamp() WHERE request_id=$1 AND send_generation=$2 AND state='sending'", [id, sendGeneration, reason.slice(0, 128)]);
    return result.rowCount === 1;
  }

  /** The provider may have processed the request. The full reservation stays charged. */
  async uncertain(id: string, sendGeneration: number, reason: string): Promise<boolean> {
    const result = await this.pool.query("UPDATE proofci_model_attempts SET state='uncertain', reason=$3, finished_at=clock_timestamp() WHERE request_id=$1 AND send_generation=$2 AND state='sending'", [id, sendGeneration, reason.slice(0, 128)]);
    return result.rowCount === 1;
  }

  async recordValidation(lease: Lease, id: string, decision: 'accepted' | 'rejected' | 'unavailable'): Promise<boolean> {
    const result = await this.pool.query(`UPDATE proofci_model_attempts SET validation=$3 WHERE request_id=$4 AND run_id=$1 AND state='settled' AND NOT late AND EXISTS (${ACTIVE_RUN})`,
      [lease.id, lease.generation, decision, id]);
    return result.rowCount === 1;
  }

  /** A new run generation turns every send left open by an earlier generation into an explicit uncertain attempt. */
  async recover(lease: Lease): Promise<number> {
    const result = await this.pool.query("UPDATE proofci_model_attempts SET state='uncertain', reason='response_not_recorded', finished_at=clock_timestamp() WHERE run_id=$1 AND state='sending' AND send_generation < $2", [lease.id, lease.generation]);
    return result.rowCount ?? 0;
  }

  /** Release unsent reservations and mark open sends uncertain once a run generation stops. */
  async close(lease: Lease): Promise<void> {
    await this.pool.query("UPDATE proofci_model_attempts SET state=CASE WHEN state='reserved' THEN 'released' ELSE 'uncertain' END, reason=CASE WHEN state='reserved' THEN 'run_finished' ELSE 'response_not_recorded' END, finished_at=clock_timestamp() WHERE run_id=$1 AND state IN ('reserved','sending') AND coalesce(send_generation, run_generation) <= $2", [lease.id, lease.generation]);
  }

  /** Apply the same closing rule to runs that were cancelled, superseded, or fenced while no worker was active. */
  async sweep(): Promise<number> {
    const result = await this.pool.query(`UPDATE proofci_model_attempts a SET state=CASE WHEN a.state='reserved' THEN 'released' ELSE 'uncertain' END,
      reason=CASE WHEN a.state='reserved' THEN 'run_finished' ELSE 'response_not_recorded' END, finished_at=clock_timestamp()
      FROM proofci_runs r WHERE r.id=a.run_id AND a.state IN ('reserved','sending') AND (r.state <> 'running' OR NOT r.applicable)`);
    return result.rowCount ?? 0;
  }

  /** Record an operator's provider-side reconciliation of an uncertain attempt. Responses are never imported. */
  async reconcile(scope: RepositoryScope, id: string, outcome: { kind: 'charged'; inputTokens: number; outputTokens: number } | { kind: 'not_processed' }): Promise<boolean> {
    return this.transaction(async client => {
      const attempt = await client.query<{ limits: unknown }>(`SELECT p.limits FROM proofci_model_attempts a JOIN proofci_model_policies p ON p.installation_id=a.installation_id AND p.repository_id=a.repository_id
        WHERE a.request_id=$1 AND a.installation_id=$2 AND a.repository_id=$3 AND a.state='uncertain' FOR UPDATE OF a`, [id, scope.installationId, scope.repositoryId]);
      const limits = attempt.rows[0]?.limits;
      if (!attempt.rowCount) return false;
      if (!validLimits(limits)) throw new Error('Stored model policy is invalid');
      const usage = outcome.kind === 'charged' ? outcome : { inputTokens: 0, outputTokens: 0 };
      if (!Number.isSafeInteger(usage.inputTokens) || usage.inputTokens < 0 || !Number.isSafeInteger(usage.outputTokens) || usage.outputTokens < 0) throw new Error('Invalid reconciled usage');
      const exactCost = cost(usage.inputTokens, limits.inputMicrosPerMillion) + cost(usage.outputTokens, limits.outputMicrosPerMillion);
      await client.query(`UPDATE proofci_model_attempts SET state='reconciled', input_tokens=$2, output_tokens=$3, cost_micros=$4, late=true, reason=$5, finished_at=clock_timestamp() WHERE request_id=$1`,
        [id, usage.inputTokens, usage.outputTokens, exactCost, outcome.kind === 'charged' ? 'reconciled_charged' : 'reconciled_not_processed']);
      return true;
    });
  }

  async attempts(runId: string, obligation?: string): Promise<Attempt[]> {
    const result = await this.pool.query<Attempt>(`SELECT ${ATTEMPT} FROM proofci_model_attempts WHERE run_id=$1 AND ($2::text IS NULL OR obligation=$2) ORDER BY obligation, attempt`, [runId, obligation ?? null]);
    return result.rows;
  }

  async attempt(scope: RepositoryScope, id: string): Promise<Attempt | null> {
    const result = await this.pool.query<Attempt>(`SELECT ${ATTEMPT} FROM proofci_model_attempts WHERE request_id=$1 AND installation_id=$2 AND repository_id=$3`, [id, scope.installationId, scope.repositoryId]);
    return result.rows[0] ?? null;
  }

  /** Upper-bound repository spending, for quota checks such as fork approvals. */
  async repositorySpending(scope: RepositoryScope): Promise<Usage> {
    const result = await this.pool.query<{ input: number; output: number; cost: number }>(`SELECT ${CHARGED} FROM proofci_model_attempts WHERE installation_id=$1 AND repository_id=$2`, [scope.installationId, scope.repositoryId]);
    const row = result.rows[0]!;
    return { inputTokens: row.input, outputTokens: row.output, costMicros: row.cost };
  }

  /** Report exact usage only where it was recorded. Unknown outcomes are charged at their reservation. */
  async usage(runId: string): Promise<ModelUsage | null> {
    const attempts = await this.attempts(runId);
    if (attempts.length === 0) return null;
    const zero = (): Usage => ({ inputTokens: 0, outputTokens: 0, costMicros: 0 });
    const add = (total: Usage, item: Usage) => { total.inputTokens += item.inputTokens; total.outputTokens += item.outputTokens; total.costMicros += item.costMicros; };
    const exact = zero();
    const upper = zero();
    const rows = attempts.map(item => {
      const bound = item.state === 'released' ? zero() : item.exact ?? item.reserved;
      if (item.exact) add(exact, item.exact);
      add(upper, bound);
      return { request_id: item.requestId, obligation: item.obligation, attempt: item.attempt, state: item.state, exact: item.exact, charged_upper_bound: bound, validation: item.validation, late: item.late, reason: item.reason };
    });
    return {
      model_calls: attempts.filter(item => item.sendCount > 0).length, attempts: rows, exact, upper_bound: upper,
      unknown_usage_attempts: attempts.filter(item => item.state !== 'released' && item.exact === null).length,
      uncertain_attempts: attempts.filter(item => item.state === 'uncertain').length,
      failed_attempts: attempts.filter(item => item.state === 'failed').length,
    };
  }
}
