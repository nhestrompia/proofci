import { createHash, randomUUID } from 'node:crypto';
import type { Pool, PoolClient } from 'pg';
import type { RepositoryScope } from './enrollment-store.ts';
import type { PushDelivery } from './push-events.ts';
import type { PullDelivery } from './pull-events.ts';

export type Candidate = { kind: 'head-snapshot' | 'resolved'; installationId: number; repositoryId: number; lane: string; head: string; base: string; baseline: string; pullHead?: string | null };
export type DeliveryLease = PushDelivery & { generation: number; selectionGeneration: string };
export type PullLease = PullDelivery & { generation: number; selectionGeneration: string };
export type Lease = { id: string; generation: number; candidate: Candidate };
export type Publication = { id: string; revision: number; leaseGeneration: number; runGeneration: number; candidate: Candidate; state: 'queued' | 'running' | 'completed' | 'cancelled'; applicable: boolean; report: unknown; evidenceSha256: string | null };

function validateCandidate(candidate: Candidate): void {
  if ((candidate.kind !== 'head-snapshot' && candidate.kind !== 'resolved') || !Number.isSafeInteger(candidate.installationId) || candidate.installationId < 1 ||
      !Number.isSafeInteger(candidate.repositoryId) || candidate.repositoryId < 1 ||
      !candidate.lane || candidate.lane.length > 512 ||
      !/^[a-f0-9]{40}$/.test(candidate.head) || !/^[a-f0-9]{40}$/.test(candidate.base) ||
      !/^[a-f0-9]{64}$/.test(candidate.baseline) ||
      (candidate.kind === 'resolved' && /^pull\/[1-9]\d*$/.test(candidate.lane) && (typeof candidate.pullHead !== 'string' || !/^[a-f0-9]{40}$/.test(candidate.pullHead)))) throw new Error('Invalid immutable candidate');
}

async function insertCandidate(client: PoolClient, candidate: Candidate, selectionGeneration: string): Promise<string> {
  await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`${candidate.installationId}:${candidate.repositoryId}:${candidate.lane}`]);
  const params = [candidate.installationId, candidate.repositoryId, candidate.lane, candidate.head, candidate.base, candidate.baseline, candidate.kind];
  const existing = await client.query<{ id: string }>('SELECT id FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND head=$4 AND base=$5 AND baseline=$6 AND kind=$7 AND selection_generation=$8 AND pull_head IS NOT DISTINCT FROM $9 AND applicable', [...params, selectionGeneration, candidate.pullHead ?? null]);
  if (existing.rows[0]) return existing.rows[0].id;
  await client.query(`WITH changed AS (UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable RETURNING id)
    UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed)`, params.slice(0, 3));
  const id = randomUUID();
  await client.query("INSERT INTO proofci_runs (id, installation_id, repository_id, lane, head, base, baseline, kind, selection_generation, pull_head, state) VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'queued')", [id, ...params, selectionGeneration, candidate.pullHead ?? null]);
  if (candidate.kind === 'resolved' && /^pull\/[1-9]\d*$/.test(candidate.lane)) await client.query('INSERT INTO proofci_publications (run_id) VALUES ($1)', [id]);
  return id;
}

type Run = { id: string; applicable: boolean; state: 'queued' | 'running' | 'completed' | 'cancelled'; report: unknown };

/** Durable lifecycle for already authorized, immutable candidates. */
export class RunStore {
  private readonly pool: Pool;
  constructor(pool: Pool) { this.pool = pool; }

  async initialize(): Promise<void> {
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_runs (
      id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL,
      lane TEXT NOT NULL, head TEXT NOT NULL, base TEXT NOT NULL, baseline TEXT NOT NULL, kind TEXT NOT NULL CHECK (kind IN ('head-snapshot','resolved')), selection_generation TEXT NOT NULL,
      state TEXT NOT NULL CHECK (state IN ('queued', 'running', 'completed', 'cancelled')),
      generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, report JSONB,
      applicable BOOLEAN NOT NULL DEFAULT true,
      created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp(), first_started_at TIMESTAMPTZ, started_at TIMESTAMPTZ, completed_at TIMESTAMPTZ,
      recovery_seconds DOUBLE PRECISION NOT NULL DEFAULT 0
    )`);
    await this.pool.query('CREATE UNIQUE INDEX IF NOT EXISTS proofci_runs_applicable_lane ON proofci_runs (installation_id, repository_id, lane) WHERE applicable');
    await this.pool.query('ALTER TABLE proofci_runs ADD COLUMN IF NOT EXISTS evidence BYTEA, ADD COLUMN IF NOT EXISTS evidence_sha256 TEXT, ADD COLUMN IF NOT EXISTS pull_head TEXT');
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_publications (
      run_id UUID PRIMARY KEY REFERENCES proofci_runs(id), pending BOOLEAN NOT NULL DEFAULT true,
      revision INTEGER NOT NULL DEFAULT 1, generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ,
      last_error TEXT, published_at TIMESTAMPTZ
    )`);
    await this.pool.query('ALTER TABLE proofci_publications ADD COLUMN IF NOT EXISTS needs_revalidation BOOLEAN NOT NULL DEFAULT false');
    await this.pool.query("INSERT INTO proofci_publications (run_id) SELECT id FROM proofci_runs WHERE kind='resolved' AND lane ~ '^pull/[1-9][0-9]*$' ON CONFLICT DO NOTHING");
    await this.pool.query(`CREATE OR REPLACE FUNCTION proofci_fence_selection() RETURNS trigger LANGUAGE plpgsql AS $$
      BEGIN
        IF TG_OP = 'UPDATE' AND NEW.generation = OLD.generation THEN RETURN NEW; END IF;
        WITH changed AS (UPDATE proofci_runs SET applicable=false,
          state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END,
          lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END
          WHERE installation_id=OLD.installation_id AND repository_id=OLD.repository_id AND selection_generation=OLD.generation AND applicable RETURNING id)
        UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed);
        RETURN OLD;
      END $$`);
    await this.pool.query('DROP TRIGGER IF EXISTS proofci_fence_selection_trigger ON proofci_repository_selections');
    await this.pool.query('CREATE TRIGGER proofci_fence_selection_trigger AFTER DELETE OR UPDATE OF generation ON proofci_repository_selections FOR EACH ROW EXECUTE FUNCTION proofci_fence_selection()');
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_push_deliveries (
      delivery_id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL,
      ref TEXT NOT NULL, head TEXT NOT NULL, deleted BOOLEAN NOT NULL, selection_generation TEXT NOT NULL,
      state TEXT NOT NULL DEFAULT 'queued' CHECK (state IN ('queued','processing','done')),
      generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, last_error TEXT,
      created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp()
    )`);
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_pull_deliveries (
      delivery_id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, number BIGINT NOT NULL,
      selection_generation TEXT NOT NULL, state TEXT NOT NULL DEFAULT 'queued' CHECK (state IN ('queued','processing','done')),
      generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, last_error TEXT, created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp()
    )`);
  }

  async acceptPullDelivery(event: PullDelivery): Promise<boolean> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query("SET LOCAL lock_timeout='2s'");
      await client.query("SET LOCAL statement_timeout='5s'");
      await client.query('INSERT INTO proofci_installation_revisions (installation_id) VALUES ($1) ON CONFLICT DO NOTHING', [event.installationId]);
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [event.installationId]);
      const selected = await client.query<{ generation: string }>('SELECT generation FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2', [event.installationId, event.repositoryId]);
      if (!selected.rows[0]) { await client.query('COMMIT'); return false; }
      const result = await client.query(`INSERT INTO proofci_pull_deliveries (delivery_id, installation_id, repository_id, number, selection_generation) VALUES ($1,$2,$3,$4,$5)
        ON CONFLICT (delivery_id) DO UPDATE SET delivery_id=EXCLUDED.delivery_id WHERE proofci_pull_deliveries.installation_id=EXCLUDED.installation_id
        AND proofci_pull_deliveries.repository_id=EXCLUDED.repository_id AND proofci_pull_deliveries.number=EXCLUDED.number
        AND proofci_pull_deliveries.selection_generation=EXCLUDED.selection_generation RETURNING delivery_id`, [event.deliveryId, event.installationId, event.repositoryId, event.number, selected.rows[0].generation]);
      await client.query('COMMIT');
      return result.rowCount === 1;
    } catch (error) { await client.query('ROLLBACK'); throw error; } finally { client.release(); }
  }

  async claimPullDelivery(leaseMs: number): Promise<PullLease | null> {
    if (!Number.isSafeInteger(leaseMs) || leaseMs < 1 || leaseMs > 3_600_000) throw new Error('Invalid lease');
    const result = await this.pool.query<PullLease>(`UPDATE proofci_pull_deliveries SET state='processing', generation=generation+1, lease_until=clock_timestamp()+($1 * interval '1 millisecond')
      WHERE delivery_id=(SELECT delivery_id FROM proofci_pull_deliveries WHERE state='queued' OR (state='processing' AND lease_until <= clock_timestamp()) ORDER BY created_at, delivery_id FOR UPDATE SKIP LOCKED LIMIT 1)
      RETURNING delivery_id AS "deliveryId", installation_id::float8 AS "installationId", repository_id::float8 AS "repositoryId", number::float8 AS number, generation, selection_generation AS "selectionGeneration"`, [leaseMs]);
    return result.rows[0] ?? null;
  }

  async recordPullFailure(delivery: PullLease): Promise<void> {
    await this.pool.query("UPDATE proofci_pull_deliveries SET last_error='resolution_unavailable', lease_until=clock_timestamp()+interval '30 seconds' WHERE delivery_id=$1 AND generation=$2 AND state='processing'", [delivery.deliveryId, delivery.generation]);
  }

  async processPullDelivery(delivery: PullLease, resolve: (delivery: PullLease) => Promise<Candidate | string>): Promise<boolean> {
    const client = await this.pool.connect();
    const lane = `pull/${delivery.number}`;
    const key = `pull-delivery:${delivery.installationId}:${delivery.repositoryId}:${delivery.number}`;
    try {
      await client.query('SELECT pg_advisory_lock(hashtextextended($1, 0))', [key]);
      const candidate = await resolve(delivery);
      if (typeof candidate !== 'string') {
        validateCandidate(candidate);
        if (candidate.kind !== 'resolved' || candidate.installationId !== delivery.installationId || candidate.repositoryId !== delivery.repositoryId || candidate.lane !== lane) throw new Error('Resolved candidate does not match pull request');
      } else if (!/^[a-z][a-z0-9_]{0,127}$/.test(candidate)) throw new Error('Invalid resolution reason');
      await client.query('BEGIN');
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [delivery.installationId]);
      const current = await client.query<{ selection_generation: string }>("SELECT selection_generation FROM proofci_pull_deliveries WHERE delivery_id=$1 AND generation=$2 AND state='processing' AND lease_until > clock_timestamp() FOR UPDATE", [delivery.deliveryId, delivery.generation]);
      if (!current.rows[0]) { await client.query('ROLLBACK'); return false; }
      const selected = await client.query('SELECT 1 FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2 AND generation=$3', [delivery.installationId, delivery.repositoryId, current.rows[0].selection_generation]);
      const retry = typeof candidate === 'string' && ['merge_unresolved', 'merge_ref_missing', 'merge_ref_mismatch', 'merge_parents_mismatch', 'baseline_unavailable'].includes(candidate);
      if (selected.rowCount === 1) {
        if (typeof candidate !== 'string') {
          const id = await insertCandidate(client, candidate, current.rows[0].selection_generation);
          await client.query('UPDATE proofci_publications SET pending=true, revision=revision+1, needs_revalidation=false WHERE run_id=$1 AND needs_revalidation', [id]);
        } else if (retry) {
          await client.query(`UPDATE proofci_publications SET pending=true, revision=revision+1, needs_revalidation=true
            WHERE run_id IN (SELECT id FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable) AND NOT needs_revalidation`, [delivery.installationId, delivery.repositoryId, lane]);
        } else {
          await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`${delivery.installationId}:${delivery.repositoryId}:${lane}`]);
          await client.query(`WITH changed AS (UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable RETURNING id)
            UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed)`, [delivery.installationId, delivery.repositoryId, lane]);
        }
      }
      await client.query("UPDATE proofci_pull_deliveries SET state=CASE WHEN $3 THEN 'processing' ELSE 'done' END, lease_until=CASE WHEN $3 THEN clock_timestamp()+interval '30 seconds' ELSE NULL END, last_error=$2 WHERE delivery_id=$1", [delivery.deliveryId, typeof candidate === 'string' ? candidate : null, retry]);
      await client.query('COMMIT');
      return true;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { try { await client.query('SELECT pg_advisory_unlock(hashtextextended($1, 0))', [key]); } finally { client.release(); } }
  }

  async acceptDelivery(event: PushDelivery): Promise<boolean> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query("SET LOCAL lock_timeout='2s'");
      await client.query("SET LOCAL statement_timeout='5s'");
      await client.query('INSERT INTO proofci_installation_revisions (installation_id) VALUES ($1) ON CONFLICT DO NOTHING', [event.installationId]);
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [event.installationId]);
      const selected = await client.query<{ generation: string }>('SELECT generation FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2', [event.installationId, event.repositoryId]);
      if (!selected.rows[0]) { await client.query('COMMIT'); return false; }
      const result = await client.query(`INSERT INTO proofci_push_deliveries
        (delivery_id, installation_id, repository_id, ref, head, deleted, selection_generation) VALUES ($1,$2,$3,$4,$5,$6,$7)
        ON CONFLICT (delivery_id) DO UPDATE SET delivery_id=EXCLUDED.delivery_id
        WHERE proofci_push_deliveries.installation_id=EXCLUDED.installation_id AND proofci_push_deliveries.repository_id=EXCLUDED.repository_id
        AND proofci_push_deliveries.ref=EXCLUDED.ref AND proofci_push_deliveries.head=EXCLUDED.head AND proofci_push_deliveries.deleted=EXCLUDED.deleted
        AND proofci_push_deliveries.selection_generation=EXCLUDED.selection_generation RETURNING delivery_id`,
        [event.deliveryId, event.installationId, event.repositoryId, event.ref, event.head, event.deleted, selected.rows[0].generation]);
      await client.query('COMMIT');
      return result.rowCount === 1;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  async claimDelivery(leaseMs: number): Promise<DeliveryLease | null> {
    if (!Number.isSafeInteger(leaseMs) || leaseMs < 1 || leaseMs > 3_600_000) throw new Error('Invalid lease');
    const result = await this.pool.query<PushDelivery & { generation: number; selectionGeneration: string }>(`UPDATE proofci_push_deliveries SET state='processing', generation=generation+1, lease_until=clock_timestamp()+($1 * interval '1 millisecond')
      WHERE delivery_id=(SELECT delivery_id FROM proofci_push_deliveries WHERE state='queued' OR (state='processing' AND lease_until <= clock_timestamp()) ORDER BY created_at, delivery_id FOR UPDATE SKIP LOCKED LIMIT 1)
      RETURNING delivery_id AS "deliveryId", installation_id::float8 AS "installationId", repository_id::float8 AS "repositoryId", ref, head, deleted, generation, selection_generation AS "selectionGeneration"`, [leaseMs]);
    return result.rows[0] ?? null;
  }

  async recordDeliveryFailure(delivery: DeliveryLease): Promise<void> {
    await this.pool.query("UPDATE proofci_push_deliveries SET last_error='resolution_unavailable' WHERE delivery_id=$1 AND generation=$2 AND state='processing'", [delivery.deliveryId, delivery.generation]);
  }

  async listDeliveries(scope: RepositoryScope): Promise<Array<{ deliveryId: string; ref: string; state: string; lastError: string | null }>> {
    const result = await this.pool.query<{ deliveryId: string; ref: string; state: string; lastError: string | null }>('SELECT delivery_id AS "deliveryId", ref, state, last_error AS "lastError" FROM proofci_push_deliveries WHERE installation_id=$1 AND repository_id=$2 ORDER BY created_at DESC LIMIT 100', [scope.installationId, scope.repositoryId]);
    return result.rows;
  }

  async inspectPull(scope: RepositoryScope, number: number): Promise<{ state: string; lastError: string | null } | null> {
    const result = await this.pool.query<{ state: string; lastError: string | null }>('SELECT state, last_error AS "lastError" FROM proofci_pull_deliveries WHERE installation_id=$1 AND repository_id=$2 AND number=$3 ORDER BY created_at DESC LIMIT 1', [scope.installationId, scope.repositoryId, number]);
    return result.rows[0] ?? null;
  }

  /** Recheck published candidates when the protected baseline changes or becomes unavailable. */
  async reconcileBaseline(scope: RepositoryScope, baseline: string | null): Promise<number[]> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query(`UPDATE proofci_publications p SET pending=true, revision=revision+1, needs_revalidation=true
        FROM proofci_runs r WHERE p.run_id=r.id AND r.installation_id=$1 AND r.repository_id=$2 AND r.applicable
        AND r.baseline IS DISTINCT FROM $3 AND NOT p.needs_revalidation`, [scope.installationId, scope.repositoryId, baseline]);
      const result = await client.query<{ number: number }>(`SELECT substring(r.lane FROM 6)::float8 AS number FROM proofci_runs r JOIN proofci_publications p ON p.run_id=r.id
        WHERE r.installation_id=$1 AND r.repository_id=$2 AND r.applicable AND p.needs_revalidation AND r.lane ~ '^pull/[1-9][0-9]*$'
        AND NOT EXISTS (SELECT 1 FROM proofci_pull_deliveries d WHERE d.installation_id=r.installation_id AND d.repository_id=r.repository_id
          AND d.number=substring(r.lane FROM 6)::bigint AND d.state IN ('queued','processing'))`, [scope.installationId, scope.repositoryId]);
      await client.query('COMMIT');
      return result.rows.map(row => row.number);
    } catch (error) { await client.query('ROLLBACK'); throw error; } finally { client.release(); }
  }

  /** Resolve under a per-lane lock; only a current lease and selection may admit work. */
  async processDelivery(delivery: DeliveryLease, resolve: (delivery: DeliveryLease) => Promise<Candidate | 'deleted' | null>): Promise<boolean> {
    const client = await this.pool.connect();
    const key = `delivery:${delivery.installationId}:${delivery.repositoryId}:${delivery.ref}`;
    try {
      await client.query('SELECT pg_advisory_lock(hashtextextended($1, 0))', [key]);
      const candidate = await resolve(delivery);
      if (candidate && candidate !== 'deleted') {
        validateCandidate(candidate);
        if (candidate.kind !== 'head-snapshot' || candidate.installationId !== delivery.installationId || candidate.repositoryId !== delivery.repositoryId ||
            candidate.lane !== delivery.ref || candidate.head !== delivery.head) throw new Error('Resolved candidate does not match delivery');
      }
      await client.query('BEGIN');
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [delivery.installationId]);
      const current = await client.query<{ selection_generation: string }>(`SELECT selection_generation FROM proofci_push_deliveries
        WHERE delivery_id=$1 AND generation=$2 AND state='processing' AND lease_until > clock_timestamp() FOR UPDATE`, [delivery.deliveryId, delivery.generation]);
      if (!current.rows[0]) { await client.query('ROLLBACK'); return false; }
      const selected = await client.query('SELECT 1 FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2 AND generation=$3', [delivery.installationId, delivery.repositoryId, current.rows[0].selection_generation]);
      if (candidate && selected.rowCount === 1) {
        if (candidate === 'deleted') {
          if (!delivery.deleted) throw new Error('Invalid deletion result');
          await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`${delivery.installationId}:${delivery.repositoryId}:${delivery.ref}`]);
          await client.query("UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable", [delivery.installationId, delivery.repositoryId, delivery.ref]);
        } else await insertCandidate(client, candidate, current.rows[0].selection_generation);
      }
      await client.query("UPDATE proofci_push_deliveries SET state='done', lease_until=NULL, last_error=NULL WHERE delivery_id=$1", [delivery.deliveryId]);
      await client.query('COMMIT');
      return true;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally {
      try { await client.query('SELECT pg_advisory_unlock(hashtextextended($1, 0))', [key]); } finally { client.release(); }
    }
  }

  async admit(candidate: Candidate): Promise<string> {
    validateCandidate(candidate);
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query('INSERT INTO proofci_installation_revisions (installation_id) VALUES ($1) ON CONFLICT DO NOTHING', [candidate.installationId]);
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [candidate.installationId]);
      const selected = await client.query<{ generation: string }>('SELECT generation FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2', [candidate.installationId, candidate.repositoryId]);
      if (!selected.rows[0]) throw new Error('Repository not enrolled');
      const id = await insertCandidate(client, candidate, selected.rows[0].generation);
      await client.query('COMMIT');
      return id;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  async claim(leaseMs: number): Promise<Lease | null> {
    if (!Number.isSafeInteger(leaseMs) || leaseMs < 1 || leaseMs > 3_600_000) throw new Error('Invalid lease');
    await this.pool.query("UPDATE proofci_runs r SET state='cancelled', lease_until=NULL, completed_at=clock_timestamp() WHERE state IN ('queued','running') AND NOT EXISTS (SELECT 1 FROM proofci_repository_selections s WHERE s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation)");
    const result = await this.pool.query<Lease>(`UPDATE proofci_runs SET state='running', generation=generation+1,
      first_started_at=COALESCE(first_started_at, clock_timestamp()),
      recovery_seconds=recovery_seconds+CASE WHEN state='running' THEN greatest(0, extract(epoch from clock_timestamp()-lease_until)) ELSE 0 END,
      started_at=clock_timestamp(), lease_until=clock_timestamp()+($1 * interval '1 millisecond')
      WHERE id=(SELECT r.id FROM proofci_runs r WHERE ((r.state='queued' AND (r.lease_until IS NULL OR r.lease_until <= clock_timestamp())) OR (r.state='running' AND r.lease_until <= clock_timestamp()))
      AND EXISTS (SELECT 1 FROM proofci_repository_selections s WHERE s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation)
      ORDER BY r.created_at, r.id FOR UPDATE OF r SKIP LOCKED LIMIT 1) RETURNING id, generation,
      json_strip_nulls(json_build_object('kind', kind, 'installationId', installation_id, 'repositoryId', repository_id, 'lane', lane,
                        'head', head, 'base', base, 'baseline', baseline, 'pullHead', pull_head)) AS candidate`, [leaseMs]);
    return result.rows[0] ?? null;
  }

  async renew(lease: Lease, leaseMs: number): Promise<boolean> {
    if (!Number.isSafeInteger(leaseMs) || leaseMs < 1 || leaseMs > 3_600_000) throw new Error('Invalid lease');
    const result = await this.pool.query(`WITH selection AS MATERIALIZED (
      SELECT s.generation FROM proofci_repository_selections s JOIN proofci_runs r ON
      s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
      WHERE r.id=$1 FOR SHARE OF s)
      UPDATE proofci_runs SET lease_until=clock_timestamp()+($3 * interval '1 millisecond')
      WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp() AND EXISTS (SELECT 1 FROM selection)`, [lease.id, lease.generation, leaseMs]);
    return result.rowCount === 1;
  }

  async retry(lease: Lease): Promise<boolean> {
    const result = await this.pool.query("UPDATE proofci_runs SET state='queued', lease_until=clock_timestamp()+interval '30 seconds' WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp()", [lease.id, lease.generation]);
    return result.rowCount === 1;
  }

  async fail(lease: Lease, reason: string): Promise<boolean> {
    if (!/^[a-z][a-z0-9_]{0,127}$/.test(reason)) throw new Error('Invalid failure reason');
    return this.complete(lease, { version: 1, status: 'error', reason });
  }

  async complete(lease: Lease, report: unknown, evidence: Buffer | null = null): Promise<boolean> {
    const digest = evidence === null ? null : createHash('sha256').update(evidence).digest('hex');
    const result = await this.pool.query(`WITH selection AS MATERIALIZED (
      SELECT s.generation FROM proofci_repository_selections s JOIN proofci_runs r ON
      s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
      WHERE r.id=$1 FOR SHARE OF s)
      , changed AS (UPDATE proofci_runs SET state='completed', evidence=$4, evidence_sha256=$5, report=$3::jsonb || jsonb_build_object('evidence_bundle_sha256', $5::text, 'scheduler', jsonb_build_object(
        'scope', CASE WHEN kind='head-snapshot' THEN 'head-snapshot-nonenforcing' ELSE 'resolved-candidate' END, 'pull_head', pull_head, 'queue_seconds', extract(epoch from first_started_at-created_at),
        'execution_seconds', extract(epoch from clock_timestamp()-started_at), 'recovery_seconds', recovery_seconds,
        'recoveries', generation-1)), lease_until=NULL, completed_at=clock_timestamp()
      WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp() AND EXISTS (SELECT 1 FROM selection) RETURNING id),
      marked AS (UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed))
      SELECT id FROM changed`, [lease.id, lease.generation, JSON.stringify(report), evidence, digest]);
    return result.rowCount === 1;
  }

  async claimPublication(leaseMs: number): Promise<Publication | null> {
    if (!Number.isSafeInteger(leaseMs) || leaseMs < 1 || leaseMs > 3_600_000) throw new Error('Invalid lease');
    const result = await this.pool.query<Publication>(`WITH claimed AS (UPDATE proofci_publications SET generation=generation+1, lease_until=clock_timestamp()+($1 * interval '1 millisecond')
      WHERE run_id=(SELECT run_id FROM proofci_publications WHERE pending AND (lease_until IS NULL OR lease_until <= clock_timestamp()) ORDER BY run_id FOR UPDATE SKIP LOCKED LIMIT 1)
      RETURNING run_id, revision, generation)
      SELECT r.id, c.revision, c.generation AS "leaseGeneration", r.generation AS "runGeneration", r.state, r.applicable, r.report, r.evidence_sha256 AS "evidenceSha256",
      json_build_object('kind',r.kind,'installationId',r.installation_id::float8,'repositoryId',r.repository_id::float8,'lane',r.lane,'head',r.head,'base',r.base,'baseline',r.baseline,'pullHead',r.pull_head) AS candidate
      FROM claimed c JOIN proofci_runs r ON r.id=c.run_id`, [leaseMs]);
    return result.rows[0] ?? null;
  }

  async publicationCurrent(item: Publication): Promise<boolean> {
    const result = await this.pool.query(`UPDATE proofci_publications p SET lease_until=clock_timestamp()+interval '5 minutes' FROM proofci_runs r
      JOIN proofci_repository_selections s ON s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
      WHERE r.id=p.run_id AND r.id=$1 AND p.generation=$2 AND p.revision=$3 AND p.lease_until > clock_timestamp() AND r.generation=$4 AND r.state=$5 AND r.applicable`, [item.id, item.leaseGeneration, item.revision, item.runGeneration, item.state]);
    return result.rowCount === 1;
  }

  async ownsPublication(item: Publication): Promise<boolean> {
    const result = await this.pool.query('SELECT 1 FROM proofci_publications WHERE run_id=$1 AND generation=$2 AND pending AND lease_until > clock_timestamp()', [item.id, item.leaseGeneration]);
    return result.rowCount === 1;
  }

  async markPublicationUnresolved(item: Publication): Promise<void> {
    await this.pool.query('UPDATE proofci_publications SET needs_revalidation=true WHERE run_id=$1 AND generation=$2 AND lease_until > clock_timestamp()', [item.id, item.leaseGeneration]);
  }

  async finishPublication(item: Publication): Promise<boolean> {
    const result = await this.pool.query(`WITH finished AS (UPDATE proofci_publications SET pending=false, lease_until=NULL, last_error=NULL, published_at=clock_timestamp()
      WHERE run_id=$1 AND generation=$2 AND revision=$3 AND lease_until > clock_timestamp() RETURNING run_id)
      UPDATE proofci_runs SET report=CASE WHEN report IS NULL THEN NULL ELSE jsonb_set(report,'{scheduler,publication_seconds}',to_jsonb(greatest(0,extract(epoch from clock_timestamp()-completed_at)))) END
      WHERE id IN (SELECT run_id FROM finished)`, [item.id, item.leaseGeneration, item.revision]);
    return result.rowCount === 1;
  }

  async retryPublication(item: Publication): Promise<void> {
    await this.pool.query("UPDATE proofci_publications SET lease_until=clock_timestamp()+interval '30 seconds', last_error='publication_unavailable' WHERE run_id=$1 AND generation=$2 AND pending", [item.id, item.leaseGeneration]);
  }

  async withPublicationLock(id: string, publish: () => Promise<void>): Promise<boolean> {
    const client = await this.pool.connect();
    const key = `publication:${id}`;
    let locked = false;
    try {
      const result = await client.query<{ locked: boolean }>('SELECT pg_try_advisory_lock(hashtextextended($1, 0)) AS locked', [key]);
      locked = result.rows[0]?.locked === true;
      if (!locked) return false;
      await publish();
      return true;
    } finally {
      try { if (locked) await client.query('SELECT pg_advisory_unlock(hashtextextended($1, 0))', [key]); } finally { client.release(); }
    }
  }

  async cancelLease(lease: Lease): Promise<boolean> {
    const result = await this.pool.query(`WITH changed AS (UPDATE proofci_runs SET state='cancelled', lease_until=NULL, completed_at=clock_timestamp() WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp() RETURNING id),
      marked AS (UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed)) SELECT id FROM changed`, [lease.id, lease.generation]);
    return result.rowCount === 1;
  }

  async cancel(scope: RepositoryScope, id: string): Promise<boolean> {
    const result = await this.pool.query(`WITH changed AS (UPDATE proofci_runs SET state='cancelled', lease_until=NULL, completed_at=clock_timestamp() WHERE id=$1 AND installation_id=$2 AND repository_id=$3 AND state IN ('queued','running') RETURNING id),
      marked AS (UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed)) SELECT id FROM changed`, [id, scope.installationId, scope.repositoryId]);
    return result.rowCount === 1;
  }

  async list(scope: RepositoryScope): Promise<Run[]> {
    const result = await this.pool.query<Run>('SELECT id, state, applicable, report FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 ORDER BY created_at DESC LIMIT 100', [scope.installationId, scope.repositoryId]);
    return result.rows;
  }

  async inspect(scope: RepositoryScope, id: string): Promise<Run | null> {
    const result = await this.pool.query<Run>('SELECT id, state, applicable, report FROM proofci_runs WHERE id=$1 AND installation_id=$2 AND repository_id=$3', [id, scope.installationId, scope.repositoryId]);
    return result.rows[0] ?? null;
  }

  async evidence(scope: RepositoryScope, id: string): Promise<{ bytes: Buffer; sha256: string } | null> {
    const result = await this.pool.query<{ bytes: Buffer; sha256: string }>('SELECT evidence AS bytes, evidence_sha256 AS sha256 FROM proofci_runs WHERE id=$1 AND installation_id=$2 AND repository_id=$3 AND evidence IS NOT NULL', [id, scope.installationId, scope.repositoryId]);
    return result.rows[0] ?? null;
  }
}
