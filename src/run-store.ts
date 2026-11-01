import { randomUUID } from 'node:crypto';
import type { Pool, PoolClient } from 'pg';
import type { RepositoryScope } from './enrollment-store.ts';
import type { PushDelivery } from './push-events.ts';

export type Candidate = { kind: 'head-snapshot' | 'resolved'; installationId: number; repositoryId: number; lane: string; head: string; base: string; baseline: string };
export type DeliveryLease = PushDelivery & { generation: number; selectionGeneration: string };
export type Lease = { id: string; generation: number; candidate: Candidate };

function validateCandidate(candidate: Candidate): void {
  if ((candidate.kind !== 'head-snapshot' && candidate.kind !== 'resolved') || !Number.isSafeInteger(candidate.installationId) || candidate.installationId < 1 ||
      !Number.isSafeInteger(candidate.repositoryId) || candidate.repositoryId < 1 ||
      !candidate.lane || candidate.lane.length > 512 ||
      !/^[a-f0-9]{40}$/.test(candidate.head) || !/^[a-f0-9]{40}$/.test(candidate.base) ||
      !/^[a-f0-9]{64}$/.test(candidate.baseline)) throw new Error('Invalid immutable candidate');
}

async function insertCandidate(client: PoolClient, candidate: Candidate, selectionGeneration: string): Promise<string> {
  await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`${candidate.installationId}:${candidate.repositoryId}:${candidate.lane}`]);
  const params = [candidate.installationId, candidate.repositoryId, candidate.lane, candidate.head, candidate.base, candidate.baseline, candidate.kind];
  const existing = await client.query<{ id: string }>('SELECT id FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND head=$4 AND base=$5 AND baseline=$6 AND kind=$7 AND selection_generation=$8 AND applicable', [...params, selectionGeneration]);
  if (existing.rows[0]) return existing.rows[0].id;
  await client.query("UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable", params.slice(0, 3));
  const id = randomUUID();
  await client.query("INSERT INTO proofci_runs (id, installation_id, repository_id, lane, head, base, baseline, kind, selection_generation, state) VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,'queued')", [id, ...params, selectionGeneration]);
  return id;
}

type Run = { id: string; applicable: boolean; state: 'queued' | 'running' | 'completed' | 'failed' | 'cancelled'; report: unknown };

/** Durable lifecycle for already authorized, immutable candidates. */
export class RunStore {
  private readonly pool: Pool;
  constructor(pool: Pool) { this.pool = pool; }

  async initialize(): Promise<void> {
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_runs (
      id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL,
      lane TEXT NOT NULL, head TEXT NOT NULL, base TEXT NOT NULL, baseline TEXT NOT NULL, kind TEXT NOT NULL CHECK (kind IN ('head-snapshot','resolved')), selection_generation TEXT NOT NULL,
      state TEXT NOT NULL CHECK (state IN ('queued', 'running', 'completed', 'failed', 'cancelled')),
      generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, report JSONB,
      applicable BOOLEAN NOT NULL DEFAULT true,
      created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp(), first_started_at TIMESTAMPTZ, started_at TIMESTAMPTZ, completed_at TIMESTAMPTZ,
      recovery_seconds DOUBLE PRECISION NOT NULL DEFAULT 0
    )`);
    await this.pool.query(`DO $$ BEGIN
      PERFORM pg_advisory_xact_lock(hashtextextended('proofci_runs_state_migration', 0));
      IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conrelid='proofci_runs'::regclass
        AND conname='proofci_runs_state_check' AND pg_get_constraintdef(oid) LIKE '%''failed''%') THEN
        ALTER TABLE proofci_runs DROP CONSTRAINT IF EXISTS proofci_runs_state_check;
        ALTER TABLE proofci_runs ADD CONSTRAINT proofci_runs_state_check CHECK (state IN ('queued','running','completed','failed','cancelled'));
      END IF;
    END $$`);
    await this.pool.query('CREATE UNIQUE INDEX IF NOT EXISTS proofci_runs_applicable_lane ON proofci_runs (installation_id, repository_id, lane) WHERE applicable');
    await this.pool.query('ALTER TABLE proofci_runs ADD COLUMN IF NOT EXISTS evidence_id UUID');
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_evidence (
      id UUID PRIMARY KEY, run_id UUID NOT NULL REFERENCES proofci_runs(id), generation INTEGER NOT NULL,
      object_key TEXT NOT NULL UNIQUE, sha256 TEXT NOT NULL, bytes INTEGER NOT NULL,
      state TEXT NOT NULL CHECK (state IN ('pending','ready','deleting','expired')),
      created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp(), expires_at TIMESTAMPTZ
    )`);
    await this.pool.query("CREATE UNIQUE INDEX IF NOT EXISTS proofci_evidence_ready_run ON proofci_evidence(run_id) WHERE state='ready'");
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_push_deliveries (
      delivery_id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL,
      ref TEXT NOT NULL, head TEXT NOT NULL, deleted BOOLEAN NOT NULL, selection_generation TEXT NOT NULL,
      state TEXT NOT NULL DEFAULT 'queued' CHECK (state IN ('queued','processing','done')),
      generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, last_error TEXT,
      created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp()
    )`);
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
      json_build_object('kind', kind, 'installationId', installation_id, 'repositoryId', repository_id, 'lane', lane,
                        'head', head, 'base', base, 'baseline', baseline) AS candidate`, [leaseMs]);
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

  async complete(lease: Lease, report: unknown): Promise<boolean> {
    const result = await this.pool.query(`WITH selection AS MATERIALIZED (
      SELECT s.generation FROM proofci_repository_selections s JOIN proofci_runs r ON
      s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
      WHERE r.id=$1 FOR SHARE OF s)
      UPDATE proofci_runs SET state=CASE WHEN $3::jsonb->>'status'='error' THEN 'failed' ELSE 'completed' END, report=$3::jsonb || jsonb_build_object('scheduler', jsonb_build_object(
        'scope', CASE WHEN kind='head-snapshot' THEN 'head-snapshot-nonenforcing' ELSE 'resolved-candidate' END, 'queue_seconds', extract(epoch from first_started_at-created_at),
        'execution_seconds', extract(epoch from clock_timestamp()-started_at), 'recovery_seconds', recovery_seconds,
        'recoveries', generation-1)), lease_until=NULL, completed_at=clock_timestamp()
      WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp() AND EXISTS (SELECT 1 FROM selection)`, [lease.id, lease.generation, JSON.stringify(report)]);
    return result.rowCount === 1;
  }

  async reserveEvidence(lease: Lease, id: string, key: string, digest: string, bytes: number): Promise<boolean> {
    const result = await this.pool.query(`INSERT INTO proofci_evidence (id,run_id,generation,object_key,sha256,bytes,state)
      SELECT $3,r.id,r.generation,$4,$5,$6,'pending' FROM proofci_runs r
      JOIN proofci_repository_selections s ON s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
      WHERE r.id=$1 AND r.generation=$2 AND r.state='running' AND r.lease_until > clock_timestamp()
        AND r.installation_id=$7 AND r.repository_id=$8 AND r.head=$9 AND r.base=$10 AND r.baseline=$11`,
      [lease.id, lease.generation, id, key, digest, bytes, lease.candidate.installationId, lease.candidate.repositoryId,
        lease.candidate.head, lease.candidate.base, lease.candidate.baseline]);
    return result.rowCount === 1;
  }

  async completeEvidence(lease: Lease, id: string, report: unknown, retentionSeconds: number): Promise<boolean> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      const completed = await client.query(`WITH selection AS MATERIALIZED (
        SELECT s.generation FROM proofci_repository_selections s JOIN proofci_runs r ON
        s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
        WHERE r.id=$1 FOR SHARE OF s)
        UPDATE proofci_runs SET state='completed', report=$4::jsonb || jsonb_build_object('scheduler', jsonb_build_object(
          'scope', CASE WHEN kind='head-snapshot' THEN 'head-snapshot-nonenforcing' ELSE 'resolved-candidate' END,
          'queue_seconds', extract(epoch from first_started_at-created_at), 'execution_seconds', extract(epoch from clock_timestamp()-started_at),
          'recovery_seconds', recovery_seconds, 'recoveries', generation-1)) || jsonb_build_object('evidence', jsonb_build_object(
          'sha256', (SELECT sha256 FROM proofci_evidence WHERE id=$3),
          'url', format('/evidence/%s/%s/%s', installation_id, repository_id, id),
          'expires_at', transaction_timestamp()+($5 * interval '1 second'))), evidence_id=$3, lease_until=NULL, completed_at=clock_timestamp()
        WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp() AND EXISTS (SELECT 1 FROM selection)
        AND EXISTS (SELECT 1 FROM proofci_evidence WHERE id=$3 AND run_id=$1 AND generation=$2 AND state='pending')`,
        [lease.id, lease.generation, id, JSON.stringify(report), retentionSeconds]);
      if (completed.rowCount !== 1) { await client.query('ROLLBACK'); return false; }
      await client.query("UPDATE proofci_evidence SET state='ready', expires_at=transaction_timestamp()+($2 * interval '1 second') WHERE id=$1", [id, retentionSeconds]);
      await client.query('COMMIT');
      return true;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  async evidence(scope: RepositoryScope, runId: string): Promise<{ key: string; sha256: string; bytes: number; expired: boolean } | null> {
    const result = await this.pool.query<{ key: string; sha256: string; bytes: number; expired: boolean }>(`SELECT e.object_key AS key,e.sha256,e.bytes,(e.state='expired' OR e.state='deleting' OR e.expires_at <= clock_timestamp()) AS expired
      FROM proofci_evidence e JOIN proofci_runs r ON r.id=e.run_id AND r.evidence_id=e.id JOIN proofci_repository_selections s
      ON s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
      WHERE r.id=$1 AND r.installation_id=$2 AND r.repository_id=$3 AND r.state='completed' AND e.state IN ('ready','deleting','expired')`, [runId, scope.installationId, scope.repositoryId]);
    return result.rows[0] ?? null;
  }

  async expiredEvidence(): Promise<Array<{ id: string; key: string }>> {
    const result = await this.pool.query<{ id: string; key: string }>(`UPDATE proofci_evidence SET state='deleting' WHERE id IN (
      SELECT id FROM proofci_evidence WHERE (state='ready' AND expires_at <= clock_timestamp()) OR (state='pending' AND created_at < clock_timestamp()-interval '2 hours') OR state='deleting'
      LIMIT 100 FOR UPDATE SKIP LOCKED) RETURNING id,object_key AS key`);
    return result.rows;
  }

  async evidenceDeleted(id: string): Promise<void> {
    await this.pool.query("UPDATE proofci_evidence SET state='expired' WHERE id=$1 AND state='deleting'", [id]);
  }

  async cancelLease(lease: Lease): Promise<boolean> {
    const result = await this.pool.query("UPDATE proofci_runs SET state='cancelled', lease_until=NULL, completed_at=clock_timestamp() WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp()", [lease.id, lease.generation]);
    return result.rowCount === 1;
  }

  async cancel(scope: RepositoryScope, id: string): Promise<boolean> {
    const result = await this.pool.query("UPDATE proofci_runs SET state='cancelled', lease_until=NULL, completed_at=clock_timestamp() WHERE id=$1 AND installation_id=$2 AND repository_id=$3 AND state IN ('queued','running')", [id, scope.installationId, scope.repositoryId]);
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
}
