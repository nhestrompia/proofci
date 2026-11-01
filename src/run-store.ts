import { createHash, randomUUID } from 'node:crypto';
import type { Pool, PoolClient } from 'pg';
import type { RepositoryScope } from './enrollment-store.ts';
import type { PushDelivery } from './push-events.ts';
import type { PullDelivery } from './pull-events.ts';

type CandidateInputs = { installationId: number; repositoryId: number; lane: string; head: string; base: string; baseline: string; pullHead?: string | null; mergeHead?: string | null; authorityEpoch?: number };
export type Candidate = CandidateInputs & ({ kind: 'head-snapshot' | 'resolved' } | { kind: 'pull-request'; sourceRepositoryId: number; number: number });
export type PullLease = PullDelivery & { generation: number; selectionGeneration: string };

export type DeliveryLease = PushDelivery & { generation: number; selectionGeneration: string };
export type Lease = { id: string; generation: number; candidate: Candidate };
export type Publication = { id: string; revision: number; leaseGeneration: number; runGeneration: number; candidate: Candidate; state: 'queued' | 'running' | 'completed' | 'cancelled'; applicable: boolean; report: unknown; evidenceSha256: string | null };

function validateCandidate(candidate: Candidate): void {
  if ((candidate.kind !== 'head-snapshot' && candidate.kind !== 'resolved' && candidate.kind !== 'pull-request') || !Number.isSafeInteger(candidate.installationId) || candidate.installationId < 1 ||
      !Number.isSafeInteger(candidate.repositoryId) || candidate.repositoryId < 1 ||
      !candidate.lane || candidate.lane.length > 512 ||
      (candidate.kind === 'pull-request' && (!Number.isSafeInteger(candidate.sourceRepositoryId) || candidate.sourceRepositoryId < 1 || !Number.isSafeInteger(candidate.number) || candidate.number < 1 || candidate.lane !== `pull/${candidate.number}`)) ||
      !/^[a-f0-9]{40}$/.test(candidate.head) || !/^[a-f0-9]{40}$/.test(candidate.base) ||
      !/^[a-f0-9]{64}$/.test(candidate.baseline) ||
      (candidate.kind === 'resolved' && /^pull\/[1-9]\d*$/.test(candidate.lane) && (typeof candidate.pullHead !== 'string' || !/^[a-f0-9]{40}$/.test(candidate.pullHead)))) throw new Error('Invalid immutable candidate');
}

async function insertCandidate(client: PoolClient, candidate: Candidate, selectionGeneration: string, authorityEpoch: number | null): Promise<string> {
  await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`${candidate.installationId}:${candidate.repositoryId}:${candidate.lane}`]);
  const params = [candidate.installationId, candidate.repositoryId, candidate.lane, candidate.head, candidate.base, candidate.baseline, candidate.kind, candidate.kind === 'pull-request' ? candidate.sourceRepositoryId : null, candidate.kind === 'pull-request' ? candidate.number : null, candidate.mergeHead ?? null, candidate.pullHead ?? null];
  const existing = await client.query<{ id: string }>('SELECT id FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND head=$4 AND base=$5 AND baseline=$6 AND kind=$7 AND source_repository_id IS NOT DISTINCT FROM $8 AND pull_number IS NOT DISTINCT FROM $9 AND merge_head IS NOT DISTINCT FROM $10 AND pull_head IS NOT DISTINCT FROM $11 AND selection_generation=$12 AND authority_epoch IS NOT DISTINCT FROM $13 AND applicable', [...params, selectionGeneration, authorityEpoch]);
  if (existing.rows[0]) return existing.rows[0].id;
  if (candidate.kind === 'pull-request') {
    await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-policy:${candidate.installationId}:${candidate.repositoryId}:${candidate.number}`]);
    await client.query(`INSERT INTO proofci_fork_policy_revisions (installation_id, repository_id, pull_number, revision) VALUES ($1,$2,$3,1)
      ON CONFLICT (installation_id, repository_id, pull_number) DO UPDATE SET revision=proofci_fork_policy_revisions.revision+1`, [candidate.installationId, candidate.repositoryId, candidate.number]);
    await client.query('DELETE FROM proofci_fork_decisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', [candidate.installationId, candidate.repositoryId, candidate.number]);
  }
  await client.query(`WITH changed AS (UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable RETURNING id) UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed)`, params.slice(0, 3));
  const id = randomUUID();
  await client.query("INSERT INTO proofci_runs (id, installation_id, repository_id, lane, head, base, baseline, kind, source_repository_id, pull_number, merge_head, pull_head, selection_generation, authority_epoch, state) VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,$12,$13,$14,'queued')", [id, ...params, selectionGeneration, authorityEpoch]);

  if (candidate.kind === 'pull-request' || (candidate.kind === 'resolved' && /^pull\/[1-9]\d*$/.test(candidate.lane))) await client.query('INSERT INTO proofci_publications (run_id) VALUES ($1)', [id]);
  return id;
}

type Run = { id: string; applicable: boolean; state: 'queued' | 'running' | 'completed' | 'cancelled'; report: unknown };
type StoredRun = Run & { authority_epoch: string | null };

/** Durable lifecycle for already authorized, immutable candidates. */
export class RunStore {
  private readonly pool: Pool;
  private readonly authority?: { current(scope: RepositoryScope): Promise<number | null> };
  constructor(pool: Pool, authority?: { current(scope: RepositoryScope): Promise<number | null> }) { this.pool = pool; this.authority = authority; }

  private async applicability(scope: RepositoryScope, runs: StoredRun[]): Promise<Run[]> {
    const epoch = await this.authority?.current(scope) ?? null;
    return runs.map(({ authority_epoch: admittedEpoch, ...run }) => {
      if (!run.applicable) return run;
      if (!this.authority && admittedEpoch === null) return run;
      if (epoch === null || admittedEpoch !== String(epoch)) return { ...run, applicable: false };
      if (run.state !== 'completed') return run;
      const report = run.report;
      const valid = typeof report === 'object' && report !== null &&
        'authority_epoch' in report && report.authority_epoch === epoch;
      return { ...run, applicable: valid };
    });
  }

  async initialize(): Promise<void> {
    const migration = await this.pool.connect();
    try {
      await migration.query('BEGIN');
      await migration.query("SELECT pg_advisory_xact_lock(hashtextextended(current_schema() || ':proofci-runs-migration', 0))");
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_runs (
      id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL,
      lane TEXT NOT NULL, head TEXT NOT NULL, base TEXT NOT NULL, baseline TEXT NOT NULL, kind TEXT NOT NULL CHECK (kind IN ('head-snapshot','resolved','pull-request')), source_repository_id BIGINT, pull_number BIGINT, selection_generation TEXT NOT NULL,
      state TEXT NOT NULL CHECK (state IN ('queued', 'running', 'completed', 'cancelled')),
      generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, report JSONB,
      applicable BOOLEAN NOT NULL DEFAULT true,
      created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp(), first_started_at TIMESTAMPTZ, started_at TIMESTAMPTZ, completed_at TIMESTAMPTZ,
      recovery_seconds DOUBLE PRECISION NOT NULL DEFAULT 0
    )`);
      await migration.query('ALTER TABLE proofci_runs ADD COLUMN IF NOT EXISTS authority_epoch BIGINT');
      await migration.query('ALTER TABLE proofci_runs ADD COLUMN IF NOT EXISTS source_repository_id BIGINT, ADD COLUMN IF NOT EXISTS pull_number BIGINT');
      await migration.query('ALTER TABLE proofci_runs DROP CONSTRAINT IF EXISTS proofci_runs_kind_check');
      await migration.query("ALTER TABLE proofci_runs ADD CONSTRAINT proofci_runs_kind_check CHECK (kind IN ('head-snapshot','resolved','pull-request'))");
      await migration.query('CREATE UNIQUE INDEX IF NOT EXISTS proofci_runs_applicable_lane ON proofci_runs (installation_id, repository_id, lane) WHERE applicable');
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_fork_decisions (
        installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, pull_number BIGINT NOT NULL,
        decision JSONB NOT NULL, created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp(),
        PRIMARY KEY (installation_id, repository_id, pull_number))`);
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_fork_policy_revisions (
        installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, pull_number BIGINT NOT NULL, revision BIGINT NOT NULL DEFAULT 0,
        PRIMARY KEY (installation_id, repository_id, pull_number))`);
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_fork_policies (
        installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, digest TEXT NOT NULL, revision BIGINT NOT NULL DEFAULT 1,
        PRIMARY KEY (installation_id, repository_id))`);
      await migration.query('ALTER TABLE proofci_fork_policies ADD COLUMN IF NOT EXISTS revision BIGINT NOT NULL DEFAULT 1');
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_pull_deliveries (
        delivery_id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, pull_number BIGINT NOT NULL, selection_generation TEXT NOT NULL,
        state TEXT NOT NULL DEFAULT 'queued' CHECK (state IN ('queued','processing','done')), generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp()
      )`);
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_push_deliveries (
        delivery_id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL,
        ref TEXT NOT NULL, head TEXT NOT NULL, deleted BOOLEAN NOT NULL, selection_generation TEXT NOT NULL,
        state TEXT NOT NULL DEFAULT 'queued' CHECK (state IN ('queued','processing','done')),
        generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ, last_error TEXT,
        created_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp()
      )`);
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_push_fences (
        delivery_id UUID PRIMARY KEY, installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL,
        ref TEXT NOT NULL, head TEXT NOT NULL, deleted BOOLEAN NOT NULL, selection_generation TEXT NOT NULL
      )`);
      await migration.query(`CREATE TABLE IF NOT EXISTS proofci_repository_push_revisions (installation_id BIGINT NOT NULL, repository_id BIGINT NOT NULL, revision BIGINT NOT NULL DEFAULT 0, PRIMARY KEY (installation_id, repository_id))`);
    await migration.query('ALTER TABLE proofci_runs ADD COLUMN IF NOT EXISTS evidence BYTEA, ADD COLUMN IF NOT EXISTS evidence_sha256 TEXT, ADD COLUMN IF NOT EXISTS pull_head TEXT, ADD COLUMN IF NOT EXISTS merge_head TEXT');
    await migration.query(`CREATE TABLE IF NOT EXISTS proofci_publications (
      run_id UUID PRIMARY KEY REFERENCES proofci_runs(id), pending BOOLEAN NOT NULL DEFAULT true,
      revision INTEGER NOT NULL DEFAULT 1, generation INTEGER NOT NULL DEFAULT 0, lease_until TIMESTAMPTZ,
      last_error TEXT, published_at TIMESTAMPTZ
    )`);
    await migration.query('ALTER TABLE proofci_publications ADD COLUMN IF NOT EXISTS needs_revalidation BOOLEAN NOT NULL DEFAULT false');
    await migration.query("INSERT INTO proofci_publications (run_id) SELECT id FROM proofci_runs WHERE kind='resolved' AND lane ~ '^pull/[1-9][0-9]*$' ON CONFLICT DO NOTHING");
    await migration.query(`CREATE OR REPLACE FUNCTION proofci_fence_selection() RETURNS trigger LANGUAGE plpgsql AS $$
      BEGIN
        IF TG_OP = 'UPDATE' AND NEW.generation = OLD.generation THEN RETURN NEW; END IF;
        WITH changed AS (UPDATE proofci_runs SET applicable=false,
          state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END,
          lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END
          WHERE installation_id=OLD.installation_id AND repository_id=OLD.repository_id AND selection_generation=OLD.generation AND applicable RETURNING id)
        UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id IN (SELECT id FROM changed);
        RETURN OLD;
      END $$`);
    await migration.query('DROP TRIGGER IF EXISTS proofci_fence_selection_trigger ON proofci_repository_selections');
    await migration.query('CREATE TRIGGER proofci_fence_selection_trigger AFTER DELETE OR UPDATE OF generation ON proofci_repository_selections FOR EACH ROW EXECUTE FUNCTION proofci_fence_selection()');
      await migration.query(`CREATE OR REPLACE FUNCTION proofci_queue_run_change() RETURNS trigger LANGUAGE plpgsql AS $$
        BEGIN
          IF NEW.applicable IS DISTINCT FROM OLD.applicable OR NEW.state IS DISTINCT FROM OLD.state OR NEW.generation IS DISTINCT FROM OLD.generation THEN
            UPDATE proofci_publications SET pending=true, revision=revision+1 WHERE run_id=NEW.id;
          END IF;
          RETURN NEW;
        END $$`);
      await migration.query('DROP TRIGGER IF EXISTS proofci_queue_run_change_trigger ON proofci_runs');
      await migration.query('CREATE TRIGGER proofci_queue_run_change_trigger AFTER UPDATE ON proofci_runs FOR EACH ROW EXECUTE FUNCTION proofci_queue_run_change()');
      await migration.query('ALTER TABLE proofci_pull_deliveries ADD COLUMN IF NOT EXISTS last_error TEXT');
      await migration.query('COMMIT');
    } catch (error) { await migration.query('ROLLBACK'); throw error; }
    finally { migration.release(); }

  }

  async acceptDelivery(event: PushDelivery, scheduleHead = true, invalidatePulls = true): Promise<boolean> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query("SET LOCAL lock_timeout='2s'");
      await client.query("SET LOCAL statement_timeout='5s'");
      await client.query('INSERT INTO proofci_installation_revisions (installation_id) VALUES ($1) ON CONFLICT DO NOTHING', [event.installationId]);
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [event.installationId]);
      const selected = await client.query<{ generation: string }>('SELECT generation FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2', [event.installationId, event.repositoryId]);
      if (!selected.rows[0]) { await client.query('COMMIT'); return false; }
      if (invalidatePulls) {
        const values = [event.deliveryId, event.installationId, event.repositoryId, event.ref, event.head, event.deleted, selected.rows[0].generation];
        const inserted = await client.query(`INSERT INTO proofci_push_fences (delivery_id, installation_id, repository_id, ref, head, deleted, selection_generation)
          VALUES ($1,$2,$3,$4,$5,$6,$7) ON CONFLICT (delivery_id) DO NOTHING RETURNING delivery_id`, values);
        if (!inserted.rowCount) {
          const prior = await client.query('SELECT 1 FROM proofci_push_fences WHERE delivery_id=$1 AND installation_id=$2 AND repository_id=$3 AND ref=$4 AND head=$5 AND deleted=$6 AND selection_generation=$7', values);
          if (!prior.rowCount) { await client.query('ROLLBACK'); return false; }
        } else {
          await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-resource:${event.installationId}:${event.repositoryId}`]);
          await client.query(`INSERT INTO proofci_repository_push_revisions (installation_id, repository_id, revision) VALUES ($1,$2,1)
            ON CONFLICT (installation_id, repository_id) DO UPDATE SET revision=proofci_repository_push_revisions.revision+1`, [event.installationId, event.repositoryId]);
          await client.query(`INSERT INTO proofci_pull_deliveries (delivery_id, installation_id, repository_id, pull_number, selection_generation)
            SELECT gen_random_uuid(), $1, $2, number, $3 FROM (SELECT DISTINCT pull_number AS number FROM proofci_runs
              WHERE installation_id=$1 AND repository_id=$2 AND kind='pull-request' AND applicable) pulls`, [event.installationId, event.repositoryId, selected.rows[0].generation]);
          await client.query('UPDATE proofci_fork_policies SET revision=revision+1 WHERE installation_id=$1 AND repository_id=$2', [event.installationId, event.repositoryId]);
          await client.query('DELETE FROM proofci_fork_decisions WHERE installation_id=$1 AND repository_id=$2', [event.installationId, event.repositoryId]);
          await client.query("UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND kind='pull-request' AND applicable", [event.installationId, event.repositoryId]);
        }
      }
      if (!scheduleHead) { await client.query('COMMIT'); return true; }
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

  async acceptPullDelivery(event: PullDelivery, invalidate = true): Promise<boolean> {
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query("SET LOCAL lock_timeout='2s'");
      await client.query("SET LOCAL statement_timeout='5s'");
      await client.query('INSERT INTO proofci_installation_revisions (installation_id) VALUES ($1) ON CONFLICT DO NOTHING', [event.installationId]);
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [event.installationId]);
      const selected = await client.query<{ generation: string }>('SELECT generation FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2', [event.installationId, event.repositoryId]);
      if (!selected.rows[0]) { await client.query('COMMIT'); return false; }
      await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`${event.installationId}:${event.repositoryId}:pull/${event.number}`]);
      await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-policy:${event.installationId}:${event.repositoryId}:${event.number}`]);
      if (!invalidate) {
        const pending = await client.query("SELECT 1 FROM proofci_pull_deliveries WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3 AND selection_generation=$4 AND state IN ('queued','processing') LIMIT 1", [event.installationId, event.repositoryId, event.number, selected.rows[0].generation]);
        if (pending.rowCount) { await client.query('COMMIT'); return true; }
      }
      const result = await client.query(`INSERT INTO proofci_pull_deliveries (delivery_id, installation_id, repository_id, pull_number, selection_generation)
        VALUES ($1,$2,$3,$4,$5) ON CONFLICT (delivery_id) DO NOTHING RETURNING delivery_id`,
      [event.deliveryId, event.installationId, event.repositoryId, event.number, selected.rows[0].generation]);
      if (result.rowCount === 1 && invalidate) {
        await client.query("UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable AND state IN ('queued','running')", [event.installationId, event.repositoryId, `pull/${event.number}`]);
        await client.query(`UPDATE proofci_publications SET pending=true, revision=revision+1, needs_revalidation=true
          WHERE run_id IN (SELECT id FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable)`, [event.installationId, event.repositoryId, `pull/${event.number}`]);
        await client.query(`INSERT INTO proofci_fork_policy_revisions (installation_id, repository_id, pull_number, revision) VALUES ($1,$2,$3,1)
          ON CONFLICT (installation_id, repository_id, pull_number) DO UPDATE SET revision=proofci_fork_policy_revisions.revision+1`, [event.installationId, event.repositoryId, event.number]);
        await client.query('DELETE FROM proofci_fork_decisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', [event.installationId, event.repositoryId, event.number]);
      } else if (!result.rowCount) {
        const existing = await client.query('SELECT 1 FROM proofci_pull_deliveries WHERE delivery_id=$1 AND installation_id=$2 AND repository_id=$3 AND pull_number=$4 AND selection_generation=$5', [event.deliveryId, event.installationId, event.repositoryId, event.number, selected.rows[0].generation]);
        if (!existing.rowCount) { await client.query('ROLLBACK'); return false; }
      }
      await client.query('COMMIT');
      return true;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  async reconcilePulls(scope: RepositoryScope, openNumbers: number[], includeKnown = true): Promise<void> {
    const known = includeKnown ? (await this.pool.query<{ number: number }>("SELECT pull_number::float8 AS number FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 AND kind='pull-request' AND applicable", [scope.installationId, scope.repositoryId])).rows.map(item => item.number) : [];
    for (const number of new Set([...openNumbers, ...known])) await this.acceptPullDelivery({ ...scope, number, deliveryId: randomUUID() }, false);
  }

  async claimPullDelivery(leaseMs: number): Promise<PullLease | null> {
    if (!Number.isSafeInteger(leaseMs) || leaseMs < 1 || leaseMs > 3_600_000) throw new Error('Invalid lease');
    const result = await this.pool.query<PullLease>(`UPDATE proofci_pull_deliveries SET state='processing', generation=generation+1, lease_until=clock_timestamp()+($1 * interval '1 millisecond')
      WHERE delivery_id=(SELECT delivery_id FROM proofci_pull_deliveries WHERE state='queued' OR (state='processing' AND lease_until <= clock_timestamp()) ORDER BY created_at, delivery_id FOR UPDATE SKIP LOCKED LIMIT 1)
      RETURNING delivery_id AS "deliveryId", installation_id::float8 AS "installationId", repository_id::float8 AS "repositoryId", pull_number::float8 AS number, generation, selection_generation AS "selectionGeneration"`, [leaseMs]);
    return result.rows[0] ?? null;
  }

  async recordPullFailure(delivery: PullLease): Promise<void> {
    await this.pool.query("UPDATE proofci_pull_deliveries SET last_error='resolution_unavailable', lease_until=clock_timestamp()+interval '30 seconds' WHERE delivery_id=$1 AND generation=$2 AND state='processing'", [delivery.deliveryId, delivery.generation]);
  }

  /** Resolve each notification under a per-PR lock and fence stale selections and leases. */
  async processPullDelivery(delivery: PullLease, resolve: (delivery: PullLease) => Promise<Candidate | 'closed' | 'baseline-unavailable' | 'merge-conflict' | 'merge-unavailable' | null>): Promise<boolean> {
    const client = await this.pool.connect();
    const key = `pull:${delivery.installationId}:${delivery.repositoryId}:${delivery.number}`;
    try {
      await client.query('SELECT pg_advisory_lock(hashtextextended($1, 0))', [key]);
      const values = [delivery.installationId, delivery.repositoryId, delivery.number];
      const before = await client.query<{ revision: string }>('SELECT revision FROM proofci_fork_policy_revisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', values);
      const pushBefore = await client.query<{ revision: string }>('SELECT revision FROM proofci_repository_push_revisions WHERE installation_id=$1 AND repository_id=$2', values.slice(0, 2));
      const candidate = await resolve(delivery);
      if (candidate && typeof candidate !== 'string') {
        validateCandidate(candidate);
        if (candidate.kind !== 'pull-request' || candidate.installationId !== delivery.installationId || candidate.repositoryId !== delivery.repositoryId || candidate.number !== delivery.number) throw new Error('Resolved candidate does not match delivery');
      }
      await client.query('BEGIN');
      await client.query('SELECT revision FROM proofci_installation_revisions WHERE installation_id=$1 FOR UPDATE', [delivery.installationId]);
      const current = await client.query<{ selection_generation: string }>("SELECT selection_generation FROM proofci_pull_deliveries WHERE delivery_id=$1 AND generation=$2 AND state='processing' AND lease_until > clock_timestamp() FOR UPDATE", [delivery.deliveryId, delivery.generation]);
      if (!current.rows[0]) { await client.query('ROLLBACK'); return false; }
      const selected = await client.query('SELECT 1 FROM proofci_repository_selections WHERE installation_id=$1 AND repository_id=$2 AND generation=$3', [delivery.installationId, delivery.repositoryId, current.rows[0].selection_generation]);
      if (candidate && selected.rowCount === 1) {
        const lane = `pull/${delivery.number}`;
        await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`${delivery.installationId}:${delivery.repositoryId}:${lane}`]);
        await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-policy:${delivery.installationId}:${delivery.repositoryId}:${delivery.number}`]);
        const now = await client.query<{ revision: string }>('SELECT revision FROM proofci_fork_policy_revisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', values);
        const pushNow = await client.query<{ revision: string }>('SELECT revision FROM proofci_repository_push_revisions WHERE installation_id=$1 AND repository_id=$2', values.slice(0, 2));
        if ((before.rows[0]?.revision ?? '0') !== (now.rows[0]?.revision ?? '0') || (pushBefore.rows[0]?.revision ?? '0') !== (pushNow.rows[0]?.revision ?? '0')) {
          await client.query("UPDATE proofci_pull_deliveries SET state='queued', lease_until=NULL WHERE delivery_id=$1", [delivery.deliveryId]);
          await client.query('COMMIT');
          return true;
        }
        if (candidate === 'merge-conflict' || candidate === 'merge-unavailable') {
          await client.query(`UPDATE proofci_publications SET pending=true, revision=revision+1, needs_revalidation=true
            WHERE run_id IN (SELECT id FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable) AND NOT needs_revalidation`, [delivery.installationId, delivery.repositoryId, lane]);
          await client.query("UPDATE proofci_pull_deliveries SET state='processing', lease_until=clock_timestamp()+interval '30 seconds', last_error=$2 WHERE delivery_id=$1", [delivery.deliveryId, candidate]);
          await client.query('COMMIT');
          return true;
        }
        if (candidate === 'closed' || candidate === 'baseline-unavailable') {
          await client.query(`INSERT INTO proofci_fork_policy_revisions (installation_id, repository_id, pull_number, revision) VALUES ($1,$2,$3,1)
            ON CONFLICT (installation_id, repository_id, pull_number) DO UPDATE SET revision=proofci_fork_policy_revisions.revision+1`, [delivery.installationId, delivery.repositoryId, delivery.number]);
          await client.query('DELETE FROM proofci_fork_decisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', [delivery.installationId, delivery.repositoryId, delivery.number]);
          await client.query("UPDATE proofci_runs SET applicable=false, state=CASE WHEN state IN ('queued','running') THEN 'cancelled' ELSE state END, lease_until=NULL, completed_at=CASE WHEN state IN ('queued','running') THEN clock_timestamp() ELSE completed_at END WHERE installation_id=$1 AND repository_id=$2 AND lane=$3 AND applicable", [delivery.installationId, delivery.repositoryId, lane]);
        } else {
          const epoch = await this.authority?.current(candidate) ?? null;
          if (this.authority && epoch === null) throw new Error('Repository authority unavailable');
          const id = await insertCandidate(client, candidate, current.rows[0].selection_generation, epoch);
          await client.query('UPDATE proofci_publications SET pending=true, revision=revision+1, needs_revalidation=false WHERE run_id=$1 AND needs_revalidation', [id]);
        }
      }
      await client.query("UPDATE proofci_pull_deliveries SET state='done', lease_until=NULL, last_error=NULL WHERE delivery_id=$1", [delivery.deliveryId]);
      await client.query('COMMIT');
      return true;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { try { await client.query('SELECT pg_advisory_unlock(hashtextextended($1, 0))', [key]); } finally { client.release(); } }
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
    const result = await this.pool.query<{ state: string; lastError: string | null }>('SELECT state, last_error AS "lastError" FROM proofci_pull_deliveries WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3 ORDER BY created_at DESC LIMIT 1', [scope.installationId, scope.repositoryId, number]);
    return result.rows[0] ?? null;
  }

  /** Recheck published candidates when the protected baseline changes or becomes unavailable. */
  async reconcileBaseline(scope: RepositoryScope, baseline: string | null): Promise<number[]> {
    const epoch = this.authority ? await this.authority.current(scope) : null;
    const client = await this.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query(`UPDATE proofci_publications p SET pending=true, revision=revision+1, needs_revalidation=true
        FROM proofci_runs r WHERE p.run_id=r.id AND r.installation_id=$1 AND r.repository_id=$2 AND r.applicable
        AND (r.baseline IS DISTINCT FROM $3 OR ($4::boolean AND ($5::bigint IS NULL OR r.authority_epoch IS DISTINCT FROM $5))) AND NOT p.needs_revalidation`, [scope.installationId, scope.repositoryId, baseline, !!this.authority, epoch]);
      const result = await client.query<{ number: number }>(`SELECT substring(r.lane FROM 6)::float8 AS number FROM proofci_runs r JOIN proofci_publications p ON p.run_id=r.id
        WHERE r.installation_id=$1 AND r.repository_id=$2 AND r.applicable AND p.needs_revalidation AND r.lane ~ '^pull/[1-9][0-9]*$'
        AND NOT EXISTS (SELECT 1 FROM proofci_pull_deliveries d WHERE d.installation_id=r.installation_id AND d.repository_id=r.repository_id
          AND d.pull_number=substring(r.lane FROM 6)::bigint AND d.state IN ('queued','processing'))`, [scope.installationId, scope.repositoryId]);
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
        } else {
          const epoch = await this.authority?.current(candidate) ?? null;
          if (this.authority && epoch === null) throw new Error('Repository authority unavailable');
          await insertCandidate(client, candidate, current.rows[0].selection_generation, epoch);
        }
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
      const epoch = await this.authority?.current(candidate) ?? null;
      if (this.authority && epoch === null) throw new Error('Repository authority unavailable');
      const id = await insertCandidate(client, candidate, selected.rows[0].generation, epoch);
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
      jsonb_strip_nulls(jsonb_build_object('kind', kind, 'installationId', installation_id, 'repositoryId', repository_id, 'lane', lane,
                        'head', head, 'base', base, 'baseline', baseline, 'mergeHead', merge_head, 'pullHead', pull_head, 'authorityEpoch', authority_epoch)) || CASE WHEN kind='pull-request' THEN json_build_object('sourceRepositoryId', source_repository_id::float8, 'number', pull_number::float8)::jsonb ELSE '{}'::jsonb END AS candidate`, [leaseMs]);

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

  /** Start the process while holding the run and selection locks, then release them. */
  async startDispatch(lease: Lease, start: () => Promise<Record<string, unknown>>, abort: () => void): Promise<Record<string, unknown>> {
    const client = await this.pool.connect();
    let operation: Promise<Record<string, unknown>> | undefined;
    try {
      await client.query('BEGIN');
      const selected = await client.query(`SELECT r.id FROM proofci_runs r JOIN proofci_repository_selections s ON
        s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
        WHERE r.id=$1 AND r.generation=$2 AND r.state='running' AND r.applicable AND r.lease_until > clock_timestamp() FOR UPDATE OF r FOR SHARE OF s`, [lease.id, lease.generation]);
      if (!selected.rowCount) throw new Error('Run is no longer active');
      operation = start();
      void operation.catch(() => {});
      await client.query('COMMIT');
    } catch (error) { if (operation) abort(); await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
    return operation;
  }

  async retry(lease: Lease, report: unknown = null): Promise<boolean> {
    const result = await this.pool.query("UPDATE proofci_runs SET state='queued', report=COALESCE($3::jsonb, report), lease_until=clock_timestamp()+interval '30 seconds' WHERE id=$1 AND generation=$2 AND state='running' AND lease_until > clock_timestamp()", [lease.id, lease.generation, report === null ? null : JSON.stringify(report)]);

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
      json_build_object('kind',r.kind,'installationId',r.installation_id::float8,'repositoryId',r.repository_id::float8,'lane',r.lane,'head',r.head,'base',r.base,'baseline',r.baseline,'pullHead',r.pull_head,'mergeHead',r.merge_head,'number',r.pull_number,'sourceRepositoryId',r.source_repository_id,'authorityEpoch',r.authority_epoch) AS candidate
      FROM claimed c JOIN proofci_runs r ON r.id=c.run_id`, [leaseMs]);
    return result.rows[0] ?? null;
  }

  async publicationCurrent(item: Publication): Promise<boolean> {
    const result = await this.pool.query(`UPDATE proofci_publications p SET lease_until=clock_timestamp()+interval '5 minutes' FROM proofci_runs r
      JOIN proofci_repository_selections s ON s.installation_id=r.installation_id AND s.repository_id=r.repository_id AND s.generation=r.selection_generation
      WHERE r.id=p.run_id AND r.id=$1 AND p.generation=$2 AND p.revision=$3 AND p.lease_until > clock_timestamp() AND NOT p.needs_revalidation AND r.generation=$4 AND r.state=$5 AND r.applicable`, [item.id, item.leaseGeneration, item.revision, item.runGeneration, item.state]);
    if (result.rowCount !== 1) return false;
    if (!this.authority) return true;
    return item.candidate.authorityEpoch != null && await this.authority.current(item.candidate) === item.candidate.authorityEpoch;
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
    const result = await this.pool.query<StoredRun>('SELECT id, state, applicable, report, authority_epoch FROM proofci_runs WHERE installation_id=$1 AND repository_id=$2 ORDER BY created_at DESC LIMIT 100', [scope.installationId, scope.repositoryId]);
    return this.applicability(scope, result.rows);
  }

  async inspect(scope: RepositoryScope, id: string): Promise<Run | null> {
    const result = await this.pool.query<StoredRun>('SELECT id, state, applicable, report, authority_epoch FROM proofci_runs WHERE id=$1 AND installation_id=$2 AND repository_id=$3', [id, scope.installationId, scope.repositoryId]);
    const run = result.rows[0];
    return run ? (await this.applicability(scope, [run]))[0] ?? null : null;
  }

  async evidence(scope: RepositoryScope, id: string): Promise<{ bytes: Buffer; sha256: string } | null> {
    const result = await this.pool.query<{ bytes: Buffer; sha256: string }>('SELECT evidence AS bytes, evidence_sha256 AS sha256 FROM proofci_runs WHERE id=$1 AND installation_id=$2 AND repository_id=$3 AND evidence IS NOT NULL', [id, scope.installationId, scope.repositoryId]);
    return result.rows[0] ?? null;
  }

  async findPull(scope: RepositoryScope, number: number): Promise<{ id: string; candidate: Extract<Candidate, { kind: 'pull-request' }> } | null> {
    const result = await this.pool.query<{ id: string; candidate: Extract<Candidate, { kind: 'pull-request' }> }>(`SELECT id, jsonb_strip_nulls(jsonb_build_object(
      'kind', kind, 'installationId', installation_id::float8, 'repositoryId', repository_id::float8,
      'lane', lane, 'number', pull_number::float8, 'sourceRepositoryId', source_repository_id::float8,
      'head', head, 'base', base, 'baseline', baseline, 'authorityEpoch', authority_epoch)) AS candidate FROM proofci_runs
      WHERE installation_id=$1 AND repository_id=$2 AND kind='pull-request' AND pull_number=$3 AND applicable AND state <> 'cancelled'`, [scope.installationId, scope.repositoryId, number]);

    const run = result.rows[0];
    if (!run) return null;
    if (this.authority && (run.candidate.authorityEpoch == null || await this.authority.current(scope) !== run.candidate.authorityEpoch)) return null;
    return run;
  }
}
