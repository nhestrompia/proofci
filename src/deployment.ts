import type { Pool, PoolClient } from 'pg';

/**
 * Deployment schema identity.
 *
 * Schema 1 is every database created before releases were pinned. Those databases
 * have ProofCI tables but no `proofci_deployment` row. Schema 2 adds the row and
 * the shared service lock. Each component still owns its own idempotent table
 * migrations; this record only states which release last completed them.
 */
export const RELEASE = '0.23.0';
export const SCHEMA_VERSION = 2;
export const MINIMUM_UPGRADABLE_SCHEMA = 1;
/** The only portable report and baseline format this release reads or writes. */
export const REPORT_VERSION = 1;

/** Held in shared mode by each running control process, and exclusively by backup and restore. */
const SERVICE_LOCK = "hashtextextended(current_schema() || ':proofci-service', 0)";

export class DeploymentError extends Error {
  readonly instructions: string;
  constructor(message: string, instructions: string) {
    super(`${message}\n${instructions}`);
    this.instructions = instructions;
  }
}

export type SchemaState =
  | { kind: 'fresh' }
  | { kind: 'current'; release: string }
  | { kind: 'upgrade'; from: number; release: string | null }
  | { kind: 'newer'; version: number; release: string }
  | { kind: 'unsupported'; version: number; release: string | null };

async function hasTable(client: Pool | PoolClient, name: string): Promise<boolean> {
  const result = await client.query<{ present: boolean }>("SELECT to_regclass(current_schema() || '.' || $1) IS NOT NULL AS present", [name]);
  return result.rows[0]?.present === true;
}

export async function schemaState(client: Pool | PoolClient): Promise<SchemaState> {
  if (await hasTable(client, 'proofci_deployment')) {
    const row = (await client.query<{ schema_version: number; release: string }>('SELECT schema_version, release FROM proofci_deployment WHERE id=1')).rows[0];
    if (!row) throw new DeploymentError('The deployment record is missing.', 'Restore the database from a verified backup; do not recreate the record by hand.');
    if (row.schema_version === SCHEMA_VERSION) return { kind: 'current', release: row.release };
    if (row.schema_version > SCHEMA_VERSION) return { kind: 'newer', version: row.schema_version, release: row.release };
    if (row.schema_version < MINIMUM_UPGRADABLE_SCHEMA) return { kind: 'unsupported', version: row.schema_version, release: row.release };
    return { kind: 'upgrade', from: row.schema_version, release: row.release };
  }
  const legacy = await client.query<{ count: string }>("SELECT count(*) FROM pg_tables WHERE schemaname=current_schema() AND tablename LIKE 'proofci\\_%'");
  return Number(legacy.rows[0]?.count ?? 0) > 0 ? { kind: 'upgrade', from: 1, release: null } : { kind: 'fresh' };
}

/** Explain a state that this release must not touch. */
export function refusal(state: SchemaState): DeploymentError | null {
  if (state.kind === 'newer') return new DeploymentError(
    `The database was last migrated by ProofCI ${state.release} (schema ${state.version}); this release (${RELEASE}) supports schema ${SCHEMA_VERSION}.`,
    'Downgrades are not supported. Run the release recorded in the database, or restore the backup taken before the upgrade (see deploy/README.md, "Roll back an upgrade").');
  if (state.kind === 'unsupported') return new DeploymentError(
    `The database uses schema ${state.version}, which ProofCI ${RELEASE} cannot upgrade directly.`,
    `Upgrade through a release that supports schema ${state.version} first, then install ${RELEASE}.`);
  return null;
}

/** Run before any component migration. Refuses newer or unsupported databases without changing them. */
export async function checkUpgrade(pool: Pool): Promise<SchemaState> {
  const state = await schemaState(pool);
  const error = refusal(state);
  if (error) throw error;
  return state;
}

/**
 * Stored reports and baselines must use the single supported format. A mismatch
 * means data written by another release, so the service must not reinterpret it.
 */
export async function checkStoredReports(pool: Pool): Promise<void> {
  if (!await hasTable(pool, 'proofci_runs')) return;
  const result = await pool.query<{ count: string }>("SELECT count(*) FROM proofci_runs WHERE report IS NOT NULL AND (report->'version') IS DISTINCT FROM to_jsonb($1::int)", [REPORT_VERSION]);
  const count = Number(result.rows[0]?.count ?? 0);
  if (count > 0) throw new DeploymentError(`${count} stored run reports use a report format other than version ${REPORT_VERSION}.`,
    'Run the release that wrote them, export the affected runs with `node src/backup.ts create`, and follow that release\'s migration notes. Do not edit stored reports.');
}

/**
 * Record completion after every component migration has committed. Pass the state observed
 * before those migrations ran, so a fresh database is not mistaken for an upgraded one.
 */
export async function recordSchema(pool: Pool, initial?: SchemaState): Promise<void> {
  const client = await pool.connect();
  try {
    await client.query('BEGIN');
    await client.query("SELECT pg_advisory_xact_lock(hashtextextended(current_schema() || ':proofci-deployment', 0))");
    const state = await schemaState(client);
    const error = refusal(state);
    if (error) throw error;
    await client.query(`CREATE TABLE IF NOT EXISTS proofci_deployment (
      id INTEGER PRIMARY KEY CHECK (id = 1), schema_version INTEGER NOT NULL, release TEXT NOT NULL,
      upgraded_from INTEGER, updated_at TIMESTAMPTZ NOT NULL DEFAULT clock_timestamp())`);
    const observed = initial ?? state;
    const from = observed.kind === 'upgrade' ? observed.from : null;
    await client.query(`INSERT INTO proofci_deployment (id, schema_version, release, upgraded_from) VALUES (1, $1, $2, $3)
      ON CONFLICT (id) DO UPDATE SET schema_version=EXCLUDED.schema_version, release=EXCLUDED.release,
      upgraded_from=COALESCE(EXCLUDED.upgraded_from, proofci_deployment.upgraded_from), updated_at=clock_timestamp()`, [SCHEMA_VERSION, RELEASE, from]);
    await client.query('COMMIT');
  } catch (error) { await client.query('ROLLBACK'); throw error; }
  finally { client.release(); }
}

/** Keep a dedicated connection holding the shared service lock for the life of the process. */
export async function holdServiceLock(pool: Pool): Promise<() => Promise<void>> {
  const client = await pool.connect();
  const locked = await client.query<{ ok: boolean }>(`SELECT pg_try_advisory_lock_shared(${SERVICE_LOCK}) AS ok`);
  if (!locked.rows[0]?.ok) {
    client.release();
    throw new DeploymentError('A backup or restore holds the deployment lock.', 'Wait for it to finish, then start the service again.');
  }
  return async () => { try { await client.query(`SELECT pg_advisory_unlock_shared(${SERVICE_LOCK})`); } finally { client.release(); } };
}

/** Backup and restore require every control process to be stopped. */
export async function holdExclusiveLock(client: PoolClient): Promise<void> {
  const locked = await client.query<{ ok: boolean }>(`SELECT pg_try_advisory_lock(${SERVICE_LOCK}) AS ok`);
  if (!locked.rows[0]?.ok) throw new DeploymentError('A control service is running against this database.',
    'Stop every control process (for example `docker compose stop control`), then run the command again.');
}
