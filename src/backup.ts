import { createHash } from 'node:crypto';
import { execFile } from 'node:child_process';
import { constants } from 'node:fs';
import { mkdir, open, readFile, readdir } from 'node:fs/promises';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { promisify } from 'node:util';
import { GetBucketVersioningCommand, GetObjectCommand, PutObjectCommand, S3Client } from '@aws-sdk/client-s3';
import { Pool, type PoolClient } from 'pg';
import { requiredCredential } from './credentials.ts';
import { DeploymentError, RELEASE, SCHEMA_VERSION, holdExclusiveLock, recordSchema, schemaState } from './deployment.ts';
import { EnrollmentStore } from './enrollment-store.ts';
import { ModelLedger } from './model-ledger.ts';
import { readPilotConfiguration } from './pilot-configuration.ts';
import type { PilotConfiguration } from './run-service.ts';
import { RunStore } from './run-store.ts';

const run = promisify(execFile);
const storeHelper = fileURLToPath(new URL('../deploy/store_snapshot.py', import.meta.url));
const FORMAT = 'proofci-deployment-backup';
const MAX_OBJECT = 256 * 1024 * 1024;

type Scoping = 'repository' | 'installation' | 'run' | 'global';
/** Every ProofCI table, in restore order. An unknown table makes backup fail rather than silently omit state. */
export const TABLES: ReadonlyArray<{ name: string; scoping: Scoping; order: string }> = [
  { name: 'proofci_repository_selections', scoping: 'repository', order: 'installation_id, repository_id' },
  { name: 'proofci_installation_revisions', scoping: 'installation', order: 'installation_id' },
  { name: 'proofci_installation_deliveries', scoping: 'global', order: 'delivery_id' },
  { name: 'proofci_runs', scoping: 'repository', order: 'created_at, id' },
  { name: 'proofci_evidence', scoping: 'run', order: 'created_at, id' },
  { name: 'proofci_publications', scoping: 'run', order: 'run_id' },
  { name: 'proofci_fork_policies', scoping: 'repository', order: 'installation_id, repository_id' },
  { name: 'proofci_fork_policy_revisions', scoping: 'repository', order: 'installation_id, repository_id, pull_number' },
  { name: 'proofci_fork_decisions', scoping: 'repository', order: 'installation_id, repository_id, pull_number' },
  { name: 'proofci_push_deliveries', scoping: 'repository', order: 'created_at, delivery_id' },
  { name: 'proofci_push_fences', scoping: 'repository', order: 'delivery_id' },
  { name: 'proofci_repository_push_revisions', scoping: 'repository', order: 'installation_id, repository_id' },
  { name: 'proofci_pull_deliveries', scoping: 'repository', order: 'created_at, delivery_id' },
  { name: 'proofci_merge_group_deliveries', scoping: 'repository', order: 'created_at, delivery_id' },
  { name: 'proofci_merge_group_retirements', scoping: 'repository', order: 'installation_id, repository_id, head_ref, head_sha' },
  { name: 'proofci_model_policies', scoping: 'repository', order: 'installation_id, repository_id' },
  { name: 'proofci_model_attempts', scoping: 'repository', order: 'run_id, obligation, attempt' },
];
/** Rewritten by the restoring release rather than copied. */
const DERIVED = new Set(['proofci_deployment']);

export type Scope = { installationId: number; repositoryId: number };
type Row = Record<string, unknown>;
export type StoreDescription = {
  tables: string[]; repositories: string[]; baselines: number; active_revision: number | null;
  active: { reviewed_sha256: string; baseline_sha256: string; repository: string } | null;
  authority: { repository: string; ref: string; head: string; epoch: number; pending: boolean; enabled: boolean; members: number[] } | null;
  migrations: Array<{ id: string; status: string; replacement: string }>;
};
export type Manifest = {
  format: typeof FORMAT; version: 1; release: string; schema_version: number; created_at: string;
  scopes: Scope[] | 'all';
  files: Record<string, { sha256: string; bytes: number }>;
  tables: Record<string, number>;
  stores: Array<Scope & { repository: string; file: string; description: StoreDescription }>;
  evidence: Array<{ id: string; run_id: string; key: string; sha256: string; bytes: number; state: string; file: string | null }>;
  summary: Summary;
};
export type Summary = {
  active_baselines: Array<Scope & { reviewed_sha256: string | null; revision: number | null; authority_epoch: number | null }>;
  approvals: { fork_decisions: number; migrations: number; maintainers: number };
  runs: Record<string, number>; evidence_references: number; reservations: { model: number; evidence: number };
  pending_publications: number; uncertain_model_attempts: number;
};

const key = (scope: Scope) => `${scope.installationId}:${scope.repositoryId}`;
const sha256 = (bytes: Uint8Array) => createHash('sha256').update(bytes).digest('hex');
const number = (value: unknown) => typeof value === 'number' ? value : Number(value);

export function parseScope(text: string): Scope {
  const match = /^([1-9]\d*):([1-9]\d*)$/.exec(text);
  const scope = match ? { installationId: Number(match[1]), repositoryId: Number(match[2]) } : null;
  if (!scope || !Number.isSafeInteger(scope.installationId) || !Number.isSafeInteger(scope.repositoryId)) throw new Error(`Invalid scope: ${text}`);
  return scope;
}

/**
 * Reject any row, object, or store that would let one repository's state reach another.
 * Used both when creating a backup and before restoring one.
 */
export function checkIsolation(input: { scopes: Scope[] | 'all'; rows: Record<string, Row[]>; evidence: Manifest['evidence']; stores: Manifest['stores']; repositories?: PilotConfiguration[] }): void {
  const allowed = input.scopes === 'all' ? null : new Set(input.scopes.map(key));
  const inScope = (scope: Scope) => allowed === null || allowed.has(key(scope));
  const runs = new Map<string, Scope>();
  for (const row of input.rows.proofci_runs ?? []) runs.set(String(row.id), { installationId: number(row.installation_id), repositoryId: number(row.repository_id) });
  for (const table of TABLES) {
    for (const row of input.rows[table.name] ?? []) {
      if (table.scoping === 'repository') {
        const scope = { installationId: number(row.installation_id), repositoryId: number(row.repository_id) };
        if (!inScope(scope)) throw new Error(`${table.name} contains a row outside the backup scope`);
        if ('run_id' in row) {
          const owner = runs.get(String(row.run_id));
          if (!owner || key(owner) !== key(scope)) throw new Error(`${table.name} row belongs to a run in another repository`);
        }
      } else if (table.scoping === 'run') {
        if (!runs.has(String(row.run_id))) throw new Error(`${table.name} row refers to a run outside the backup`);
      } else if (table.scoping === 'installation') {
        if (allowed !== null && ![...allowed].some(item => item.startsWith(`${number(row.installation_id)}:`))) throw new Error(`${table.name} contains an installation outside the backup scope`);
      } else if (allowed !== null && (input.rows[table.name]?.length ?? 0) > 0) throw new Error(`${table.name} is only included in full backups`);
    }
  }
  const evidenceRows = new Map((input.rows.proofci_evidence ?? []).map(row => [String(row.id), row]));
  for (const item of input.evidence) {
    const row = evidenceRows.get(item.id);
    const owner = runs.get(item.run_id);
    if (!row || String(row.run_id) !== item.run_id || row.object_key !== item.key || row.sha256 !== item.sha256 || !owner) throw new Error('Evidence object does not match its database reference');
    if (!item.key.startsWith(`evidence/${owner.installationId}/${owner.repositoryId}/${item.run_id}/`)) throw new Error('Evidence object key is outside its run repository');
  }
  const seen = new Set<string>();
  for (const store of input.stores) {
    if (!inScope(store) || seen.has(key(store))) throw new Error('Baseline store is outside the backup scope');
    seen.add(key(store));
    const configured = input.repositories?.find(item => key(item) === key(store));
    if (input.repositories && (!configured || configured.repository !== store.repository)) throw new Error(`Baseline store ${key(store)} is not configured for the same repository here`);
    if (store.description.repositories.some(repository => repository !== store.repository)) throw new Error(`Baseline store ${key(store)} contains another repository`);
  }
}

function summarize(rows: Record<string, Row[]>, stores: Manifest['stores']): Summary {
  const runs: Record<string, number> = {};
  for (const row of rows.proofci_runs ?? []) runs[String(row.state)] = (runs[String(row.state)] ?? 0) + 1;
  const attempts = rows.proofci_model_attempts ?? [];
  return {
    active_baselines: stores.map(store => ({ installationId: store.installationId, repositoryId: store.repositoryId,
      reviewed_sha256: store.description.active?.reviewed_sha256 ?? null, revision: store.description.active_revision,
      authority_epoch: store.description.authority?.epoch ?? null })),
    approvals: { fork_decisions: rows.proofci_fork_decisions?.length ?? 0,
      migrations: stores.reduce((total, store) => total + store.description.migrations.length, 0),
      maintainers: stores.reduce((total, store) => total + (store.description.authority?.members.length ?? 0), 0) },
    runs, evidence_references: (rows.proofci_evidence ?? []).length,
    reservations: { model: attempts.filter(row => row.state === 'reserved' || row.state === 'sending').length,
      evidence: (rows.proofci_evidence ?? []).filter(row => row.state === 'pending').length },
    pending_publications: (rows.proofci_publications ?? []).filter(row => row.pending === true).length,
    uncertain_model_attempts: attempts.filter(row => row.state === 'uncertain').length,
  };
}

async function writeFileExclusive(path: string, bytes: Uint8Array): Promise<void> {
  await mkdir(dirname(path), { recursive: true, mode: 0o700 });
  const file = await open(path, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600);
  try { await file.writeFile(bytes); await file.sync(); } finally { await file.close(); }
}

function inside(root: string, path: string): string {
  const target = resolve(root, path);
  if (!target.startsWith(resolve(root) + sep)) throw new Error('Backup path escapes its directory');
  return target;
}

async function storeCommand(command: 'describe' | 'copy' | 'install', source: string, target?: string): Promise<StoreDescription> {
  const { stdout } = await run('python3', [storeHelper, command, source, ...(target ? [target] : [])], {
    timeout: 120_000, maxBuffer: 1024 * 1024, env: { PATH: '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', PYTHONDONTWRITEBYTECODE: '1' } });
  return JSON.parse(stdout) as StoreDescription;
}

async function tables(client: PoolClient): Promise<string[]> {
  const result = await client.query<{ tablename: string }>("SELECT tablename FROM pg_tables WHERE schemaname=current_schema() AND tablename LIKE 'proofci\\_%' ORDER BY tablename");
  return result.rows.map(row => row.tablename);
}

function s3Client(env: NodeJS.ProcessEnv): { s3: S3Client; bucket: string } {
  const region = env.PROOFCI_S3_REGION, bucket = env.PROOFCI_S3_BUCKET, endpoint = env.PROOFCI_S3_ENDPOINT;
  if (!region || !bucket) throw new Error('Missing configuration: PROOFCI_S3_REGION and PROOFCI_S3_BUCKET');
  return { s3: new S3Client({ region, endpoint, forcePathStyle: Boolean(endpoint) }), bucket };
}

async function readObject(s3: S3Client, bucket: string, objectKey: string): Promise<Buffer | null> {
  try {
    const object = await s3.send(new GetObjectCommand({ Bucket: bucket, Key: objectKey }));
    if (!object.Body || (object.ContentLength ?? 0) > MAX_OBJECT) throw new Error('Invalid stored evidence');
    return Buffer.from(await object.Body.transformToByteArray());
  } catch (error) {
    if (error instanceof Error && (error.name === 'NoSuchKey' || error.name === 'NotFound')) return null;
    throw error;
  }
}

/** Create a consistent offline backup. Every control process must be stopped. */
export async function createBackup(env: NodeJS.ProcessEnv, output: string, scopes: Scope[] | 'all'): Promise<Manifest> {
  const root = resolve(output);
  await mkdir(root, { mode: 0o700 });
  const repositories = env.PROOFCI_LOCAL_PILOT_CONFIG ? readPilotConfiguration(env.PROOFCI_LOCAL_PILOT_CONFIG) : [];
  if (scopes !== 'all') for (const scope of scopes) if (!repositories.some(item => key(item) === key(scope))) throw new Error(`Scope ${key(scope)} is not in the pilot configuration`);
  const pool = new Pool({ connectionString: requiredCredential(env, 'DATABASE_URL'), max: 2 });
  const lock = await pool.connect();
  const files: Manifest['files'] = {};
  const record = async (path: string, bytes: Uint8Array) => {
    await writeFileExclusive(inside(root, path), bytes);
    files[path] = { sha256: sha256(bytes), bytes: bytes.length };
  };
  try {
    await holdExclusiveLock(lock);
    const state = await schemaState(lock);
    if (state.kind !== 'current') throw new DeploymentError(`The database schema is ${state.kind}, not the schema of ProofCI ${RELEASE}.`,
      'Start this release once so it completes its migrations, stop it, then take the backup.');
    const present = await tables(lock);
    const unknown = present.filter(name => !DERIVED.has(name) && !TABLES.some(table => table.name === name));
    if (unknown.length) throw new Error(`This release cannot back up unknown tables: ${unknown.join(', ')}`);
    const rows: Record<string, Row[]> = {};
    const filter = scopes === 'all' ? null : scopes;
    await lock.query('BEGIN ISOLATION LEVEL REPEATABLE READ READ ONLY');
    try {
      for (const table of TABLES) {
        if (!present.includes(table.name)) { rows[table.name] = []; continue; }
        if (filter && table.scoping === 'global') { rows[table.name] = []; continue; }
        const ids = filter?.map(scope => [scope.installationId, scope.repositoryId]) ?? [];
        const installations = filter ? [...new Set(filter.map(scope => scope.installationId))] : [];
        const where = !filter ? 'true'
          : table.scoping === 'repository' ? 'EXISTS (SELECT 1 FROM jsonb_to_recordset($1::jsonb) AS s(i bigint, r bigint) WHERE s.i=t.installation_id AND s.r=t.repository_id)'
          : table.scoping === 'installation' ? 't.installation_id = ANY($1::bigint[])'
          : 't.run_id IN (SELECT id FROM proofci_runs WHERE EXISTS (SELECT 1 FROM jsonb_to_recordset($1::jsonb) AS s(i bigint, r bigint) WHERE s.i=installation_id AND s.r=repository_id))';
        const params = !filter ? [] : table.scoping === 'installation' ? [installations] : [JSON.stringify(ids.map(([i, r]) => ({ i, r })))];
        const result = await lock.query<{ row: Row }>(`SELECT row_to_json(t) AS row FROM ${table.name} t WHERE ${where} ORDER BY ${table.order}`, params);
        rows[table.name] = result.rows.map(item => item.row);
      }
      await lock.query('COMMIT');
    } catch (error) { await lock.query('ROLLBACK'); throw error; }
    for (const table of TABLES) await record(`database/${table.name}.jsonl`, Buffer.from(rows[table.name]!.map(row => JSON.stringify(row) + '\n').join('')));
    const stores: Manifest['stores'] = [];
    for (const item of repositories) {
      if (scopes !== 'all' && !scopes.some(scope => key(scope) === key(item))) continue;
      const file = `stores/${item.installationId}-${item.repositoryId}.db`;
      await mkdir(join(root, 'stores'), { recursive: true, mode: 0o700 });
      const description = await storeCommand('copy', item.store, inside(root, file));
      const bytes = await readFile(inside(root, file));
      files[file] = { sha256: sha256(bytes), bytes: bytes.length };
      stores.push({ installationId: item.installationId, repositoryId: item.repositoryId, repository: item.repository, file, description });
    }
    const evidence: Manifest['evidence'] = [];
    const objects = (rows.proofci_evidence ?? []).filter(row => row.state === 'pending' || row.state === 'ready');
    const storage = objects.length ? s3Client(env) : null;
    for (const row of objects) {
      const entry = { id: String(row.id), run_id: String(row.run_id), key: String(row.object_key), sha256: String(row.sha256), bytes: number(row.bytes), state: String(row.state), file: null as string | null };
      const bytes = await readObject(storage!.s3, storage!.bucket, entry.key);
      if (bytes === null) {
        if (row.state === 'ready') throw new Error(`Ready evidence object is missing: ${entry.key}`);
      } else {
        if (bytes.length !== entry.bytes || sha256(bytes) !== entry.sha256) throw new Error(`Evidence object digest mismatch: ${entry.key}`);
        entry.file = `objects/${entry.key}`;
        await record(entry.file, bytes);
      }
      evidence.push(entry);
    }
    checkIsolation({ scopes, rows, evidence, stores, repositories });
    const counts = Object.fromEntries(TABLES.map(table => [table.name, rows[table.name]!.length]));
    const manifest: Manifest = { format: FORMAT, version: 1, release: RELEASE, schema_version: SCHEMA_VERSION, created_at: new Date().toISOString(),
      scopes, files, tables: counts, stores, evidence, summary: summarize(rows, stores) };
    await writeFileExclusive(join(root, 'manifest.json'), Buffer.from(JSON.stringify(manifest, null, 2) + '\n'));
    return manifest;
  } finally { lock.release(); await pool.end(); }
}

/** Verify file digests and isolation without contacting any service. */
export async function verifyBackup(input: string): Promise<{ manifest: Manifest; rows: Record<string, Row[]> }> {
  const root = resolve(input);
  const manifest = JSON.parse(await readFile(join(root, 'manifest.json'), 'utf8')) as Manifest;
  if (manifest.format !== FORMAT || manifest.version !== 1) throw new Error('Not a ProofCI deployment backup');
  const listed = new Set(Object.keys(manifest.files));
  const walk = async (directory: string): Promise<string[]> => (await Promise.all((await readdir(directory, { withFileTypes: true })).map(async entry => {
    const path = join(directory, entry.name);
    if (entry.isSymbolicLink()) throw new Error('Backup contains a symbolic link');
    return entry.isDirectory() ? walk(path) : [relative(root, path).split(sep).join('/')];
  }))).flat();
  for (const path of await walk(root)) if (path !== 'manifest.json' && !listed.has(path)) throw new Error(`Backup contains an unlisted file: ${path}`);
  for (const [path, expected] of Object.entries(manifest.files)) {
    const bytes = await readFile(inside(root, path));
    if (bytes.length !== expected.bytes || sha256(bytes) !== expected.sha256) throw new Error(`Backup file digest mismatch: ${path}`);
  }
  const rows: Record<string, Row[]> = {};
  for (const table of TABLES) {
    const text = await readFile(inside(root, `database/${table.name}.jsonl`), 'utf8');
    rows[table.name] = text.split('\n').filter(Boolean).map(line => JSON.parse(line) as Row);
    if (rows[table.name]!.length !== manifest.tables[table.name]) throw new Error(`Row count mismatch: ${table.name}`);
  }
  for (const item of manifest.evidence) if (item.file && manifest.files[item.file]?.sha256 !== item.sha256) throw new Error(`Evidence copy mismatch: ${item.key}`);
  checkIsolation({ scopes: manifest.scopes, rows, evidence: manifest.evidence, stores: manifest.stores });
  return { manifest, rows };
}

/**
 * Restore into an empty database, empty store paths, and a bucket without versioning.
 * Stores and objects are written first; the database commits last, in one transaction.
 */
export async function restoreBackup(env: NodeJS.ProcessEnv, input: string): Promise<Manifest> {
  const root = resolve(input);
  const { manifest, rows } = await verifyBackup(root);
  if (manifest.schema_version !== SCHEMA_VERSION) throw new DeploymentError(`The backup was taken by ProofCI ${manifest.release} (schema ${manifest.schema_version}).`,
    `Restore it with that release, start it once, then upgrade to ${RELEASE} following deploy/README.md.`);
  const repositories = env.PROOFCI_LOCAL_PILOT_CONFIG ? readPilotConfiguration(env.PROOFCI_LOCAL_PILOT_CONFIG) : [];
  checkIsolation({ scopes: manifest.scopes, rows, evidence: manifest.evidence, stores: manifest.stores, repositories });
  const runScopes = new Set((rows.proofci_runs ?? []).map(row => `${number(row.installation_id)}:${number(row.repository_id)}`));
  for (const scope of runScopes) if (!repositories.some(item => key(item) === scope)) throw new Error(`Runs for ${scope} have no configured repository here`);
  const pool = new Pool({ connectionString: requiredCredential(env, 'DATABASE_URL'), max: 2 });
  const client = await pool.connect();
  try {
    await holdExclusiveLock(client);
    if ((await tables(client)).length) throw new Error('Restore requires an empty database schema. Create a new database or schema and point DATABASE_URL at it.');
    for (const store of manifest.stores) {
      const target = repositories.find(item => key(item) === key(store))!;
      const description = await storeCommand('install', inside(root, store.file), target.store);
      if (JSON.stringify(description) !== JSON.stringify(store.description)) throw new Error(`Restored store ${key(store)} differs from the backup`);
    }
    const copies = manifest.evidence.filter(item => item.file !== null);
    if (copies.length) {
      const { s3, bucket } = s3Client(env);
      const versioning = await s3.send(new GetBucketVersioningCommand({ Bucket: bucket }));
      if (versioning.Status) throw new Error('Evidence bucket must not have versioning enabled or suspended');
      for (const item of copies) {
        const bytes = await readFile(inside(root, item.file!));
        const existing = await readObject(s3, bucket, item.key);
        if (existing !== null) {
          if (sha256(existing) !== item.sha256) throw new Error(`Evidence object already exists with different contents: ${item.key}`);
          continue;
        }
        await s3.send(new PutObjectCommand({ Bucket: bucket, Key: item.key, Body: bytes, ContentType: 'application/x-tar', IfNoneMatch: '*' }));
      }
    }
    // Create this release's schema with the owning components, then load rows in dependency order.
    await new EnrollmentStore(pool).initialize();
    await new RunStore(pool).initialize();
    await new ModelLedger(pool).initialize();
    const present = await tables(client);
    await client.query('BEGIN');
    try {
      for (const table of TABLES) {
        if (!present.includes(table.name)) { if (rows[table.name]!.length) throw new Error(`Missing table ${table.name}`); continue; }
        for (const row of rows[table.name]!) await client.query(`INSERT INTO ${table.name} SELECT * FROM json_populate_record(NULL::${table.name}, $1::json)`, [JSON.stringify(row)]);
      }
      await client.query('COMMIT');
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    await recordSchema(pool, { kind: 'fresh' });
    return manifest;
  } finally { client.release(); await pool.end(); }
}

/** Compare database state with a backup, for restoration exercises. */
export async function compareDatabase(env: NodeJS.ProcessEnv, input: string): Promise<string[]> {
  const { manifest, rows } = await verifyBackup(input);
  const pool = new Pool({ connectionString: requiredCredential(env, 'DATABASE_URL'), max: 1 });
  const differences: string[] = [];
  try {
    for (const table of TABLES) {
      const result = await pool.query<{ row: Row }>(`SELECT row_to_json(t) AS row FROM ${table.name} t ORDER BY ${table.order}`);
      const current = result.rows.map(item => JSON.stringify(item.row)).sort();
      const expected = rows[table.name]!.map(row => JSON.stringify(row)).sort();
      if (manifest.scopes !== 'all' && table.scoping === 'global') continue;
      if (JSON.stringify(current) !== JSON.stringify(expected)) differences.push(table.name);
    }
  } finally { await pool.end(); }
  return differences;
}

async function main(): Promise<void> {
  const [command, ...args] = process.argv.slice(2);
  const option = (name: string) => { const index = args.indexOf(name); return index >= 0 ? args[index + 1] : undefined; };
  const usage = 'Usage: node src/backup.ts create --output DIR [--scope INSTALLATION_ID:REPOSITORY_ID ...] | verify --input DIR | restore --input DIR | compare --input DIR';
  if (command === 'create' && option('--output')) {
    const scopes = args.flatMap((value, index) => args[index - 1] === '--scope' ? [parseScope(value)] : []);
    const manifest = await createBackup(process.env, option('--output')!, scopes.length ? scopes : 'all');
    const digest = sha256(await readFile(join(resolve(option('--output')!), 'manifest.json')));
    process.stdout.write(`${JSON.stringify({ manifest_sha256: digest, summary: manifest.summary }, null, 2)}\n`);
  } else if (command === 'verify' && option('--input')) {
    const { manifest } = await verifyBackup(option('--input')!);
    process.stdout.write(`${JSON.stringify({ verified: true, release: manifest.release, scopes: manifest.scopes, summary: manifest.summary }, null, 2)}\n`);
  } else if (command === 'restore' && option('--input')) {
    const manifest = await restoreBackup(process.env, option('--input')!);
    process.stdout.write(`${JSON.stringify({ restored: true, summary: manifest.summary }, null, 2)}\n`);
  } else if (command === 'compare' && option('--input')) {
    const differences = await compareDatabase(process.env, option('--input')!);
    process.stdout.write(`${JSON.stringify({ identical: differences.length === 0, differences }, null, 2)}\n`);
    if (differences.length) process.exitCode = 1;
  } else throw new Error(usage);
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  await main().catch(error => {
    process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = error instanceof DeploymentError ? 3 : 2;
  });
}
