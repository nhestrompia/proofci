import { Pool } from 'pg';
import { requiredCredential } from './credentials.ts';
import { diagnose, type Diagnosis } from './diagnostics.ts';
import { LocalAuthority } from './local-authority.ts';
import { ModelLedger } from './model-ledger.ts';
import { readPilotConfiguration } from './pilot-configuration.ts';
import { RunStore } from './run-store.ts';

const [installation, repository, id] = process.argv.slice(2);
const installationId = Number(installation), repositoryId = Number(repository);
if (!Number.isSafeInteger(installationId) || installationId < 1 || !Number.isSafeInteger(repositoryId) || repositoryId < 1 ||
    (id !== undefined && !/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(id))) {
  throw new Error('Usage: DATABASE_URL=... node src/run-diagnose.ts INSTALLATION_ID REPOSITORY_ID [RUN_ID]');
}
const pool = new Pool({ connectionString: requiredCredential(process.env, 'DATABASE_URL') });
try {
  const configuration = process.env.PROOFCI_LOCAL_PILOT_CONFIG;
  const store = new RunStore(pool, configuration ? new LocalAuthority(readPilotConfiguration(configuration)) : undefined);
  const ledger = new ModelLedger(pool);
  const scope = { installationId, repositoryId };
  const runs = id ? [await store.inspect(scope, id)].filter(run => run !== null) : await store.list(scope);
  if (id && runs.length === 0) { process.stderr.write('Run not found.\n'); process.exitCode = 1; }
  const modelTable = (await pool.query<{ present: boolean }>("SELECT to_regclass(current_schema() || '.proofci_model_attempts') IS NOT NULL AS present")).rows[0]?.present;
  const diagnoses: Diagnosis[] = [];
  for (const run of runs) {
    const publication = (await pool.query<{ pending: boolean; last_error: string | null; published_at: Date | null }>(
      'SELECT pending, last_error, published_at FROM proofci_publications WHERE run_id=$1', [run.id])).rows[0];
    diagnoses.push(diagnose(run, modelTable ? await ledger.usage(run.id) : null,
      publication ? { pending: publication.pending, last_error: publication.last_error, published_at: publication.published_at?.toISOString() ?? null } : null, scope));
  }
  const totals = Object.fromEntries(['passed', 'proof_failure', 'infrastructure_failure', 'superseded', 'in_progress'].map(kind => [kind, diagnoses.filter(item => item.outcome === kind).length]));
  const uncertain = diagnoses.reduce((total, item) => total + (item.model?.uncertain.length ?? 0), 0);
  process.stdout.write(`${JSON.stringify({ totals: { ...totals, uncertain_model_attempts: uncertain, pending_publications: diagnoses.filter(item => item.publication?.pending).length }, runs: diagnoses }, null, 2)}\n`);
} finally { await pool.end(); }
