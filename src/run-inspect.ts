import { Pool } from 'pg';
import { RunStore } from './run-store.ts';

const [installation, repository, id] = process.argv.slice(2);
const installationId = Number(installation);
const repositoryId = Number(repository);
if (!Number.isSafeInteger(installationId) || installationId < 1 || !Number.isSafeInteger(repositoryId) || repositoryId < 1 ||
    (id !== undefined && !/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(id)) || !process.env.DATABASE_URL) {
  throw new Error('Usage: DATABASE_URL=... node src/run-inspect.ts INSTALLATION_ID REPOSITORY_ID [RUN_ID]');
}
const pool = new Pool({ connectionString: process.env.DATABASE_URL });
try {
  const store = new RunStore(pool);
  const scope = { installationId, repositoryId };
  const run = id ? await store.inspect(scope, id) : { runs: await store.list(scope), deliveries: await store.listDeliveries(scope) };
  if (run === null) { process.stderr.write('Run not found.\n'); process.exitCode = 1; }
  else process.stdout.write(`${JSON.stringify(run, null, 2)}\n`);
} finally { await pool.end(); }
