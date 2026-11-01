import { Pool } from 'pg';
import { RunStore } from './run-store.ts';

const [installation, repository, id] = process.argv.slice(2);
const installationId = Number(installation);
const repositoryId = Number(repository);
if (!Number.isSafeInteger(installationId) || installationId < 1 || !Number.isSafeInteger(repositoryId) || repositoryId < 1 ||
    !id || !/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(id) || !process.env.DATABASE_URL) {
  throw new Error('Usage: DATABASE_URL=... node src/run-cancel.ts INSTALLATION_ID REPOSITORY_ID RUN_ID');
}
const pool = new Pool({ connectionString: process.env.DATABASE_URL });
try {
  if (await new RunStore(pool).cancel({ installationId, repositoryId }, id)) process.stdout.write('Run cancelled.\n');
  else { process.stderr.write('No cancellable run found.\n'); process.exitCode = 1; }
} finally { await pool.end(); }
