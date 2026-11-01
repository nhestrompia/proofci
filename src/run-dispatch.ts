import { Pool } from 'pg';
import { RunStore } from './run-store.ts';
import { LocalAuthority } from './local-authority.ts';
import { readPilotConfiguration } from './pilot-configuration.ts';

const [installation, repository, head, base, baseline, lane] = process.argv.slice(2);
const installationId = Number(installation);
const repositoryId = Number(repository);
if (!Number.isSafeInteger(installationId) || installationId < 1 || !Number.isSafeInteger(repositoryId) || repositoryId < 1 ||
    !head || !base || !baseline || !lane || !process.env.DATABASE_URL) {
  throw new Error('Usage: DATABASE_URL=... node src/run-dispatch.ts INSTALLATION_ID REPOSITORY_ID HEAD BASE BASELINE_SHA256 LANE');
}
const pool = new Pool({ connectionString: process.env.DATABASE_URL });
try {
  const configuration = process.env.PROOFCI_LOCAL_PILOT_CONFIG;
  const authority = configuration ? new LocalAuthority(readPilotConfiguration(configuration)) : undefined;
  const id = await new RunStore(pool, authority).admit({ kind: 'resolved', installationId, repositoryId, head, base, baseline, lane });
  process.stdout.write(`${id}\n`);
} finally { await pool.end(); }
