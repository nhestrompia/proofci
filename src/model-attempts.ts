import { readFileSync } from 'node:fs';
import { Pool } from 'pg';
import { ModelLedger } from './model-ledger.ts';
import { RunStore } from './run-store.ts';

const usage = `Usage: DATABASE_URL=... node src/model-attempts.ts COMMAND INSTALLATION_ID REPOSITORY_ID ...
  policy INSTALLATION_ID REPOSITORY_ID POLICY_JSON_FILE
  revoke-consent INSTALLATION_ID REPOSITORY_ID
  disable INSTALLATION_ID REPOSITORY_ID
  inspect INSTALLATION_ID REPOSITORY_ID RUN_ID
  reconcile INSTALLATION_ID REPOSITORY_ID REQUEST_ID charged INPUT_TOKENS OUTPUT_TOKENS
  reconcile INSTALLATION_ID REPOSITORY_ID REQUEST_ID not-processed`;

const [command, installation, repository, ...rest] = process.argv.slice(2);
const installationId = Number(installation);
const repositoryId = Number(repository);
if (!command || !Number.isSafeInteger(installationId) || installationId < 1 || !Number.isSafeInteger(repositoryId) || repositoryId < 1 || !process.env.DATABASE_URL) throw new Error(usage);
const scope = { installationId, repositoryId };
const pool = new Pool({ connectionString: process.env.DATABASE_URL });
const ledger = new ModelLedger(pool);
const tokens = (value: string | undefined) => { const number = Number(value); if (!value || !/^\d+$/.test(value) || !Number.isSafeInteger(number)) throw new Error(usage); return number; };
try {
  if (command === 'policy' && rest.length === 1) {
    await ledger.setPolicy(scope, JSON.parse(readFileSync(rest[0]!, 'utf8')));
    process.stdout.write('Model policy stored.\n');
  } else if ((command === 'revoke-consent' || command === 'disable') && rest.length === 0) {
    const changed = command === 'disable' ? await ledger.disable(scope) : await ledger.revokeConsent(scope);
    if (changed) process.stdout.write(command === 'disable' ? 'Model assistance disabled.\n' : 'Source consent revoked.\n');
    else { process.stderr.write('No model policy found.\n'); process.exitCode = 1; }
  } else if (command === 'inspect' && rest.length === 1 && /^[0-9a-f-]{36}$/i.test(rest[0]!)) {
    if (!await new RunStore(pool).inspect(scope, rest[0]!)) { process.stderr.write('Run not found.\n'); process.exitCode = 1; }
    else process.stdout.write(`${JSON.stringify(await ledger.usage(rest[0]!), null, 2)}\n`);
  } else if (command === 'reconcile' && /^[a-f0-9]{64}$/.test(rest[0] ?? '') && ((rest[1] === 'charged' && rest.length === 4) || (rest[1] === 'not-processed' && rest.length === 2))) {
    const outcome = rest[1] === 'charged' ? { kind: 'charged' as const, inputTokens: tokens(rest[2]), outputTokens: tokens(rest[3]) } : { kind: 'not_processed' as const };
    if (await ledger.reconcile(scope, rest[0]!, outcome)) process.stdout.write('Uncertain attempt reconciled.\n');
    else { process.stderr.write('No uncertain attempt found.\n'); process.exitCode = 1; }
  } else throw new Error(usage);
} finally { await pool.end(); }
