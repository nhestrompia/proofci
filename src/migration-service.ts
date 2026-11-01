import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { mkdtemp, readFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import type { RepositoryScope, EnrollmentStore } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { OAuthSessions } from './oauth.ts';
import type { PilotConfiguration } from './run-service.ts';
import { authorizeNewWork } from './repository-authorization.ts';

const run = promisify(execFile);
const helper = fileURLToPath(new URL('../portable/service_migration.py', import.meta.url));
type Input = { session: string; scope: RepositoryScope; head: string; previous: string; replacement: string };
type Dependencies = { sessions: Pick<OAuthSessions, 'checkMaintainer'>; github: Pick<GitHubApp, 'checkMaintainerAccess' | 'installationAccess' | 'resolveHead' | 'stageSnapshot'>; selections: Pick<EnrollmentStore, 'readVersion' | 'removeIfVersion'>; repositories: PilotConfiguration[] };

export class MigrationService {
  private readonly dependencies: Dependencies;
  constructor(dependencies: Dependencies) { this.dependencies = dependencies; }

  async migrate(input: Input): Promise<Record<string, unknown>> {
    const { sessions, github, selections } = this.dependencies;
    const config = this.dependencies.repositories.find(item => item.installationId === input.scope.installationId && item.repositoryId === input.scope.repositoryId);
    if (!config || !/^[a-f0-9]{40}$/.test(input.head) || !/^[a-f0-9]{64}$/.test(input.previous) || !/^[a-f0-9]{64}$/.test(input.replacement)) throw new Error('Invalid migration request');
    const generation = await selections.readVersion(input.scope);
    const actor = await sessions.checkMaintainer({ session: input.session, scope: input.scope, github });
    if (generation === null || actor === null || !await authorizeNewWork({ scope: input.scope, selections, github }) || await selections.readVersion(input.scope) !== generation || await github.resolveHead(input.scope, config.ref) !== input.head) throw new Error('Migration authorization denied or stale');
    const root = await mkdtemp(join(tmpdir(), 'proofci-migration-service-'));
    const signal = AbortSignal.timeout(1_000_000);
    const args = ['--store', config.store, '--repository', config.repository];
    const call = async (operation: string, extra: string[]) => run('python3', [helper, operation, ...args, ...extra], { timeout: 1_000_000, maxBuffer: 8 * 1024 * 1024, env: { PATH: process.env.PATH ?? '/usr/bin:/bin', HOME: process.env.HOME ?? '/tmp', PYTHONDONTWRITEBYTECODE: '1', ...Object.fromEntries(['DOCKER_HOST', 'PROOFCI_APPLE_RUNTIME', 'PROOFCI_APPLE_KERNEL', 'PROOFCI_APPLE_KERNEL_SHA256'].filter(key => process.env[key]).map(key => [key, process.env[key]])) } });
    try {
      const staged = await github.stageSnapshot(input.scope, { head: input.head, base: input.head, root, signal });
      if (staged.repository !== config.repository || await github.resolveHead(input.scope, config.ref) !== input.head) throw new Error('Candidate changed');
      const prepared = await call('prepare', ['--snapshot', staged.snapshot, '--head', input.head, '--previous', input.previous, '--replacement', input.replacement, '--actor', String(actor), '--generation', generation]);
      const value: unknown = JSON.parse(prepared.stdout);
      if (typeof value !== 'object' || value === null || !('migration' in value) || typeof value.migration !== 'string' || !/^[a-f0-9]{32}$/.test(value.migration)) throw new Error('Invalid migration record');
      const report = join(root, 'report.json');
      try {
        await call('verify', ['--snapshot', staged.snapshot, '--migration', value.migration, '--report', report]);
      } catch (error) {
        if (error instanceof Error && 'code' in error && (error.code === 1 || error.code === 2)) {
          const failed: unknown = JSON.parse(await readFile(report, 'utf8'));
          if (typeof failed === 'object' && failed !== null && 'status' in failed && (failed.status === 'blocked' || failed.status === 'error')) return Object.fromEntries(Object.entries(failed));
        }
        throw error;
      }
      if (await sessions.checkMaintainer({ session: input.session, scope: input.scope, github }) !== actor || !await authorizeNewWork({ scope: input.scope, selections, github }) || await selections.readVersion(input.scope) !== generation || await github.resolveHead(input.scope, config.ref) !== input.head) throw new Error('Migration authorization is stale');
      const activated = await call('activate', ['--migration', value.migration, '--head', input.head, '--actor', String(actor), '--generation', generation]);
      const result: unknown = JSON.parse(activated.stdout);
      if (typeof result !== 'object' || result === null || !('status' in result) || result.status !== 'passed') throw new Error('Invalid migration result');
      return Object.fromEntries(Object.entries(result));
    } finally { await rm(root, { recursive: true, force: true }); }
  }
}
