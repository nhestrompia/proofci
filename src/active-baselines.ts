import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';
import { isAbsolute } from 'node:path';
import type { RepositoryScope } from './enrollment-store.ts';

const run = promisify(execFile);
const helper = fileURLToPath(new URL('../portable/service_baseline.py', import.meta.url));
export type BaselineConfiguration = RepositoryScope & { store: string; repository: string };

/** Protected operator configuration binds an enrollment to its approved store. */
export class ActiveBaselines {
  private readonly configurations: BaselineConfiguration[];
  constructor(configurations: BaselineConfiguration[]) {
    for (const item of configurations) {
      if (!Number.isSafeInteger(item.installationId) || item.installationId < 1 || !Number.isSafeInteger(item.repositoryId) || item.repositoryId < 1 ||
          !isAbsolute(item.store) || !/^https:\/\/github\.com\/[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+\.git$/.test(item.repository)) throw new Error('Invalid baseline configuration');
    }
    if (new Set(configurations.map(c => `${c.installationId}:${c.repositoryId}`)).size !== configurations.length) throw new Error('Duplicate baseline configuration');
    this.configurations = configurations;
  }

  configuration(scope: RepositoryScope): BaselineConfiguration | undefined {
    return this.configurations.find(item => item.installationId === scope.installationId && item.repositoryId === scope.repositoryId);
  }

  async active(scope: RepositoryScope): Promise<string | null> {
    return (await this.activeIdentity(scope))?.digest ?? null;
  }

  async activeIdentity(scope: RepositoryScope): Promise<{ digest: string; revision: number | null } | null> {
    const config = this.configuration(scope);
    if (!config) return null;
    let stdout: string;
    try {
      ({ stdout } = await run('python3', [helper, '--store', config.store, '--repository', config.repository], {
        timeout: 10_000, maxBuffer: 65536, env: { PATH: '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', PYTHONDONTWRITEBYTECODE: '1' },
      }));
    } catch (error) {
      if (error instanceof Error && 'code' in error && error.code === 3) return null;
      throw error;
    }
    const value: unknown = JSON.parse(stdout);
    if (typeof value !== 'object' || value === null || !('baseline_sha256' in value) ||
        typeof value.baseline_sha256 !== 'string' || !/^[a-f0-9]{64}$/.test(value.baseline_sha256) || !('active_revision' in value) ||
        (value.active_revision !== null && (typeof value.active_revision !== 'number' || !Number.isSafeInteger(value.active_revision) || value.active_revision < 1))) throw new Error('Invalid active baseline');
    return { digest: value.baseline_sha256, revision: value.active_revision };
  }
}
