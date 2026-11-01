import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';
import type { RepositoryScope } from './enrollment-store.ts';
import type { PilotConfiguration } from './run-service.ts';

const run = promisify(execFile);
const helper = fileURLToPath(new URL('../portable/authority.py', import.meta.url));

/** Fences enrollment changes in each configured protected baseline store. */
export class LocalAuthority {
  private readonly repositories: PilotConfiguration[];
  constructor(repositories: PilotConfiguration[]) { this.repositories = repositories; }

  private async change(repository: PilotConfiguration, operation: 'enable' | 'disable'): Promise<void> {
    await run('python3', [helper, operation, '--store', repository.store, '--repository', repository.repository], {
      timeout: 10_000, maxBuffer: 65536,
      env: { PATH: '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', PYTHONDONTWRITEBYTECODE: '1' },
    });
  }

  async disable(installationId: number, repositoryIds: number[] | null): Promise<void> {
    for (const repository of this.repositories) {
      if (repository.installationId === installationId && (repositoryIds === null || repositoryIds.includes(repository.repositoryId))) {
        await this.change(repository, 'disable');
      }
    }
  }

  async current(scope: RepositoryScope): Promise<number | null> {
    const repository = this.repositories.find(item => item.installationId === scope.installationId && item.repositoryId === scope.repositoryId);
    if (!repository) return null;
    try {
      const result = await run('python3', [helper, 'observe', '--store', repository.store, '--repository', repository.repository], {
        timeout: 10_000, maxBuffer: 65536,
        env: { PATH: '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', PYTHONDONTWRITEBYTECODE: '1' },
      });
      const value: unknown = JSON.parse(result.stdout);
      return typeof value === 'object' && value !== null && 'epoch' in value &&
        typeof value.epoch === 'number' && Number.isSafeInteger(value.epoch) && value.epoch > 0 ? value.epoch : null;
    } catch { return null; }
  }

  async enable(scope: RepositoryScope): Promise<void> {
    const repository = this.repositories.find(item => item.installationId === scope.installationId && item.repositoryId === scope.repositoryId);
    if (repository) await this.change(repository, 'enable');
  }
}
