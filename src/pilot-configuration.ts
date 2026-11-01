import { lstatSync, readFileSync } from 'node:fs';
import { isAbsolute } from 'node:path';
import type { PilotConfiguration } from './run-service.ts';

export function readPilotConfiguration(path: string): PilotConfiguration[] {
  if (!isAbsolute(path)) throw new Error('Pilot configuration path must be absolute');
  const stat = lstatSync(path);
  if (!stat.isFile() || stat.isSymbolicLink() || (stat.mode & 0o022) !== 0 || stat.size > 65536) throw new Error('Invalid pilot configuration file');
  const raw: unknown = JSON.parse(readFileSync(path, 'utf8'));
  if (!Array.isArray(raw)) throw new Error('Invalid pilot configuration');
  return raw.map((entry: unknown) => {
    if (typeof entry !== 'object' || entry === null || !('installationId' in entry) || typeof entry.installationId !== 'number' ||
        !('repositoryId' in entry) || typeof entry.repositoryId !== 'number' || !('store' in entry) || typeof entry.store !== 'string' ||
        !('repository' in entry) || typeof entry.repository !== 'string' || !('ref' in entry) || typeof entry.ref !== 'string' ||
        !entry.ref.startsWith('refs/heads/')) throw new Error('Invalid pilot configuration');
    return { installationId: entry.installationId, repositoryId: entry.repositoryId, store: entry.store, repository: entry.repository, ref: entry.ref };
  });
}
