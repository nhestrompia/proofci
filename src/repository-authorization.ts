import type { RepositoryScope } from './enrollment-store.ts';
import type { InstallationAccess } from './github-app.ts';

type Selections = { readVersion(scope: RepositoryScope): Promise<string | null>; removeIfVersion(scope: RepositoryScope, version: string): Promise<void> };
type Installation = { installationAccess(scope: RepositoryScope): Promise<InstallationAccess> };

/** Recheck at dispatch; only an observed revocation of this selection can remove it. */
export async function authorizeNewWork(options: { scope: RepositoryScope; selections: Selections; github: Installation }): Promise<boolean> {
  try {
    const version = await options.selections.readVersion(options.scope);
    if (version === null) return false;
    const access = await options.github.installationAccess(options.scope);
    if (access === 'revoked') await options.selections.removeIfVersion(options.scope, version);
    return access === 'allowed' && await options.selections.readVersion(options.scope) === version;
  } catch { return false; }
}
