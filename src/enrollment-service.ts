import type { RepositoryScope } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { OAuthSessions } from './oauth.ts';
import type { Enforcement } from './enforcement.ts';

type Dependencies = {
  store: { beginSelection(scope: RepositoryScope): Promise<string>; selectIfUnchanged(scope: RepositoryScope, revision: string): Promise<boolean>; remove(scope: RepositoryScope): Promise<void>; isSelected(scope: RepositoryScope): Promise<boolean> };
  sessions: Pick<OAuthSessions, 'checkMaintainer'>;
  github: Pick<GitHubApp, 'checkMaintainerAccess' | 'inspectEnforcement'>;
};
type Request = { session: string; scope: RepositoryScope };

export class EnrollmentService {
  private readonly dependencies: Dependencies;
  constructor(dependencies: Dependencies) { this.dependencies = dependencies; }

  private async authorized(input: Request): Promise<boolean> {
    const { sessions, github } = this.dependencies;
    return await sessions.checkMaintainer({ ...input, github }) !== null;
  }

  async enroll(input: Request): Promise<boolean> {
    try {
      const revision = await this.dependencies.store.beginSelection(input.scope);
      if (!await this.authorized(input)) return false;
      return await this.dependencies.store.selectIfUnchanged(input.scope, revision);
    } catch { return false; }
  }

  async remove(input: Request): Promise<boolean> {
    try {
      if (!await this.authorized(input)) return false;
      await this.dependencies.store.remove(input.scope);
      return true;
    } catch { return false; }
  }

  async inspect(input: Request): Promise<Enforcement | null> {
    try {
      if (!await this.authorized(input) || !await this.dependencies.store.isSelected(input.scope)) return null;
      return await this.dependencies.github.inspectEnforcement(input.scope);
    } catch { return null; }
  }
}
