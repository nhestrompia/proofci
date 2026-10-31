import { createSign, type KeyObject } from 'node:crypto';
import { assessEnforcement, type Enforcement } from './enforcement.ts';

type AppOptions = { appId: number; privateKey: KeyObject; request?: typeof fetch };
type RepositoryScope = { installationId: number; repositoryId: number };
export type InstallationAccess = 'allowed' | 'revoked' | 'unavailable';
class GitHubStatusError extends Error { readonly status: number; constructor(status: number) { super('GitHub access check failed'); this.status = status; } }
class AccessRevoked extends Error {}
type Repository = { id: number; name: string; owner: string; defaultBranch: string | null; token: string };

function object(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

/** Low-level GitHub checks. Enrollment and trusted session authorization are separate prerequisites. */
export class GitHubApp {
  private readonly appId: number;
  private readonly privateKey: KeyObject;
  private readonly request: typeof fetch;

  constructor(options: AppOptions) {
    this.appId = options.appId;
    this.privateKey = options.privateKey;
    this.request = options.request ?? fetch;
  }

  private appToken(): string {
    const now = Math.floor(Date.now() / 1000);
    const encode = (value: unknown) => Buffer.from(JSON.stringify(value)).toString('base64url');
    const data = `${encode({ alg: 'RS256', typ: 'JWT' })}.${encode({ iat: now - 60, exp: now + 540, iss: String(this.appId) })}`;
    return `${data}.${createSign('RSA-SHA256').update(data).sign(this.privateKey, 'base64url')}`;
  }

  private async api(path: string, token: string, body?: unknown): Promise<unknown> {
    const response = await this.request(`https://api.github.com${path}`, {
      method: body === undefined ? 'GET' : 'POST',
      headers: { accept: 'application/vnd.github+json', authorization: `Bearer ${token}`, 'x-github-api-version': '2022-11-28', ...(body === undefined ? {} : { 'content-type': 'application/json' }) },
      body: body === undefined ? undefined : JSON.stringify(body),
      redirect: 'error', signal: AbortSignal.timeout(15_000),
    });
    if (!response.ok) throw new GitHubStatusError(response.status);
    return response.json();
  }

  private async repository(scope: RepositoryScope, inspect = false): Promise<Repository> {
    if (!Number.isSafeInteger(scope.installationId) || scope.installationId <= 0 || !Number.isSafeInteger(scope.repositoryId) || scope.repositoryId <= 0) throw new Error('Invalid repository scope');
    const jwt = this.appToken();
    const path = `/app/installations/${scope.installationId}`;
    let installation: unknown;
    try { installation = await this.api(path, jwt); } catch (error) { if (error instanceof GitHubStatusError && error.status === 404) throw new AccessRevoked(); throw error; }
    if (object(installation) && installation.suspended_at !== null && typeof installation.suspended_at === 'string') throw new AccessRevoked();
    if (!object(installation) || installation.id !== scope.installationId || installation.app_id !== this.appId || installation.suspended_at !== null || !object(installation.permissions) || installation.permissions.contents !== 'read' || installation.permissions.pull_requests !== 'read' || installation.permissions.checks !== 'write' || installation.permissions.metadata !== 'read') throw new Error('GitHub access check failed');
    const permissions: Record<string, string> = { contents: 'read', pull_requests: 'read', checks: 'write' };
    if (inspect && (installation.permissions.administration === 'read' || installation.permissions.administration === 'write')) permissions.administration = 'read';
    let issued: unknown;
    try { issued = await this.api(`${path}/access_tokens`, jwt, { repository_ids: [scope.repositoryId], permissions }); } catch (error) { if (error instanceof GitHubStatusError && error.status === 404) throw new AccessRevoked(); throw error; }
    if (!object(issued) || typeof issued.token !== 'string' || !issued.token || !Array.isArray(issued.repositories) || issued.repositories.length !== 1 || !object(issued.repositories[0]) || issued.repositories[0].id !== scope.repositoryId || !object(issued.permissions)) throw new Error('GitHub access check failed');
    const allowedPermissions = { ...permissions, metadata: 'read' };
    const returnedPermissions = issued.permissions;
    if (Object.keys(returnedPermissions).some(key => !Object.hasOwn(allowedPermissions, key)) || Object.entries(allowedPermissions).some(([key, level]) => returnedPermissions[key] !== level)) throw new Error('GitHub access check failed');
    const repo = await this.api(`/repositories/${scope.repositoryId}`, issued.token);
    if (!object(repo) || repo.id !== scope.repositoryId || typeof repo.name !== 'string' || !object(repo.owner) || typeof repo.owner.login !== 'string') throw new Error('GitHub access check failed');
    return { id: scope.repositoryId, name: repo.name, owner: repo.owner.login, defaultBranch: typeof repo.default_branch === 'string' ? repo.default_branch : null, token: issued.token };
  }

  /** List only repositories visible to this App's authenticated user. */
  async listUserRepositories(userToken: string): Promise<Array<{ installationId: number; repositoryId: number; name: string }>> {
    if (!userToken) throw new Error('GitHub access check failed');
    const installations: number[] = [];
    for (let page = 1; page <= 10; page++) {
      const result = await this.api(`/user/installations?per_page=100&page=${page}`, userToken);
      if (!object(result) || !Array.isArray(result.installations)) throw new Error('GitHub access check failed');
      for (const item of result.installations) {
        if (!object(item) || typeof item.id !== 'number' || !Number.isSafeInteger(item.id) || item.id <= 0 || typeof item.app_id !== 'number') throw new Error('GitHub access check failed');
        if (item.app_id === this.appId) installations.push(item.id);
      }
      if (result.installations.length < 100) break;
      if (page === 10) throw new Error('GitHub access check failed');
    }
    const repositories: Array<{ installationId: number; repositoryId: number; name: string }> = [];
    for (const installationId of installations) {
      for (let page = 1; page <= 10; page++) {
        const result = await this.api(`/user/installations/${installationId}/repositories?per_page=100&page=${page}`, userToken);
        if (!object(result) || !Array.isArray(result.repositories)) throw new Error('GitHub access check failed');
        for (const item of result.repositories) {
          if (!object(item) || typeof item.id !== 'number' || !Number.isSafeInteger(item.id) || item.id <= 0 || typeof item.full_name !== 'string') throw new Error('GitHub access check failed');
          repositories.push({ installationId, repositoryId: item.id, name: item.full_name });
        }
        if (result.repositories.length < 100) break;
        if (page === 10) throw new Error('GitHub access check failed');
      }
    }
    return repositories;
  }

  /** Does not establish enrollment: check selected repository records separately. */
  async installationAccess(scope: RepositoryScope): Promise<InstallationAccess> {
    try { await this.repository(scope); return 'allowed'; } catch (error) { return error instanceof AccessRevoked ? 'revoked' : 'unavailable'; }
  }

  async checkInstallationAccess(scope: RepositoryScope): Promise<boolean> { return await this.installationAccess(scope) === 'allowed'; }

  /** Inspect the default branch when GitHub grants access to protection and rule evidence. */
  async inspectEnforcement(scope: RepositoryScope): Promise<Enforcement> {
    try {
      const repo = await this.repository(scope, true);
      if (!repo.defaultBranch) return 'unconfirmed';
      const prefix = `/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}`;
      const branch = encodeURIComponent(repo.defaultBranch);
      const protection = await this.api(`${prefix}/branches/${branch}/protection`, repo.token);
      const rules = await this.api(`${prefix}/rules/branches/${branch}?per_page=100`, repo.token);
      return assessEnforcement({ appId: this.appId, protection, rules });
    } catch { return 'unconfirmed'; }
  }

  /** The caller must supply a token from a trusted, authenticated GitHub App session. */
  async checkMaintainerAccess(scope: RepositoryScope, userToken: string): Promise<number | null> {
    try {
      if (!userToken) return null;
      const repo = await this.repository(scope);
      const user = await this.api('/user', userToken);
      const current = await this.api(`/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}`, userToken);
      if (!object(user) || !Number.isSafeInteger(user.id) || typeof user.id !== 'number' || user.id <= 0 || !object(current) || current.id !== repo.id || !object(current.permissions) || (current.permissions.admin !== true && current.permissions.maintain !== true)) return null;
      return user.id;
    } catch { return null; }
  }
}
