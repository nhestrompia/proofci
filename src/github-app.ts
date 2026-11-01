import { createSign, type KeyObject } from 'node:crypto';
import { assessEnforcement, type Enforcement } from './enforcement.ts';
import { fetchSnapshot } from './snapshot-fetch.ts';

type AppOptions = { appId: number; privateKey: KeyObject; request?: typeof fetch };
type RepositoryScope = { installationId: number; repositoryId: number };
export type InstallationAccess = 'allowed' | 'revoked' | 'unavailable';
export type PullMerge = { kind: 'resolved'; merge: string; head: string; base: string } | { kind: 'blocked'; reason: 'pull_unavailable' | 'merge_unresolved' | 'merge_conflict' | 'merge_ref_missing' | 'merge_ref_mismatch' | 'merge_parents_mismatch' };
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

  private async api(path: string, token: string, body?: unknown, method?: 'PATCH'): Promise<unknown> {
    const response = await this.request(`https://api.github.com${path}`, {
      method: body === undefined ? 'GET' : method ?? 'POST',
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

  private async findCheck(repo: Repository, sha: string, runId: string): Promise<number | undefined> {
    const prefix = `/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}`;
    const found: number[] = [];
    for (let page = 1; page <= 10; page++) {
      const result = await this.api(`${prefix}/commits/${sha}/check-runs?filter=all&per_page=100&page=${page}`, repo.token);
      if (!object(result) || !Array.isArray(result.check_runs)) throw new Error('Invalid check list');
      for (const check of result.check_runs) {
        if (object(check) && check.external_id === runId && object(check.app) && check.app.id === this.appId && typeof check.id === 'number' && Number.isSafeInteger(check.id)) found.push(check.id);
      }
      if (result.check_runs.length < 100) break;
      if (page === 10) throw new Error('Check list exceeds limit');
    }
    if (found.length > 1) throw new Error('Duplicate logical checks');
    return found[0];
  }

  async invalidateCheck(scope: RepositoryScope, input: { runId: string; sha: string }): Promise<void> {
    if (!/^[0-9a-f-]{36}$/.test(input.runId) || !/^[a-f0-9]{40}$/.test(input.sha)) throw new Error('Invalid check identity');
    const repo = await this.repository(scope);
    const id = await this.findCheck(repo, input.sha, input.runId);
    if (id === undefined) return;
    const prefix = `/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}`;
    await this.api(`${prefix}/check-runs/${id}`, repo.token, { status: 'completed', conclusion: 'failure', output: { title: 'ProofCI result is stale', summary: 'The pull request, baseline, or run generation changed.' } }, 'PATCH');
  }

  /** Reconcile a check by its stable run ID before creating or updating it. */
  async publishCheck(scope: RepositoryScope, input: { runId: string; sha: string; detailsUrl: string; output: { title: string; summary: string; conclusion: 'success' | 'failure' } | null; annotations: Array<{ path: string; start_line: number; end_line: number; annotation_level: 'notice' | 'failure'; message: string }>; fresh(): Promise<boolean> }): Promise<void> {
    if (!/^[0-9a-f-]{36}$/.test(input.runId) || !/^[a-f0-9]{40}$/.test(input.sha)) throw new Error('Invalid check identity');
    const repo = await this.repository(scope);
    const prefix = `/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}`;
    let id = await this.findCheck(repo, input.sha, input.runId);
    if (id === undefined) {
      if (!await input.fresh()) throw new Error('Check is stale');
      const created = await this.api(`${prefix}/check-runs`, repo.token, { name: 'ProofCI', head_sha: input.sha, external_id: input.runId, status: 'in_progress', details_url: input.detailsUrl, output: { title: 'ProofCI running', summary: 'Verification is in progress.' } });
      if (!object(created) || typeof created.id !== 'number' || !Number.isSafeInteger(created.id)) throw new Error('Invalid check response');
      id = created.id;
    }
    if (!input.output) return;
    const existing = new Set<string>();
    for (let page = 1; page <= 100; page++) {
      const result = await this.api(`${prefix}/check-runs/${id}/annotations?per_page=100&page=${page}`, repo.token);
      if (!Array.isArray(result)) throw new Error('Invalid annotation list');
      for (const annotation of result) if (object(annotation) && typeof annotation.message === 'string') existing.add(annotation.message);
      if (result.length < 100) break;
      if (!await input.fresh()) throw new Error('Check is stale');
      if (page === 100) throw new Error('Annotation list exceeds limit');
    }
    const missing = input.annotations.filter(annotation => !existing.has(annotation.message));
    for (let index = 0; index < missing.length; index += 50) {
      if (!await input.fresh()) throw new Error('Check is stale');
      await this.api(`${prefix}/check-runs/${id}`, repo.token, { output: { title: input.output.title, summary: input.output.summary, annotations: missing.slice(index, index + 50) } }, 'PATCH');
    }
    if (!await input.fresh()) throw new Error('Check is stale');
    await this.api(`${prefix}/check-runs/${id}`, repo.token, { status: 'completed', conclusion: input.output.conclusion, details_url: input.detailsUrl, output: { title: input.output.title, summary: input.output.summary } }, 'PATCH');
  }

  /** Resolve GitHub's own test merge and verify that it binds the current PR inputs. */
  async resolvePullMerge(scope: RepositoryScope, number: number): Promise<PullMerge> {
    if (!Number.isSafeInteger(number) || number < 1) throw new Error('Invalid pull request number');
    const repo = await this.repository(scope);
    const prefix = `/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}`;
    let pull: unknown;
    try { pull = await this.api(`${prefix}/pulls/${number}`, repo.token); }
    catch (error) { if (error instanceof GitHubStatusError && error.status === 404) return { kind: 'blocked', reason: 'pull_unavailable' }; throw error; }
    if (!object(pull) || pull.number !== number || pull.state !== 'open' || !object(pull.base) || !object(pull.base.repo) || pull.base.repo.id !== scope.repositoryId || !object(pull.head)) return { kind: 'blocked', reason: 'pull_unavailable' };
    if (pull.mergeable === false) return { kind: 'blocked', reason: 'merge_conflict' };
    const sha = (value: unknown): value is string => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
    if (pull.mergeable !== true || !sha(pull.merge_commit_sha) || !sha(pull.head.sha) || !sha(pull.base.sha)) return { kind: 'blocked', reason: 'merge_unresolved' };
    const { merge_commit_sha: merge, head: { sha: head }, base: { sha: base } } = pull;
    let ref: unknown;
    try { ref = await this.api(`${prefix}/git/ref/pull/${number}/merge`, repo.token); }
    catch (error) { if (error instanceof GitHubStatusError && error.status === 404) return { kind: 'blocked', reason: 'merge_ref_missing' }; throw error; }
    if (!object(ref) || ref.ref !== `refs/pull/${number}/merge` || !object(ref.object) || ref.object.type !== 'commit' || ref.object.sha !== merge) return { kind: 'blocked', reason: 'merge_ref_mismatch' };
    const commit = await this.api(`${prefix}/git/commits/${merge}`, repo.token);
    if (!object(commit) || commit.sha !== merge || !Array.isArray(commit.parents) || commit.parents.length !== 2 || !object(commit.parents[0]) || !object(commit.parents[1]) || commit.parents[0].sha !== base || commit.parents[1].sha !== head) return { kind: 'blocked', reason: 'merge_parents_mismatch' };
    return { kind: 'resolved', merge, head, base };
  }

  /** Reconciliation treats this list as observations; each PR is resolved separately. */
  async *listOpenPullRequests(scope: RepositoryScope): AsyncGenerator<number[]> {
    const repo = await this.repository(scope);
    for (let page = 1; page <= 1000; page++) {
      const numbers = new Set<number>();
      const result = await this.api(`/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}/pulls?state=open&per_page=100&page=${page}`, repo.token);
      if (!Array.isArray(result)) throw new Error('Invalid pull request list');
      for (const item of result) {
        if (!object(item) || typeof item.number !== 'number' || !Number.isSafeInteger(item.number) || item.number < 1) throw new Error('Invalid pull request list');
        numbers.add(item.number);
      }
      yield [...numbers];
      if (result.length < 100) return;
    }
    throw new Error('Pull request list exceeds reconciliation limit');
  }

  /** Resolve the PR itself under the destination installation, not a check association. */
  async resolvePullRequest(scope: RepositoryScope, number: number): Promise<{ number: number; sourceRepositoryId: number; destinationRepositoryId: number; head: string; base: string } | null> {
    if (!Number.isSafeInteger(number) || number < 1) throw new Error('Invalid pull request number');
    const repo = await this.repository(scope);
    const result = await this.api(`/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}/pulls/${number}`, repo.token);
    if (!object(result) || result.number !== number || (result.state !== 'open' && result.state !== 'closed') ||
        !object(result.base) || !object(result.base.repo) || result.base.repo.id !== scope.repositoryId) throw new Error('Invalid pull request identity');
    if (result.state === 'closed') return null;
    if (
        !object(result.head) || !object(result.head.repo) || typeof result.head.repo.id !== 'number' ||
        !Number.isSafeInteger(result.head.repo.id) || result.head.repo.id < 1 ||
        typeof result.head.sha !== 'string' || !/^[a-f0-9]{40}$/.test(result.head.sha) ||
        typeof result.base.sha !== 'string' || !/^[a-f0-9]{40}$/.test(result.base.sha)) throw new Error('Invalid pull request identity');
    return { number, sourceRepositoryId: result.head.repo.id, destinationRepositoryId: scope.repositoryId, head: result.head.sha, base: result.base.sha };
  }

  /** Resolve a branch through the installation-scoped GitHub API. */
  async resolveHead(scope: RepositoryScope, ref: string): Promise<string | null> {
    if (!ref.startsWith('refs/heads/') || ref.length > 512 || ref.length === 'refs/heads/'.length ||
        /[\x00-\x20\x7f~^:?*\[\\]/.test(ref) || ref.includes('..') || ref.includes('@{') ||
        ref.endsWith('/') || ref.endsWith('.') || ref.split('/').some(part => !part || part.startsWith('.') || part.endsWith('.lock'))) throw new Error('Invalid branch ref');
    const repo = await this.repository(scope);
    const branch = ref.slice('refs/heads/'.length).split('/').map(encodeURIComponent).join('/');
    let result: unknown;
    try { result = await this.api(`/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}/git/ref/heads/${branch}`, repo.token); }
    catch (error) { if (error instanceof GitHubStatusError && error.status === 404) return null; throw error; }
    if (!object(result) || result.ref !== ref || !object(result.object) || result.object.type !== 'commit' ||
        typeof result.object.sha !== 'string' || !/^[a-f0-9]{40}$/.test(result.object.sha)) throw new Error('Invalid branch head');
    return result.object.sha;
  }

  /** Stage an immutable checkout without exposing the installation token to the verifier. */
  async stageSnapshot(scope: RepositoryScope, input: { head: string; base: string; root: string; signal: AbortSignal }): Promise<{ snapshot: string; repository: string }> {
    const repo = await this.repository(scope);
    return fetchSnapshot({ ...input, owner: repo.owner, name: repo.name, token: repo.token });
  }

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
