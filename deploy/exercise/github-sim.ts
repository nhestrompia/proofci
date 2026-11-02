/**
 * A local GitHub API simulator for operational exercises. It implements only the
 * endpoints the control service calls, verifies App JWTs against registered public
 * keys, scopes installation tokens to one repository, and records published checks.
 * It is not a security boundary and must never be exposed outside an exercise network.
 */
import { createPublicKey, createVerify, randomBytes, type KeyObject } from 'node:crypto';
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';

type Repo = { id: number; installationId: number; owner: string; name: string; defaultBranch: string };
type Pull = { number: number; state: 'open' | 'closed'; head: string; headRepoId: number; base: string; merge: string | null; mergeable: boolean | null };
type Check = { id: number; repoId: number; head_sha: string; external_id: string; name: string; status: string; conclusion: string | null; details_url: string | null; output: unknown; annotations: unknown[]; history: unknown[] };
type Token = { kind: 'installation'; installationId: number; repoId: number; expires: number } | { kind: 'user'; userId: number; expires: number };

const state = {
  appId: 0, keys: [] as KeyObject[], clientId: '', clientSecrets: [] as string[],
  user: { id: 0, login: 'maintainer' },
  repos: new Map<number, Repo>(),
  refs: new Map<string, string>(), // `${repo}:${ref}` -> sha
  commits: new Map<string, string[]>(), // `${repo}:${sha}` -> parents
  pulls: new Map<string, Pull>(), // `${repo}:${number}`
  checks: [] as Check[],
  tokens: new Map<string, Token>(),
  failCheckWrites: false, unavailable: false,
  rejectedJwts: 0, requests: new Map<string, number>(),
};

function send(response: ServerResponse, status: number, body: unknown): void {
  response.writeHead(status, { 'content-type': 'application/json' });
  response.end(JSON.stringify(body));
}
async function json(request: IncomingMessage): Promise<Record<string, unknown>> {
  let data = '';
  for await (const chunk of request) data += chunk;
  return data ? JSON.parse(data) : {};
}
function verifyJwt(token: string): boolean {
  const [header, payload, signature] = token.split('.');
  if (!header || !payload || !signature) return false;
  const claims = JSON.parse(Buffer.from(payload, 'base64url').toString());
  if (claims.iss !== String(state.appId) || claims.exp < Date.now() / 1000) return false;
  return state.keys.some(key => createVerify('RSA-SHA256').update(`${header}.${payload}`).verify(key, Buffer.from(signature, 'base64url')));
}
function bearer(request: IncomingMessage): string { return (request.headers.authorization ?? '').replace(/^Bearer /, ''); }
function repoByName(owner: string, name: string): Repo | undefined { return [...state.repos.values()].find(repo => repo.owner === owner && repo.name === name); }
function pullJson(repo: Repo, pull: Pull) {
  return { number: pull.number, state: pull.state, mergeable: pull.mergeable, merge_commit_sha: pull.merge,
    head: { sha: pull.head, repo: { id: pull.headRepoId } }, base: { sha: pull.base, repo: { id: repo.id } } };
}

const server = createServer(async (request, response) => {
  try {
    const url = new URL(request.url ?? '/', 'http://sim');
    const path = url.pathname, method = request.method ?? 'GET';
    state.requests.set(`${method} ${path.replace(/\/[0-9a-f]{40}/g, '/SHA').replace(/\/\d+/g, '/N')}`, (state.requests.get(`${method} ${path.replace(/\/[0-9a-f]{40}/g, '/SHA').replace(/\/\d+/g, '/N')}`) ?? 0) + 1);

    // Exercise control API.
    if (path.startsWith('/admin/')) {
      const body = method === 'POST' ? await json(request) : {};
      if (path === '/admin/app') {
        state.appId = Number(body.appId); state.clientId = String(body.clientId);
        state.keys = (body.publicKeys as string[]).map(pem => createPublicKey(pem));
        state.clientSecrets = body.clientSecrets as string[];
        state.user = body.user as typeof state.user;
        return send(response, 200, { ok: true });
      }
      if (path === '/admin/repo') { state.repos.set(Number(body.id), body as unknown as Repo); return send(response, 200, { ok: true }); }
      if (path === '/admin/ref') { state.refs.set(`${body.repoId}:${body.ref}`, String(body.sha)); return send(response, 200, { ok: true }); }
      if (path === '/admin/commit') { state.commits.set(`${body.repoId}:${body.sha}`, body.parents as string[]); return send(response, 200, { ok: true }); }
      if (path === '/admin/pull') { state.pulls.set(`${body.repoId}:${body.number}`, body.pull as Pull); return send(response, 200, { ok: true }); }
      if (path === '/admin/faults') { state.failCheckWrites = Boolean(body.failCheckWrites); state.unavailable = Boolean(body.unavailable); return send(response, 200, { ok: true }); }
      if (path === '/admin/state') return send(response, 200, { checks: state.checks, rejectedJwts: state.rejectedJwts, requests: Object.fromEntries(state.requests) });
      return send(response, 404, {});
    }
    if (state.unavailable) return send(response, 503, { message: 'unavailable' });

    // OAuth.
    if (path === '/login/oauth/access_token' && method === 'POST') {
      const body = await json(request);
      if (body.client_id !== state.clientId || !state.clientSecrets.includes(String(body.client_secret)) || !body.code_verifier) return send(response, 401, { error: 'bad_verification_code' });
      const token = `ghu_${randomBytes(16).toString('hex')}`;
      state.tokens.set(token, { kind: 'user', userId: state.user.id, expires: Date.now() + 3600_000 });
      return send(response, 200, { access_token: token, token_type: 'bearer' });
    }

    // App JWT endpoints.
    const installation = /^\/app\/installations\/(\d+)(\/access_tokens)?$/.exec(path);
    if (installation) {
      if (!verifyJwt(bearer(request))) { state.rejectedJwts++; return send(response, 401, { message: 'A JSON web token could not be decoded' }); }
      const id = Number(installation[1]);
      const repos = [...state.repos.values()].filter(repo => repo.installationId === id);
      if (!repos.length) return send(response, 404, {});
      const permissions = { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' };
      if (!installation[2]) return send(response, 200, { id, app_id: state.appId, suspended_at: null, permissions });
      const body = await json(request);
      const ids = body.repository_ids as number[];
      if (ids.length !== 1 || !repos.some(repo => repo.id === ids[0])) return send(response, 422, {});
      const token = `ghs_${randomBytes(16).toString('hex')}`;
      state.tokens.set(token, { kind: 'installation', installationId: id, repoId: ids[0]!, expires: Date.now() + 3600_000 });
      return send(response, 201, { token, repositories: [{ id: ids[0] }], permissions: { ...(body.permissions as object), metadata: 'read' } });
    }

    const token = state.tokens.get(bearer(request));
    if (!token || token.expires < Date.now()) return send(response, 401, { message: 'Bad credentials' });

    // User-token endpoints.
    if (token.kind === 'user') {
      if (path === '/user') return send(response, 200, { id: state.user.id, login: state.user.login });
      if (path === '/user/installations') return send(response, 200, { installations: [...new Set([...state.repos.values()].map(repo => repo.installationId))].map(id => ({ id, app_id: state.appId })) });
      const listed = /^\/user\/installations\/(\d+)\/repositories$/.exec(path);
      if (listed) return send(response, 200, { repositories: [...state.repos.values()].filter(repo => repo.installationId === Number(listed[1])).map(repo => ({ id: repo.id, full_name: `${repo.owner}/${repo.name}` })) });
      const repoPath = /^\/repos\/([^/]+)\/([^/]+)$/.exec(path);
      const repo = repoPath && repoByName(decodeURIComponent(repoPath[1]!), decodeURIComponent(repoPath[2]!));
      if (repo) return send(response, 200, { id: repo.id, permissions: { admin: true, maintain: true, push: true } });
      return send(response, 404, {});
    }

    // Installation-token endpoints are limited to the token's repository.
    const repo = state.repos.get(token.repoId)!;
    if (path === `/repositories/${repo.id}`) return send(response, 200, { id: repo.id, name: repo.name, owner: { login: repo.owner }, default_branch: repo.defaultBranch });
    const prefix = `/repos/${encodeURIComponent(repo.owner)}/${encodeURIComponent(repo.name)}`;
    if (!path.startsWith(prefix + '/')) return send(response, 404, {});
    const rest = path.slice(prefix.length);
    let match: RegExpExecArray | null;
    if (rest === '/pulls' && method === 'GET') return send(response, 200, [...state.pulls.entries()].filter(([key, pull]) => key.startsWith(`${repo.id}:`) && pull.state === 'open').map(([, pull]) => ({ number: pull.number })));
    if ((match = /^\/pulls\/(\d+)$/.exec(rest))) {
      const pull = state.pulls.get(`${repo.id}:${match[1]}`);
      return pull ? send(response, 200, pullJson(repo, pull)) : send(response, 404, {});
    }
    if ((match = /^\/git\/ref\/(.+)$/.exec(rest))) {
      const ref = `refs/${decodeURIComponent(match[1]!)}`;
      const sha = state.refs.get(`${repo.id}:${ref}`);
      return sha ? send(response, 200, { ref, object: { type: 'commit', sha } }) : send(response, 404, {});
    }
    if ((match = /^\/git\/commits\/([0-9a-f]{40})$/.exec(rest))) {
      const parents = state.commits.get(`${repo.id}:${match[1]}`);
      return parents ? send(response, 200, { sha: match[1], parents: parents.map(sha => ({ sha })) }) : send(response, 404, {});
    }
    if ((match = /^\/commits\/([0-9a-f]{40})\/check-runs$/.exec(rest))) {
      return send(response, 200, { check_runs: state.checks.filter(check => check.repoId === repo.id && check.head_sha === match![1]).map(check => ({ id: check.id, external_id: check.external_id, app: { id: state.appId } })) });
    }
    if (rest === '/check-runs' && method === 'POST') {
      if (state.failCheckWrites) return send(response, 502, { message: 'injected failure' });
      const body = await json(request);
      const check: Check = { id: state.checks.length + 1, repoId: repo.id, head_sha: String(body.head_sha), external_id: String(body.external_id), name: String(body.name),
        status: String(body.status), conclusion: null, details_url: String(body.details_url ?? ''), output: body.output, annotations: [], history: [body] };
      state.checks.push(check);
      return send(response, 201, { id: check.id });
    }
    if ((match = /^\/check-runs\/(\d+)(\/annotations)?$/.exec(rest))) {
      const check = state.checks.find(item => item.id === Number(match![1]) && item.repoId === repo.id);
      if (!check) return send(response, 404, {});
      if (match[2]) return send(response, 200, check.annotations);
      if (method !== 'PATCH') return send(response, 200, check);
      if (state.failCheckWrites) return send(response, 502, { message: 'injected failure' });
      const body = await json(request);
      check.history.push(body);
      if (typeof body.status === 'string') check.status = body.status;
      if (typeof body.conclusion === 'string') check.conclusion = body.conclusion;
      if (typeof body.details_url === 'string') check.details_url = body.details_url;
      if (body.output && typeof body.output === 'object') {
        const output = body.output as { annotations?: unknown[] };
        if (output.annotations) check.annotations.push(...output.annotations);
        check.output = { ...output, annotations: undefined };
      }
      return send(response, 200, { id: check.id });
    }
    return send(response, 404, {});
  } catch (error) { send(response, 500, { message: error instanceof Error ? error.message : String(error) }); }
});

server.listen(Number(process.env.PORT ?? '8080'), process.env.HOST ?? '0.0.0.0');
for (const signal of ['SIGTERM', 'SIGINT'] as const) process.once(signal, () => server.close());
