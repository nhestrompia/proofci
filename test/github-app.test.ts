import { test } from 'node:test';
import assert from 'node:assert/strict';
import { generateKeyPairSync } from 'node:crypto';
import { GitHubApp } from '../src/github-app.ts';

const { privateKey } = generateKeyPairSync('rsa', { modulusLength: 2048 });

test('checks current installation and requests access for only the selected repository', async () => {
  const calls: string[] = [];
  const request: typeof fetch = async (input, init) => {
    const path = new URL(String(input)).pathname;
    calls.push(path);
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, suspended_at: null });
    if (path === '/app/installations/12/access_tokens') {
      assert.deepEqual(JSON.parse(String(init?.body)), { repository_ids: [34], permissions: { contents: 'read', pull_requests: 'read', checks: 'write' } });
      return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    }
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    throw new Error('unexpected request');
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  assert.equal(await app.checkInstallationAccess({ installationId: 12, repositoryId: 34 }), true);
  assert.deepEqual(calls, ['/app/installations/12', '/app/installations/12/access_tokens', '/repositories/34']);
});

test('rejects suspended installations and removed repositories', async () => {
  for (const condition of ['suspended', 'removed']) {
    const calls: string[] = [];
    const request: typeof fetch = async (input) => {
      const path = new URL(String(input)).pathname;
      calls.push(path);
      if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, suspended_at: condition === 'suspended' ? '2026-01-01' : null });
      if (path === '/app/installations/12/access_tokens' && condition === 'removed') return new Response('secret must not leak', { status: 404 });
      throw new Error('unexpected request');
    };
    const app = new GitHubApp({ appId: 7, privateKey, request });
    assert.equal(await app.checkInstallationAccess({ installationId: 12, repositoryId: 34 }), false);
    assert.deepEqual(calls, condition === 'suspended' ? ['/app/installations/12'] : ['/app/installations/12', '/app/installations/12/access_tokens']);
  }
});

test('uses authenticated identity and rejects revoked repository permissions', async () => {
  for (const allowed of [true, false]) {
    const calls: string[] = [];
    const request: typeof fetch = async (input, init) => {
      const path = new URL(String(input)).pathname;
      calls.push(path);
      if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, suspended_at: null });
      if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'installation-secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
      if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
      if (path === '/user') {
        assert.equal(new Headers(init?.headers).get('authorization'), 'Bearer user-secret');
        return Response.json({ id: 56 });
      }
      if (path === '/repos/owner/repo') return Response.json({ id: 34, permissions: { maintain: allowed } });
      throw new Error('unexpected request');
    };
    const app = new GitHubApp({ appId: 7, privateKey, request });
    assert.equal(await app.checkMaintainerAccess({ installationId: 12, repositoryId: 34 }, 'user-secret'), allowed ? 56 : null);
    assert.deepEqual(calls, ['/app/installations/12', '/app/installations/12/access_tokens', '/repositories/34', '/user', '/repos/owner/repo']);
  }
});

test('rejects installations missing the required App permissions', async () => {
  let calls = 0;
  const request: typeof fetch = async () => {
    calls++;
    return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'read', metadata: 'read' } });
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  assert.equal(await app.checkInstallationAccess({ installationId: 12, repositoryId: 34 }), false);
  assert.equal(calls, 1);
});

test('rejects unnecessary write access to repository contents', async () => {
  const request: typeof fetch = async () => Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'write', pull_requests: 'read', checks: 'write', metadata: 'read' } });
  assert.equal(await new GitHubApp({ appId: 7, privateKey, request }).checkInstallationAccess({ installationId: 12, repositoryId: 34 }), false);
});

test('reports unconfirmed when branch protection evidence is unavailable', async () => {
  const calls: string[] = [];
  const request: typeof fetch = async (input) => {
    const url = new URL(String(input)); calls.push(url.pathname);
    if (url.pathname === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (url.pathname === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (url.pathname === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' }, default_branch: 'main' });
    if (url.pathname === '/repos/owner/repo/branches/main/protection') return new Response('', { status: 403 });
    throw new Error('unexpected request');
  };
  assert.equal(await new GitHubApp({ appId: 7, privateKey, request }).inspectEnforcement({ installationId: 12, repositoryId: 34 }), 'unconfirmed');
  assert.ok(calls.includes('/repos/owner/repo/branches/main/protection'));
});

test('rejects an installation token that is not restricted to the selected repository', async () => {
  const paths: string[] = [];
  const request: typeof fetch = async (input) => {
    const path = new URL(String(input)).pathname; paths.push(path);
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }, { id: 35 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    throw new Error('unexpected request');
  };
  assert.equal(await new GitHubApp({ appId: 7, privateKey, request }).checkInstallationAccess({ installationId: 12, repositoryId: 34 }), false);
  assert.deepEqual(paths, ['/app/installations/12', '/app/installations/12/access_tokens']);
});

test('lists only repositories the signed-in user can access through this App', async () => {
  const request: typeof fetch = async (input, init) => {
    assert.equal(new Headers(init?.headers).get('authorization'), 'Bearer user-secret');
    const path = new URL(String(input)).pathname;
    if (path === '/user/installations') return Response.json({ installations: [{ id: 12, app_id: 7 }, { id: 13, app_id: 8 }] });
    if (path === '/user/installations/12/repositories') return Response.json({ repositories: [{ id: 34, full_name: 'owner/repo' }] });
    throw new Error('unexpected request');
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  assert.deepEqual(await app.listUserRepositories('user-secret'), [{ installationId: 12, repositoryId: 34, name: 'owner/repo' }]);
});

test('rejects an installation token with permissions outside the requested set', async () => {
  const paths: string[] = [];
  const request: typeof fetch = async (input) => {
    const path = new URL(String(input)).pathname; paths.push(path);
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read', issues: 'write' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', repositories: [{ id: 34 }], permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read', issues: 'write' } });
    throw new Error('unexpected request');
  };
  assert.equal(await new GitHubApp({ appId: 7, privateKey, request }).checkInstallationAccess({ installationId: 12, repositoryId: 34 }), false);
  assert.deepEqual(paths, ['/app/installations/12', '/app/installations/12/access_tokens']);
});

test('treats an ambiguous GitHub validation response as unavailable, not revoked', async () => {
  const request: typeof fetch = async (input) => {
    const path = new URL(String(input)).pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return new Response('', { status: 422 });
    throw new Error('unexpected request');
  };
  assert.equal(await new GitHubApp({ appId: 7, privateKey, request }).installationAccess({ installationId: 12, repositoryId: 34 }), 'unavailable');
});

test('uninstalled and removed repository scopes cannot authorize access', async () => {
  for (const unavailable of ['installation', 'repository']) {
    const paths: string[] = [];
    const request: typeof fetch = async (input) => {
      const path = new URL(String(input)).pathname;
      paths.push(path);
      if (path === '/app/installations/12' && unavailable === 'installation') return new Response('', { status: 404 });
      if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
      if (path === '/app/installations/12/access_tokens') return new Response('', { status: 422 });
      throw new Error('unexpected request');
    };
    const app = new GitHubApp({ appId: 7, privateKey, request });
    assert.equal(await app.checkInstallationAccess({ installationId: 12, repositoryId: 34 }), false);
    assert.deepEqual(paths, unavailable === 'installation' ? ['/app/installations/12'] : ['/app/installations/12', '/app/installations/12/access_tokens']);
  }
});

test('resolves the current immutable head with repository-scoped credentials', async () => {
  const request: typeof fetch = async input => {
    const path = new URL(String(input)).pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === '/repos/owner/repo/git/ref/heads/main') return Response.json({ ref: 'refs/heads/main', object: { type: 'commit', sha: 'a'.repeat(40) } });
    throw new Error(`unexpected path ${path}`);
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  assert.equal(await app.resolveHead({ installationId: 12, repositoryId: 34 }, 'refs/heads/main'), 'a'.repeat(40));
});

test('resolves only the current GitHub test merge whose parents match the pull request', async () => {
  const base = 'a'.repeat(40), head = 'b'.repeat(40), merge = 'c'.repeat(40);
  let ref = merge;
  const request: typeof fetch = async input => {
    const path = new URL(String(input)).pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === '/repos/owner/repo/pulls/5') return Response.json({ number: 5, state: 'open', mergeable: true, merge_commit_sha: merge, base: { sha: base, repo: { id: 34 } }, head: { sha: head } });
    if (path === '/repos/owner/repo/git/ref/pull/5/merge') return Response.json({ ref: 'refs/pull/5/merge', object: { type: 'commit', sha: ref } });
    if (path === `/repos/owner/repo/git/commits/${merge}`) return Response.json({ sha: merge, parents: [{ sha: base }, { sha: head }] });
    throw new Error(`unexpected path ${path}`);
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  assert.deepEqual(await app.resolvePullMerge({ installationId: 12, repositoryId: 34 }, 5), { kind: 'resolved', merge, head, base });
  ref = 'd'.repeat(40);
  assert.deepEqual(await app.resolvePullMerge({ installationId: 12, repositoryId: 34 }, 5), { kind: 'blocked', reason: 'merge_ref_mismatch' });
});

test('blocks unresolved, conflicting, missing, or stale pull request test merges', async () => {
  const base = 'a'.repeat(40), head = 'b'.repeat(40), merge = 'c'.repeat(40);
  for (const [scenario, reason] of [
    ['unresolved', 'merge_unresolved'], ['conflict', 'merge_conflict'],
    ['missing', 'merge_ref_missing'], ['parents', 'merge_parents_mismatch'],
  ]) {
    const request: typeof fetch = async input => {
      const path = new URL(String(input)).pathname;
      if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
      if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
      if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
      if (path === '/repos/owner/repo/pulls/5') return Response.json({ number: 5, state: 'open', mergeable: scenario === 'unresolved' ? null : scenario !== 'conflict', merge_commit_sha: merge, base: { sha: base, repo: { id: 34 } }, head: { sha: head } });
      if (path === '/repos/owner/repo/git/ref/pull/5/merge') return scenario === 'missing' ? new Response('', { status: 404 }) : Response.json({ ref: 'refs/pull/5/merge', object: { type: 'commit', sha: merge } });
      if (path === `/repos/owner/repo/git/commits/${merge}`) return Response.json({ sha: merge, parents: [{ sha: base }, { sha: 'd'.repeat(40) }] });
      throw new Error(`unexpected path ${path}`);
    };
    const app = new GitHubApp({ appId: 7, privateKey, request });
    assert.deepEqual(await app.resolvePullMerge({ installationId: 12, repositoryId: 34 }, 5), { kind: 'blocked', reason });
  }
});

test('reconciles a check after an ambiguous error and batches annotations without duplicates', async () => {
  const sha = 'a'.repeat(40), runId = '12345678-1234-4234-8234-123456789abc';
  let created = false, failed = false, creates = 0, completed = false;
  const stored: Array<{ message: string }> = [];
  const request: typeof fetch = async (input, init) => {
    const url = new URL(String(input)), path = url.pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === `/repos/owner/repo/commits/${sha}/check-runs`) return Response.json({ check_runs: created ? [{ id: 9, external_id: runId, app: { id: 7 } }] : [] });
    if (path === '/repos/owner/repo/check-runs' && init?.method === 'POST') { created = true; creates++; return Response.json({ id: 9 }); }
    if (path === '/repos/owner/repo/check-runs/9/annotations') {
      const page = Number(url.searchParams.get('page')); return Response.json(stored.slice((page - 1) * 100, page * 100));
    }
    if (path === '/repos/owner/repo/check-runs/9' && init?.method === 'PATCH') {
      const body = JSON.parse(String(init.body));
      if (body.output.annotations) {
        assert.ok(body.output.annotations.length <= 50);
        stored.push(...body.output.annotations);
        if (stored.length === 100 && !failed) { failed = true; throw new Error('response lost'); }
      }
      if (body.status === 'completed') { assert.equal(body.conclusion, 'success'); completed = true; }
      return Response.json({ id: 9 });
    }
    throw new Error(`unexpected path ${path}`);
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  const annotations = Array.from({ length: 120 }, (_, index) => ({ path: 'candidate.lean', start_line: 1, end_line: 1, annotation_level: 'notice' as const, message: `property ${index}` }));
  const input = { runId, sha, detailsUrl: 'https://example.com/run', output: { title: 'Verified', summary: 'all verified', conclusion: 'success' as const }, annotations, fresh: async () => true };
  await assert.rejects(app.publishCheck({ installationId: 12, repositoryId: 34 }, input));
  await app.publishCheck({ installationId: 12, repositoryId: 34 }, input);
  assert.equal(creates, 1); assert.equal(stored.length, 120); assert.equal(new Set(stored.map(item => item.message)).size, 120); assert.equal(completed, true);
});
