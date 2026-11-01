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

test('resolves a fork pull request from its destination repository, with explicit immutable identities', async () => {
  const request: typeof fetch = async input => {
    const path = new URL(String(input)).pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === '/repos/owner/repo/pulls/5') return Response.json({ number: 5, state: 'open', head: { sha: 'a'.repeat(40), repo: { id: 99 } }, base: { sha: 'b'.repeat(40), repo: { id: 34 } } });
    throw new Error(`unexpected path ${path}`);
  };
  const app = new GitHubApp({ appId: 7, privateKey, request });
  assert.deepEqual(await app.resolvePullRequest({ installationId: 12, repositoryId: 34 }, 5), { number: 5, sourceRepositoryId: 99, destinationRepositoryId: 34, head: 'a'.repeat(40), base: 'b'.repeat(40) });
});

test('rejects closed, malformed, or mismatched pull request identities', async () => {
  const valid = { number: 5, state: 'open', head: { sha: 'a'.repeat(40), repo: { id: 99 } }, base: { sha: 'b'.repeat(40), repo: { id: 34 } } };
  for (const pr of [{ ...valid, number: 6 }, { ...valid, head: { ...valid.head, repo: null } }, { ...valid, base: { ...valid.base, repo: { id: 35 } } }, { ...valid, head: { ...valid.head, sha: 'bad' } }]) {
    const request: typeof fetch = async input => {
      const path = new URL(String(input)).pathname;
      if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
      if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
      if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
      if (path === '/repos/owner/repo/pulls/5') return Response.json(pr);
      throw new Error(`unexpected path ${path}`);
    };
    await assert.rejects(new GitHubApp({ appId: 7, privateKey, request }).resolvePullRequest({ installationId: 12, repositoryId: 34 }, 5));
  }
});

test('lists open pull requests from the enrolled destination for reconciliation', async () => {
  const request: typeof fetch = async input => {
    const url = new URL(String(input)), path = url.pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === '/repos/owner/repo/pulls' && url.searchParams.get('state') === 'open') return Response.json([{ number: 5 }, { number: 7 }]);
    throw new Error(`unexpected path ${path}`);
  };
  const pages = [];
  for await (const page of new GitHubApp({ appId: 7, privateKey, request }).listOpenPullRequests({ installationId: 12, repositoryId: 34 })) pages.push(...page);
  assert.deepEqual(pages, [5, 7]);
});


test('reconciliation yields each page before fetching the next one', async () => {
  const request: typeof fetch = async input => {
    const url = new URL(String(input)), path = url.pathname;
    if (path === '/app/installations/12') return Response.json({ id: 12, app_id: 7, suspended_at: null, permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' } });
    if (path === '/app/installations/12/access_tokens') return Response.json({ token: 'secret', permissions: { contents: 'read', pull_requests: 'read', checks: 'write', metadata: 'read' }, repositories: [{ id: 34 }] });
    if (path === '/repositories/34') return Response.json({ id: 34, name: 'repo', owner: { login: 'owner' } });
    if (path === '/repos/owner/repo/pulls' && url.searchParams.get('page') === '1') return Response.json(Array.from({ length: 100 }, (_, i) => ({ number: i + 1 })));
    if (path === '/repos/owner/repo/pulls' && url.searchParams.get('page') === '2') throw new Error('page unavailable');
    throw new Error(`unexpected path ${path}`);
  };
  const pages = new GitHubApp({ appId: 7, privateKey, request }).listOpenPullRequests({ installationId: 12, repositoryId: 34 });
  assert.equal((await pages.next()).value?.length, 100);
  await assert.rejects(pages.next(), /page unavailable/);
});
