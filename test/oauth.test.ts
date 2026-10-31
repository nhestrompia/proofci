import { test } from 'node:test';
import assert from 'node:assert/strict';
import { OAuthSessions } from '../src/oauth.ts';

test('OAuth state is browser-bound and single use, and sessions do not expose user tokens', async () => {
  let exchanges = 0;
  const request: typeof fetch = async () => { exchanges++; return Response.json({ access_token: 'private-token', token_type: 'bearer' }); };
  const sessions = new OAuthSessions({ clientId: 'client', clientSecret: 'secret', redirectUri: 'https://example.test/callback', request });
  const login = sessions.start();
  const state = new URL(login.url).searchParams.get('state');
  assert.ok(state);
  assert.equal(await sessions.finish({ state, binding: 'wrong', code: 'code' }), null);
  assert.equal(exchanges, 0);
  const session = await sessions.finish({ state, binding: login.binding, code: 'code' });
  assert.ok(session);
  assert.notEqual(session, 'private-token');
  assert.deepEqual(await sessions.listRepositories(session, { listUserRepositories: async token => token === 'private-token' ? [{ installationId: 1, repositoryId: 2, name: 'owner/repo' }] : [] }), [{ installationId: 1, repositoryId: 2, name: 'owner/repo' }]);
  assert.equal(await sessions.listRepositories('unknown', { listUserRepositories: async () => { throw new Error('must not be called'); } }), null);
  assert.equal(await sessions.finish({ state, binding: login.binding, code: 'code' }), null);
  assert.equal(exchanges, 1);
  assert.equal(await sessions.checkMaintainer({ session, scope: { installationId: 1, repositoryId: 2 }, github: { checkMaintainerAccess: async (_scope, token) => token === 'private-token' ? 3 : null } }), 3);
});
