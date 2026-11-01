import { createPrivateKey } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { Pool } from 'pg';
import { EnrollmentStore } from './enrollment-store.ts';
import { EnrollmentService } from './enrollment-service.ts';
import { GitHubApp } from './github-app.ts';
import { OAuthSessions } from './oauth.ts';
import { processInstallationEvent } from './installation-events.ts';
import { processPushEvent } from './push-events.ts';
import { RunStore } from './run-store.ts';
import { ActiveBaselines } from './active-baselines.ts';
import { RunService, type PilotConfiguration } from './run-service.ts';
import { MigrationService } from './migration-service.ts';
import { LocalAuthority } from './local-authority.ts';
import { readPilotConfiguration } from './pilot-configuration.ts';

function required(name: string): string {
  const value = process.env[name];
  if (!value) throw new Error(`Missing configuration: ${name}`);
  return value;
}
const origin = new URL(required('PROOFCI_ORIGIN'));
const localHTTP = origin.protocol === 'http:' && ['127.0.0.1', 'localhost'].includes(origin.hostname);
if ((origin.protocol !== 'https:' && !localHTTP) || origin.pathname !== '/' || origin.search || origin.hash || origin.username || origin.password) throw new Error('PROOFCI_ORIGIN must be HTTPS or loopback HTTP');
const appId = Number(required('GITHUB_APP_ID'));
if (!Number.isSafeInteger(appId) || appId <= 0) throw new Error('Invalid GITHUB_APP_ID');
const github = new GitHubApp({ appId, privateKey: createPrivateKey(readFileSync(required('GITHUB_PRIVATE_KEY_FILE'))) });
const sessions = new OAuthSessions({ clientId: required('GITHUB_CLIENT_ID'), clientSecret: required('GITHUB_CLIENT_SECRET'), redirectUri: new URL('/oauth/callback', origin).toString() });
const pool = new Pool({ connectionString: required('DATABASE_URL') });
const store = new EnrollmentStore(pool);
await store.initialize();
const enrollment = new EnrollmentService({ store, sessions, github });
let runs: RunStore | undefined;
let runService: RunService | undefined;
let migrationService: MigrationService | undefined;
let pilotRepositories: PilotConfiguration[] = [];
const pilotConfig = process.env.PROOFCI_LOCAL_PILOT_CONFIG;
if (pilotConfig) {
  const repositories = readPilotConfiguration(pilotConfig);
  pilotRepositories = repositories;
  const authority = new LocalAuthority(repositories);
  store.setAuthority(authority);
  const baselines = new ActiveBaselines(repositories);
  migrationService = new MigrationService({ sessions, github, selections: store, repositories });
  runs = new RunStore(pool, authority); await runs.initialize();
  runService = new RunService({ store: runs, selections: store, github, baselines, repositories });
  runService.start();
}

function cookie(request: IncomingMessage, name: string): string {
  const entry = (request.headers.cookie ?? '').split('; ').find((part) => part.startsWith(`${name}=`));
  return entry?.slice(name.length + 1) ?? '';
}
function setCookie(response: ServerResponse, name: string, value: string, maxAge: number): void {
  response.setHeader('Set-Cookie', `${name}=${value}; Path=/; ${localHTTP ? '' : 'Secure; '}HttpOnly; SameSite=Lax; Max-Age=${maxAge}`);
}
function reply(response: ServerResponse, status: number, body: string): void {
  response.writeHead(status, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store', 'content-security-policy': "default-src 'none'; form-action 'self'; base-uri 'none'; frame-ancestors 'none'", 'x-content-type-options': 'nosniff', 'referrer-policy': 'same-origin' });
  response.end(body);
}
async function form(request: IncomingMessage): Promise<URLSearchParams> {
  if (request.headers['content-type'] !== 'application/x-www-form-urlencoded') throw new Error('Invalid content type');
  let data = '';
  for await (const chunk of request) { data += chunk; if (data.length > 4096) throw new Error('Form too large'); }
  return new URLSearchParams(data);
}
const page = `<!doctype html><title>ProofCI enrollment</title><h1>ProofCI enrollment</h1>
<p>Enrollment requires App permissions: contents read, pull requests read, checks write, and metadata read. Optional administration read is only for policy inspection.</p>
<p>Installing or enrolling a repository does not activate contracts or protect merges.</p>
<p>Configure the GitHub installation and repository-selection webhooks to clear enrollments when access is removed.</p>
<p>Before enforcement, require the ProofCI check from the expected App and require fresh merge results or a merge queue. Policy inspection may require administration read access and reports only observed branch settings.</p>
<p><a href="/login">Sign in with GitHub</a></p>`;

function escapeHtml(text: string): string {
  return text.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;').replaceAll("'", '&#39;');
}

const server = createServer(async (request, response) => {
  try {
    const url = new URL(request.url ?? '/', origin);
    if (request.method === 'GET' && url.pathname === '/') {
      const repositories = await sessions.listRepositories(cookie(request, 'proofci_session'), github);
      if (!repositories) return reply(response, 200, `${page}<p>Sign in to select a repository from an installed App.</p>`);
      if (repositories.length === 0) return reply(response, 200, `${page}<p>No repositories are available. Install the App on a repository you can maintain.</p><form method="post" action="/logout"><button>Sign out</button></form>`);
      const options = repositories.map(repo => `<option value="${repo.installationId}:${repo.repositoryId}">${escapeHtml(repo.name)}</option>`).join('');
      return reply(response, 200, `${page}<form method="post" action="/migrate"><h2>Authorize contract migration</h2><label>Repository <select name="repository" required>${options}</select></label><label>Candidate commit <input name="head" required pattern="[0-9a-f]{40}"></label><label>Current manifest SHA-256 <input name="previous" required pattern="[0-9a-f]{64}"></label><label>Replacement manifest SHA-256 <input name="replacement" required pattern="[0-9a-f]{64}"></label><button>Authorize and verify migration</button></form><form method="post" action="/enroll"><label>Repository <select name="repository" required>${options}</select></label><button>Enroll repository</button><button formaction="/inspect">Check policy</button><button formaction="/remove">Remove enrollment</button></form><form method="post" action="/logout"><button>Sign out</button></form>`);
    }
    if (request.method === 'GET' && url.pathname === '/login') {
      const login = sessions.start();
      setCookie(response, 'proofci_login', login.binding, 300);
      response.writeHead(303, { location: login.url, 'cache-control': 'no-store', 'referrer-policy': 'no-referrer' }); return response.end();
    }
    if (request.method === 'GET' && url.pathname === '/oauth/callback') {
      const session = await sessions.finish({ state: url.searchParams.get('state') ?? '', code: url.searchParams.get('code') ?? '', binding: cookie(request, 'proofci_login') });
      if (!session) return reply(response, 403, 'Sign-in failed.');
      setCookie(response, 'proofci_session', session, 1800);
      response.writeHead(303, { location: '/', 'cache-control': 'no-store', 'referrer-policy': 'no-referrer' }); return response.end();
    }
    if (request.method === 'POST' && url.pathname === '/webhooks/github') {
      const secret = process.env.GITHUB_WEBHOOK_SECRET;
      if (!secret) return reply(response, 503, 'GitHub webhook is not configured.');
      const chunks: Buffer[] = [];
      let size = 0;
      for await (const chunk of request) {
        const bytes = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
        size += bytes.length;
        if (size > 1024 * 1024) return reply(response, 413, 'Webhook body too large.');
        chunks.push(bytes);
      }
      const signature = request.headers['x-hub-signature-256'];
      const event = request.headers['x-github-event'];
      const deliveryId = request.headers['x-github-delivery'];
      if (typeof signature !== 'string' || typeof event !== 'string' || typeof deliveryId !== 'string') return reply(response, 401, 'Invalid webhook.');
      const body = Buffer.concat(chunks);
      if (event === 'push') {
        const runStore = runs;
        if (!runStore) return reply(response, 503, 'Run scheduling is not configured.');
        if (!await processPushEvent({ body, signature, event, deliveryId, secret, store: { acceptDelivery: delivery => pilotRepositories.some(item => item.installationId === delivery.installationId && item.repositoryId === delivery.repositoryId && item.ref === delivery.ref) ? runStore.acceptDelivery(delivery) : Promise.resolve(true) } })) return reply(response, 401, 'Invalid or unauthorized webhook.');
      } else if (!await processInstallationEvent({ body, signature, event, deliveryId, secret, store })) return reply(response, 401, 'Invalid webhook.');
      response.writeHead(204, { 'cache-control': 'no-store' }); return response.end();
    }
    if (request.method === 'POST' && url.pathname === '/migrate') {
      if (request.headers.origin !== origin.origin || !migrationService) return reply(response, 403, 'Migration denied.');
      const data = await form(request);
      const selection = data.get('repository') ?? '';
      if (!/^[1-9]\d*:[1-9]\d*$/.test(selection)) return reply(response, 400, 'Invalid repository selection.');
      const [installationId, repositoryId] = selection.split(':').map(Number);
      try {
        const result = await migrationService.migrate({ session: cookie(request, 'proofci_session'), scope: { installationId, repositoryId }, head: data.get('head') ?? '', previous: data.get('previous') ?? '', replacement: data.get('replacement') ?? '' });
        return reply(response, result.status === 'passed' ? 200 : 422, `<h1>${result.status === 'passed' ? 'Policy changed' : 'Migration not activated'}</h1><pre>${escapeHtml(JSON.stringify(result, null, 2))}</pre>`);
      } catch { return reply(response, 403, 'Migration failed or authorization is stale. The previous baseline remains active unless another migration replaced it.'); }
    }
    if (request.method === 'POST' && url.pathname === '/logout') {
      if (request.headers.origin !== origin.origin) return reply(response, 403, 'Request denied.');
      sessions.end(cookie(request, 'proofci_session'));
      setCookie(response, 'proofci_session', '', 0);
      response.writeHead(303, { location: '/', 'cache-control': 'no-store', 'referrer-policy': 'no-referrer' }); return response.end();
    }
    if (request.method === 'POST' && ['/enroll', '/inspect', '/remove'].includes(url.pathname)) {
      if (request.headers.origin !== origin.origin) return reply(response, 403, 'Request denied.');
      const data = await form(request);
      const selection = data.get('repository') ?? '';
      if (!/^[1-9]\d*:[1-9]\d*$/.test(selection)) return reply(response, 400, 'Invalid repository selection.');
      const [installationId, repositoryId] = selection.split(':').map(Number);
      const scope = { installationId, repositoryId };
      const input = { session: cookie(request, 'proofci_session'), scope };
      if (url.pathname === '/remove') {
        if (!await enrollment.remove(input)) return reply(response, 403, 'Removal denied. Sign in and check your current repository authority and App access.');
        return reply(response, 200, 'Enrollment removed. New work is no longer authorized for this selection.');
      }
      if (url.pathname === '/enroll' && !await enrollment.enroll(input)) return reply(response, 403, 'Enrollment denied. Sign in and check your current repository authority and App access.');
      const observed = await enrollment.inspect(input);
      if (observed === null && url.pathname !== '/enroll') return reply(response, 403, 'Policy inspection denied. Sign in and check your enrollment and current repository authority.');
      const enforcement = observed ?? 'unconfirmed';
      return reply(response, 200, `GitHub required-check configuration: ${enforcement}. This describes branch settings only; it does not confirm check publication, contract activation, or verification of merges. Require the ProofCI check from this App and fresh merge results or a merge queue.`);
    }
    return reply(response, 404, 'Not found.');
  } catch { return reply(response, 500, 'Request failed.'); }
});
const port = Number(process.env.PORT ?? '3000');
if (!Number.isInteger(port) || port < 1 || port > 65535) throw new Error('Invalid PORT');
server.listen(port, '127.0.0.1');
process.once('SIGTERM', () => { runService?.stop(); server.close(); });
process.once('SIGINT', () => { runService?.stop(); server.close(); });
