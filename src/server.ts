import { createHash, createPrivateKey } from 'node:crypto';
import { lstatSync, readFileSync } from 'node:fs';
import { isAbsolute } from 'node:path';
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { Pool } from 'pg';
import { EnrollmentStore } from './enrollment-store.ts';
import { EnrollmentService } from './enrollment-service.ts';
import { GitHubApp } from './github-app.ts';
import { OAuthSessions } from './oauth.ts';
import { processInstallationEvent } from './installation-events.ts';
import { processPullEvent } from './pull-events.ts';
import { processPushEvent } from './push-events.ts';
import { RunStore } from './run-store.ts';
import { ForkPolicy, policyDigest } from './fork-policy.ts';
import { ActiveBaselines } from './active-baselines.ts';
import { RunService, type PilotConfiguration } from './run-service.ts';
import { GetBucketVersioningCommand, S3Client } from '@aws-sdk/client-s3';
import { EvidenceStore } from './evidence-store.ts';
import { downloadEvidence } from './evidence-access.ts';

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
let evidenceStore: EvidenceStore | undefined;
let forkPolicy: ForkPolicy | undefined;
let activeBaselines: ActiveBaselines | undefined;
let pilotRepositories: PilotConfiguration[] = [];
const pilotConfig = process.env.PROOFCI_LOCAL_PILOT_CONFIG;
if (pilotConfig) {
  if (!isAbsolute(pilotConfig)) throw new Error('Pilot configuration path must be absolute');
  const stat = lstatSync(pilotConfig);
  if (!stat.isFile() || stat.isSymbolicLink() || (stat.mode & 0o022) !== 0 || stat.size > 65536) throw new Error('Invalid pilot configuration file');
  const raw: unknown = JSON.parse(readFileSync(pilotConfig, 'utf8'));
  if (!Array.isArray(raw)) throw new Error('Invalid pilot configuration');
  const repositories: PilotConfiguration[] = [];
  for (const entry of raw) {
    if (typeof entry !== 'object' || entry === null || !('installationId' in entry) || typeof entry.installationId !== 'number' ||
        !('repositoryId' in entry) || typeof entry.repositoryId !== 'number' || !('store' in entry) || typeof entry.store !== 'string' ||
        !('repository' in entry) || typeof entry.repository !== 'string' || !('ref' in entry) || typeof entry.ref !== 'string' ||
        !entry.ref.startsWith('refs/heads/')) throw new Error('Invalid pilot configuration');
    const assistanceQuotaMicros = 'assistanceQuotaMicros' in entry ? entry.assistanceQuotaMicros : 0;
    if (typeof assistanceQuotaMicros !== 'number' || !Number.isSafeInteger(assistanceQuotaMicros) || assistanceQuotaMicros < 0) throw new Error('Invalid assistance quota');
    repositories.push({ installationId: entry.installationId, repositoryId: entry.repositoryId, store: entry.store, repository: entry.repository, ref: entry.ref, assistanceQuotaMicros });
  }
  pilotRepositories = repositories;
  const baselines = new ActiveBaselines(repositories);
  activeBaselines = baselines;
  runs = new RunStore(pool); await runs.initialize();
  forkPolicy = new ForkPolicy({ pool, selections: store, github, sessions, baselines });
  for (const repository of repositories) await forkPolicy.syncPolicy(repository, repository.assistanceQuotaMicros);
  const retentionDays = Number(process.env.PROOFCI_EVIDENCE_RETENTION_DAYS ?? '30');
  if (!Number.isInteger(retentionDays) || retentionDays < 1 || retentionDays > 3650) throw new Error('Invalid evidence retention');
  const endpoint = process.env.PROOFCI_S3_ENDPOINT;
  const s3 = new S3Client({ region: required('PROOFCI_S3_REGION'), endpoint, forcePathStyle: Boolean(endpoint) });
  const bucket = required('PROOFCI_S3_BUCKET');
  const versioning = await s3.send(new GetBucketVersioningCommand({ Bucket: bucket }));
  if (versioning.Status) throw new Error('Evidence bucket must not have versioning enabled or suspended');
  evidenceStore = new EvidenceStore(runs, s3, bucket, retentionDays * 86400);
  runService = new RunService({ store: runs, selections: store, github, baselines, repositories, evidence: evidenceStore, origin: origin.origin });
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
    const evidenceMatch = /^\/evidence\/([1-9]\d*)\/([1-9]\d*)\/([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})$/i.exec(url.pathname);
    if (request.method === 'GET' && evidenceMatch && evidenceStore) {
      const scope = { installationId: Number(evidenceMatch[1]), repositoryId: Number(evidenceMatch[2]) };
      if (!Number.isSafeInteger(scope.installationId) || !Number.isSafeInteger(scope.repositoryId)) return reply(response, 404, 'Not found.');
      const result = await downloadEvidence({ scope, runId: evidenceMatch[3], session: cookie(request, 'proofci_session'),
        sessions, github, selections: store, evidence: evidenceStore });
      if (result.kind === 'missing') return reply(response, 404, 'Not found.');
      if (result.kind === 'expired') return reply(response, 410, 'Evidence has expired. Historical property results remain unchanged.');
      response.writeHead(200, { 'content-type': 'application/x-tar', 'content-disposition': 'attachment; filename="proofci-evidence.tar"',
        'content-length': result.bytes.length, 'cache-control': 'no-store', 'x-content-type-options': 'nosniff', 'x-proofci-sha256': result.sha256 });
      return response.end(result.bytes);
    }
    if (request.method === 'GET' && url.pathname === '/') {
      const repositories = await sessions.listRepositories(cookie(request, 'proofci_session'), github);
      if (!repositories) return reply(response, 200, `${page}<p>Sign in to select a repository from an installed App.</p>`);
      if (repositories.length === 0) return reply(response, 200, `${page}<p>No repositories are available. Install the App on a repository you can maintain.</p><form method="post" action="/logout"><button>Sign out</button></form>`);
      const options = repositories.map(repo => `<option value="${repo.installationId}:${repo.repositoryId}">${escapeHtml(repo.name)}</option>`).join('');
      return reply(response, 200, `${page}<form method="post" action="/enroll"><label>Repository <select name="repository" required>${options}</select></label><button>Enroll repository</button><button formaction="/inspect">Check policy</button><button formaction="/remove">Remove enrollment</button></form><form method="post" action="/logout"><button>Sign out</button></form>`);
    }
    if (request.method === 'GET' && url.pathname === '/login') {
      const login = sessions.start();
      setCookie(response, 'proofci_login', login.binding, 300);
      response.writeHead(303, { location: login.url, 'cache-control': 'no-store', 'referrer-policy': 'no-referrer' }); return response.end();
    }
    const pullPath = /^\/pulls\/([1-9]\d*)\/([1-9]\d*)\/([1-9]\d*)$/.exec(url.pathname);
    if (request.method === 'GET' && pullPath && runs) {
      const scope = { installationId: Number(pullPath[1]), repositoryId: Number(pullPath[2]) }, number = Number(pullPath[3]);
      if (!Number.isSafeInteger(scope.installationId) || !Number.isSafeInteger(scope.repositoryId) || !Number.isSafeInteger(number) ||
          await sessions.checkMaintainer({ session: cookie(request, 'proofci_session'), scope, github }) === null || !await store.isSelected(scope)) return reply(response, 404, 'Not found.');
      const result = await runs.inspectPull(scope, number);
      if (!result) return reply(response, 404, 'Not found.');
      response.writeHead(200, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store', 'x-content-type-options': 'nosniff' });
      return response.end(JSON.stringify(result));
    }
    const runPath = /^\/runs\/([1-9]\d*)\/([1-9]\d*)\/([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})(\/evidence)?$/i.exec(url.pathname);
    if (request.method === 'GET' && runPath && runs) {
      const scope = { installationId: Number(runPath[1]), repositoryId: Number(runPath[2]) };
      if (!Number.isSafeInteger(scope.installationId) || !Number.isSafeInteger(scope.repositoryId) ||
          await sessions.checkMaintainer({ session: cookie(request, 'proofci_session'), scope, github }) === null ||
          !await store.isSelected(scope)) return reply(response, 404, 'Not found.');
      if (runPath[4]) {
        if (!evidenceStore) return reply(response, 404, 'Not found.');
        const result = await downloadEvidence({ scope, runId: runPath[3], session: cookie(request, 'proofci_session'), sessions, github, selections: store, evidence: evidenceStore });
        if (result.kind === 'missing') return reply(response, 404, 'Not found.');
        if (result.kind === 'expired') return reply(response, 410, 'Evidence has expired. Historical property results remain unchanged.');
        response.writeHead(200, { 'content-type': 'application/x-tar', 'content-disposition': 'attachment; filename="proofci-evidence.tar"', 'cache-control': 'no-store', 'x-content-type-options': 'nosniff', 'x-proofci-sha256': result.sha256 });
        return response.end(result.bytes);
      }
      const run = await runs.inspect(scope, runPath[3]);
      if (!run) return reply(response, 404, 'Not found.');
      response.writeHead(200, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store', 'x-content-type-options': 'nosniff' });
      return response.end(JSON.stringify(run));
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
        if (!await processPushEvent({ body, signature, event, deliveryId, secret, store: { acceptDelivery: delivery => {
          const config = pilotRepositories.find(item => item.installationId === delivery.installationId && item.repositoryId === delivery.repositoryId);
          return config ? runStore.acceptDelivery(delivery, config.ref === delivery.ref) : Promise.resolve(true);
        } } })) return reply(response, 401, 'Invalid or unauthorized webhook.');
      } else if (event === 'pull_request') {
        const runStore = runs;
        if (!runStore) return reply(response, 503, 'Run scheduling is not configured.');
        if (!await processPullEvent({ body, signature, event, deliveryId, secret, store: { acceptPullDelivery: delivery => pilotRepositories.some(item => item.installationId === delivery.installationId && item.repositoryId === delivery.repositoryId) ? runStore.acceptPullDelivery(delivery) : Promise.resolve(true) } })) return reply(response, 401, 'Invalid or unauthorized webhook.');

      } else if (!await processInstallationEvent({ body, signature, event, deliveryId, secret, store })) return reply(response, 401, 'Invalid webhook.');
      response.writeHead(204, { 'cache-control': 'no-store' }); return response.end();
    }
    if ((request.method === 'GET' || request.method === 'POST') && url.pathname === '/fork-assistance') {
      const runStore = runs, policy = forkPolicy, baselines = activeBaselines;
      if (!runStore || !policy || !baselines) return reply(response, 503, 'Run scheduling is not configured.');
      if (request.method === 'POST' && request.headers.origin !== origin.origin) return reply(response, 403, 'Request denied.');
      const data = request.method === 'POST' ? await form(request) : url.searchParams;
      const selection = data.get('repository') ?? '', numberText = data.get('number') ?? '';
      if (!/^[1-9]\d*:[1-9]\d*$/.test(selection) || !/^[1-9]\d*$/.test(numberText)) return reply(response, 400, 'Invalid selection.');
      const [installationId, repositoryId] = selection.split(':').map(Number), number = Number(numberText);
      if (![installationId, repositoryId, number].every(Number.isSafeInteger)) return reply(response, 400, 'Invalid selection.');
      const scope = { installationId, repositoryId }, session = cookie(request, 'proofci_session');
      const config = pilotRepositories.find(item => item.installationId === installationId && item.repositoryId === repositoryId);
      if (!config || await sessions.checkMaintainer({ session, scope, github }) === null || !await store.isSelected(scope)) return reply(response, 403, 'Request denied.');
      const run = await runStore.findPull(scope, number);
      if (request.method === 'POST' && data.get('action') === 'revoke') {
        if (!await policy.revoke({ session, scope, number })) return reply(response, 403, 'Request denied.');
        return reply(response, 200, 'Fork assistance approval revoked.');
      }
      if (!run || run.candidate.sourceRepositoryId === repositoryId) return reply(response, 404, 'No current fork run found.');
      const baseline = await baselines.activeIdentity(scope);
      if (!baseline || baseline.digest !== run.candidate.baseline || baseline.revision === null) return reply(response, 409, 'The active baseline is unavailable or needs revision tracking.');
      const digest = createHash('sha256').update(JSON.stringify([run.id, run.candidate, baseline.revision, policyDigest(config.assistanceQuotaMicros)])).digest('hex');
      if (request.method === 'POST') {
        if (data.get('action') !== 'approve' || data.get('digest') !== digest || data.get('consent') !== 'yes') return reply(response, 409, 'The candidate or policy changed, or consent was not given. Review it again.');
        if (!await policy.approve({ session, candidate: run.candidate, quotaMicros: config.assistanceQuotaMicros, baselineRevision: baseline.revision, consent: true })) return reply(response, 403, 'Approval denied or candidate changed.');
        return reply(response, 200, 'Approval recorded. Hosted assistance remains deferred until durable request recovery is enabled.');
      }
      const c = run.candidate;
      return reply(response, 200, `<h1>Fork assistance</h1><p>Source repository ID: ${c.sourceRepositoryId}. Destination repository ID: ${c.repositoryId}. Pull request: ${c.number}.</p><p>Head: ${c.head}<br>Base: ${c.base}<br>Baseline: ${c.baseline}<br>Baseline revision: ${baseline.revision}<br>Resource policy: ${policyDigest(config.assistanceQuotaMicros)}<br>Repository quota: ${config.assistanceQuotaMicros} microdollars.</p><p>Hosted assistance is deferred until durable request recovery is enabled.</p><form method="post"><input type="hidden" name="repository" value="${selection}"><input type="hidden" name="number" value="${number}"><input type="hidden" name="digest" value="${digest}"><label><input type="checkbox" name="consent" value="yes" required>Allow source transmission for these exact inputs</label><button name="action" value="approve">Approve</button><button name="action" value="revoke" formnovalidate>Revoke approval</button></form>`);
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
