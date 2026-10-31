import { createCipheriv, createDecipheriv, createHash, randomBytes } from 'node:crypto';
import type { RepositoryScope } from './enrollment-store.ts';

type Options = { clientId: string; clientSecret: string; redirectUri: string; request?: typeof fetch };
type Pending = { state: string; verifier: string; expires: number };
type Session = { token: string; expires: number };
type RepositoryListing = { listUserRepositories(token: string): Promise<Array<{ installationId: number; repositoryId: number; name: string }>> };
type MaintainerAccess = { checkMaintainerAccess(scope: RepositoryScope, token: string): Promise<number | null> };
const random = () => randomBytes(32).toString('base64url');

/** In-memory sessions expire on restart; tokens never leave the control process. */
export class OAuthSessions {
  private readonly options: Options;
  private readonly key = randomBytes(32);
  private readonly used = new Map<string, number>();
  private readonly inFlight = new Set<string>();
  private readonly sessions = new Map<string, Session>();

  constructor(options: Options) { this.options = options; }

  start(): { url: string; binding: string } {
    for (const [key, expires] of this.used) if (expires <= Date.now()) this.used.delete(key);
    for (const [key, value] of this.sessions) if (value.expires <= Date.now()) this.sessions.delete(key);
    const state = random(), verifier = random(), nonce = randomBytes(12);
    const cipher = createCipheriv('aes-256-gcm', this.key, nonce);
    const payload = Buffer.concat([cipher.update(JSON.stringify({ state, verifier, expires: Date.now() + 5 * 60_000 })), cipher.final()]);
    const binding = Buffer.concat([nonce, cipher.getAuthTag(), payload]).toString('base64url');
    const url = new URL('https://github.com/login/oauth/authorize');
    url.search = new URLSearchParams({ client_id: this.options.clientId, redirect_uri: this.options.redirectUri, state, code_challenge: createHash('sha256').update(verifier).digest('base64url'), code_challenge_method: 'S256', scope: 'offline_access' }).toString();
    return { url: url.toString(), binding };
  }

  private readBinding(binding: string): Pending | null {
    try {
      const raw = Buffer.from(binding, 'base64url');
      if (raw.length < 29 || raw.length > 1024) return null;
      const decipher = createDecipheriv('aes-256-gcm', this.key, raw.subarray(0, 12));
      decipher.setAuthTag(raw.subarray(12, 28));
      const value: unknown = JSON.parse(Buffer.concat([decipher.update(raw.subarray(28)), decipher.final()]).toString());
      if (typeof value !== 'object' || value === null || !('state' in value) || typeof value.state !== 'string' || !('verifier' in value) || typeof value.verifier !== 'string' || !('expires' in value) || typeof value.expires !== 'number') return null;
      return { state: value.state, verifier: value.verifier, expires: value.expires };
    } catch { return null; }
  }

  async finish(input: { state: string; binding: string; code: string }): Promise<string | null> {
    const pending = this.readBinding(input.binding);
    if (!pending || pending.state !== input.state || pending.expires <= Date.now() || !input.code || this.used.has(input.state) || this.inFlight.has(input.state) || this.sessions.size + this.inFlight.size >= 1000) return null;
    this.inFlight.add(input.state);
    try {
      const response = await (this.options.request ?? fetch)('https://github.com/login/oauth/access_token', {
        method: 'POST', headers: { accept: 'application/json', 'content-type': 'application/json' }, redirect: 'error', signal: AbortSignal.timeout(15_000),
        body: JSON.stringify({ client_id: this.options.clientId, client_secret: this.options.clientSecret, code: input.code, redirect_uri: this.options.redirectUri, code_verifier: pending.verifier }),
      });
      if (!response.ok) return null;
      const result: unknown = await response.json();
      if (typeof result !== 'object' || result === null || !('access_token' in result) || typeof result.access_token !== 'string' || !result.access_token) return null;
      this.used.set(input.state, pending.expires);
      const session = random();
      this.sessions.set(session, { token: result.access_token, expires: Date.now() + 30 * 60_000 });
      setTimeout(() => this.sessions.delete(session), 30 * 60_000).unref();
      return session;
    } catch { return null; } finally { this.inFlight.delete(input.state); }
  }

  async listRepositories(sessionId: string, github: RepositoryListing): Promise<Array<{ installationId: number; repositoryId: number; name: string }> | null> {
    const session = this.sessions.get(sessionId);
    if (!session || session.expires <= Date.now()) { this.sessions.delete(sessionId); return null; }
    try { return await github.listUserRepositories(session.token); } catch { return null; }
  }

  async checkMaintainer(input: { session: string; scope: RepositoryScope; github: MaintainerAccess }): Promise<number | null> {
    const session = this.sessions.get(input.session);
    if (!session || session.expires <= Date.now()) { this.sessions.delete(input.session); return null; }
    return input.github.checkMaintainerAccess(input.scope, session.token);
  }

  end(session: string): void { this.sessions.delete(session); }
}
