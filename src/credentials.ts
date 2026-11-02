import { createHmac, timingSafeEqual } from 'node:crypto';
import { lstatSync, readFileSync } from 'node:fs';
import { isAbsolute } from 'node:path';

/**
 * Control-process credentials. A `NAME_FILE` setting takes precedence over `NAME`.
 * Credential files must be absolute, regular, and not writable by group or other users.
 * Candidate workers never receive these values: isolated dispatch builds its own environment.
 */
export function readCredentialFile(path: string): string {
  if (!isAbsolute(path)) throw new Error('Credential file path must be absolute');
  const stat = lstatSync(path);
  if (!stat.isFile() || stat.isSymbolicLink() || (stat.mode & 0o022) !== 0 || stat.size > 65536) throw new Error(`Invalid credential file: ${path}`);
  return readFileSync(path, 'utf8');
}

export function credential(env: NodeJS.ProcessEnv, name: string): string | undefined {
  const file = env[`${name}_FILE`];
  if (file) {
    const value = readCredentialFile(file).trim();
    if (!value) throw new Error(`Empty credential file for ${name}`);
    return value;
  }
  return env[name] || undefined;
}

export function requiredCredential(env: NodeJS.ProcessEnv, name: string): string {
  const value = credential(env, name);
  if (!value) throw new Error(`Missing configuration: ${name} or ${name}_FILE`);
  return value;
}

/** Path-based private key settings remain the only supported form for the App key. */
export function privateKeyPath(env: NodeJS.ProcessEnv): string {
  const path = env.GITHUB_PRIVATE_KEY_FILE;
  if (!path) throw new Error('Missing configuration: GITHUB_PRIVATE_KEY_FILE');
  return path;
}

/**
 * Webhook secrets support rotation without a restart. The first non-empty line of
 * `GITHUB_WEBHOOK_SECRET_FILE` is current; one optional second line is the previous
 * secret, accepted only until the operator removes it. The file is reread when it changes.
 */
export class WebhookSecrets {
  private readonly env: NodeJS.ProcessEnv;
  private cached: { key: string; secrets: string[] } | null = null;
  constructor(env: NodeJS.ProcessEnv) { this.env = env; }

  current(): string[] {
    const file = this.env.GITHUB_WEBHOOK_SECRET_FILE;
    if (!file) return this.env.GITHUB_WEBHOOK_SECRET ? [this.env.GITHUB_WEBHOOK_SECRET] : [];
    const stat = lstatSync(file);
    const key = `${stat.ino}:${stat.size}:${stat.mtimeMs}:${stat.ctimeMs}`;
    if (this.cached?.key === key) return this.cached.secrets;
    const secrets = parseWebhookSecrets(readCredentialFile(file));
    this.cached = { key, secrets };
    return secrets;
  }

  /** Return the configured secret that signed this body, or null. */
  match(body: Buffer, signature: string): string | null {
    if (!/^sha256=[a-f0-9]{64}$/.test(signature)) return null;
    const received = Buffer.from(signature.slice(7), 'hex');
    let matched: string | null = null;
    // Compare against every configured secret so timing does not reveal which one matched.
    for (const secret of this.current()) {
      if (timingSafeEqual(received, createHmac('sha256', secret).update(body).digest()) && matched === null) matched = secret;
    }
    return matched;
  }
}

export function parseWebhookSecrets(text: string): string[] {
  const secrets = text.split('\n').map(line => line.replace(/\r$/, '')).filter(line => line.length > 0);
  if (secrets.length < 1 || secrets.length > 2) throw new Error('Webhook secret file must contain the current secret and at most one previous secret');
  if (secrets.some(secret => secret.length < 20 || secret.length > 512 || /\s/.test(secret))) throw new Error('Webhook secrets must be 20 to 512 characters without whitespace');
  if (secrets.length === 2 && secrets[0] === secrets[1]) throw new Error('Webhook secret file repeats a secret');
  return secrets;
}
