import { createHmac, timingSafeEqual } from 'node:crypto';

type Store = { removeRepositories(installationId: number, repositoryIds: number[], deliveryId: string): Promise<void>; removeInstallation(installationId: number, deliveryId: string): Promise<void> };
function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }
function id(value: unknown): value is number { return typeof value === 'number' && Number.isSafeInteger(value) && value > 0; }

export function verifyWebhook(input: { body: Buffer; signature: string; deliveryId: string; secret: string }): boolean {
  if (!/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(input.deliveryId) || !input.secret || !/^sha256=[a-f0-9]{64}$/.test(input.signature)) return false;
  const received = Buffer.from(input.signature.slice(7), 'hex');
  const expected = createHmac('sha256', input.secret).update(input.body).digest();
  return timingSafeEqual(received, expected);
}

/** Verify GitHub's signature before invalidating any selections. */
export async function processInstallationEvent(input: { body: Buffer; signature: string; event: string; deliveryId: string; secret: string; store: Store }): Promise<boolean> {
  if (!verifyWebhook(input)) return false;
  if (input.event !== 'installation' && input.event !== 'installation_repositories') return true;
  let value: unknown;
  try { value = JSON.parse(input.body.toString('utf8')); } catch { return false; }
  if (!object(value) || typeof value.action !== 'string' || !object(value.installation) || !id(value.installation.id)) return false;
  const installationId = value.installation.id;
  if (input.event === 'installation' && (value.action === 'deleted' || value.action === 'suspend')) {
    await input.store.removeInstallation(installationId, input.deliveryId);
  } else if (input.event === 'installation_repositories' && value.action === 'removed') {
    if (!Array.isArray(value.repositories_removed) || !value.repositories_removed.every(repo => object(repo) && id(repo.id))) return false;
    const repositoryIds: number[] = [];
    for (const repo of value.repositories_removed) { if (object(repo) && id(repo.id)) repositoryIds.push(repo.id); }
    await input.store.removeRepositories(installationId, repositoryIds, input.deliveryId);
  }
  return true;
}
