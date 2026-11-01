import { verifyWebhook } from './installation-events.ts';

export type PushDelivery = { deliveryId: string; installationId: number; repositoryId: number; ref: string; head: string; deleted: boolean };
type Store = { acceptDelivery(event: PushDelivery): Promise<boolean> };
function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }
function id(value: unknown): value is number { return typeof value === 'number' && Number.isSafeInteger(value) && value > 0; }

export async function processPushEvent(input: { body: Buffer; signature: string; event: string; deliveryId: string; secret: string; store: Store }): Promise<boolean> {
  if (!verifyWebhook(input)) return false;
  if (input.event !== 'push') return true;
  let value: unknown;
  try { value = JSON.parse(input.body.toString('utf8')); } catch { return false; }
  if (!object(value) || !object(value.installation) || !id(value.installation.id) || !object(value.repository) || !id(value.repository.id) ||
      typeof value.ref !== 'string' || !value.ref.startsWith('refs/heads/') || value.ref.length > 512 ||
      typeof value.after !== 'string' || !/^[a-f0-9]{40}$/.test(value.after) || typeof value.deleted !== 'boolean' ||
      (value.deleted ? value.after !== '0'.repeat(40) : value.after === '0'.repeat(40))) return false;
  return input.store.acceptDelivery({ deliveryId: input.deliveryId, installationId: value.installation.id, repositoryId: value.repository.id, ref: value.ref, head: value.after, deleted: value.deleted });
}
