import { verifyWebhook } from './installation-events.ts';

export type PullDelivery = { deliveryId: string; installationId: number; repositoryId: number; number: number };
function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }
function id(value: unknown): value is number { return typeof value === 'number' && Number.isSafeInteger(value) && value > 0; }

/** Verify and persist an observation; the current PR is resolved by the delivery worker. */
export async function processPullEvent(input: { body: Buffer; signature: string; deliveryId: string; secret: string; store: { acceptPullDelivery(event: PullDelivery): Promise<boolean> } }): Promise<boolean> {
  if (!verifyWebhook(input)) return false;
  let value: unknown;
  try { value = JSON.parse(input.body.toString('utf8')); } catch { return false; }
  if (!object(value) || typeof value.action !== 'string' || !object(value.installation) || !id(value.installation.id) ||
      !object(value.repository) || !id(value.repository.id) || !id(value.number)) return false;
  if (!['opened', 'reopened', 'synchronize', 'edited', 'closed'].includes(value.action)) return true;
  return input.store.acceptPullDelivery({ deliveryId: input.deliveryId, installationId: value.installation.id, repositoryId: value.repository.id, number: value.number });
}
