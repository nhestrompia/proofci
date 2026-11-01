import { verifyWebhook } from './installation-events.ts';

export type PullDelivery = { deliveryId: string; installationId: number; repositoryId: number; number: number };
function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }
function id(value: unknown): value is number { return typeof value === 'number' && Number.isSafeInteger(value) && value > 0; }

/**
 * How a pull request action affects existing runs. Actions that can change the
 * candidate (head, target branch, or open state) supersede queued and running work
 * immediately. Readiness changes only re-resolve, so an unchanged candidate keeps its run.
 */
export function pullAction(action: string, changes: unknown): 'invalidate' | 'resolve' | 'ignore' {
  if (['opened', 'reopened', 'synchronize', 'closed'].includes(action)) return 'invalidate';
  if (action === 'edited') return object(changes) && object(changes.base) ? 'invalidate' : 'ignore';
  if (action === 'ready_for_review' || action === 'converted_to_draft') return 'resolve';
  return 'ignore';
}

/** The payload identifies work to resolve, not an authorization or candidate. */
export async function processPullEvent(input: { body: Buffer; signature: string; event: string; deliveryId: string; secret: string; store: { acceptPullDelivery(delivery: PullDelivery, invalidate: boolean): Promise<boolean> } }): Promise<boolean> {
  if (!verifyWebhook(input)) return false;
  if (input.event !== 'pull_request') return true;
  let value: unknown;
  try { value = JSON.parse(input.body.toString('utf8')); } catch { return false; }
  if (!object(value) || typeof value.action !== 'string' || !id(value.number) || !object(value.installation) || !id(value.installation.id) ||
      !object(value.repository) || !id(value.repository.id) || !object(value.pull_request) || value.pull_request.number !== value.number ||
      !object(value.pull_request.base) || !object(value.pull_request.base.repo) || value.pull_request.base.repo.id !== value.repository.id) return false;
  const effect = pullAction(value.action, value.changes);
  if (effect === 'ignore') return true;
  return input.store.acceptPullDelivery({ deliveryId: input.deliveryId, installationId: value.installation.id, repositoryId: value.repository.id, number: value.number }, effect === 'invalidate');
}
