import { verifyWebhook } from './installation-events.ts';

/** A merge-group notification names a candidate; it is not trusted until resolved through GitHub. */
export type MergeGroupDelivery = { deliveryId: string; installationId: number; repositoryId: number; headRef: string; headSha: string; baseRef: string; baseSha: string };
export type MergeGroupRetirement = { installationId: number; repositoryId: number; headRef: string; headSha: string; reason: 'merged' | 'invalidated' | 'dequeued' };
type Store = { acceptMergeGroup(delivery: MergeGroupDelivery): Promise<boolean>; retireMergeGroup(retirement: MergeGroupRetirement): Promise<boolean> };

function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }
function id(value: unknown): value is number { return typeof value === 'number' && Number.isSafeInteger(value) && value > 0; }
const sha = (value: unknown): value is string => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
const branch = (value: unknown): value is string => typeof value === 'string' && value.startsWith('refs/heads/') && value.length > 'refs/heads/'.length && value.length <= 512 && !/[\x00-\x20\x7f~^:?*\[\\]/.test(value) && !value.includes('..');

/** GitHub names each group's temporary branch under the target branch. */
export function mergeGroupRef(headRef: string, baseRef: string): boolean {
  return branch(headRef) && branch(baseRef) && headRef.startsWith(`refs/heads/gh-readonly-queue/${baseRef.slice('refs/heads/'.length)}/`);
}

/**
 * `checks_requested` queues a group for resolution. `destroyed` retires the exact group
 * immediately so a late or replaced attempt cannot satisfy a later group on the same ref.
 */
export async function processMergeGroupEvent(input: { body: Buffer; signature: string; event: string; deliveryId: string; secret: string; store: Store }): Promise<boolean> {
  if (!verifyWebhook(input)) return false;
  if (input.event !== 'merge_group') return true;
  let value: unknown;
  try { value = JSON.parse(input.body.toString('utf8')); } catch { return false; }
  if (!object(value) || typeof value.action !== 'string' || !object(value.installation) || !id(value.installation.id) ||
      !object(value.repository) || !id(value.repository.id) || !object(value.merge_group)) return false;
  const group = value.merge_group;
  if (!sha(group.head_sha) || !sha(group.base_sha) || typeof group.head_ref !== 'string' || typeof group.base_ref !== 'string' || !mergeGroupRef(group.head_ref, group.base_ref)) return false;
  const scope = { installationId: value.installation.id, repositoryId: value.repository.id, headRef: group.head_ref, headSha: group.head_sha };
  if (value.action === 'checks_requested') return input.store.acceptMergeGroup({ ...scope, deliveryId: input.deliveryId, baseRef: group.base_ref, baseSha: group.base_sha });
  if (value.action === 'destroyed') {
    const reason = value.reason === 'merged' || value.reason === 'dequeued' ? value.reason : 'invalidated';
    return input.store.retireMergeGroup({ ...scope, reason });
  }
  return true;
}
