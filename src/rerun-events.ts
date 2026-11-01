import { verifyWebhook } from './installation-events.ts';

/** A rerun names an actor and an existing check; neither is trusted until processing. */
export type RerunRequest = { deliveryId: string; installationId: number; repositoryId: number; actorId: number; actorLogin: string; sha: string; runId: string | null };
function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }
function id(value: unknown): value is number { return typeof value === 'number' && Number.isSafeInteger(value) && value > 0; }
const sha = (value: unknown): value is string => typeof value === 'string' && /^[a-f0-9]{40}$/.test(value);
const uuid = (value: unknown): value is string => typeof value === 'string' && /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/.test(value);

/**
 * Accept `check_run` and `check_suite` rerun requests for this App's own checks.
 * Repository authority is verified later, against GitHub's current permissions.
 */
export async function processRerunEvent(input: { body: Buffer; signature: string; event: string; deliveryId: string; secret: string; appId: number; store: { acceptRerun(request: RerunRequest): Promise<boolean> } }): Promise<boolean> {
  if (!verifyWebhook(input)) return false;
  if (input.event !== 'check_run' && input.event !== 'check_suite') return true;
  let value: unknown;
  try { value = JSON.parse(input.body.toString('utf8')); } catch { return false; }
  if (!object(value) || typeof value.action !== 'string' || !object(value.installation) || !id(value.installation.id) ||
      !object(value.repository) || !id(value.repository.id) || !object(value.sender) || !id(value.sender.id) ||
      typeof value.sender.login !== 'string' || !/^[A-Za-z0-9-]{1,39}(\[bot\])?$/.test(value.sender.login)) return false;
  if (value.action !== 'rerequested') return true;
  const target = input.event === 'check_run' ? value.check_run : value.check_suite;
  if (!object(target) || !object(target.app) || target.app.id !== input.appId || !sha(target.head_sha)) return true;
  const runId = input.event === 'check_run' ? target.external_id : null;
  if (input.event === 'check_run' && !uuid(runId)) return true;
  await input.store.acceptRerun({ deliveryId: input.deliveryId, installationId: value.installation.id, repositoryId: value.repository.id,
    actorId: value.sender.id, actorLogin: value.sender.login, sha: target.head_sha, runId: runId as string | null });
  return true;
}
