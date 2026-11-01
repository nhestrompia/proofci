import type { RepositoryScope } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { Candidate, DeliveryLease } from './run-store.ts';

type Options = {
  delivery: DeliveryLease;
  selections: { readVersion(scope: RepositoryScope): Promise<string | null>; removeIfVersion(scope: RepositoryScope, version: string): Promise<void> };
  github: Pick<GitHubApp, 'installationAccess' | 'resolveHead'>;
  baselines: { active(scope: RepositoryScope): Promise<string | null> };
};

/** Resolve a nonenforcing branch-head snapshot; unavailable providers are retried. */
export async function resolveDelivery({ delivery, selections, github, baselines }: Options): Promise<Candidate | 'deleted' | null> {
  const scope = { installationId: delivery.installationId, repositoryId: delivery.repositoryId };
  if (await selections.readVersion(scope) !== delivery.selectionGeneration) return null;
  const access = await github.installationAccess(scope);
  if (access === 'revoked') { await selections.removeIfVersion(scope, delivery.selectionGeneration); return null; }
  if (access === 'unavailable') throw new Error('GitHub access unavailable');
  const head = await github.resolveHead(scope, delivery.ref);
  if (delivery.deleted) return head === null ? 'deleted' : null;
  if (head !== delivery.head) return null;
  const baseline = await baselines.active(scope);
  if (baseline === null) return null;
  return { ...scope, kind: 'head-snapshot', lane: delivery.ref, head, base: head, baseline };
}

/** Queue a fresh observation; processing re-resolves it before admission. */
export async function reconcileHead(options: {
  scope: RepositoryScope;
  ref: string;
  github: Pick<GitHubApp, 'resolveHead'>;
  store: { acceptDelivery(delivery: import('./push-events.ts').PushDelivery): Promise<boolean> };
}): Promise<boolean> {
  const { randomUUID } = await import('node:crypto');
  const head = await options.github.resolveHead(options.scope, options.ref);
  return options.store.acceptDelivery({ ...options.scope, ref: options.ref, head: head ?? '0'.repeat(40), deleted: head === null, deliveryId: randomUUID() });
}
