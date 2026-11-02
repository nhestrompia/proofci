import type { RepositoryScope } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { Candidate, MergeGroupLease } from './run-store.ts';

/** Reasons a notified merge group cannot be verified. Each one publishes a blocking check. */
export type MergeGroupUnavailable = 'merge_group_ref_missing' | 'merge_group_ref_mismatch' | 'merge_group_parents_mismatch' | 'merge_group_target_unprotected' | 'baseline_unavailable';

/**
 * Resolve the exact group commit and the trusted baseline for the protected target.
 * A PR result is never consulted: the group commit is verified on its own.
 */
export async function resolveMergeGroupDelivery(options: {
  delivery: MergeGroupLease;
  protectedRef: string | null;
  selections: { readVersion(scope: RepositoryScope): Promise<string | null>; removeIfVersion(scope: RepositoryScope, version: string): Promise<void> };
  github: Pick<GitHubApp, 'installationAccess' | 'resolveMergeGroup'>;
  baselines: { active(scope: RepositoryScope): Promise<string | null> };
}): Promise<Candidate | { unavailable: MergeGroupUnavailable } | null> {
  const { delivery, selections, github, baselines } = options;
  const scope = { installationId: delivery.installationId, repositoryId: delivery.repositoryId };
  if (await selections.readVersion(scope) !== delivery.selectionGeneration) return null;
  const access = await github.installationAccess(scope);
  if (access === 'revoked') { await selections.removeIfVersion(scope, delivery.selectionGeneration); return null; }
  if (access === 'unavailable') throw new Error('GitHub access unavailable');
  // The active baseline protects one configured branch; another target has no trusted contract.
  if (delivery.baseRef !== options.protectedRef) return { unavailable: 'merge_group_target_unprotected' };
  const group = await github.resolveMergeGroup(scope, { headRef: delivery.headRef, headSha: delivery.headSha, baseSha: delivery.baseSha });
  if (group.kind !== 'resolved') return { unavailable: group.reason };
  const baseline = await baselines.active(scope);
  if (!baseline) return { unavailable: 'baseline_unavailable' };
  return { ...scope, kind: 'merge-group', lane: delivery.headRef, head: group.head, base: group.base, mergeHead: group.head, baseline };
}
