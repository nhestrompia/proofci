import type { RepositoryScope } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { Candidate, PullLease } from './run-store.ts';

export async function resolvePullDelivery(options: {
  delivery: PullLease;
  selections: { readVersion(scope: RepositoryScope): Promise<string | null>; removeIfVersion(scope: RepositoryScope, version: string): Promise<void> };
  github: Pick<GitHubApp, 'installationAccess' | 'resolvePullRequest' | 'resolvePullMerge'> & Partial<Pick<GitHubApp, 'rerunAuthority'>>;
  baselines: { active(scope: RepositoryScope): Promise<string | null> };
}): Promise<Candidate | 'closed' | 'baseline-unavailable' | 'merge-conflict' | 'merge-unavailable' | 'rerun-denied' | null> {
  const { delivery, selections, github, baselines } = options;
  const scope = { installationId: delivery.installationId, repositoryId: delivery.repositoryId };
  if (await selections.readVersion(scope) !== delivery.selectionGeneration) return null;
  const access = await github.installationAccess(scope);
  if (access === 'revoked') { await selections.removeIfVersion(scope, delivery.selectionGeneration); return null; }
  if (access === 'unavailable') throw new Error('GitHub access unavailable');
  // A rerun cannot start work until the actor's current repository authority is confirmed.
  if (delivery.rerunActor && (!github.rerunAuthority || await github.rerunAuthority(scope, delivery.rerunActor) !== 'allowed')) return 'rerun-denied';
  const pr = await github.resolvePullRequest(scope, delivery.number);
  if (!pr) return 'closed';
  const merge = await github.resolvePullMerge(scope, delivery.number);
  if (merge.kind !== 'resolved') return merge.reason === 'merge_conflict' ? 'merge-conflict' : 'merge-unavailable';
  if (merge.head !== pr.head || merge.base !== pr.base) return 'merge-unavailable';
  const baseline = await baselines.active(scope);
  if (!baseline) return 'baseline-unavailable';
  return { ...scope, kind: 'pull-request', lane: `pull/${pr.number}`, number: pr.number, sourceRepositoryId: pr.sourceRepositoryId, head: pr.head, base: pr.base, mergeHead: merge.merge, baseline };
}
