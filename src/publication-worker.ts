import { createHash } from 'node:crypto';
import { checkReport, truncateText } from './check-report.ts';
import type { ActiveBaselines } from './active-baselines.ts';
import type { GitHubApp } from './github-app.ts';
import type { RunStore } from './run-store.ts';

function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }

/** Publish one durable outbox entry without dispatching verification again. */
export async function publishNext(options: { store: Pick<RunStore, 'claimPublication' | 'publicationCurrent' | 'ownsPublication' | 'markPublicationUnresolved' | 'finishPublication' | 'retryPublication' | 'withPublicationLock'>; github: Pick<GitHubApp, 'resolvePullMerge' | 'publishCheck' | 'invalidateCheck'>; baselines: Pick<ActiveBaselines, 'active'>; origin: string }): Promise<boolean> {
  const item = await options.store.claimPublication(300_000);
  if (!item) return false;
  const number = Number(item.candidate.lane.slice('pull/'.length));
  const scope = { installationId: item.candidate.installationId, repositoryId: item.candidate.repositoryId };
  if (!Number.isSafeInteger(number) || number < 1) throw new Error('Invalid pull request lane');
  const mergeHead = item.candidate.kind === 'pull-request' ? item.candidate.mergeHead : item.candidate.head;
  const pullHead = item.candidate.kind === 'pull-request' ? item.candidate.head : item.candidate.pullHead;
  if (!mergeHead) throw new Error('Missing merge commit');
  let currentHead: string | null = null;
  const fresh = async () => {
    if (!await options.store.publicationCurrent(item)) return false;
    const merge = await options.github.resolvePullMerge(scope, number);
    if (merge.kind !== 'resolved' || merge.merge !== mergeHead || merge.head !== pullHead || merge.base !== item.candidate.base || await options.baselines.active(scope) !== item.candidate.baseline) return false;
    currentHead = merge.head;
    return await options.store.publicationCurrent(item);
  };
  try {
    await options.store.withPublicationLock(item.id, async () => {
      if (!await options.store.ownsPublication(item)) return;
      if (!await fresh()) {
        await options.store.markPublicationUnresolved(item);
        await options.github.invalidateCheck(scope, { runId: item.id, sha: mergeHead });
        await options.store.finishPublication(item);
        return;
      }
      const report = item.report;
      const output = (item.state === 'completed' || item.state === 'failed') ? checkReport({ ...item.candidate, head: mergeHead }, report, item.evidenceSha256) : item.state === 'cancelled' ? { title: 'ProofCI cancelled', summary: 'Verification was cancelled.', conclusion: 'failure' as const } : null;
      if (output) output.summary = `Pull request head: ${currentHead}\n${output.summary}`;
      const annotations: Array<{ path: string; start_line: number; end_line: number; annotation_level: 'notice' | 'failure'; message: string }> = [];
      if (object(report) && object(report.support) && typeof report.support.admitted_candidate === 'string' && Array.isArray(report.results)) {
        const path = report.support.admitted_candidate;
        if (!path.startsWith('/') && !path.split('/').some(part => !part || part === '.' || part === '..') && !/[\x00-\x1f\x7f\\]/.test(path)) {
          report.results.forEach((result, index) => {
            if (!object(result) || typeof result.id !== 'string' || typeof result.reason !== 'string' || typeof result.decision !== 'string') return;
            const marker = createHash('sha256').update(`${item.id}:${index}:${result.id}`).digest('hex').slice(0, 16);
            annotations.push({ path, start_line: 1, end_line: 1, annotation_level: result.decision === 'verified' ? 'notice' : 'failure', message: truncateText(`${result.id}: ${result.decision} — ${result.reason}`, 60000) + `\n[ProofCI ${marker}]` });
          });
        }
      }
      const detailsUrl = new URL(`/runs/${scope.installationId}/${scope.repositoryId}/${item.id}`, options.origin).toString();
      await options.github.publishCheck(scope, { runId: item.id, sha: mergeHead, detailsUrl, output, annotations, fresh });
      await options.store.finishPublication(item);
    });
    return true;
  } finally { await options.store.retryPublication(item); }
}
