import { mkdtemp, rm, open } from 'node:fs/promises';
import { constants } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import type { ActiveBaselines } from './active-baselines.ts';
import type { GitHubApp } from './github-app.ts';
import type { Candidate } from './run-store.ts';
import { isolatedDispatch } from './isolated-dispatch.ts';
import { RunFailure } from './run-failure.ts';

/** Prepare a fresh snapshot and use the protected baseline and verifier. */
export async function executeRun(options: { candidate: Candidate; signal: AbortSignal; github: Pick<GitHubApp, 'stageSnapshot' | 'resolveHead'> & Partial<Pick<GitHubApp, 'resolvePullRequest' | 'resolvePullMerge'>>; baselines: ActiveBaselines; ensureActive?: () => Promise<boolean>; dispatch?: (start: () => Promise<Record<string, unknown>>) => Promise<Record<string, unknown>> }): Promise<{ report: Record<string, unknown>; evidence: Buffer | null }> {
  const { candidate, signal, github, baselines } = options;
  const checkCurrent = async () => {
    if (signal.aborted || (options.ensureActive && !await options.ensureActive())) throw new RunFailure('cancelled');
    if (candidate.kind === 'head-snapshot' && await github.resolveHead(candidate, candidate.lane) !== candidate.head) throw new RunFailure('candidate_superseded');
    if (candidate.kind === 'pull-request') {
      const pr = await github.resolvePullRequest?.(candidate, candidate.number);
      const merge = await github.resolvePullMerge?.(candidate, candidate.number);
      if (!merge || merge.kind !== 'resolved' || merge.merge !== candidate.mergeHead || merge.head !== candidate.head || merge.base !== candidate.base) throw new RunFailure('candidate_superseded');
      if (!pr || pr.sourceRepositoryId !== candidate.sourceRepositoryId || pr.destinationRepositoryId !== candidate.repositoryId || pr.head !== candidate.head || pr.base !== candidate.base) throw new RunFailure('candidate_superseded');
    }
    if (await baselines.active(candidate) !== candidate.baseline) throw new RunFailure('baseline_unavailable');
    if (signal.aborted || (options.ensureActive && !await options.ensureActive())) throw new RunFailure('cancelled');
  };
  const config = baselines.configuration(candidate);
  if (!config || await baselines.active(candidate) !== candidate.baseline) throw new RunFailure('baseline_unavailable');
  await checkCurrent();
  const root = await mkdtemp(join(tmpdir(), 'proofci-run-'));
  try {
    const verifiedHead = candidate.kind === 'pull-request' ? candidate.mergeHead : candidate.head;
    if (!verifiedHead) throw new RunFailure('candidate_superseded');
    const staged = await github.stageSnapshot(candidate, { head: verifiedHead, base: candidate.base, root, signal });
    if (staged.repository !== config.repository) throw new RunFailure('repository_identity_mismatch');
    await checkCurrent();
    const bundle = join(root, 'evidence.tar');
    const start = () => isolatedDispatch({ ...candidate, head: verifiedHead }, { store: config.store, repository: config.repository, snapshot: staged.snapshot, report: join(root, 'report.json'), bundle }, signal);
    const result = await (options.dispatch ? options.dispatch(start) : start());
    if (signal.aborted) throw new RunFailure('cancelled');
    if (result.status !== 'error' && candidate.authorityEpoch !== undefined && result.authority_epoch !== candidate.authorityEpoch) throw new RunFailure('candidate_superseded');
    await checkCurrent();
    let evidence: Buffer | null = null;
    if (result.status !== 'error') {
      const file = await open(bundle, constants.O_RDONLY | constants.O_NOFOLLOW);
      try {
        const stat = await file.stat();
        if (!stat.isFile() || stat.size < 1 || stat.size > 256 * 1024 * 1024) throw new Error('Invalid evidence bundle');
        evidence = await file.readFile();
        if (evidence.length !== stat.size) throw new Error('Evidence bundle changed during read');
      } finally { await file.close(); }
    }
    return { report: result, evidence };
  } finally { await rm(root, { recursive: true, force: true }); }
}
