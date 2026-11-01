import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import type { ActiveBaselines } from './active-baselines.ts';
import type { GitHubApp } from './github-app.ts';
import type { Candidate } from './run-store.ts';
import { isolatedDispatch } from './isolated-dispatch.ts';
import { RunFailure } from './run-failure.ts';

/** Prepare a fresh snapshot and use the protected baseline and verifier. */
export async function executeRun(options: { candidate: Candidate; signal: AbortSignal; github: Pick<GitHubApp, 'stageSnapshot' | 'resolveHead'>; baselines: ActiveBaselines }): Promise<Record<string, unknown>> {
  const { candidate, signal, github, baselines } = options;
  const config = baselines.configuration(candidate);
  if (!config || await baselines.active(candidate) !== candidate.baseline) throw new RunFailure('baseline_unavailable');
  if (candidate.kind === 'head-snapshot' && await github.resolveHead(candidate, candidate.lane) !== candidate.head) throw new RunFailure('candidate_superseded');
  const root = await mkdtemp(join(tmpdir(), 'proofci-run-'));
  try {
    const staged = await github.stageSnapshot(candidate, { head: candidate.head, base: candidate.base, root, signal });
    if (staged.repository !== config.repository) throw new RunFailure('repository_identity_mismatch');
    if (candidate.kind === 'head-snapshot' && await github.resolveHead(candidate, candidate.lane) !== candidate.head) throw new RunFailure('candidate_superseded');
    const result = await isolatedDispatch(candidate, { store: config.store, repository: config.repository, snapshot: staged.snapshot, report: join(root, 'report.json') }, signal);
    if (signal.aborted) throw new RunFailure('cancelled');
    if (result.status !== 'error' && candidate.authorityEpoch !== undefined && result.authority_epoch !== candidate.authorityEpoch) throw new RunFailure('candidate_superseded');
    if (candidate.kind === 'head-snapshot' && await github.resolveHead(candidate, candidate.lane) !== candidate.head) throw new RunFailure('candidate_superseded');
    if (await baselines.active(candidate) !== candidate.baseline) throw new RunFailure('baseline_unavailable');
    return result;
  } finally { await rm(root, { recursive: true, force: true }); }
}
