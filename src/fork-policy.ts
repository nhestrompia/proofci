import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import type { Pool } from 'pg';
import type { RepositoryScope } from './enrollment-store.ts';
import type { Candidate, Lease } from './run-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { OAuthSessions } from './oauth.ts';
import type { ActiveBaselines } from './active-baselines.ts';

type ForkCandidate = Extract<Candidate, { kind: 'pull-request' }>;
export type ForkDecision = RepositoryScope & { number: number; sourceRepositoryId: number; head: string; mergeHead: string; base: string; baseline: string; baselineRevision: number; selectionGeneration: string; policyDigest: string; quotaMicros: number; maintainerId: number; consent: boolean };

/** A decision is tied to the exact source, destination, policy, selection and budget. */
export function decisionMatches(approved: ForkDecision, current: ForkDecision, usedMicros: number): boolean {
  return approved.consent && current.consent && Number.isSafeInteger(usedMicros) && usedMicros >= 0 &&
    Number.isSafeInteger(approved.quotaMicros) && approved.quotaMicros > usedMicros && approved.quotaMicros === current.quotaMicros &&
    approved.installationId === current.installationId && approved.repositoryId === current.repositoryId && approved.number === current.number &&
    approved.sourceRepositoryId === current.sourceRepositoryId && approved.head === current.head && approved.mergeHead === current.mergeHead && approved.base === current.base &&
    approved.baseline === current.baseline && approved.baselineRevision === current.baselineRevision && approved.selectionGeneration === current.selectionGeneration && approved.policyDigest === current.policyDigest;
}

export function policyDigest(quotaMicros: number): string {
  const digest = createHash('sha256');
  for (const path of ['portable/resource_limits.json', 'portable/service_execute.py', 'portable/dispatch.py', 'portable/vm_container.py', 'portable/proofci.py', 'experiments/source-binding/core-dependencies.json', 'experiments/source-binding/evidence.py', 'experiments/source-binding/binding.py', 'experiments/source-binding/admission.py', 'experiments/source-binding/toolchain.py']) {
    digest.update(path).update('\0').update(readFileSync(new URL(`../${path}`, import.meta.url))).update('\0');
  }
  return digest.update(String(quotaMicros)).digest('hex');
}

/** Hosted provider calls stay disabled until durable request recovery is available. */
type Dependencies = { pool: Pool; selections: { readVersion(scope: RepositoryScope): Promise<string | null> }; github: Pick<GitHubApp, 'checkMaintainerAccess' | 'resolvePullRequest' | 'installationAccess'>; sessions: Pick<OAuthSessions, 'checkMaintainer'>; baselines: Pick<ActiveBaselines, 'activeIdentity'> };
export class ForkPolicy {
  private readonly options: Dependencies;
  constructor(options: Dependencies) { this.options = options; }

  async syncPolicy(scope: RepositoryScope, quotaMicros: number): Promise<void> {
    const client = await this.options.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-resource:${scope.installationId}:${scope.repositoryId}`]);
      const digest = policyDigest(quotaMicros);
      const existing = await client.query<{ digest: string }>('SELECT digest FROM proofci_fork_policies WHERE installation_id=$1 AND repository_id=$2', [scope.installationId, scope.repositoryId]);
      if (existing.rows[0]?.digest !== digest) {
        await client.query('DELETE FROM proofci_fork_decisions WHERE installation_id=$1 AND repository_id=$2', [scope.installationId, scope.repositoryId]);
        await client.query(`INSERT INTO proofci_fork_policies (installation_id, repository_id, digest) VALUES ($1,$2,$3)
          ON CONFLICT (installation_id, repository_id) DO UPDATE SET digest=EXCLUDED.digest, revision=proofci_fork_policies.revision+1`, [scope.installationId, scope.repositoryId, digest]);
      }
      await client.query('COMMIT');
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  private async current(candidate: ForkCandidate, quotaMicros: number): Promise<Omit<ForkDecision, 'maintainerId' | 'consent'> | null> {
    const { selections, github, baselines } = this.options;
    if (!Number.isSafeInteger(quotaMicros) || quotaMicros <= 0 || typeof candidate.mergeHead !== 'string' || !/^[a-f0-9]{40}$/.test(candidate.mergeHead)) return null;
    const selectionGeneration = await selections.readVersion(candidate);
    if (!selectionGeneration || await github.installationAccess(candidate) !== 'allowed') return null;
    const pr = await github.resolvePullRequest(candidate, candidate.number);
    const baseline = await baselines.activeIdentity(candidate);
    if (!pr || pr.sourceRepositoryId !== candidate.sourceRepositoryId || pr.destinationRepositoryId !== candidate.repositoryId || pr.head !== candidate.head || pr.base !== candidate.base || !baseline || baseline.digest !== candidate.baseline || baseline.revision === null || await selections.readVersion(candidate) !== selectionGeneration) return null;
    return { installationId: candidate.installationId, repositoryId: candidate.repositoryId, number: candidate.number, sourceRepositoryId: candidate.sourceRepositoryId, head: candidate.head, mergeHead: candidate.mergeHead, base: candidate.base, baseline: candidate.baseline, baselineRevision: baseline.revision, selectionGeneration, policyDigest: policyDigest(quotaMicros), quotaMicros };
  }

  async approve(input: { session: string; candidate: ForkCandidate; quotaMicros: number; baselineRevision: number; consent: boolean }): Promise<boolean> {
    if (!input.consent) return false;
    const { candidate } = input;
    const values = [candidate.installationId, candidate.repositoryId, candidate.number];
    const before = await this.options.pool.query<{ revision: string }>('SELECT revision FROM proofci_fork_policy_revisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', values);
    const policyBefore = await this.options.pool.query<{ revision: string }>('SELECT revision FROM proofci_fork_policies WHERE installation_id=$1 AND repository_id=$2', values.slice(0, 2));
    const maintainerId = await this.options.sessions.checkMaintainer({ session: input.session, scope: input.candidate, github: this.options.github });
    if (maintainerId === null) return false;
    const current = await this.current(input.candidate, input.quotaMicros);
    if (!current || current.baselineRevision !== input.baselineRevision) return false;
    const decision: ForkDecision = { ...current, maintainerId, consent: true };
    const client = await this.options.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-resource:${candidate.installationId}:${candidate.repositoryId}`]);
      await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-policy:${candidate.installationId}:${candidate.repositoryId}:${candidate.number}`]);
      const policyNow = await client.query<{ revision: string }>('SELECT revision FROM proofci_fork_policies WHERE installation_id=$1 AND repository_id=$2', values.slice(0, 2));
      const now = await client.query<{ revision: string }>('SELECT revision FROM proofci_fork_policy_revisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', values);
      if (!policyBefore.rows[0] || policyBefore.rows[0].revision !== policyNow.rows[0]?.revision || (before.rows[0]?.revision ?? '0') !== (now.rows[0]?.revision ?? '0')) { await client.query('ROLLBACK'); return false; }
      const result = await client.query(`INSERT INTO proofci_fork_decisions (installation_id, repository_id, pull_number, decision)
        SELECT $1,$2,$3,$4::jsonb FROM proofci_repository_selections s WHERE s.installation_id=$1 AND s.repository_id=$2 AND s.generation=$5
        AND EXISTS (SELECT 1 FROM proofci_fork_policies p WHERE p.installation_id=$1 AND p.repository_id=$2 AND p.digest=$10)
        AND EXISTS (SELECT 1 FROM proofci_runs r WHERE r.installation_id=$1 AND r.repository_id=$2 AND r.pull_number=$3 AND r.kind='pull-request' AND r.applicable AND r.state <> 'cancelled' AND r.source_repository_id=$6 AND r.head=$7 AND r.base=$8 AND r.baseline=$9 AND r.merge_head=$11)
        ON CONFLICT (installation_id, repository_id, pull_number) DO UPDATE SET decision=EXCLUDED.decision, created_at=clock_timestamp() RETURNING pull_number`,
        [decision.installationId, decision.repositoryId, decision.number, JSON.stringify(decision), decision.selectionGeneration, decision.sourceRepositoryId, decision.head, decision.base, decision.baseline, decision.policyDigest, decision.mergeHead]);
      await client.query('COMMIT');
      return result.rowCount === 1;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  async revoke(input: { session: string; scope: RepositoryScope; number: number }): Promise<boolean> {
    const maintainer = await this.options.sessions.checkMaintainer({ session: input.session, scope: input.scope, github: this.options.github });
    if (maintainer === null) return false;
    const client = await this.options.pool.connect();
    try {
      await client.query('BEGIN');
      await client.query('SELECT pg_advisory_xact_lock(hashtextextended($1, 0))', [`fork-policy:${input.scope.installationId}:${input.scope.repositoryId}:${input.number}`]);
      const values = [input.scope.installationId, input.scope.repositoryId, input.number];
      await client.query(`INSERT INTO proofci_fork_policy_revisions (installation_id, repository_id, pull_number, revision) VALUES ($1,$2,$3,1)
        ON CONFLICT (installation_id, repository_id, pull_number) DO UPDATE SET revision=proofci_fork_policy_revisions.revision+1`, values);
      await client.query('DELETE FROM proofci_fork_decisions WHERE installation_id=$1 AND repository_id=$2 AND pull_number=$3', values);
      await client.query('COMMIT');
      return true;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally { client.release(); }
  }

  async requestStatus(lease: Lease & { candidate: ForkCandidate }, quotaMicros: number, usedMicros: number): Promise<'denied' | 'deferred'> {
    const { candidate } = lease;
    const current = await this.current(candidate, quotaMicros);
    if (!current) return 'denied';
    const result = await this.options.pool.query<{ decision: ForkDecision }>(`SELECT d.decision FROM proofci_fork_decisions d JOIN proofci_runs r ON
      r.installation_id=d.installation_id AND r.repository_id=d.repository_id AND r.pull_number=d.pull_number
      WHERE r.id=$1 AND r.generation=$2 AND r.state='running' AND r.applicable AND r.lease_until > clock_timestamp()
      AND r.selection_generation=$3 AND r.source_repository_id=$4 AND r.head=$5 AND r.base=$6 AND r.baseline=$7 AND r.merge_head=$9
      AND EXISTS (SELECT 1 FROM proofci_fork_policies p WHERE p.installation_id=r.installation_id AND p.repository_id=r.repository_id AND p.digest=$8)`,
    [lease.id, lease.generation, current.selectionGeneration, candidate.sourceRepositoryId, candidate.head, candidate.base, candidate.baseline, current.policyDigest, candidate.mergeHead]);
    const approved = result.rows[0]?.decision;
    if (!approved || !decisionMatches(approved, { ...current, maintainerId: approved.maintainerId, consent: true }, usedMicros)) return 'denied';
    return 'deferred';
  }
}
