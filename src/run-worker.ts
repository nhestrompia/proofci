import type { Candidate, Lease, RunStore } from './run-store.ts';
import { RunFailure } from './run-failure.ts';
import type { EvidenceStore } from './evidence-store.ts';
import type { ModelLedger } from './model-ledger.ts';

type Store = Pick<RunStore, 'claim' | 'renew' | 'fail' | 'complete' | 'cancelLease' | 'retry' | 'startDispatch'>;

type Options = {
  store: Store;
  authorize(candidate: Candidate): Promise<'allowed' | 'revoked' | 'unavailable'>;
  execute(candidate: Candidate, signal: AbortSignal, ensureActive: () => Promise<boolean>, dispatch: (start: () => Promise<Record<string, unknown>>) => Promise<Record<string, unknown>>, lease: Lease): Promise<{ report: Record<string, unknown>; evidence: Buffer | null }>;
  evidence?: Pick<EvidenceStore, 'complete'>;
  /** Durable model accounting. Recovery and final reports go through the run lifecycle. */
  ledger?: Pick<ModelLedger, 'recover' | 'close' | 'usage'>;
  leaseMs: number;
  signal?: AbortSignal;
};

/** Execute one leased run. The executor must terminate its process tree on abort. */
export async function executeNext(options: Options): Promise<boolean> {
  if (options.signal?.aborted) return false;
  const lease = await options.store.claim(options.leaseMs);
  if (!lease) return false;
  const abort = new AbortController();
  const stop = () => abort.abort();
  options.signal?.addEventListener('abort', stop, { once: true });
  if (options.signal?.aborted) abort.abort();
  let renewing = false;
  const timer = setInterval(() => {
    if (renewing) return;
    renewing = true;
    void options.store.renew(lease, options.leaseMs).then(ok => { if (!ok) abort.abort(); }, () => abort.abort()).finally(() => { renewing = false; });
  }, Math.max(1, Math.floor(options.leaseMs / 3)));
  const ledger = options.ledger;
  /** Final reports carry every model attempt, including failed and uncertain ones. */
  const account = async (report: Record<string, unknown>): Promise<Record<string, unknown>> => {
    if (!ledger) return report;
    await ledger.close(lease);
    const model = await ledger.usage(lease.id);
    if (!model) return report;
    const usage = typeof report.usage === 'object' && report.usage !== null ? report.usage : {};
    return { ...report, usage: { ...usage, model } };
  };
  try {
    await ledger?.recover(lease);
    const access = await options.authorize(lease.candidate);
    if (access === 'revoked') {
      await options.store.cancelLease(lease);
    } else if (access === 'allowed' && !abort.signal.aborted) {
      const ensureActive = async () => {
        if (abort.signal.aborted || !await options.store.renew(lease, options.leaseMs)) return false;
        if (abort.signal.aborted) return false;
        const access = await options.authorize(lease.candidate);
        if (access === 'unavailable') throw new Error('Authorization unavailable');
        return access === 'allowed' && !abort.signal.aborted;
      };
      const result = await options.execute(lease.candidate, abort.signal, ensureActive, start => options.store.startDispatch(lease, start, stop), lease);
      const report = await account(result.report);
      if (!abort.signal.aborted && report.status === 'error' && lease.generation < 3) {
        await options.store.retry(lease, report);
      } else if (!abort.signal.aborted) {
        const current = await options.authorize(lease.candidate);
        if (current === 'allowed' && !abort.signal.aborted) {
          if (result.evidence && options.evidence) await options.evidence.complete(lease, report, result.evidence, abort.signal,
            async () => await options.authorize(lease.candidate) === 'allowed');
          else if (report.status !== 'error' && options.evidence) throw new Error('Completed run has no evidence');
          else await options.store.complete(lease, report);
        }
        else if (current === 'revoked') await options.store.cancelLease(lease);
      }
    }
  } catch (error) {
    if (!abort.signal.aborted) {
      if (!(error instanceof RunFailure) && lease.generation < 3) await options.store.retry(lease);
      else {
        const reason = error instanceof RunFailure ? error.reason : 'worker_execution_failed';
        const report = ledger ? await account({ version: 1, status: 'error', reason }).catch(() => null) : null;
        if (report && report.usage) await options.store.complete(lease, report);
        else await options.store.fail(lease, reason);
      }
    }
  } finally { clearInterval(timer); options.signal?.removeEventListener('abort', stop); }
  return true;
}
