import type { Candidate, RunStore } from './run-store.ts';
import { RunFailure } from './run-failure.ts';
import type { EvidenceStore } from './evidence-store.ts';

type Store = Pick<RunStore, 'claim' | 'renew' | 'fail' | 'complete' | 'cancelLease' | 'retry' | 'startDispatch'>;

type Options = {
  store: Store;
  authorize(candidate: Candidate): Promise<'allowed' | 'revoked' | 'unavailable'>;
  execute(candidate: Candidate, signal: AbortSignal, ensureActive: () => Promise<boolean>, dispatch: (start: () => Promise<Record<string, unknown>>) => Promise<Record<string, unknown>>): Promise<{ report: Record<string, unknown>; evidence?: Buffer }>;
  evidence?: Pick<EvidenceStore, 'complete'>;
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
  try {
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
      const result = await options.execute(lease.candidate, abort.signal, ensureActive, start => options.store.startDispatch(lease, start, stop));
      const { report } = result;
      if (!abort.signal.aborted && report.status === 'error' && lease.generation < 3) {
        await options.store.retry(lease);
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
      else await options.store.fail(lease, error instanceof RunFailure ? error.reason : 'worker_execution_failed');
    }
  } finally { clearInterval(timer); options.signal?.removeEventListener('abort', stop); }
  return true;
}
