import type { EnrollmentStore } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { ActiveBaselines, BaselineConfiguration } from './active-baselines.ts';
import type { RunStore } from './run-store.ts';
import { reconcileHead, resolveDelivery } from './delivery-worker.ts';
import { executeNext } from './run-worker.ts';
import { executeRun } from './run-executor.ts';

export type PilotConfiguration = BaselineConfiguration & { ref: string };

/** Local pilot scheduler. Hosted operation requires a separate VM worker boundary. */
export class RunService {
  private readonly stopSignal = new AbortController();
  private deliveryBusy = false;
  private workerBusy = false;
  private reconcileBusy = false;
  private nextReconcile = 0;
  private timer: NodeJS.Timeout | undefined;
  private readonly options: { store: RunStore; selections: EnrollmentStore; github: GitHubApp; baselines: ActiveBaselines; repositories: PilotConfiguration[] };

  constructor(options: { store: RunStore; selections: EnrollmentStore; github: GitHubApp; baselines: ActiveBaselines; repositories: PilotConfiguration[] }) { this.options = options; }

  start(): void {
    if (this.timer) return;
    this.timer = setInterval(() => { void this.tick(); }, 1000);
    void this.tick();
  }

  stop(): void {
    this.stopSignal.abort();
    if (this.timer) clearInterval(this.timer);
    this.timer = undefined;
  }

  private async tick(): Promise<void> {
    if (this.stopSignal.signal.aborted) return;
    const { store, selections, github, baselines, repositories } = this.options;
    if (!this.deliveryBusy) {
      this.deliveryBusy = true;
      void (async () => {
        const delivery = await store.claimDelivery(300_000);
        if (delivery) {
          try { await store.processDelivery(delivery, item => resolveDelivery({ delivery: item, selections, github, baselines })); }
          catch { await store.recordDeliveryFailure(delivery); }
        }
      })().catch(() => {}).finally(() => { this.deliveryBusy = false; });
    }
    if (!this.workerBusy) {
      this.workerBusy = true;
      void executeNext({ store, leaseMs: 30_000, signal: this.stopSignal.signal,
        authorize: async candidate => {
          const version = await selections.readVersion(candidate);
          if (version === null) return 'revoked';
          const access = await github.installationAccess(candidate);
          if (access === 'revoked') await selections.removeIfVersion(candidate, version);
          if (access === 'allowed' && await selections.readVersion(candidate) !== version) return 'revoked';
          return access;
        },
        execute: (candidate, signal) => executeRun({ candidate, signal, github, baselines }),
      }).catch(() => {}).finally(() => { this.workerBusy = false; });
    }
    if (!this.reconcileBusy && Date.now() >= this.nextReconcile) {
      this.reconcileBusy = true;
      this.nextReconcile = Date.now() + 300_000;
      void (async () => {
        for (const item of repositories) {
          if (this.stopSignal.signal.aborted) break;
          try { await reconcileHead({ scope: item, ref: item.ref, github, store }); } catch { /* Retry on the next reconciliation. */ }
        }
      })().finally(() => { this.reconcileBusy = false; });
    }
  }
}
