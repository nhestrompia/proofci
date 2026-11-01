import type { EnrollmentStore } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { ActiveBaselines, BaselineConfiguration } from './active-baselines.ts';
import type { RunStore } from './run-store.ts';
import { resolvePullDelivery } from './pull-delivery.ts';
import { reconcileHead, resolveDelivery } from './delivery-worker.ts';
import { executeNext } from './run-worker.ts';
import { executeRun } from './run-executor.ts';
import type { EvidenceStore } from './evidence-store.ts';

export type PilotConfiguration = BaselineConfiguration & { ref: string; assistanceQuotaMicros: number };

/** Local pilot scheduler. Hosted operation requires a separate VM worker boundary. */
export class RunService {
  private readonly stopSignal = new AbortController();
  private deliveryBusy = false;
  private workerBusy = false;
  private pullBusy = false;
  private reconcileBusy = false;
  private nextReconcile = 0;
  private nextExpiration = 0;
  private expirationBusy = false;
  private timer: NodeJS.Timeout | undefined;
  private readonly options: { store: RunStore; selections: EnrollmentStore; github: GitHubApp; baselines: ActiveBaselines; repositories: PilotConfiguration[]; evidence: EvidenceStore };

  constructor(options: { store: RunStore; selections: EnrollmentStore; github: GitHubApp; baselines: ActiveBaselines; repositories: PilotConfiguration[]; evidence: EvidenceStore }) { this.options = options; }

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
    const { store, selections, github, baselines, repositories, evidence } = this.options;
    if (!this.expirationBusy && Date.now() >= this.nextExpiration) {
      this.expirationBusy = true;
      this.nextExpiration = Date.now() + 60_000;
      void evidence.expire().catch(() => {}).finally(() => { this.expirationBusy = false; });
    }
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
    if (!this.pullBusy) {
      this.pullBusy = true;
      void (async () => {
        while (!this.stopSignal.signal.aborted) {
          const delivery = await store.claimPullDelivery(300_000);
          if (!delivery) break;
          await store.processPullDelivery(delivery, item => resolvePullDelivery({ delivery: item, selections, github, baselines }));
        }
      })().catch(() => {}).finally(() => { this.pullBusy = false; });
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
        evidence,
        execute: (candidate, signal, ensureActive, dispatch) => executeRun({ candidate, signal, github, baselines, evidence: true, ensureActive, dispatch }),
      }).catch(() => {}).finally(() => { this.workerBusy = false; });
    }
    if (!this.reconcileBusy && Date.now() >= this.nextReconcile) {
      this.reconcileBusy = true;
      this.nextReconcile = Date.now() + 300_000;
      void (async () => {
        for (const item of repositories) {
          if (this.stopSignal.signal.aborted) break;
          try { await reconcileHead({ scope: item, ref: item.ref, github, store: { acceptDelivery: delivery => store.acceptDelivery(delivery, true, false) } }); }
          catch { /* Retry on the next reconciliation. */ }
          try {
            await store.reconcilePulls(item, []);
            for await (const page of github.listOpenPullRequests(item)) await store.reconcilePulls(item, page, false);
          } catch { /* Retry on the next reconciliation. */ }
        }
      })().finally(() => { this.reconcileBusy = false; });
    }
  }
}
