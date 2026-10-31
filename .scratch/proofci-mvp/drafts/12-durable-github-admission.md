# 12: Turn signed GitHub events into durable verification runs

**What to build:** A signed event for an enrolled repository and active baseline becomes one durable isolated head-snapshot verification run, with explicitly nonenforcing scope, surviving duplicate deliveries and worker interruption.

**Blocked by:** 03: Enroll a GitHub installation and authorize repository access; 06: Activate and preserve reviewed contract baselines; 11: Complete a real verification run through isolated dispatch.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/12

- [ ] Validate the raw-body webhook signature and installation/repository scope before scheduling. Invalid, unauthorized, or revoked inputs create no work.
- [ ] Persist accepted events before acknowledgment and respond within the platform deadline. Delivery retries converge on one logical run generation.
- [ ] Resolve the immutable branch head and protected baseline for a nonenforcing head-snapshot run. Provide generic admission for already resolved immutable candidates so the check publisher can later submit actual GitHub test-merge commits without creating a circular dependency. Identical notifications cannot duplicate logical work.
- [ ] Leases and monotonic generations recover accepted work after service or worker restart. Late workers cannot replace a newer authoritative completion.
- [ ] Cancellation and supersession persist across restart and prevent dispatch of obsolete jobs. Run inspection exposes completed reports and clear terminal failures. Record queue, execution, and recovery timings through the shared report interface.
- [ ] A real signed pilot delivery runs the actual isolated verifier. Reconciliation recovers missed applicable deliveries without reviving obsolete candidates. Provider-charge recovery is completed separately before hosted AI is enabled.

**Agent ownership:** Own delivery persistence, generic run lifecycle, leases, scheduling, and durable cancellation. Platform-specific candidate policies and publication use these operations.

**Spec coverage:** user stories 1, 28, 29, 30, 31, 40.
