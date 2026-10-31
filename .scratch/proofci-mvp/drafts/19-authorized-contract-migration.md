# 19: Migrate contracts with exact maintainer authorization

**What to build:** An authenticated maintainer deliberately replaces an active baseline while recording changed and retired guarantees and preserving the old baseline until validation succeeds.

**Blocked by:** 03: Enroll a GitHub installation and authorize repository access; 06: Activate and preserve reviewed contract baselines; 11: Complete a real verification run through isolated dispatch.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/19

- [ ] A dedicated trusted migration operation binds the previous baseline, exact replacement, candidate, and currently authorized maintainer identity.
- [ ] Ordinary review approval, caller-supplied actor names, candidate code, or agent output cannot authorize migration.
- [ ] A changed candidate, replacement, baseline, or revoked authority invalidates the authorization. Concurrent migrations cannot overwrite a newer baseline.
- [ ] The replacement activates atomically only after all its required obligations pass deterministic verification. Failed or interrupted migration leaves the previous baseline authoritative.
- [ ] A successful record names retired guarantees and states that policy changed. It never reports preservation of removed contracts.
- [ ] Ordinary implementation runs enforce the prior baseline until activation. A live repository demonstration exercises authorized replacement and rejected stale approval.

**Agent ownership:** Own durable migration authorization records and atomic baseline transitions. Use the existing baseline store, trusted identity check, and isolated dispatch. No webhook scheduling dependency is needed.

**Spec coverage:** user stories 7, 8, 9, 28, 42.
