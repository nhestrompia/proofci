# 05: Verify every approved obligation through a portable CLI

**What to build:** A maintainer supplies an exact snapshot and protected baseline, runs deterministic verification without a model, and receives a complete report, evidence references, and public exit status.

**Blocked by:** 04: Accept proof evidence under an independent fixed trust policy.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/5

- [ ] Every registered required and advisory obligation is checked through the real adapter and validator. A diff or relevance suggestion cannot remove an obligation.
- [ ] Valid committed proofs produce verified results without model calls. Missing or obsolete proofs produce unproven results with specific reasons.
- [ ] The versioned run envelope and report carry repository, head, base, candidate, baseline, dependency, toolchain, trust-policy, resource-policy, evidence, timing, and usage identities.
- [ ] A valid policy with at least one required property passes only when all required obligations are verified. Empty baselines, missing fields, unknown versions, deleted obligations, and invalid configuration cannot pass.
- [ ] Exit 0 means a passing gate, exit 1 means completed blocking results, and exit 2 means configuration or execution failure. A report is written on failure when the destination remains available.
- [ ] Build representative passing and failing input/report fixtures and a pinned Linux distribution. Later agents can consume these public interfaces without importing Lean internals. Obtain an explicit maintainer license decision before any public distribution; a local-only image may precede that decision.
- [ ] Enforce supplied deterministic resource and time limits. Timeout and cancellation terminate the entire construction/checking process tree and produce a specific nonpassing report and exit status when possible.

**Agent ownership:** Own the public CLI, versioned input/report contracts, deterministic orchestration, and aggregate gate. This ticket establishes the shared boundary for parallel feature work.

**Spec coverage:** user stories 2, 10, 11, 12, 17, 18, 20, 21, 33, 39, 40, 41.
