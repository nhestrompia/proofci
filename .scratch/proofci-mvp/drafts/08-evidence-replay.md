# 08: Export evidence and reproduce verification in a fresh environment

**What to build:** A maintainer exports a run's evidence and reproduces validation without trusting the original worker's claimed result or contacting a model.

**Blocked by:** 05: Verify every approved obligation through a portable CLI.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/8

- [ ] An immutable bundle contains or identifies the exact baseline, candidate, dependencies, toolchain, policy, proofs, report, and their digests.
- [ ] A fresh Linux environment reconstructs recorded supported inputs and independently validates the evidence through the same verifier.
- [ ] Changed source, helpers, contracts, tools, policy, or evidence cannot appear as reproduction of the original run. A forged report cannot substitute for its underlying proof.
- [ ] Missing inputs, unavailable remote artifacts, and unsupported bundle versions produce actionable nonpassing results.
- [ ] Oversized artifacts, archive traversal, hostile names, and invalid extraction paths are rejected before entering trusted state.
- [ ] Replay explicitly distinguishes a reproduced proof result from historical CI publication and does not reuse cross-run proof-result caches.

**Agent ownership:** Own bundle packaging, safe ingestion, and replay. Hosted storage uses this format rather than inventing a second archive or verifier.

**Spec coverage:** user stories 2, 14, 20, 21, 35, 39, 40.
