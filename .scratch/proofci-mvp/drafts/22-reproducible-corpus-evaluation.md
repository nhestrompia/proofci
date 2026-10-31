# 22: Evaluate deterministic and assisted runs on a frozen corpus

**What to build:** Maintainers run a repeatable evaluation and inspect supported coverage, proof outcomes, latency, total cost, and the measured contribution of AI assistance.

**Blocked by:** 06: Activate and preserve reviewed contract baselines; 07: Distinguish checked violations from unresolved proofs; 09: Explain supported scope and uncovered changes; 10: Repair proofs within consent and spending limits.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/22

- [ ] Freeze at least 30 reviewed properties across three small Lean packages covering arithmetic, collections, and state transitions before measuring assistance.
- [ ] Include correct changes, intentional violations, valid code with obsolete proofs, contract mutations, source substitutions, forbidden axioms, and forged evidence.
- [ ] Every soundness and persistence scenario has zero false verified results. A false acceptance blocks release and cannot be hidden from the aggregate report.
- [ ] The evaluation command reports deterministic and assisted outcomes separately, including unproven reasons, unsupported inputs, invalid submissions, timeouts, failed attempts, total usage, and cost.
- [ ] Record hardware, toolchain, dependency identity, cache state, cold/warm behavior, median, and p95. Assess warm deterministic median below 60 seconds and p95 below five minutes without relaxing proof policy.
- [ ] Emit reusable machine-readable and human-readable evaluation artifacts. Report model nondeterminism and unknown cost separately from deterministic acceptance, and require measured utility before default paid assistance.

**Agent ownership:** Own the corpus, scenario runner, evaluation aggregation, and outcome metrics. This is a runnable maintainer capability, not permission to change acceptance rules for a better score.

**Spec coverage:** user stories 13, 16, 17, 19, 33, 36, 43.
