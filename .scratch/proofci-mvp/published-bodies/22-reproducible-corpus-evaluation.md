## What to build

Maintainers run a repeatable evaluation and inspect supported coverage, proof outcomes, latency, total cost, and the measured contribution of AI assistance.

## Acceptance criteria

- [ ] Freeze at least 30 reviewed properties across three small Lean packages covering arithmetic, collections, and state transitions before measuring assistance.
- [ ] Include correct changes, intentional violations, valid code with obsolete proofs, contract mutations, source substitutions, forbidden axioms, and forged evidence.
- [ ] Every soundness and persistence scenario has zero false verified results. A false acceptance blocks release and cannot be hidden from the aggregate report.
- [ ] The evaluation command reports deterministic and assisted outcomes separately, including unproven reasons, unsupported inputs, invalid submissions, timeouts, failed attempts, total usage, and cost.
- [ ] Record hardware, toolchain, dependency identity, cache state, cold/warm behavior, median, and p95. Assess warm deterministic median below 60 seconds and p95 below five minutes without relaxing proof policy.
- [ ] Emit reusable machine-readable and human-readable evaluation artifacts. Report model nondeterminism and unknown cost separately from deterministic acceptance, and require measured utility before default paid assistance.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/6
- https://github.com/nhestrompia/proofci/issues/7
- https://github.com/nhestrompia/proofci/issues/9
- https://github.com/nhestrompia/proofci/issues/10

## Agent ownership

Own the corpus, scenario runner, evaluation aggregation, and outcome metrics. This is a runnable maintainer capability, not permission to change acceptance rules for a better score.

## Specification coverage

Approved ProofCI MVP spec, user stories 13, 16, 17, 19, 33, 36, 43. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:22 -->
