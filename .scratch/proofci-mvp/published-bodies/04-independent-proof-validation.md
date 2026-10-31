## What to build

A submitted proof bundle receives an authoritative decision against the trusted, source-bound challenge in a clean validation environment.

## Acceptance criteria

- [ ] Valid evidence passes challenge comparison, export-format validation, fresh kernel replay, and a configured external checker using pinned core tooling.
- [ ] Direct and transitive sorry, custom axioms, native-evaluation trust, and unvalidated declarations cannot produce acceptance. Record the explicit permitted foundational axioms.
- [ ] Candidate checker commands, toolchains, policy files, or proof placeholders cannot override the trusted validation policy.
- [ ] Forged exports, malformed bundles, changed declarations, weakened statements, altered helpers, and wrong-candidate evidence receive blocking invalid-evidence decisions.
- [ ] Checker disagreement, contradictory evidence, build failure, or unavailable validation returns a distinct nonpassing reason. There is no weaker fallback acceptance path.
- [ ] The adversarial trust corpus has zero false acceptances. Untrusted proof construction cannot mutate the challenge or privileged validation environment.
- [ ] Establish and test protected proof construction and final validation in this ticket. Reconstruct the challenge from authoritative immutable inputs, prevent construction artifacts from replacing it, and keep untrusted elaboration and binary artifacts out of the privileged checker process. Do not defer this boundary to hosted dispatch.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/1

## Agent ownership

Own evidence validation and normalized decisions, including checker invocation. Reuse source admission from https://github.com/nhestrompia/proofci/issues/1. External callers cannot supply trusted executable commands.

## Specification coverage

Approved ProofCI MVP spec, user stories 15, 17, 18, 21, 31, 43. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:04 -->
