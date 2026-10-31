## What to build

A maintainer reviews formal contracts, activates a validated immutable baseline, and checks future candidates against the same promised guarantees.

## Acceptance criteria

- [ ] A contract retains a stable ID, explanation, owner, formal statement, assumptions, specification closure, implementation bindings, and required or advisory policy.
- [ ] Activation verifies every required property on the initial implementation through the CLI boundary. Invalid activation leaves the prior baseline authoritative.
- [ ] Approval records identify the exact reviewed baseline and trusted approving identity. Draft or AI-suggested requirements never become active automatically.
- [ ] Candidate deletion, ID rename, changed helper, stronger precondition, altered import, or required-to-advisory change appears as a proposed guarantee change and cannot silently replace the active baseline.
- [ ] Existing obligations still apply to the changed implementation. Removing required symbols or omitting registered obligations blocks the gate.
- [ ] A local initialization-and-follow-up-change demonstration records protected-source requirements and exposes immutable lookup for hosted adapters.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/5

## Agent ownership

Own baseline activation, immutable contract storage/lookup, and guarantee-change records. Use the existing run interface and validator without changing acceptance rules.

## Specification coverage

Approved ProofCI MVP spec, user stories 3, 4, 5, 7, 8, 9, 41, 42. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:06 -->
