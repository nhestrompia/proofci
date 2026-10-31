## What to build

A maintainer submits a refutation or supported counterexample and receives violated only when independent validation establishes failure of the approved property.

## Acceptance criteria

- [ ] A proof of the exact proposition's negation produces violated with bound evidence. A supported concrete witness also checks the instantiated failure and its preconditions.
- [ ] Wrong-candidate witnesses, false preconditions, malformed submissions, unsupported witness forms, and confident text without proof cannot produce violated.
- [ ] Tactic failure, missing proof, search exhaustion, and timeouts remain unproven with specific reasons.
- [ ] Refutations use the same source binding, statement identity, and trust policy as successful proofs.
- [ ] Required violated and unproven outcomes block the gate. Advisory outcomes remain visible without blocking.
- [ ] Contradictory accepted evidence becomes an explicit validation error and retains both evidence references. Do not add automatic counterexample search.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/5

## Agent ownership

Own refutation/witness admission and result classification through the existing validation boundary. Do not own AI search or general theorem acceptance.

## Specification coverage

Approved ProofCI MVP spec, user stories 16, 17, 40. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:07 -->
