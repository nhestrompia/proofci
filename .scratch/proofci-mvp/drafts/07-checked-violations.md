# 07: Distinguish checked violations from unresolved proofs

**What to build:** A maintainer submits a refutation or supported counterexample and receives violated only when independent validation establishes failure of the approved property.

**Blocked by:** 05: Verify every approved obligation through a portable CLI.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/7

- [ ] A proof of the exact proposition's negation produces violated with bound evidence. A supported concrete witness also checks the instantiated failure and its preconditions.
- [ ] Wrong-candidate witnesses, false preconditions, malformed submissions, unsupported witness forms, and confident text without proof cannot produce violated.
- [ ] Tactic failure, missing proof, search exhaustion, and timeouts remain unproven with specific reasons.
- [ ] Refutations use the same source binding, statement identity, and trust policy as successful proofs.
- [ ] Required violated and unproven outcomes block the gate. Advisory outcomes remain visible without blocking.
- [ ] Contradictory accepted evidence becomes an explicit validation error and retains both evidence references. Do not add automatic counterexample search.

**Agent ownership:** Own refutation/witness admission and result classification through the existing validation boundary. Do not own AI search or general theorem acceptance.

**Spec coverage:** user stories 16, 17, 40.
