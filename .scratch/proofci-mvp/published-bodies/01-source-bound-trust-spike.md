## What to build

A maintainer submits an approved contract and actual Lean candidate to an executable spike and gets evidence showing whether the theorem concerns that candidate, including a defective change that rejects the old proof.

## Acceptance criteria

- [ ] A pure, total function and reviewed contract produce reproducible binding evidence through real Lean tooling. The spike records candidate, contract, definition, dependency, and toolchain identities.
- [ ] A valid proof about the base implementation cannot establish the contract after the candidate changes to violate it. A separately shadowed implementation is also rejected.
- [ ] The admitted syntax, core types, imports, and declaration restrictions are executable and documented. Unsupported macros, instances, runtime replacements, and source substitutions fail closed.
- [ ] Trusted challenge construction fixes specification helpers and resolves implementation references to the admitted candidate definitions. The spike explains why source hashes or Comparator success alone do not establish this link.
- [ ] At least ten reviewed contracts and bounded mutation variants exercise correct changes, defective changes, and misleading statement dependencies. Record observed go/no-go findings rather than assumed feasibility.
- [ ] A fresh Linux environment reproduces the spike with pinned tools. Acceptance as complete requires an affirmative recorded binding go decision. A no-go finding keeps this prerequisite unresolved and requires a narrower spec before downstream verification claims proceed.

## Blocked by

None (can start immediately).

## Agent ownership

Own the trusted source/challenge adapter and admitted-definition identity. Later tickets consume this adapter rather than reconstruct source bindings.

## Specification coverage

Approved ProofCI MVP spec, user stories 6, 15, 20, 21, 43. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:01 -->
