## What to build

A trusted caller dispatches an immutable snapshot to an isolated worker and receives an authoritative result derived from independently validated evidence.

## Acceptance criteria

- [ ] The same snapshot and baseline produce equivalent normalized local and dispatched outcomes through real Lean checking.
- [ ] A restricted fetcher stages approved dependencies by immutable identity. Candidate hooks, submodule destinations, toolchain substitutions, and arbitrary dependency URLs cannot override policy.
- [ ] Candidate build and proof search receive no publishing or provider credentials, host home, arbitrary network, shared writable trusted cache, or container-management socket.
- [ ] Final validation runs separately from proof construction. A forged worker JSON report cannot establish a verified property.
- [ ] Bound raw worker artifacts by identity, size, count, path, and allowed file type; reject symlink escapes and cache-poisoning attempts. This handoff does not parse evidence archives. Archive packaging and ingestion use the separate evidence interface when integrated. Resource exhaustion or cancellation terminates the whole execution tree and yields a specific nonpassing report.
- [ ] Run inputs and result artifacts use the public CLI contracts. Dispatch is exercisable through a trusted operator command without waiting for GitHub publication.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/2
- https://github.com/nhestrompia/proofci/issues/5

## Agent ownership

Own snapshot/dependency staging and worker-to-validator dispatch integration. Reuse the VM launcher and authoritative verifier, with no GitHub-specific logic.

## Specification coverage

Approved ProofCI MVP spec, user stories 18, 20, 31, 32, 33, 35, 40. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:11 -->
