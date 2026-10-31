# 11: Complete a real verification run through isolated dispatch

**What to build:** A trusted caller dispatches an immutable snapshot to an isolated worker and receives an authoritative result derived from independently validated evidence.

**Blocked by:** 02: Run a hostile probe in a disposable Linux worker; 05: Verify every approved obligation through a portable CLI.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/11

- [ ] The same snapshot and baseline produce equivalent normalized local and dispatched outcomes through real Lean checking.
- [ ] A restricted fetcher stages approved dependencies by immutable identity. Candidate hooks, submodule destinations, toolchain substitutions, and arbitrary dependency URLs cannot override policy.
- [ ] Candidate build and proof search receive no publishing or provider credentials, host home, arbitrary network, shared writable trusted cache, or container-management socket.
- [ ] Final validation runs separately from proof construction. A forged worker JSON report cannot establish a verified property.
- [ ] Bound raw worker artifacts by identity, size, count, path, and allowed file type; reject symlink escapes and cache-poisoning attempts. This handoff does not parse evidence archives. Archive packaging and ingestion use the separate evidence interface when integrated. Resource exhaustion or cancellation terminates the whole execution tree and yields a specific nonpassing report.
- [ ] Run inputs and result artifacts use the public CLI contracts. Dispatch is exercisable through a trusted operator command without waiting for GitHub publication.

**Agent ownership:** Own snapshot/dependency staging and worker-to-validator dispatch integration. Reuse the VM launcher and authoritative verifier, with no GitHub-specific logic.

**Spec coverage:** user stories 18, 20, 31, 32, 33, 35, 40.
