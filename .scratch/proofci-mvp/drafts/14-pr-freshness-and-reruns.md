# 14: Keep PR checks fresh through updates, reruns, and cancellation

**What to build:** Contributors can update, retarget, close, and rerun a PR while obsolete proof work cannot satisfy the current merge gate.

**Blocked by:** 13: Publish an authoritative check on the actual PR merge candidate.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/14

- [ ] Creation, synchronization, reopening, readiness, retargeting, and closure follow documented run behavior through the existing scheduler.
- [ ] Force-pushes and target-branch advances resolve fresh candidates and baselines. Late old completions cannot overwrite or authorize newer inputs.
- [ ] Rerun requests verify the actor's current repository authority and create an attempt for current immutable inputs. Unauthorized and cross-repository requests are denied.
- [ ] Obsolete work is durably cancelled or superseded. Cancellation prevents later dispatch and terminates active execution through the worker boundary.
- [ ] A protected pilot PR demonstrates that an old result does not satisfy a changed candidate, including a base advance during proof search.
- [ ] Document the required fresh-branch or merge-queue policy and administrator bypass limitations. An unconfirmed repository policy is not described as enforced.

**Agent ownership:** Own PR-specific lifecycle coordination. Reuse generic generations, cancellation, candidate resolution, and publication without changing their internals.

**Spec coverage:** user stories 22, 26, 28, 29, 30.
