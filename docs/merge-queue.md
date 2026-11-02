# Merge queue candidates

A GitHub merge queue tests a temporary *merge-group commit*: the target branch, or
the group ahead of it in the queue, plus one or more queued pull requests. That
commit can differ from every PR's own test merge. ProofCI verifies each merge
group as its own candidate and publishes the `ProofCI` check on the exact group
commit. A passing PR check never stands in for a group.

## Resolution

A signed `merge_group` `checks_requested` webhook only queues an observation. The
scheduler then resolves it before admitting work:

1. The repository must be enrolled, configured for the pilot, and still accessible
   to the App.
2. The group's target (`base_ref`) must be the configured protected branch. The
   active baseline protects that branch only; any other target is blocked with
   `merge_group_target_unprotected`.
3. GitHub must report that the temporary queue branch
   (`refs/heads/gh-readonly-queue/<target>/…`) still points at the notified group
   commit (`merge_group_ref_missing`, `merge_group_ref_mismatch` otherwise).
4. The group commit's first parent must be the notified group base
   (`merge_group_parents_mismatch` otherwise).
5. The repository must have an active protected baseline (`baseline_unavailable`
   otherwise).

A resolved group becomes a run with kind `merge-group`. Its identity is the queue
branch, group commit, group base, baseline, enrollment generation, and authority
revision. It never matches a PR run, even when the commits are identical, so PR
evidence cannot be reused. The worker rechecks the queue branch, the parent, and
the baseline before dispatch and before it accepts a result.

A group that fails resolution still receives a check: ProofCI records a failed run
with the reason and publishes `failure` on the group commit, with
`Execution reason: <reason>` in the summary. A queue that requires `ProofCI` does
not wait on a missing check.

## Scope in reports

The run report's `scheduler.scope` names what was verified:

| Scope | Candidate |
| --- | --- |
| `pull-request-test-merge` | GitHub's test-merge commit for one pull request |
| `merge-group` | A merge-group commit from the merge queue |
| `head-snapshot-nonenforcing` | A configured branch head; never published as a gate |

The published check summary starts with `Candidate scope: merge group` or
`Candidate scope: pull request test merge`. A merge-group summary also names the
queue branch and group commit.

## Freshness

Each queue branch is a lane. Groups stacked in one queue use different branches,
so they are verified in parallel and do not cancel each other. A target-branch
push does not cancel group runs: each group is bound to its own base commit, and
GitHub rebuilds the groups when the queue changes.

| Event | Effect |
| --- | --- |
| `checks_requested` for a new commit on an existing queue branch (group rebuilt) | The earlier group's queued or running work is cancelled and made inapplicable; its check is marked stale |
| `destroyed` with `dequeued` or `invalidated` (or an unknown reason) | The exact group is retired: active work is cancelled and its check is marked stale |
| `destroyed` with `merged` | The group is retired. Its final published check stays as it was |
| Baseline change or loss | Published group checks are revalidated and marked stale; GitHub must re-request the group |

Retirement is durable. A redelivered or late `checks_requested` for a retired group
admits nothing (`merge_group_retired`), including one that was resolving while the
group was retired. Completion and publication use the same lease, generation, and
applicability fences as pull requests: a late result from a cancelled or replaced
group is discarded and cannot satisfy a newer group.

Reruns of a merge-group check are not accepted; GitHub re-requests checks when it
rebuilds the group.

## GitHub configuration

- Give the App the **Merge queues: read** repository permission and subscribe its
  webhook to **Merge group** events. ProofCI requests no merge-queue access in
  its installation tokens; it reads the queue branch with contents read.
- In the target branch's ruleset, enable **Require merge queue** and require the
  `ProofCI` status check from this App. GitHub then requires the check on both
  PRs and merge groups.
- Merge queues are available only for organization-owned repositories (public, or
  private with GitHub Enterprise Cloud). They cannot be enabled on a repository
  owned by a personal account.

## Validation status

Automated tests cover webhook verification and parsing, GitHub group resolution
(branch, commit, and parent checks), target and baseline binding, independence
from a passing PR run with the same commit, parallel stacked groups with one
passing and one defective result, rebuild replacement, dequeue cancellation,
retirement racing with resolution, late-completion fencing, explicit failure for
an unresolvable group, and preservation of a merged group's check. They use
PostgreSQL and the real scheduler and publisher with stubbed GitHub responses and
verifier output. `PROOFCI_TEST_VM=1 PROOFCI_TEST_MERGE_GROUP=1 node --test
test/run-executor-linux.test.ts` runs a merge-group candidate through the real
isolated Lean verifier on a host with the VM runtime.

**Not yet demonstrated: a real merge queue.** The pilot repository
`nhestrompia/proofci` is owned by a personal account, so GitHub does not offer
a merge queue for it. A live demonstration needs an organization-owned pilot
repository with the App installed, a public webhook endpoint, and a ruleset that
requires the merge queue and the `ProofCI` check. It must show that `ProofCI` is
the required check on the group commit, that a passing group merges, and that a
defective group is blocked. Until then, merge-queue enforcement is not
established. Protocol tests with mocks do not establish it.
