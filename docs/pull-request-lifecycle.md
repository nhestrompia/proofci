# Pull request lifecycle

ProofCI publishes one `ProofCI` check per pull request candidate. A candidate is
GitHub's test-merge commit, bound to the PR head, the target-branch head, and the
active protected baseline. A result applies only to the exact candidate it verified.

All notifications go through the existing durable scheduler. A webhook only queues
an observation; the scheduler resolves the pull request, its test merge, and the
baseline from GitHub and the protected store before it admits work. Duplicate
deliveries map to one queued observation and one run for the same inputs.

## Event behavior

| Notification | Effect on existing runs | Then |
| --- | --- | --- |
| `opened`, `reopened` | Queued and running work for the PR is cancelled | Resolve and admit the current candidate |
| `synchronize` (push or force-push to the head) | Same | Same |
| `edited` with a changed target branch (retarget) | Same | Same |
| `edited` without a target change (title, body) | None | Ignored |
| `ready_for_review`, `converted_to_draft` | None | Re-resolve; an unchanged candidate keeps its run, and drafts are verified like other PRs |
| `closed` (including merged) | Queued and running work is cancelled | No new run; any published check is marked stale |
| Push to any branch of the destination repository | Every PR run in the repository is cancelled and its approvals revoked | Every affected PR is resolved again, picking up a target-branch advance |
| Baseline change or loss | Published PR checks are revalidated | The PR is resolved again; without an active baseline nothing is admitted |
| Check `rerequested` (rerun) | None at acceptance | See [Reruns](#reruns) |

Reconciliation also resolves configured branches and all open pull requests every
five minutes, so a missed webhook is eventually corrected. It does not cancel
work whose inputs are unchanged.

## Freshness

Cancelling a run makes it durably inapplicable in PostgreSQL before any newer
candidate is admitted. Several fences then stop old work from satisfying the gate:

- A worker renews its lease every third of the lease period. A cancelled or
  superseded run cannot renew. The worker aborts, and isolated dispatch terminates
  the verifier's whole process group (`SIGTERM`, then `SIGKILL` after 15 seconds).
- Dispatch starts only while the run is still running, applicable, and leased.
  A cancelled run is never dispatched later.
- Completion requires the current lease generation. A late result from an old
  attempt is discarded and cannot overwrite a newer run.
- Before and during publication, the publisher rechecks the run generation, the
  current GitHub test merge, the PR head and base, and the active baseline. If any
  of them changed, it marks the old check `failure` with "ProofCI result is stale".
- A cancelled or timed-out run publishes `failure`. It never satisfies the gate.

A target-branch advance changes the test merge and the base, so it always
produces a new candidate. This includes an advance during proof search.

## Reruns

GitHub sends `check_run` and `check_suite` `rerequested` events when someone asks
to re-run the `ProofCI` check. ProofCI accepts a rerun only if all of these hold:

1. The webhook signature is valid and the check belongs to this App.
2. The repository is enrolled and configured for the pilot.
3. The check (by run ID and merge commit for `check_run`, or merge commit for
   `check_suite`) belongs to a ProofCI pull request run in the same installation
   and repository. A run ID from another repository is ignored.
4. When the scheduler processes the request, GitHub reports that the actor
   currently has write, maintain, or admin access to the destination repository,
   and the numeric user ID matches the webhook sender. Read and triage access are
   denied.

Accepting a rerun changes no runs. A denied rerun leaves existing work untouched
and is recorded as `rerun_denied` at `/pulls/INSTALLATION_ID/REPOSITORY_ID/PULL_NUMBER`.
An authorized rerun resolves the PR's current inputs, which may differ from the
rerun check's inputs. If a run for those exact inputs is queued or running, the
rerun reuses it. Otherwise a new attempt is created, including after a completed,
failed, or cancelled run, and the previous attempt's check is marked stale.

## Required merge policy

ProofCI cannot prevent a merge by itself. The protection comes from GitHub
branch policy on the target branch:

- Require the `ProofCI` status check and restrict it to this App's ID.
- Require branches to be up to date before merging (strict status checks). Without
  this, GitHub can merge a PR whose `ProofCI` result was computed against an
  older target branch. An advance between the last check and the merge click is
  then unprotected.
- Merge queues are not supported yet. ProofCI does not publish checks for
  `merge_group` candidates, so a queue that requires `ProofCI` stalls. Use strict
  up-to-date branches instead.
- Include administrators in enforcement. Do not grant bypass permission to any
  actor or ruleset bypass list.

### Bypass limitations

- Repository administrators, organization owners, and actors on a ruleset bypass
  list can merge without a passing check when enforcement allows it. ProofCI cannot
  detect or reverse such merges.
- Anyone who can change branch protection or rulesets can disable the requirement.
- Policy inspection (`/inspect`) reads legacy branch protection on the default
  branch only. It reports `confirmed` only when GitHub shows the `ProofCI` check
  restricted to this App, strict freshness, and administrator enforcement. It
  needs the optional administration-read permission. Rulesets, other target
  branches, and bypass lists are not evaluated, so they are reported as
  `unconfirmed`, not enforced. An unconfirmed repository policy must not be
  described as enforced.

## GitHub App configuration

Subscribe the App webhook to `push`, `pull_request`, `check_run`, and
`check_suite`. The rerun authority check uses
`GET /repos/{owner}/{repo}/collaborators/{username}/permission`, which needs no
permission beyond the existing metadata read.

## Validation status

Automated tests cover event classification, rerun authorization and repository
scoping, rerun deduplication, late-completion fencing, publication of a stale
check after a base advance during proof search, and worker termination on
force-push. They use PostgreSQL and the real scheduler, worker, and publisher
with stubbed GitHub responses and verifier output.

The protected pilot PR demonstration is still required. It needs a live
installation with a public webhook, a required check, and strict freshness, and
has not been run. It must show that an old result does not satisfy a changed
candidate, including a base advance during proof search.
