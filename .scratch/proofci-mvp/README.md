# Published ProofCI ticket breakdown

Status: approved, published, and verified on GitHub. See the [published issue index](published.md).

Publication target: https://github.com/nhestrompia/proofci. Applied label: `ready-for-agent`.

24 independently verifiable tickets. Immediate frontier: 01, 02, 03. The dependency graph permits up to 10 independent tickets; the current session has three child-agent slots.

The core binding, validation, and CLI sequence is a real prerequisite. The VM probe and GitHub enrollment can run alongside it. After ticket 05 and the initial spikes, 8 lanes can start: 06, 07, 08, 09, 10, 11, 17, 18. Do not turn release prerequisites into fake implementation dependencies, or treat protocol fixtures as real enforcement evidence.

## Approved tickets

1. **Demonstrate proof binding to the changed Lean implementation**. Blocked by: None. Delivers: A maintainer submits an approved contract and actual Lean candidate to an executable spike and gets evidence showing whether the theorem concerns that candidate, including a defective change that rejects the old proof. [Full draft](drafts/01-source-bound-trust-spike.md).
2. **Run a hostile probe in a disposable Linux worker**. Blocked by: None. Delivers: An operator launches an adversarial probe in an ephemeral Linux VM and receives a report of denied access, resource limits, and complete cleanup before real repository verification is connected. [Full draft](drafts/02-hostile-worker-probe.md).
3. **Enroll a GitHub installation and authorize repository access**. Blocked by: None. Delivers: A maintainer installs ProofCI, selects a repository, and sees its authorized access and enforcement configuration without exposing installation credentials. [Full draft](drafts/03-github-installation.md).
4. **Accept proof evidence under an independent fixed trust policy**. Blocked by: 01. Delivers: A submitted proof bundle receives an authoritative decision against the trusted, source-bound challenge in a clean validation environment. [Full draft](drafts/04-independent-proof-validation.md).
5. **Verify every approved obligation through a portable CLI**. Blocked by: 04. Delivers: A maintainer supplies an exact snapshot and protected baseline, runs deterministic verification without a model, and receives a complete report, evidence references, and public exit status. [Full draft](drafts/05-deterministic-cli.md).
6. **Activate and preserve reviewed contract baselines**. Blocked by: 05. Delivers: A maintainer reviews formal contracts, activates a validated immutable baseline, and checks future candidates against the same promised guarantees. [Full draft](drafts/06-approved-baselines.md).
7. **Distinguish checked violations from unresolved proofs**. Blocked by: 05. Delivers: A maintainer submits a refutation or supported counterexample and receives violated only when independent validation establishes failure of the approved property. [Full draft](drafts/07-checked-violations.md).
8. **Export evidence and reproduce verification in a fresh environment**. Blocked by: 05. Delivers: A maintainer exports a run's evidence and reproduces validation without trusting the original worker's claimed result or contacting a model. [Full draft](drafts/08-evidence-replay.md).
9. **Explain supported scope and uncovered changes**. Blocked by: 05. Delivers: A reviewer sees exactly which definitions and properties the run covers, which changes lack coverage, and why unsupported behavior blocks a required guarantee. [Full draft](drafts/09-scope-and-coverage.md).
10. **Repair proofs within consent and spending limits**. Blocked by: 05. Delivers: An unresolved property can receive an optional proof-body repair through a credential-holding broker, with independent acceptance and visible total usage. [Full draft](drafts/10-bounded-ai-repair.md).
11. **Complete a real verification run through isolated dispatch**. Blocked by: 02, 05. Delivers: A trusted caller dispatches an immutable snapshot to an isolated worker and receives an authoritative result derived from independently validated evidence. [Full draft](drafts/11-isolated-verification-dispatch.md).
12. **Turn signed GitHub events into durable verification runs**. Blocked by: 03, 06, 11. Delivers: A signed event for an enrolled repository and active baseline becomes one durable isolated head-snapshot verification run, with explicitly nonenforcing scope, surviving duplicate deliveries and worker interruption. [Full draft](drafts/12-durable-github-admission.md).
13. **Publish an authoritative check on the actual PR merge candidate**. Blocked by: 08, 12. Delivers: A real pull request receives one stable ProofCI check on GitHub's actual test-merge commit, with validated outcomes, evidence, and recoverable publication. [Full draft](drafts/13-authoritative-github-check.md).
14. **Keep PR checks fresh through updates, reruns, and cancellation**. Blocked by: 13. Delivers: Contributors can update, retarget, close, and rerun a PR while obsolete proof work cannot satisfy the current merge gate. [Full draft](drafts/14-pr-freshness-and-reruns.md).
15. **Verify merge-group candidates independently**. Blocked by: 13. Delivers: A GitHub merge queue receives a fresh check for its exact merge-group commit, even when that candidate differs from individually verified PRs. [Full draft](drafts/15-merge-queue-checks.md).
16. **Admit fork verification with explicit cost authorization**. Blocked by: 10, 12. Delivers: External contributors receive deterministic verification without secrets, while costly proof assistance requires maintainer approval and repository quota. [Full draft](drafts/16-fork-admission-and-cost-control.md).
17. **Run the verifier in an unprivileged GitHub Actions job**. Blocked by: 05. Delivers: A repository runs the pinned CLI in Actions and retains its report, evidence, and blocking exit result without creating a second verification engine. [Full draft](drafts/17-github-actions-wrapper.md).
18. **Reproduce portable verification in GitLab merge request CI**. Blocked by: 05. Delivers: A GitLab project runs the same CLI in a merge request pipeline and receives equivalent normalized outcomes without a native GitLab service. [Full draft](drafts/18-gitlab-portability.md).
19. **Migrate contracts with exact maintainer authorization**. Blocked by: 03, 06, 11. Delivers: An authenticated maintainer deliberately replaces an active baseline while recording changed and retired guarantees and preserving the old baseline until validation succeeds. [Full draft](drafts/19-authorized-contract-migration.md).
20. **Retrieve and expire repository-scoped hosted evidence**. Blocked by: 03, 08, 11. Delivers: An authorized maintainer downloads evidence from an operator-dispatched hosted run, replays it locally, and receives an explicit expiration result after the retention period, independently of GitHub webhook scheduling. [Full draft](drafts/20-hosted-evidence-lifecycle.md).
21. **Recover model attempts without blind duplicate spending**. Blocked by: 10, 12. Delivers: A hosted assisted run survives interruption while preserving its budget, request history, and uncertainty about provider calls whose responses were lost. [Full draft](drafts/21-durable-ai-attempt-recovery.md).
22. **Evaluate deterministic and assisted runs on a frozen corpus**. Blocked by: 06, 07, 09, 10. Delivers: Maintainers run a repeatable evaluation and inspect supported coverage, proof outcomes, latency, total cost, and the measured contribution of AI assistance. [Full draft](drafts/22-reproducible-corpus-evaluation.md).
23. **Deploy, recover, and upgrade a self-hosted pilot**. Blocked by: 13, 20, 21. Delivers: An operator deploys pinned service artifacts, verifies a real PR, retrieves evidence, and exercises backup, restoration, credential rotation, and upgrade. [Full draft](drafts/23-self-hosted-deployment.md).
24. **Demonstrate real merge enforcement and publish MVP release evidence**. Blocked by: 14, 15, 16, 17, 18, 19, 22, 23. Delivers: Maintainers can inspect a complete, reproducible MVP release demonstration showing that the deployed service enforces approved guarantees on real PR and merge-queue candidates. [Full draft](drafts/24-validated-mvp-release.md).

## Agent execution rules

- Work only the current frontier. Refill available agent slots as blockers finish rather than imposing global wave barriers.
- Give each implementation agent an isolated worktree after its prerequisite commits land. Uncommitted parent edits are not inherited by a worktree.
- One ticket has one implementation owner. Tests and behavior belong with that ticket, not a separate horizontal team.
- Ticket 05 owns public run/report interfaces. Other agents extend through their declared adapters and coordinate any shared-contract change.
- Shared run, contract, evidence, broker, worker, and platform responsibilities are assigned in each draft. Keep one migration author at a time while unrelated modules can proceed.
- The three property outcomes remain distinct. No agent can weaken acceptance to finish a ticket or improve a benchmark.
- Linux virtualization, a test App and pilot repositories, GitLab access, model configuration, and a license decision are external prerequisites. Missing access does not count as passing acceptance. Licensing must be approved before the first public distribution, not deferred until deployment.
- A no-go trust spike is not an accepted completed prerequisite. Replan the supported subset before allowing downstream verification claims.
- Hosted paid AI remains disabled until durable provider-attempt recovery passes. Provider response loss is an uncertain cost, not permission to retry blindly.
- Publication is complete. Implementation agents should work the current frontier in isolated checkouts. Publishing alone does not start implementation.

## Dependency waves

Waves illustrate earliest starts assuming equal durations. Actual agents can take any unblocked ticket without waiting for a whole wave.

1. 01, 02, 03
2. 04
3. 05
4. 06, 07, 08, 09, 10, 11, 17, 18
5. 12, 19, 20, 22
6. 13, 16, 21
7. 14, 15, 23
8. 24

A maximum-width frontier is 07, 09, 14, 15, 16, 17, 18, 19, 20, 21 after completing its predecessors 01, 02, 03, 04, 05, 06, 08, 10, 11, 12, 13. This is a graph-capacity witness, not a recommended reason to delay useful work or a promise of runtime slots.

## Publication

All approved issues and native blocking relationships were read back and verified. The [published index](published.md) records their URLs. The immutable approved input remains in the plan manifest, and the publication ledger records approval, its digest, issue IDs, and verification.
