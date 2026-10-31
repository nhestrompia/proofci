# ProofCI MVP

Status: proposed implementation spec. Intended issue label: `ready-for-agent`.

Research date: 2026-10-31. No implementation or proof experiment is included in this change.

## Problem Statement

Maintainers need to preserve explicit correctness guarantees as humans and AI agents change their code. Tests exercise selected cases. Reviewers can miss violations, especially when a pull request changes many files.

Maintainers also need to know what a verification result means. A theorem about a disconnected model, an altered requirement, or an older revision does not establish the promised property for the proposed change. An unsuccessful proof attempt does not establish that the property is false.

ProofCI must preserve approved contracts, bind evidence to the actual supported code, and report honest limits inside the existing review workflow.

## Solution

Provide an open-source verifier that checks approved contracts against a specific repository snapshot. The first supported code is a restricted Lean-native subset of pure, total functions with approved imports and declarations. The initial integration targets GitHub, while a CLI allows execution on other CI systems.

Maintainers approve formal properties and assumptions before enforcement. On each change, ProofCI checks every registered property, reuses valid existing proofs, and optionally asks an AI agent to repair unresolved proofs. An isolated, independent validator decides whether submitted evidence proves the approved obligation.

Each property reports `verified`, `violated`, or `unproven`, with a reason and evidence. The report also names unsupported code, excluded behavior, the contract baseline, and the exact revision. The merge gate succeeds only when every required obligation is verified and policy checks pass.

This release verifies named properties of supported definitions. It does not certify an entire repository or deployed system.

## User Stories

1. As a maintainer, I want to register a repository, so that ProofCI can check its proposed changes.
2. As a maintainer, I want to run ProofCI locally, so that I can reproduce a CI result before pushing code.
3. As a maintainer, I want human-readable explanations beside formal statements, so that I can review what each contract promises.
4. As a maintainer, I want stable property IDs, so that I can track a guarantee across code changes.
5. As a maintainer, I want explicit assumptions and preconditions, so that I can judge the scope of a guarantee.
6. As a maintainer, I want contracts bound to actual implementation symbols, so that proofs describe the code under review.
7. As a maintainer, I want approved contracts preserved by default, so that an implementation change cannot silently weaken a requirement.
8. As a maintainer, I want contract changes reviewed separately, so that intentional changes to guarantees remain visible.
9. As a maintainer, I want an initial baseline check, so that an invalid setup never appears ready for enforcement.
10. As a contributor, I want affected-property explanations, so that I can understand why my change triggered proof work.
11. As a contributor, I want all required properties checked, so that a mistaken relevance analysis cannot hide a violation.
12. As a contributor, I want existing proofs tried first, so that unchanged guarantees do not require model calls.
13. As a contributor, I want bounded AI proof repair, so that routine proof maintenance needs less manual effort.
14. As a contributor, I want generated evidence available for review, so that I can understand and retain a successful proof.
15. As a reviewer, I want a `verified` result backed by independent validation, so that an agent's confidence is irrelevant.
16. As a reviewer, I want a `violated` result backed by a checked refutation, so that a failure report identifies a real contradiction.
17. As a reviewer, I want proof-search exhaustion reported as `unproven`, so that I do not mistake uncertainty for a bug.
18. As a reviewer, I want build and infrastructure errors identified separately, so that I know what to fix or retry.
19. As a reviewer, I want unsupported code listed, so that a partial guarantee cannot appear to cover the whole change.
20. As a reviewer, I want the code revision and contract digest in the result, so that I can detect stale evidence.
21. As a reviewer, I want assumptions and validation tools listed, so that I can assess the trusted components.
22. As a GitHub maintainer, I want one stable check in each pull request, so that I can require it before merging.
23. As a GitHub contributor, I want useful annotations and a full report, so that I can find the relevant property and source.
24. As a maintainer, I want fork contributions checked without exposing secrets, so that external contributors can participate safely.
25. As a maintainer, I want costly fork runs subject to authorization and quotas, so that public contributions cannot exhaust my budget.
26. As a maintainer, I want fresh merge-result checks, so that another merged change cannot invalidate an old result unnoticed.
27. As a maintainer, I want merge queues supported, so that ProofCI checks the candidate that GitHub intends to merge.
28. As a contributor, I want reruns and cancellation, so that I can recover from outages and replace obsolete work.
29. As an operator, I want webhook deduplication, so that retries do not duplicate proof work or charges.
30. As an operator, I want durable run recovery, so that a service restart does not lose accepted work.
31. As an operator, I want isolated repository execution, so that candidate code cannot access service credentials or other repositories.
32. As an operator, I want controlled dependency retrieval, so that builds use approved, reproducible inputs.
33. As an operator, I want spending and resource limits, so that a difficult obligation terminates predictably.
34. As a private-repository owner, I want control over model access to source, so that I can enforce my data policy.
35. As an operator, I want scoped caches, so that one contributor cannot replace trusted evidence for another repository.
36. As an operator, I want latency, proof outcomes, and costs measured separately, so that I can judge service quality.
37. As a self-hosting maintainer, I want documented deployment and upgrades, so that I can operate ProofCI without a hosted account.
38. As a GitLab maintainer, I want a portable CI command, so that I can use ProofCI before a native adapter exists.
39. As a tool author, I want a versioned JSON report and stable exit codes, so that I can integrate another CI platform.
40. As a contributor, I want a report even when verification fails, so that automation and reviewers receive an explanation.
41. As a maintainer, I want invalid or empty enforcement configuration rejected, so that an empty check cannot give false assurance.
42. As a maintainer, I want explicit contract retirement records, so that removed guarantees remain auditable.
43. As an open-source contributor, I want documented support limits and fixtures, so that I can extend the verifier without overstating guarantees.
44. As a prospective Rust user, I want an honest experimental support label, so that I can distinguish translation research from supported verification.

## Implementation Decisions

All choices below are proposed defaults derived from the research. The approved end-to-end testing boundary appears under Testing Decisions.

### 1. Scope and terminology

- A contract is an approved formal predicate, its specification dependencies, assumptions, implementation bindings, ownership, and enforcement policy.
- An obligation instantiates a contract for one candidate snapshot and supported implementation binding.
- Proof evidence is a proof or refutation plus the data required for independent validation.
- A baseline is an approved, immutable contract set and trust policy selected from the target branch.
- A run binds a baseline, candidate, dependency closure, toolchain, verifier version, and resource policy.
- The candidate for merge enforcement is the resolved merge result. PR-head-only reports must say that they cover only the branch head.
- The support manifest lists allowed declarations, imports, semantics, and exclusions. Unsupported constructs prevent verification of any required property that depends on them.
- Required properties cannot disappear through changed path filters, deleted symbols, renamed IDs, empty registries, or changed project configuration.

### 2. First supported code

- Start with pure, total Lean functions over a documented set of core types and trusted libraries. Prove functional properties of those definitions.
- Exclude IO, FFI, unsafe implementation paths, partial functions, runtime replacement attributes, custom native plugins, and unapproved elaboration extensions from the verified subset.
- Do not claim compiled executable or deployment correctness. The Lean compiler, runtime, operating system, and real-world specification correspondence remain outside that guarantee.
- Pin a tested Lean toolchain, dependencies, validator configuration, and Linux image by immutable identifiers. Use the supported core validation tools rather than archived standalone repositories.
- Define the exact supported syntax and semantics in the initial spike. A label such as "Lean-native" is insufficient without this inventory.

### 3. Contract approval and persistence

- Onboarding creates draft contracts and explanations. Human approval establishes their intended meaning. AI suggestions never become enforcing requirements automatically.
- Each property records an ID, description, owner, formal statement, specification dependency digest, implementation symbol bindings, assumptions, and required or advisory policy.
- Baseline activation requires successful deterministic validation of all required properties on its initial implementation.
- Ordinary PR runs read policy and contracts from the trusted target baseline, then apply those obligations to candidate code. Candidate configuration cannot replace the baseline.
- Contract edits, deletions, stronger preconditions, and changed helper definitions appear as proposed guarantee changes. Existing obligations remain active during the implementation run.
- The MVP permits contract evolution through a dedicated maintainer-authorized migration. Authorization binds the exact baseline, proposed replacement, candidate, and approver identity. New commits invalidate it.
- A migration run validates the replacement baseline and records retired guarantees. It states that policy changed and does not claim preservation of retired contracts.
- An agent cannot approve or initiate a policy migration. Ordinary code-review approval is not migration authorization. Hosted approval uses an authenticated maintainer operation outside candidate code.
- Local and generic CI users must supply the baseline from a protected source. Document that an attacker-controlled invocation cannot establish an authoritative merge gate.

### 4. Code, statement, and evidence binding

- Build a trusted challenge from approved contract syntax and approved specification helpers. Bind its implementation references to the supported candidate definitions.
- Freeze the whole specification dependency closure, including notations and instances that affect its meaning. Human-readable prose and theorem names alone do not identify a proposition.
- Keep candidate implementation declarations distinct from specification and proof declarations. Reject unsupported shadowing or elaboration behavior instead of guessing its meaning.
- Demonstrate that the expected implementation body corresponds to the candidate source. Matching a proof to an export or recording a source hash alone does not establish this relationship.
- Use independent challenge comparison, proof export validation, kernel replay, and a configured external checker in a clean environment. The final acceptance policy cannot come from candidate configuration.
- Permit only the explicitly approved foundational axioms. Reject solution dependence on `sorryAx`, custom axioms, native-evaluation trust, or unvalidated declarations.
- Trusted challenge placeholders are not accepted proof evidence. Every selected solution theorem and its dependencies must pass the solution policy.
- A malicious or malformed evidence bundle becomes `unproven` with an invalid-evidence reason and a failing gate. Preserve security diagnostics outside candidate-controlled logs.
- Stop release if the spike cannot defend candidate binding and statement identity. Do not compensate with a confidence score or agent review.

The implementation details and validation commands must follow the pinned toolchain. Current [Lake validation documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) informs this design, but the spike must test the full ProofCI binding process.

### 5. Scheduling and change analysis

- Use the complete Git diff to explain changes and prioritize agent work. Treat filenames and repository text as untrusted data.
- Check every registered obligation in the MVP. AI analysis cannot remove an obligation from the required set.
- Resolve all inputs to immutable revisions. Do not execute Git hooks or accept candidate-controlled submodule URLs without policy validation.
- Record unsupported changed code and uncovered supported symbols separately from the property counts.
- Fail setup when enforcement has no required properties. An unrelated change can pass only after existing required properties are actually rechecked.
- Defer selective verification and cross-run proof-result reuse. Initially allow only trusted, pinned dependency caches.

### 6. AI proof assistance

- Attempt committed proofs and deterministic tactics before model calls. Provide a mode that disables the model entirely.
- Give the agent an obligation, relevant allowed source, approved assumptions, and sanitized diagnostics. Treat all repository instructions as data.
- Allow edits only in the proof workspace. The agent cannot change approved statements, assumptions, source bindings, required status, budgets, dependencies, or validator commands.
- A broker holds model credentials and enforces context, call, token, wall-clock, and spending limits. The worker receives no raw provider or GitHub publishing keys.
- The broker does not expose arbitrary network calls or publishing operations. It authorizes each request against the run's repository and remaining budget.
- Default pilot limits are five repair attempts per obligation, a 120-second obligation budget, a 15-minute run limit, and operator-configured token and monetary ceilings. These are initial controls, not measured completion targets.
- A missing model, unavailable provider, or exhausted budget leaves the property `unproven` unless deterministic checking already established it.
- Make source transmission opt-in for private repositories. Support provider replacement without changing the proof acceptance policy.
- Return generated proofs as artifacts or patch suggestions. Automatic commits and PR comments are outside this release.

### 7. Property results and aggregate gate

- `verified` means the independent validator accepts evidence of the exact required proposition for the bound candidate under the recorded trust policy.
- `violated` means the independent validator accepts a proof of the proposition's negation, or a concrete witness that proves the appropriate instantiated failure and satisfies its preconditions.
- `unproven` means neither result is established. Reasons include missing proof, search exhaustion, timeout, unsupported semantics, build failure, dependency failure, invalid evidence, and unavailable validation.
- Optional counterexample search may propose witnesses. A model-generated example without validation cannot produce `violated`.
- If contradictory accepted evidence appears, report a validation error, fail the run, and retain evidence for investigation.
- Keep property outcomes separate from run execution state and gate outcome. A report can contain verified properties and still fail because execution or policy validation failed.
- The enforcing aggregate succeeds only if policy is valid, at least one required property exists, and every required obligation is verified for the current run inputs.
- Advisory outcomes remain visible and do not block. A changed candidate cannot demote an existing required property.
- Use exit code 0 for a passing gate, 1 for a completed blocking result, and 2 for configuration or execution failure. A cancellation returns nonzero and records the reason when the report destination remains available.
- Do not expose raw validator exit codes as ProofCI's public result contract. Normalize them through the authoritative report.

### 8. Interfaces and records

- The portable verification interface accepts a repository snapshot, baseline, candidate identity, support policy, resource limits, and output destination. An equivalent invocation works outside GitHub.
- The versioned run envelope includes repository identity, platform, change ID, target base, head, candidate tree or commit, baseline digest, toolchain digest, dependency digest, and request ID.
- The versioned JSON report includes run state, gate outcome, input identities, property results and reasons, assumptions, support exclusions, validation tools, evidence digests, timing, and model usage.
- Each property result identifies its formal obligation and evidence. Missing fields or unsupported report versions are errors, not successful empty results.
- Store installations, repositories, baselines, approvals, deliveries, runs, obligations, attempts, evidence references, usage, and pending publications as related records.
- Scope all reads and writes by installation and repository identity. A user-supplied repository name is insufficient authorization.
- Use leases and monotonic run generations. Durable publication records make retries safe without duplicate checks or charges.
- Store source and proof artifacts outside the run table. Validate size limits and paths before ingestion. Never unpack an archive directly into trusted configuration.

### 9. Process and hosting design

- Use a TypeScript CLI and modular Node.js control service, Lean inspection helpers, PostgreSQL, and an S3-compatible artifact store. Final versions are pinned during implementation.
- Separate the platform adapter, contract service, scheduler, execution worker, model broker, independent validator, and reporter by responsibility. They need not all be separate network services.
- Keep verification on disposable Linux workers with VM isolation for hosted untrusted repositories. Local execution uses the documented Linux image and retains an explicit local trust boundary.
- Candidate build tools, elaborators, and tactics never run inside the credentialed control process. Final checking runs separately from proof construction.
- Stage approved dependencies with a restricted fetcher. Build and final validation have no general network access, host home access, service credentials, or container-management socket.
- Set CPU, memory, disk, process, log, and time limits. Terminate the whole task process tree on cancellation or timeout.
- Repository output cannot choose executable paths or checker commands in the trusted validator. Reject candidate toolchain substitutions.
- Use a 30-day default retention for hosted run evidence, configurable by the operator. Document what expiration removes and how it affects reproduction.
- Publish deployment, backup, credential rotation, upgrade, and recovery instructions before calling the hosted pilot supported. Choose an explicit open-source license before distribution.

### 10. GitHub integration

- Register a GitHub App with contents read, pull requests read, checks write, and metadata access. No contents write or pull requests write permission is required for the proposed read-and-report workflow.
- Authenticate and deduplicate webhook deliveries before scheduling. Acknowledge durably accepted deliveries promptly and process proof work asynchronously.
- Handle PR creation, synchronization, reopening, readiness, retargeting, and closure. Handle authorized check reruns, installation changes, target-branch changes, and merge-group checks.
- Subscribe only to events needed by this lifecycle. Route multiple notifications about the same candidate to one run generation.
- Resolve fork source and destination repositories explicitly. Never infer PR association solely from the check API's returned PR list.
- Create one stable `ProofCI` aggregate check. Publish progress, a concise summary, supported scope, and an evidence link. Batch annotations to the API limit.
- Map a passing gate to success. Map completed blocking results and execution errors to failure with distinct reasons. Cancelled or timed-out runs cannot satisfy the required gate.
- Reconcile check publication after API failures without rerunning successful proof work. Validate permissions and ownership for rerun requests.
- On target changes, invalidate the old candidate and schedule a fresh merge result. Do not overwrite a newer run with an older completion.
- Before publication, confirm the applicable head, base, baseline, and run generation. Branch protection with fresh-branch requirements or a merge queue closes the remaining merge race.
- Publish on the actual GitHub test-merge or merge-group commit, not a locally created commit that merely has the same tree. Missing or conflicting merge refs produce a blocking result with a clear reason.
- Handle merge-group candidates explicitly. If ProofCI cannot resolve a candidate, fail with a clear execution reason instead of reusing a PR result.
- Onboarding documents a required check restricted to the expected App and fresh merge policy. Verify configuration when permissions allow. Otherwise report enforcement as unconfirmed, not enabled. Automated policy inspection may require a separately documented administration-read permission.
- App credentials stay in the publisher. Workers cannot publish checks. A protected, authoritative check cannot rely solely on editable candidate workflow code.

### 11. GitHub Actions and other CI

- Ship a pinned CLI image and an Actions wrapper after the local verifier works. The wrapper generates the same JSON report and evidence bundle.
- Use an unprivileged PR workflow for candidate execution. Never execute candidate code in a privileged `pull_request_target` context to obtain secrets.
- Deterministic verification works without model credentials. Fork AI assistance requires separate authorization through the hosted broker or remains disabled.
- Document that a portable job inherits its host CI's trust and merge-policy configuration. The wrapper alone does not stop workflow tampering.
- Validate the same CLI in a GitLab merge request pipeline as a portability check. A native GitLab App and external status-check lifecycle are deferred.
- Other platform integrations must supply immutable identities, a protected baseline, isolation, report artifacts, and a nonzero blocking status before claiming support.

The [CI research](../research/ci-and-architecture.md) cites the platform requirements and explains the GitLab tier and timeout constraints.

### 12. Delivery sequence and release gates

1. Complete the trust spike. Use real candidate definitions, approved challenge statements, a fresh validator, and an adversarial fixture corpus. Produce reproducible acceptance evidence.
2. Deliver deterministic local verification. Support baseline initialization, full obligation checks, stable reports, exit codes, evidence bundles, and offline replay.
3. Add bounded proof assistance. Measure improvement over deterministic verification without changing its acceptance policy.
4. Deliver the GitHub pilot. Add App installation, durable event processing, isolated workers, fork handling, freshness, check reporting, and merge enforcement guidance.
5. Validate portable execution in GitLab CI. Keep native platform expansion separate.

Release requires every soundness and enforcement fixture to pass with zero false verified results. Any accepted weakened statement, stale source proof, forbidden axiom, or forged report blocks release.

Use an initial corpus of at least 30 properties across three small Lean packages, covering arithmetic, collection behavior, and state transitions. Include correct changes, intentional violations, and valid changes with broken proof scripts. Freeze the corpus before measuring agent assistance.

For a pilot, target a warm deterministic median below 60 seconds and a 95th percentile below five minutes for that corpus. Record hardware, toolchain, cache state, and full failures. Missing these targets changes scope or budgets, never acceptance rules.

Publish deterministic and agent-assisted outcomes separately, including unproven counts and total cost. No minimum model solve rate is a soundness requirement. Agent assistance must show useful improvement within the chosen budget before it becomes a default paid operation.

## Testing Decisions

The user approved one primary boundary: submit a repository snapshot and approved contracts, then inspect the machine-readable report, exit status, and CI result with real Lean validation inside.

Use this boundary for the core acceptance corpus. A good test distinguishes behavior a maintainer can observe. It does not assert a private function sequence, exact prompt wording, queue implementation, or a model's prose.

Test the verifier, contract lifecycle, scheduler, model limits, independent validator, and reporter through the same run interface. Add focused protocol tests only where signatures, authorization, isolation, or platform APIs cannot be exercised reliably through that boundary.

There are no existing tests or seams in the repository. Use upstream challenge-validation examples and documented GitHub webhook patterns as prior art. Do not mock Lean in the soundness corpus. A deterministic model stub can test budgets and malformed suggestions, while a separately reported live-model evaluation measures assistance quality.

| Scenario | Required observable behavior |
| --- | --- |
| Valid implementation and valid existing proof | Verified property, passing gate, exit 0, no model call |
| Correct change with an obsolete proof script | Verified only after accepted repair, otherwise unproven |
| Incorrect implementation with a checked counterexample | Violated property with bound witness evidence and blocking gate |
| Incorrect implementation without checked refutation | Unproven and blocking, never an invented violation |
| AI returns confident text without a proof | Unproven and blocking |
| Direct or imported `sorry`, custom axiom, or native trust | Evidence rejected, no verified result |
| Changed predicate, assumptions, notation, or specification helper | Baseline preserved or explicit migration required |
| Proof refers to old code or a shadow implementation | Binding rejection and blocking gate |
| Forged export, malformed archive, or forged worker report | Rejection outside candidate control |
| Candidate changes toolchain, checker command, or build configuration | Trusted policy remains authoritative or run blocks |
| Unsupported behavior enters a required dependency | Unproven with a support reason and blocking gate |
| Required symbol or all contracts disappear | Blocking policy or binding error |
| Implementation changes outside the registered scope | Report exclusions and recheck existing obligations |
| Agent, checker, dependency fetch, or worker times out | Nonzero result with a specific execution or proof reason |
| Private source transmission is disabled | No model request containing repository source |
| Candidate attempts secret, host, cache, or network access | Isolation test denies access and records the attempt |
| Duplicate or replayed webhook | One logical run and publication for the same generation |
| Service restarts after enqueue or publication | Work resumes without duplicate model charges or checks |
| Force-push or base advance during proof search | Old evidence cannot satisfy the new candidate gate |
| Merge-group candidate differs from PR candidate | Fresh check for the merge group |
| Unauthorized rerun, migration, or cross-repository artifact access | Request denied without execution or disclosure |
| Authorized contract migration followed by another push | Prior authorization no longer applies |
| GitHub returns transient publication errors | Publication retries reuse evidence without proof rerun |
| More than one annotation batch is needed | All annotations publish without changing the aggregate outcome |
| CLI runs in GitHub and GitLab environments | Equivalent inputs produce equivalent normalized reports and exit codes |

End-to-end GitHub verification must use a dedicated pilot repository with real installations, fork PRs, required checks, and a merge queue where available. API mocks alone do not establish merge enforcement. Record the exact tested GitHub configuration and any unsupported account feature.

Test exported evidence replay in a fresh environment with the recorded immutable inputs. A successful recheck is evidence reproduction, not a promise that an expired artifact remains downloadable.

## Out of Scope

- General verification of TypeScript, Python, C++, or arbitrary application code.
- A supported Rust frontend. Rust/Aeneas remains a separately specified experiment.
- Autonomous approval of requirements, automatic contract weakening, or natural-language specifications treated as formal guarantees.
- Proof of deployed binaries, compiler correctness, external services, IO behavior, concurrency, liveness, or undefined foreign-language behavior.
- Treating test success, an SMT solver's unsupported claim, or an AI review as Lean proof evidence.
- Replacing CI orchestration, deployment pipelines, release tooling, or hosting providers.
- Native integrations for every platform, a production dashboard, billing, a proof marketplace, or general multi-tenant scale guarantees.
- Selective obligation skipping, cross-run proof-result caching, automatic code commits, automatic PR creation, and comment-based approvals.

## Further Notes

The architectural research and verification research contain primary-source citations and explain the limits behind these choices. Release claims must track the tested supported subset and actual trust policy.

The repository has no configured tracker or Git remote. This spec is ready for review locally but is not published as an issue. Run `/setup-matt-pocock-skills` to configure the tracker before publication with `ready-for-agent`.

The first implementation task is the trust spike, followed by the deterministic CLI. A polished integration cannot compensate for missing code-to-proof binding.
