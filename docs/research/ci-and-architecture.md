# ProofCI feasibility, architecture, and CI integration

Research date: 2026-10-31. This document records findings and proposed decisions, not a working implementation.

## Recommendation

Build ProofCI as an open-source verification gate that existing CI systems can run. Start with a restricted set of Lean-native functions and approved Lean contracts. Add a GitHub App for authoritative reporting and bounded AI proof repair after the local verifier works.

The broad product is conditionally feasible. The difficult work is connecting each proof to the exact implementation and protecting the meaning of persistent contracts. GitHub integration is established engineering. Automatic formalization of arbitrary application code is a separate research problem.

The first supported guarantee should read:

> These named properties hold for these Lean definitions at this revision, under the listed assumptions and validation policy.

Do not describe this as proof that an entire repository, compiled binary, deployment, or external service is correct. A correct theorem can still express the wrong business requirement.

The companion [verification research](verification-feasibility.md) examines the proof trust model and foreign-language options. The [implementation spec](../specs/proofci-mvp.md) defines the proposed behavior.

## Current repository

The repository contains a README and an icon. It has no application, dependency manifest, tests, Lean toolchain, domain glossary, or architecture decisions. No Git remote or issue-tracker configuration is present. The design therefore introduces new boundaries rather than extending existing ones.

Neither `lean` nor `lake` is available on the current shell path. This research does not claim a local proof, performance benchmark, or integration experiment succeeded.

## Feasibility by capability

| Capability | Assessment | Release decision |
| --- | --- | --- |
| Recheck human-authored Lean properties against changed Lean code | Feasible within a declared supported subset | First release |
| Let an agent repair proof bodies | Feasible as bounded search with independent validation | After deterministic verification |
| Turn prose into a correct formal contract | Requires human review of meaning and assumptions | Draft suggestions only |
| Detect every affected property from a diff with AI | No justified completeness guarantee | Recheck every registered property initially |
| Report violated properties | Requires a validated refutation or counterexample | Never infer violation from proof-search failure |
| Verify selected Rust through Aeneas | Plausible, with additional semantics and tooling assumptions | Separate experimental milestone |
| Verify arbitrary TypeScript, Python, C++, or mixed repositories | No general source-to-Lean solution established by this research | Unsupported in the MVP |
| Block merges through GitHub | Supported through required checks and repository policy | GitHub-first integration |
| Run on other CI platforms | Feasible through a container and CLI | Portable execution first, native adapters later |

These assessments are engineering judgments. They are not measured solve rates or claims that formal verification decides every property.

## Why a CI gate comes before a CI platform

ProofCI needs checkout, contract management, proof construction, independent validation, and reporting. It does not initially need to replace build orchestration, deployment, release management, or artifact distribution.

GitHub documents the external CI pattern with App events and check runs. This establishes a supported integration route without building a replacement for Actions. [GitHub CI App guide](https://docs.github.com/en/apps/creating-github-apps/writing-code-for-a-github-app/building-ci-checks-with-a-github-app)

An Actions job is the fastest distribution route for a local verifier. A GitHub App is the better authoritative gate for hostile PRs because its code and credentials stay outside the proposed workflow changes. An editable PR workflow must not be the only authority that can declare its own verification successful. This is a design inference from the privilege boundary, not a GitHub guarantee.

## Proposed architecture

Use a modular control service and separate Linux workers. Avoid a large distributed service graph before workload measurements justify one.

1. A platform adapter receives a change event and resolves immutable repository identities and commit IDs.
2. A contract service loads the approved baseline, trust policy, and supported-code declarations from a trusted revision.
3. A scheduler creates a durable run and cancels superseded attempts.
4. A snapshot service fetches the exact source and pinned dependencies without executing repository hooks.
5. A verifier checks support boundaries, constructs obligations, and tries existing proofs and deterministic tactics.
6. A proof agent receives unresolved obligations through a bounded model broker. It can propose proof bodies and witnesses.
7. A separate validator checks the submitted evidence against a trusted challenge and the bound candidate definitions.
8. A reporter writes the versioned report and updates the platform result only for the applicable revision and policy.

The agent's output is untrusted. Its role is to find evidence. Only the validator can establish a property result.

### Suggested implementation choices

- Use TypeScript on an active Node.js LTS release for the CLI and control service. Use Lean for proof inspection and validation helpers. Pin versions during implementation.
- Use PostgreSQL for installations, contract approvals, run state, queue leases, and a publication outbox. A transactional queue is enough initially.
- Keep larger logs, source bundles, and proof evidence in an S3-compatible object store. Local execution writes the same evidence bundle to disk.
- Run verification in dedicated Linux virtual machines or microVMs. Keep disposable proof execution separate from result publication.
- Ship a pinned Linux image and a provider-neutral command interface. A hosted service remains optional for maintainers who prefer self-hosting.
- Delay a dashboard until checks, downloadable reports, and local reproduction solve the initial workflow.

These are proposed choices for a repository with no existing stack. They are not prerequisites imposed by Lean.

### Contracts and proof binding

Separate the contract's meaning from the proof that establishes it. Store stable property IDs, formal statements, supported implementation symbols, assumptions, required status, and ownership in the approved baseline.

A candidate implementation can change. The approved predicate and specification helpers cannot change silently. Construct the expected proposition from trusted contract content and independently bind its implementation references to the candidate's exact definitions. Hashing a source archive alone does not prove this binding.

The first technical spike must demonstrate this process with real changing definitions. It must reject proofs about an old implementation, a shadow definition, or a weakened predicate. If the spike cannot establish that connection, stop the verified-code claim and narrow the supported input further.

Current Lake documentation describes challenge comparison, permitted axioms, exported evidence, and Linux sandboxing. Export-only checking does not itself relate an export to workspace source. ProofCI must establish that relationship. [Lake challenges and external checkers](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator)

Treat contract changes as changes to the promised guarantee. In the MVP, ordinary implementation runs enforce the existing baseline. A separate, authorized contract-change process can adopt a replacement baseline only after it passes its own checks and records the removed guarantees. An approval of code review alone must not silently authorize weaker contracts.

### Diff analysis

Use the complete Git object diff for changed-code summaries and agent scheduling. Do not use an LLM's relevance decision to skip required checks. Recheck all registered obligations in the first release.

GitHub's PR file API caps responses at 3,000 files. A paginated API response is therefore not a complete dependency analysis for every repository. [Pull request file API](https://docs.github.com/en/rest/pulls/pulls#list-pull-requests-files)

Later optimization can use a validated dependency graph and content-addressed evidence. Toolchain, contract, dependency, and trust-policy changes invalidate relevant reuse. Unknown dependencies require broader checking.

## GitHub implementation requirements

### Registration and credentials

Register a GitHub App with a reachable HTTPS webhook endpoint. Proposed repository permissions are contents read, pull requests read, and checks write, plus metadata access. Subscribe to relevant installation, pull request, check rerun, base-branch push, and merge-group events. The exact event list must be tested against the registered App permissions.

Keep the App private key and webhook secret in the control service. Use installation credentials restricted to the selected repository. GitHub provides an installation-token endpoint and SDK support for token renewal. Workers must never receive these publishing credentials. [Installation authentication](https://docs.github.com/en/apps/creating-github-apps/authenticating-with-a-github-app/generating-an-installation-access-token-for-a-github-app)

Check webhook signatures over the raw request body with HMAC-SHA256 and constant-time comparison. [Webhook validation](https://docs.github.com/en/webhooks/using-webhooks/validating-webhook-deliveries)

Persist accepted events before acknowledging them. Deduplicate deliveries, process asynchronously, and provide missed-delivery reconciliation. GitHub asks receivers to respond within ten seconds and documents the delivery identifier for deduplication. [Webhook practices](https://docs.github.com/en/webhooks/using-webhooks/best-practices-for-using-webhooks)

### Check results and enforcement

Publish one stable aggregate check, `ProofCI`, with a summary and evidence link. Add property annotations where source locations are meaningful. GitHub check runs bind to a commit ID and support queued, in-progress, and completed states. The API accepts at most 50 annotations per request. [Check runs API](https://docs.github.com/en/rest/checks/runs)

The required gate must return failure for unresolved required properties, malformed policy, or unavailable verification. Preserve a separate reason so users can distinguish a counterexample from a worker outage. Use neutral or skipped conclusions only outside the enforcing aggregate gate.

GitHub branch protection can accept neutral and skipped checks. It can also restrict a required check to an expected App. Configure the expected source and require fresh results through an up-to-date branch policy or merge queue. Repository administrators control bypasses, so ProofCI cannot promise enforcement against administrators. [Protected branches](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches)

Run the verifier against the resolved merge result for merge gating, and report that exact target. Also handle merge-group checks for repositories with a merge queue. GitHub documents merge-group events as distinct from PR events. [Workflow events](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#merge_group)

Publish the enforcing check on GitHub's actual test-merge commit or merge-group commit. A locally synthesized merge with different metadata can have a different commit ID despite an identical tree. GitHub distinguishes checks on the test merge from checks on the head, so this mapping requires a real integration test. [Required-check troubleshooting](https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks)

### Forks and untrusted execution

Fork PRs must not gain model keys, installation tokens, signing keys, or access to another repository's cache. The hosted App can authorize a bounded run without giving its credentials to candidate code. Apply repository quotas and maintainer approval requirements for costly fork runs.

For the Actions distribution, use an unprivileged PR job for deterministic checking. External AI repair for forks must use an approved external service, or remain disabled until authorization. Never solve missing fork secrets by executing candidate code inside a privileged workflow. GitHub explicitly documents this risk for `pull_request_target` and `workflow_run`. [Actions security guidance](https://docs.github.com/en/actions/reference/security/secure-use)

## Other platforms

### GitLab

The portable CLI can run in a merge request pipeline on GitLab's Free tier. Ordinary merge request pipelines check the source branch, so merged-result claims require a different pipeline mode. [GitLab merge request pipelines](https://docs.gitlab.com/ci/pipelines/merge_request_pipelines/)

A native adapter can publish external commit statuses for the exact source commit and identify the intended pipeline to avoid ambiguity. [GitLab commit status API](https://docs.gitlab.com/api/commits/#set-commit-pipeline-status)

GitLab's external status-check feature is Ultimate-tier functionality. Its pending checks time out after two minutes, so it is a poor default lifecycle for long proof searches. Use CI jobs first. [GitLab external status checks](https://docs.gitlab.com/user/project/merge_requests/status_checks/)

### Other CI systems

Jenkins, Buildkite, CircleCI, Azure Pipelines, and Bitbucket are later adapter candidates. This research does not validate their native review APIs. The initial portable contract is a pinned Linux execution environment, a versioned input envelope, a JSON report, evidence artifacts, and a nonzero blocking exit status. Native annotations and merge enforcement require platform-specific work and testing.

## Operating requirements and cost

Treat repository builds and tactics as hostile executable code. Use ephemeral isolation, no host mounts, no container-management socket, bounded resources, and no network during final validation. A staged fetcher retrieves approved dependencies before candidate execution. Firecracker is one possible KVM-based isolation technology, not a committed hosting dependency. [Firecracker architecture](https://firecracker-microvm.github.io/)

Keep final validation separate from proof search. Do not accept a worker's JSON assertion that a proof passed. Reconstruct the authoritative report from validated evidence. Scope caches and artifacts by installation and repository, and prevent untrusted writes to trusted dependency caches.

A model broker holds provider keys, limits context and spending, and exposes only proof-assistance operations. Repository text and compiler logs are data, not instructions that can grant tools. Private repositories require explicit configuration before source leaves the deployment.

Measure deterministic success, agent-assisted success, unsupported inputs, invalid submissions, timeout rate, latency, and cost per resolved obligation separately. Include failed agent attempts in cost. Do not publish a solve percentage before measuring a representative corpus.

For planning, cost per run is worker runtime plus all model requests, storage, and publication overhead. Monthly cost also includes idle service capacity and retries. Pricing depends on provider, model, corpus, and cache hit rate. This research does not establish a credible dollar figure.

## Delivery and decision gates

1. Prove the trust design locally on Linux. Demonstrate real candidate binding, adversarial proof rejection, and the three property outcomes. Do this before a hosted integration.
2. Ship the deterministic CLI with human-authored contracts and evidence bundles. Check every registered property.
3. Add bounded AI repair. Compare it against deterministic baselines using the same obligations and budgets.
4. Add a GitHub App, durable scheduling, isolated workers, merge freshness, and a pilot repository.
5. Validate the portable CLI in GitLab CI. Develop a native adapter only if it adds value for users.
6. Run a separate Rust/Aeneas feasibility milestone. Do not extend the guarantee until semantics, supported features, and source binding are documented and tested.

A planning allowance of 8–12 engineering weeks for a narrow GitHub pilot is a rough estimate for two experienced engineers, including Lean expertise. It assumes the trust spike succeeds and existing model access and Linux hosting are available. It is not a delivery promise. A foreign-language verifier, general automatic formalization, or multi-tenant production service can exceed that range substantially.

The immediate decision is to fund the trust spike, not a broad-language launch. Its output should be executable acceptance evidence and a measured input subset.
