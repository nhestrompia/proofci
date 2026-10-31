## What to build

A GitLab project runs the same CLI in a merge request pipeline and receives equivalent normalized outcomes without a native GitLab service.

## Acceptance criteria

- [ ] A real merge request pipeline runs representative passing, unproven, and execution-failure snapshots through the same pinned distribution and baselines as local acceptance.
- [ ] Equivalent immutable inputs yield equivalent normalized property outcomes, gate results, and exit codes. Platform metadata differences remain explicit.
- [ ] Reports and available evidence remain accessible after nonzero verification results.
- [ ] Source-branch pipelines state their head-only scope. Merged-result claims require an actually exercised corresponding pipeline mode.
- [ ] Baseline retrieval uses protected CI configuration and documents credential and fork limitations.
- [ ] The example requires neither GitLab Ultimate external status checks nor native adapter support. It remains independent of the Actions wrapper.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/5

## Agent ownership

Own GitLab examples, identity mapping, and live portability acceptance. Use the shared CLI and image unchanged.

## Specification coverage

Approved ProofCI MVP spec, user stories 2, 24, 38, 39, 40. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:18 -->
