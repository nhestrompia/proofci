# 18: Reproduce portable verification in GitLab merge request CI

**What to build:** A GitLab project runs the same CLI in a merge request pipeline and receives equivalent normalized outcomes without a native GitLab service.

**Blocked by:** 05: Verify every approved obligation through a portable CLI.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/18

- [ ] A real merge request pipeline runs representative passing, unproven, and execution-failure snapshots through the same pinned distribution and baselines as local acceptance.
- [ ] Equivalent immutable inputs yield equivalent normalized property outcomes, gate results, and exit codes. Platform metadata differences remain explicit.
- [ ] Reports and available evidence remain accessible after nonzero verification results.
- [ ] Source-branch pipelines state their head-only scope. Merged-result claims require an actually exercised corresponding pipeline mode.
- [ ] Baseline retrieval uses protected CI configuration and documents credential and fork limitations.
- [ ] The example requires neither GitLab Ultimate external status checks nor native adapter support. It remains independent of the Actions wrapper.

**Agent ownership:** Own GitLab examples, identity mapping, and live portability acceptance. Use the shared CLI and image unchanged.

**Spec coverage:** user stories 2, 24, 38, 39, 40.
