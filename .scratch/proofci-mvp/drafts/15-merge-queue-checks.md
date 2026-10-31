# 15: Verify merge-group candidates independently

**What to build:** A GitHub merge queue receives a fresh check for its exact merge-group commit, even when that candidate differs from individually verified PRs.

**Blocked by:** 13: Publish an authoritative check on the actual PR merge candidate.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/15

- [ ] Merge-group events resolve the actual group commit and trusted baseline and create an independently identified run generation.
- [ ] Successful PR evidence cannot substitute for a different merge-group candidate. Reports distinguish test-merge and merge-group scope.
- [ ] Replacement, cancellation, and outdated groups cannot let late completions satisfy the current group. Missing candidates produce explicit nonpassing results.
- [ ] A real pilot merge queue demonstrates correct required-check association, a passing group, and a blocked defective group.
- [ ] If the account lacks the required queue feature, record the external prerequisite and leave acceptance incomplete. Protocol mocks do not establish queue enforcement.

**Agent ownership:** Own merge-group event handling and queue-specific freshness. Share resolver and generation interfaces with the PR lane; do not depend on its full lifecycle feature.

**Spec coverage:** user stories 26, 27, 28.
