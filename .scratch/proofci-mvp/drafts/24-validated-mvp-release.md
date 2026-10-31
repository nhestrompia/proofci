# 24: Demonstrate real merge enforcement and publish MVP release evidence

**What to build:** Maintainers can inspect a complete, reproducible MVP release demonstration showing that the deployed service enforces approved guarantees on real PR and merge-queue candidates.

**Blocked by:** 14: Keep PR checks fresh through updates, reruns, and cancellation; 15: Verify merge-group candidates independently; 16: Admit fork verification with explicit cost authorization; 17: Run the verifier in an unprivileged GitHub Actions job; 18: Reproduce portable verification in GitLab merge request CI; 19: Migrate contracts with exact maintainer authorization; 22: Evaluate deterministic and assisted runs on a frozen corpus; 23: Deploy, recover, and upgrade a self-hosted pilot.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/24

- [ ] A dedicated real pilot repository exercises passing, violated, unproven, execution-failed, fork, retargeted, force-pushed, and base-advanced PRs with required checks restricted to the expected App.
- [ ] A real merge queue verifies a changed group independently. Unsupported account features remain unmet release prerequisites rather than mocked acceptance.
- [ ] Verify all three property outcomes through the App, Actions wrapper, and portable GitLab invocation with equivalent normalized input/output behavior where their candidate scope matches.
- [ ] Exercise a baseline migration and stale-approval rejection, hosted evidence download/replay, and restart recovery. Demonstrate a real authorized fork proof repair after durable accounting is enabled, plus cancellation of an assisted run with no subsequent unauthorized requests.
- [ ] Attach the trust/isolation corpus results, frozen evaluation, operational exercises, tested permissions and branch policy, immutable release manifest, license, and known exclusions.
- [ ] Any false verification, stale merge acceptance, secret disclosure, forbidden trust dependence, or missing prerequisite blocks the release. Performance misses adjust scope or budgets, never the acceptance policy.

**Agent ownership:** Own cross-feature release demonstration and evidence collation. File defects with the responsible ticket owner instead of rewriting their modules during integration.

**Spec coverage:** user stories 1, 7, 13, 15, 16, 17, 22, 24, 26, 27, 28, 30, 37, 38, 39, 43.
