# 23: Deploy, recover, and upgrade a self-hosted pilot

**What to build:** An operator deploys pinned service artifacts, verifies a real PR, retrieves evidence, and exercises backup, restoration, credential rotation, and upgrade.

**Blocked by:** 13: Publish an authoritative check on the actual PR merge candidate; 20: Retrieve and expire repository-scoped hosted evidence; 21: Recover model attempts without blind duplicate spending.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/23

- [ ] A clean documented Linux deployment provisions the control service, PostgreSQL, S3-compatible artifacts, credentials, and disposable workers and completes a real Lean-backed PR run.
- [ ] Backup and restoration preserve active baselines, approval records, runs, evidence references, reservations, and pending publications consistently, without cross-repository access.
- [ ] A restart/recovery exercise preserves accepted work and retries publication without repeating validated proof construction or blindly repeating provider calls.
- [ ] Credential rotation restores webhook validation, App publishing, and optional model access while keeping credentials outside candidate execution.
- [ ] A supported upgrade preserves baseline/report compatibility or fails with explicit migration instructions. Operator-visible diagnostics distinguish proof failure, infrastructure failure, and uncertain model attempts.
- [ ] Document prerequisites, resource limits, retention, tested enforcement configuration, support limits, and release pinning. Confirm and include an explicit maintainer-approved open-source license before distribution.

**Agent ownership:** Own deployment packaging and operational exercises. Component implementations and their state contracts stay with their existing owners.

**Spec coverage:** user stories 1, 22, 24, 30, 31, 32, 33, 35, 36, 37, 40.
