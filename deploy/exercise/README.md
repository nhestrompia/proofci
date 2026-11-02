# Operational exercise

`run.ts` deploys the pinned compose stack on the local Docker host and exercises the procedures in the [deployment guide](../README.md). It writes `exercise.json` (every step with its evidence), `exercise.md`, and `diagnostics.json` to the output directory.

```sh
npm ci
node deploy/exercise/run.ts docs/evidence/ticket-23
```

## Requirements

- Docker, with the pinned `proofci-vm-verifier` and validator images loaded (see `deploy/release.json`).
- Python 3.11 or later and Git on the host. The exercise runs `portable/baselines.py activate` and `portable/replay.py` there.
- Free loopback ports 23000–23001, 25432–25433, 27070–27071, and 28080.
- About 30 to 60 minutes. Each real Lean verification takes several minutes under software emulation.

Set `PROOFCI_EXERCISE_KEEP=1` to keep containers, volumes, and state for inspection. Set `PROOFCI_EXERCISE_ROOT` to choose the parent directory; on macOS it must be a path shared with Docker Desktop, such as `/private/tmp`.

## What is real and what is simulated

Real:

- The Linux control image, PostgreSQL, the versitygw object store, and the compose files.
- Credential files and the protected SQLite stores.
- Baseline activation through the pinned validator, and every pull request run through the pinned Lean VM verifier.
- Webhook signature checks, OAuth sign-in, maintainer authorization, check publication, evidence storage and download, and replay.
- Backup, restore, restart, the upgrade checks, and diagnostics.

Simulated:

- GitHub. `control-sim.ts` is the production `startControl` with two substitutions. GitHub HTTPS requests go to `github-sim.ts`, and snapshots are fetched from a local bare repository.
- The simulator verifies App JWTs against the registered public keys and accepts only the registered OAuth client secrets. That is why the key and secret rotation steps can show failure before the rotation and success after it.

The exercise does not show GitHub's merge enforcement, the public webhook path through a reverse proxy, or behavior of the real GitHub API beyond the endpoints the service calls.

To exercise real model access, the in-flight model attempt is written through the production `ModelLedger` (reserve, then begin send), as a broker does immediately before contacting a provider. No provider is contacted. Hosted model calls stay disabled.

## Phases

1. **Deploy:**
   - Build the image and generate credential files.
   - Activate reviewed baselines through the pinned verifier, and bootstrap the authority.
   - Run preflight, then start the stack.
2. **Enroll:** a maintainer signs in through OAuth and enrolls two repositories.
3. **Pull request:**
   - A signed webhook triggers a real Lean run on the test merge commit.
   - While it runs, the exercise inspects the dispatcher process and the VM container for credentials.
   - A check is published, the maintainer downloads the evidence bundle, cross-repository and anonymous downloads are refused, and the bundle is replayed.
4. **Crash:**
   - A second run completes while check writes fail, so its publication stays pending.
   - A third run is executing, with one model attempt `sending` and one `reserved`.
   - The control container is killed.
5. **Backup:**
   - Take full and scoped backups of the stopped deployment.
   - Confirm that verification detects tampering, and that backup is refused while the service runs.
6. **Recovery:**
   - Restart the service. The pending publication is retried without reverification.
   - The in-flight attempt becomes `uncertain` and is not resent, and the interrupted run is reclaimed.
   - Diagnostics and reconciliation follow.
7. **Rotation:**
   - The webhook secret rotates without a restart.
   - The App key and OAuth client secret fail after GitHub-side rotation, and recover after the files are replaced and the service restarts.
8. **Diagnostics:** passed or proof-failure, infrastructure-failure, and superseded runs are told apart.
9. **Restore:**
   - Restore the crash-time backup into a new deployment with empty volumes, and compare it row for row.
   - Check the stores, download evidence again, and confirm repository scoping.
   - The restored service retries the pending publication and recovers the in-flight attempt without resending it.
10. **Upgrade:**
    - A database written by the previous release's code is upgraded in place.
    - A database recorded by a newer release, and one with an unsupported report format, are refused with instructions.
