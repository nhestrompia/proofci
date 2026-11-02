# Self-hosted pilot deployment

This guide deploys the ProofCI control service on one Linux host. It also covers verification of real pull requests, evidence retrieval, backup and restoration, recovery after a crash, credential rotation, and upgrades. Every procedure here was run in the [operational exercise](exercise/README.md). The [recorded results](../docs/evidence/ticket-23/README.md) state what that run did and did not establish.

> **License.** ProofCI is released under the [MIT License](../LICENSE), recorded as `"license": {"spdx": "MIT"}` in `deploy/release.json`. The control image carries the license at `/opt/proofci/LICENSE` and in its `org.opencontainers.image.licenses` label. Third-party components (the Node and Docker base images, Debian packages, npm dependencies, Lean, and the verifier image) keep their own licenses.

## What runs where

| Component | Runs as | Holds |
| --- | --- | --- |
| `control` | Container, UID 1000, read-only root, no capabilities | GitHub App key, OAuth client secret, webhook secret, database URL, object-store credentials |
| `postgres` | Container, PostgreSQL 16.11 | Enrollments, runs, reports, publications, model ledger, evidence references |
| `objects` | Container, versitygw v1.10.0 (S3 API on a POSIX volume) | Hosted evidence bundles |
| `bucket-init` | One-shot container | Creates the evidence bucket; refuses versioning |
| Verifier VM | Disposable container started for each phase of each run (`proofci-vm-*`) | Read-only snapshot, protected baseline, envelope. No network, credentials, or store access |
| Protected stores | SQLite files in `PROOFCI_STATE_DIR` | Reviewed baselines, migration approvals, maintainer grants, authority revision |

Each verifier VM is started by the control service through the host Docker socket. Access to that socket is equivalent to root on the host. Treat the control container, `PROOFCI_STATE_DIR`, and `PROOFCI_SECRETS_DIR` as root-equivalent assets.

The verifier's environment is built from an allowlist: `PATH`, `HOME`, `TMPDIR`, `DOCKER_HOST`, and the Apple runtime settings. No credential, credential path, or database setting reaches it. The exercise checks this on a live run. It reads the dispatcher's environment from `/proc` and inspects the VM container's environment, mounts, and network.

## Prerequisites

- **Host:** Linux on ARM64 (`linux/arm64`) with KVM (`/dev/kvm`). The pinned verifier VM image is ARM64 only.
  - Without KVM, the VM falls back to QEMU software emulation. The exercise host had no KVM: Lean took over 120 seconds on a one-line obligation and reported `unproven` with `obligation_budget_exhausted`. Software emulation is therefore not a supported configuration for passing results.
- **Docker:** Docker Engine 24 or later with Compose v2.20 or later.
- **Resources:** At least 4 CPUs, 8 GiB RAM, and 40 GiB of disk for images, the database, evidence, and backups.
  - Each verification phase uses one VM with 1 CPU and 3 GiB.
  - Each control process verifies one run at a time.
- **Verifier images:** Build them as described in the [portable guide](../portable/README.md) and the [repository README](../README.md#run-the-verification-pilot).
  - `docker image inspect --format '{{.Id}}' proofci-vm-verifier` must print the `verifier_vm` ID in `release.json`. The launcher refuses any other image.
  - Baseline activation uses the validator container. Its ID must also match `release.json`.
- **Network:**
  - A public HTTPS hostname and a reverse proxy that terminates TLS, applies request rate limits, and forwards to `127.0.0.1:3000`.
  - Outbound HTTPS to `api.github.com` and `github.com`.
- **GitHub App:**
  - Repository permissions: contents read, pull requests read, checks write, and metadata read. Administration read is optional and used only for policy inspection.
  - Webhook URL `https://HOST/webhooks/github`. Subscribe to installation, installation repositories, push, pull request, check run, check suite, and merge group events.
  - OAuth callback `https://HOST/oauth/callback`.
  - Only GitHub.com is supported.

## Install

1. Create the credential and state directories, then generate local credentials. The directories must be absolute paths. The work directory must have the same path on the host and in the container, because the verifier VM bind-mounts staged inputs by host path.

   ```sh
   deploy/init.sh /srv/proofci/secrets /srv/proofci/state /srv/proofci/work
   ```

   This writes `deploy/.env` and generates the PostgreSQL password, database URL, object-store keys, and webhook secret.

2. Add the GitHub credentials:
   - Save the App private key as `secrets/github-app.pem`.
   - Save the OAuth client secret as `secrets/github-client-secret`.
   - Set `PROOFCI_ORIGIN`, `GITHUB_APP_ID`, and `GITHUB_CLIENT_ID` in `deploy/.env`.
   - Copy `secrets/github-webhook-secret` into the App's webhook settings.

   The secrets directory is mounted read-only at `/run/proofci-secrets` in the control container, and the control service reads each credential from its file (`*_FILE` settings). Only PostgreSQL's password is passed as a Compose secret. Credential files must not be writable by group or other users. The control container runs as UID 1000, so give it ownership:

   ```sh
   sudo chown -R 1000:1000 /srv/proofci/secrets /srv/proofci/state /srv/proofci/work
   sudo chmod 0400 /srv/proofci/secrets/*
   ```

   `PROOFCI_DOCKER_GID` in `.env` must be the group that owns `/var/run/docker.sock`. `init.sh` detects it.

3. Build the control image and start the storage services:

   ```sh
   docker compose -f deploy/compose.yaml -f deploy/compose.kvm.yaml --env-file deploy/.env build
   docker compose -f deploy/compose.yaml -f deploy/compose.kvm.yaml --env-file deploy/.env up -d postgres objects bucket-init
   ```

   The remaining commands abbreviate `docker compose -f deploy/compose.yaml -f deploy/compose.kvm.yaml --env-file deploy/.env` as `dc`.

4. Activate the reviewed baseline and initialize the authority for each repository. Follow [Reviewed local baselines](../portable/README.md#reviewed-local-baselines) and [Run the verification pilot](../README.md#run-the-verification-pilot). Keep each store at an absolute path inside `PROOFCI_STATE_DIR`.

   The exercise runs these two documented commands through [`exercise/prepare_repository.py`](exercise/prepare_repository.py):

   ```sh
   python3 portable/baselines.py activate --store STORE --snapshot CHECKOUT --envelope ENVELOPE \
     --report REPORT --manifest-path contracts.json --reviewed-sha256 SHA256 --approver MAINTAINER_ID
   python3 portable/authority.py bootstrap --store STORE --repository https://github.com/OWNER/REPO.git \
     --ref refs/heads/main --head MAIN_COMMIT --actor MAINTAINER_ID
   ```

5. Write `PROOFCI_STATE_DIR/pilot.json` with one entry per repository (see the repository README). It must not be writable by group or other users.

6. Run preflight. It must report no `FAIL` lines. A warning about missing `/dev/kvm` means passing results are not achievable.

   ```sh
   dc run --rm --no-deps control node src/preflight.ts
   ```

   Preflight checks:
   - Configuration and credential files, the App key, and webhook secrets.
   - Database reachability and schema compatibility, and stored report versions.
   - Each protected store: integrity, repository binding, active baseline, and authority state.
   - The evidence bucket and its versioning, and the retention setting.
   - Python and Git, the pinned verifier image ID, and hardware virtualization.

7. Start the service, then enroll each repository as a maintainer at `https://HOST/`:

   ```sh
   dc up -d control
   ```

A pull request event then produces a run on GitHub's test merge commit. A `ProofCI` check run is published on that commit, and its details link points to the report. A signed-in maintainer downloads the replay bundle from the details page, at the same path with `/evidence` appended. Replay it with `portable/replay.py replay --bundle FILE --sha256 DIGEST`.

## Resource limits

These limits are fixed by the release. Changing them changes the trust policy and the release manifest.

| Limit | Value | Source |
| --- | --- | --- |
| Per-obligation proof budget | 120 s | `portable/proofci.py` |
| Run timeout, CPU time | 900 s, 900 s | `portable/resource_limits.json` |
| Verifier memory, file size, processes | 2 GiB, 2 GiB, 256 | `portable/resource_limits.json` |
| VM container | 1 CPU, 3 GiB, 128 PIDs, no network, read-only root, 256 MiB `/tmp` | `portable/vm_container.py` |
| Staged snapshot | 256 MiB total, 128 MiB per file, 100,000 files | `src/snapshot-fetch.ts` |
| Report, evidence bundle | 8 MiB, 256 MiB | `src/isolated-dispatch.ts`, `src/evidence-store.ts` |
| Webhook body, form body | 1 MiB, 4 KiB | `src/control.ts` |
| Concurrent verifications | 1 per control process | `src/run-service.ts` |
| Run lease, retry generations | 30 s, 3 | `src/run-service.ts`, `src/run-worker.ts` |
| Reconciliation of branches and open pull requests | every 5 minutes | `src/run-service.ts` |
| Model attempts per obligation | at most 5, within the stored policy ceilings | `src/model-ledger.ts` |

## Retention

- **Hosted evidence** expires `PROOFCI_EVIDENCE_RETENTION_DAYS` after completion. The default is 30 and the range is 1 to 3650. A timer deletes expired objects every minute, independently of webhooks. After expiry, the download returns 410, and the report and property results remain.
- **Runs, reports, publication records, model attempts, and delivery records** are kept indefinitely. There is no automatic pruning in this release. Monitor the database size.
- **Protected stores** keep every reviewed baseline, migration record, and authority event.
- **Backups** contain evidence bundles, so they contain candidate source code. Keep them encrypted at rest and delete them according to your own retention policy. Backups never contain credentials.

## Backup and restoration

A backup is consistent across PostgreSQL, the protected stores, and the evidence bucket. It is taken while every control process is stopped. Each running control process holds a shared PostgreSQL advisory lock. `backup.ts` takes the same lock exclusively and refuses to run while any service holds it. Do not run operator commands that write the protected stores during a backup.

```sh
dc stop control
dc run --rm --no-deps -v /srv/proofci/backups:/srv/proofci/backups control \
  node src/backup.ts create --output /srv/proofci/backups/2026-11-02
dc up -d control
```

The command prints the manifest SHA-256 and a summary. Record both. The backup contains:

- Every ProofCI table, read in one repeatable-read transaction. This covers enrollments, runs and reports, evidence references, pending publications, model policies and attempts (including reservations and uncertain sends), fork approvals, and delivery queues.
- An online SQLite backup of each protected store: active baselines and revisions, migration approvals, maintainer grants, and authority state.
- A copy of every pending or ready evidence object, checked against its recorded SHA-256.

`create` fails if the database contains a table this release does not know, or if a ready evidence object is missing or altered.

`--scope INSTALLATION_ID:REPOSITORY_ID` (repeatable) limits a backup to the listed repositories. It excludes unscoped delivery records. Use it to move a repository to another deployment.

Both backup creation and restoration enforce repository isolation:

- Every row must belong to an in-scope repository.
- Every run-linked row must belong to a run in the backup.
- Every model attempt must belong to its run's repository.
- Every evidence object key must lie under its run's `evidence/INSTALLATION/REPOSITORY/RUN/` prefix.
- Every store must contain only its configured repository.

To check a backup without contacting any service:

```sh
node src/backup.ts verify --input DIR
```

`verify` checks every file digest and rejects unlisted files and symbolic links. It also repeats the isolation checks.

To restore onto a new or rebuilt host:

1. Install as above, with the same release, but do not start `control`. Create an empty database and bucket.
2. Write `pilot.json` for the new host. Every repository in the backup must be configured, with the same repository URL. The configured store paths must not exist yet.
3. Restore and compare:

   ```sh
   dc run --rm --no-deps -v BACKUPS:BACKUPS control node src/backup.ts restore --input BACKUPS/DIR
   dc run --rm --no-deps -v BACKUPS:BACKUPS control node src/backup.ts compare --input BACKUPS/DIR
   dc run --rm --no-deps control node src/preflight.ts
   dc up -d control
   ```

`restore` verifies the backup first. It then installs the stores and evidence objects, refusing to overwrite different contents. Last, it loads the database rows in one transaction. It refuses a non-empty database and a backup from another schema version. `compare` must report `"identical": true`.

After start, the restored service behaves as after a crash, as described in the next section.

## Restart and crash recovery

- A run whose generation was interrupted keeps its lease for up to 30 seconds. The next start then reclaims it with a new generation and verifies it again. Proof construction is repeated only for work that had not been accepted.
- A completed run is never verified again. Its check publication is an outbox entry in PostgreSQL. It is retried until GitHub accepts it, using the persisted report and evidence digest.
- Every model attempt that was `sending` when the service stopped becomes `uncertain` when its run is reclaimed. It is never resent automatically. Unsent reservations stay `reserved` and still count against the ceilings. When the run ends, they are released.
- OAuth sessions live in memory, so maintainers sign in again after a restart.
- A verifier container started before a crash (`docker ps --filter name=proofci-vm-`) is orphaned. It finishes within the 900-second run timeout, and its result is never accepted. Remove it with `docker rm -f` once the service is running again.
- Webhooks delivered while the service is down fail at GitHub. Redeliver them from the App's advanced settings. Reconciliation also lists open pull requests every five minutes.

## Diagnostics

```sh
dc run --rm --no-deps control node src/run-diagnose.ts INSTALLATION_ID REPOSITORY_ID [RUN_ID]
```

Each run is classified into exactly one outcome:

| Outcome | Meaning | Operator action |
| --- | --- | --- |
| `passed` | Every required property verified. | None |
| `proof_failure` | The verifier finished and judged a property `violated` or `unproven`. The check fails on the code, not on the service. | Read `properties[].reason`. `obligation_budget_exhausted` on many runs suggests the host lacks KVM or is overloaded. |
| `infrastructure_failure` | No property judgment was produced, because of a snapshot, VM, store, or GitHub failure. | Read `reason`. Check `dc logs control`, preflight, and GitHub access. |
| `superseded` | The run was cancelled or the candidate changed. | None |
| `in_progress` | Queued or running. | None |

Uncertain model attempts are listed separately under `model.uncertain`, because they can accompany any outcome. Obtain the provider's own usage record, then reconcile the attempt:

```sh
dc run --rm --no-deps control node src/model-attempts.ts reconcile INSTALLATION_ID REPOSITORY_ID REQUEST_ID charged INPUT_TOKENS OUTPUT_TOKENS
dc run --rm --no-deps control node src/model-attempts.ts reconcile INSTALLATION_ID REPOSITORY_ID REQUEST_ID not-processed
```

`publication.pending` and `publication.last_error` show check publications that GitHub has not yet accepted. `node src/run-inspect.ts` lists delivery errors.

## Credential rotation

Rotate a credential at its issuer first, then replace the local file atomically: write a new file and `mv` it into place. Never edit a credential file in place.

- **Webhook secret.** No restart is needed. The service rereads the file on change.
  1. Write the new secret on the first line and the current secret on the second line.
  2. Change the secret in the GitHub App settings.
  3. Once deliveries succeed, remove the second line. After that, the old secret is rejected with 401.
- **App private key.** GitHub allows several active keys.
  1. Generate a new key in the App settings and replace `github-app.pem`.
  2. Run `dc restart control`, and confirm that a check publishes.
  3. Delete the old key in GitHub.

  If the old key is revoked before the restart, GitHub rejects the service's JWTs. Webhook deliveries then stay queued with a delivery error, and nothing is lost. They are processed after the restart.
- **OAuth client secret.** Generate a new client secret, replace `github-client-secret`, run `dc restart control`, sign in once, then delete the old secret in GitHub.
- **Database password.**
  1. Run `ALTER ROLE proofci PASSWORD '...'` through `dc exec postgres psql -U proofci`.
  2. Replace both `postgres-password` and `database-url`.
  3. Run `dc restart control`.
- **Object-store keys.** Change `PROOFCI_S3_ACCESS_KEY` and `PROOFCI_S3_SECRET_KEY` in `.env`, and replace `s3-credentials`. Then run `dc up -d objects control`.
- **Model provider key (optional).** Hosted model calls from the service are disabled, and no provider adapter is wired into it. The portable broker reads `PROOFCI_OPENAI_API_KEY_FILE` at each invocation, so replacing the file rotates the key. The key stays in the broker process, and the isolated worker never receives it.

## Upgrade and rollback

The database records the schema version and the release that last migrated it, in `proofci_deployment`. A release refuses to start in these cases, and prints the reason and the instructions below:

- The schema is newer than the release supports. Downgrades are refused.
- The schema is older than the oldest schema it can upgrade.
- A stored report uses a format other than version 1.

Databases created before release pinning are treated as schema 1 and upgraded in place.

To upgrade:

1. Read the new release's notes and compare its `release.json`.
2. Run preflight with the new image. It reports `schema N will be upgraded to M`.
3. Stop the service and take a backup.
4. Start the new release, and confirm that `SELECT * FROM proofci_deployment` shows the new schema.
5. Run `run-diagnose` and download one recent evidence bundle.

### Roll back an upgrade

Stop the service. Restore the backup taken before the upgrade into a new, empty database and bucket, using the previous release. Then start the previous release. Never point an older release at a database that a newer release has migrated: it refuses to start.

Protected stores are SQLite files whose components migrate them additively. Their reviewed baselines and reports are read with the same version 1 format.

## Tested enforcement configuration

A check enforces nothing until the branch policy requires it. Configure the protected branch as described in [Pull request lifecycle](../docs/pull-request-lifecycle.md#required-merge-policy):

- Require the `ProofCI` check, restricted to this App.
- Require branches to be up to date, or use a merge queue.
- Include administrators.
- Grant no bypass actors.

The operational exercise establishes the following:

- The check is created on GitHub's test merge commit, with this App's identity and the run ID as `external_id`.
- A blocked or failed run publishes the `failure` conclusion.
- A publication that GitHub rejects remains pending and is retried without verifying again.

The exercise used a GitHub API simulator, not github.com. Live merge enforcement on a protected branch, including bypass behavior, is the subject of ticket 24 and has not been demonstrated by this ticket.

## Support limits

- One host and one control process. Several processes can share the database, because the lock is shared, but that configuration has not been exercised.
- `linux/arm64` with KVM only. The Apple container runtime path is for local pilots on macOS.
- GitHub.com only. GitHub Enterprise Server is not supported.
- Hosted model assistance is disabled, and fork assistance only records approvals.
- Backups are offline and require stopping `control`. Point-in-time recovery is not provided.
- Single-region object storage on a local volume. For durability, back the `objects` volume with redundant storage, or point `PROOFCI_S3_ENDPOINT` at a managed S3-compatible service with versioning disabled.

## Release pinning

`deploy/release.json` lists everything a release depends on:

- **Image digests:** Node.js base, Docker CLI, PostgreSQL, versitygw, the verifier VM image, and the validator image.
- **Debian package snapshot**, used when building the control image.
- **npm lockfile digest.**
- **Verifier digests:** the Lean toolchain, the trust policy, the core dependency list, and the resource limits.

`test/release.test.ts` fails if a deployment file or code constant drifts from the manifest, or if any image reference is not pinned by digest. To check a running deployment, compare `docker compose images` with `release.json`, and run preflight. Preflight confirms the verifier image ID that the launcher will require.
