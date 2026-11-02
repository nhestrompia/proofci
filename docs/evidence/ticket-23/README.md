# Ticket 23 self-hosted pilot exercise

[`deploy/exercise/run.ts`](../../../deploy/exercise/run.ts) produced [`exercise.json`](exercise.json), [`exercise.md`](exercise.md), and [`diagnostics.json`](diagnostics.json). It ran from a clean commit on an ARM64 macOS host, using the Docker Desktop Linux VM (`linux/arm64`) as the deployment host. Each step records its own evidence in `exercise.json`.

## Host limitation: no KVM

This host has no `/dev/kvm`, so the verifier VM ran under QEMU software emulation. Every real Lean run therefore reported `unproven` with `obligation_budget_exhausted`, because the one-line obligation took more than its fixed 120 s budget. Consequences:

- The runs are real, Lean-backed, authoritative, and replayable. The replay `reproduced` the same result in a fresh VM.
- The exercise did **not** produce a passing check. A passing PR run needs a KVM host, as `deploy/README.md` states.
- The trust policy and budgets were not changed.

## Acceptance criteria

### 1. Clean Linux deployment and a real Lean-backed PR run

Established:

- The pinned compose stack ran from an empty state: the control image, PostgreSQL 16.11, versitygw, and the bucket initializer.
- The App key, OAuth client secret, webhook secret, database URL, and S3 credentials were provided as files.
- Reviewed baselines were activated through `portable/baselines.py activate` with the pinned validator.
- Preflight passed, and a maintainer enrolled two repositories through OAuth.
- A signed `pull_request` webhook produced a run on the real Git test merge commit. The run used the pinned Lean VM, published a `ProofCI` check on that merge commit, and stored the evidence in S3.
- The maintainer downloaded the evidence. Downloads through the other repository's path, or without a session, returned 404.
- The bundle replayed in a fresh VM.

Not established: GitHub was the local simulator ([`deploy/exercise/README.md`](../../../deploy/exercise/README.md)), not github.com.

### 2. Backup and restoration

Established:

- A full backup of the crashed deployment was taken while the service was stopped. It held:
  - 2 active baselines with revisions and authority revisions, and 2 maintainer grants.
  - Runs in the completed, running, and cancelled states, and evidence references with their objects.
  - 2 model reservations (one `sending`, one `reserved`) and pending publications.
- A scoped backup omitted the other repository's rows and store.
- Altered content was rejected. Backup was refused while the service ran.
- The restore went into new volumes. It matched the backup row for row, and the stores matched.
- In the restored deployment:
  - Evidence downloaded with the original digest and stayed repository-scoped.
  - The pending publication completed without reverification.
  - The in-flight attempt became `uncertain` without being resent.

Not established: no fork approval or migration records existed in this exercise. Their tables and SQLite rows are included by the same mechanism, and `test/deployment.test.ts` covers the round trip.

### 3. Restart and recovery

Established, after a `SIGKILL` during verification:

- A completed run's failed publication was retried from PostgreSQL. The run's generation, start and completion times, report, and evidence were unchanged.
- The in-flight model attempt became `uncertain` with `send_count` 1, and the unsent reservation stayed `reserved`.
- The interrupted run was reclaimed by a new generation.
- Diagnostics listed the uncertain attempt with reconciliation instructions, and the operator reconciled it.
- Closing the PR released the reservation without any send.

### 4. Credential rotation

Established:

- **Webhook secret:** during rotation, both secrets were accepted; afterwards, only the new one, with no restart.
- **App key and OAuth client secret:** after GitHub-side rotation, the old ones failed. JWTs were rejected, the delivery stayed queued, and sign-in failed. After replacing the files and restarting, both recovered, and the queued work published a check.
- **Isolation:** while a run executed, the dispatcher's environment held only `PATH`, `HOME`, `PYTHONDONTWRITEBYTECODE`, and `TMPDIR`. The VM container had only `PATH`, network `none`, and read-only mounts of the snapshot, baseline, and envelope.

Not established: model access. The service has no provider adapter, and hosted calls are disabled. `PROOFCI_OPENAI_API_KEY_FILE` rotation in the portable broker is covered by `portable/test_model_credentials.py`, not by a live provider call.

### 5. Upgrade and diagnostics

Established:

- A database written by the previous release's code (`origin/main` at the branch point) was announced by preflight and upgraded in place to schema 2. Its reports were kept.
- A database recorded by a newer release was refused with downgrade and rollback instructions.
- A stored report in format version 2 was refused with instructions.
- Diagnostics separated `proof_failure` (the budget-exhausted runs), `infrastructure_failure` (a merge commit missing from the repository), and `superseded` runs.

### 6. Documentation and license

[`deploy/README.md`](../../../deploy/README.md) documents:

- Prerequisites and resource limits.
- Retention.
- The enforcement configuration, and what about it was exercised.
- Support limits.
- Release pinning ([`deploy/release.json`](../../../deploy/release.json), checked by `test/release.test.ts`).

License: the maintainer approved the MIT License after the exercise ran. It is in [`LICENSE`](../../../LICENSE), recorded in `release.json` and `package.json`, and shipped in the control image. `test/release.test.ts` checks all of these.

## Defect found and fixed: duplicate runs from the publication freshness race

The exercise counted runs that were cancelled and then re-admitted with identical inputs (see `known defect` in `exercise.json`, count 8). The sequence:

1. The publication worker claims a new run's publication while the run is `queued`.
2. The run moves to `running` before the freshness check. The run-change trigger bumps the publication revision, so `publicationCurrent` fails, and `markPublicationUnresolved` sets `needs_revalidation`.
3. Within 5 s, baseline reconciliation re-delivers the pull request with `invalidate=true`.
4. That cancels the in-flight run and admits a new one.

On fast-failing runs this repeated until a run finished between reconciliation ticks. Each cancelled run discarded its verification work. It did not produce a wrong result, because only the final applicable run publishes.

Fix (in `src/run-store.ts` and `src/publication-worker.ts`): `markPublicationUnresolved` now marks only a claim that still holds the latest revision, and reports whether it did. A superseded claim leaves the check alone and lets the newer revision publish. A candidate that really is stale (a different merge commit, baseline, or authority revision) is still marked and invalidated as before.

Regression tests: `test/run-store.test.ts` ("a run starting during publication…", against PostgreSQL) fails without the fix, because the check was invalidated and the run re-delivered. `test/publication-worker.test.ts` covers the superseded-revision path.

The recorded exercise ran before the fix, so its count of 8 describes the old behavior. The exercise was not re-run after the fix.
