<img src="assets/icon.svg" width="64" height="64" alt="">

# proofci

ProofCI aims to preserve approved correctness contracts across code changes through AI-assisted proof construction and Lean 4 validation.

The project is in the research and specification stage. No verifier is implemented yet.

- [Feasibility, architecture, and CI integration](docs/research/ci-and-architecture.md)
- [Verification trust model and language support](docs/research/verification-feasibility.md)
- [MVP implementation spec](docs/specs/proofci-mvp.md)

## GitHub enrollment

The Node.js 24 control service stores selected installation and repository IDs in PostgreSQL. The repository-authorization interface checks the stored selection and live App access. The scheduler is a separate, not yet implemented component and must call this interface before dispatch. Maintainers select a repository after signing in; enrollment, removal, and policy inspection recheck their current repository authority. GitHub App and user tokens remain in the control process. Sessions are held in memory and expire on restart.

Register a GitHub App with repository permissions for contents read, pull requests read, checks write, and metadata read. The service rejects contents or pull-request write access. Administration read is optional and is intended only for policy inspection. Install it on the selected repository. Configure an OAuth callback at `https://YOUR-ORIGIN/oauth/callback`. A pilot App was installed on `nhestrompia/proofci` and tested for repository-scoped token issuance, OAuth maintainer enrollment, rejection of an unselected public repository, and denial during an actual suspension followed by successful restoration.

Set `DATABASE_URL`, `GITHUB_APP_ID`, `GITHUB_CLIENT_ID`, `GITHUB_CLIENT_SECRET`, `GITHUB_PRIVATE_KEY_FILE`, and `PROOFCI_ORIGIN`. Set `GITHUB_WEBHOOK_SECRET` to the same high-entropy secret configured on the App webhook and route the public HTTPS webhook URL to `/webhooks/github`. GitHub delivers installation and installation-repository events automatically when the App webhook is active. The origin must use HTTPS, except `http://127.0.0.1:3000` may be used for a local pilot. Run `npm ci`, then `npm start`. The service listens on localhost port 3000, or `PORT`. Remote use requires an HTTPS reverse proxy with request rate limits. Keep the private key file and environment secrets accessible only to the control service.

Run `npm test` and `npm run typecheck`. Set `PROOFCI_TEST_DATABASE_URL` to an isolated PostgreSQL database to run the persistence test. The test creates a `proofci_repository_selections` table and writes test IDs. Set `PROOFCI_TEST_SERVICE_URL` to a separately running test service to run the HTTP boundary test. Set `PROOFCI_TEST_WEBHOOK_SECRET` to its webhook secret to include the signed-webhook HTTP test. To run the live GitHub test, set `PROOFCI_TEST_GITHUB_KEY_FILE`, `PROOFCI_TEST_GITHUB_APP_ID`, `PROOFCI_TEST_GITHUB_INSTALLATION_ID`, `PROOFCI_TEST_GITHUB_REPOSITORY_ID`, and `PROOFCI_TEST_GITHUB_UNSELECTED_REPOSITORY_ID`.

Enrollment does not activate contracts or protect merges. Policy inspection checks available default-branch protection and active rules. Missing permissions and unsupported rulesets leave the required-check configuration unconfirmed. A confirmed configuration means GitHub reports the expected App check, strict freshness, and administrator enforcement; it does not establish that checks are published or that any contract is active. Live repository removal, uninstall, and merge-enforcement tests have not yet been completed. Access checks fail closed while a repository is unavailable. A verified installation deletion, suspension, or repository-removal webhook clears the affected enrollment; an unambiguous revocation observed during an access check also clears it. Configure and monitor webhook delivery and redeliver failures: a removal and restoration between checks cannot be detected if its webhook is missed. The local pilot App webhook is currently disabled and needs a publicly reachable HTTPS endpoint before these events can be received. Configure a required check restricted to the expected App and require fresh merge results or a merge queue. Administration read may be needed to inspect branch protection.

## Run the head-snapshot pilot

The pilot schedules nonenforcing runs for explicitly configured branches. It does
not publish GitHub checks or enable hosted AI. Use a Linux ARM64 host with KVM,
Docker, PostgreSQL, and the pinned verifier images. Software emulation can exceed
the verifier's fixed obligation budget. Build the verifier image as described in
[the portable verifier guide](portable/README.md), tag it
`proofci-ticket12-verifier`, and build the VM image:

```sh
docker buildx build --platform linux/arm64 -f worker-probe/Dockerfile \
  -t proofci-worker-probe --load worker-probe
docker buildx build --provenance=false --build-arg SOURCE_DATE_EPOCH=0 \
  --platform linux/arm64 -f worker-probe/Dockerfile.verify \
  -t proofci-vm-verifier --load .
docker image inspect --format '{{.Id}}' proofci-vm-verifier
```

The image ID must match `VM_IMAGE_ID` in `portable/vm_container.py`; otherwise
the launcher refuses to run. Supply the exact reviewed image when a local build
has a different ID. Run `PROOFCI_TEST_VM=1 python3 -m unittest discover -s portable -p test_vm_linux.py`
to check the VM and Lean on the host.

On an Apple Silicon Mac with nested virtualization, an operator can use the
Apple container runtime for a local pilot. Load the pinned VM image into that
runtime, then set `PROOFCI_APPLE_RUNTIME` to its absolute executable path,
`PROOFCI_APPLE_KERNEL` to the absolute path of a KVM-enabled Linux kernel,
and `PROOFCI_APPLE_KERNEL_SHA256` to that kernel's SHA-256 digest. The launcher
checks the image and kernel identities and runs the container without network
access. The operator must protect these settings and the kernel file.

Activate a reviewed baseline using the procedure in
[Reviewed local baselines](portable/README.md#reviewed-local-baselines). Keep
its SQLite store outside the candidate checkout. Create a service-owned JSON
file that is not writable by other users:

```json
[
  {
    "installationId": 123,
    "repositoryId": 456,
    "store": "/absolute/protected/baselines.db",
    "repository": "https://github.com/OWNER/REPOSITORY.git",
    "ref": "refs/heads/main"
  }
]
```

Set `PROOFCI_LOCAL_PILOT_CONFIG` to the absolute path of this file. Set
`PROOFCI_S3_BUCKET` and `PROOFCI_S3_REGION` for a private, unversioned
S3-compatible bucket. The service uses the AWS SDK credential provider chain;
keep those credentials in the control process and give it object read, write,
delete, and bucket versioning inspection permissions. For another S3-compatible
server, set `PROOFCI_S3_ENDPOINT` to its endpoint. Do not grant candidate
workers access to the bucket. Versioned or versioning-suspended buckets are
rejected because deleting only the current version would retain evidence.

Completed verification reports contain an evidence link, SHA-256 digest, and
expiration time. Sign in as a current repository maintainer to download the
bundle. Replay it with the digest from the report using the commands in the
[portable guide](portable/README.md#export-and-replay-evidence). The service
checks access again for each download. It returns an expiration message after
the deadline, even if cleanup is delayed. Expiration removes the hosted bundle,
not the historical report or its property outcomes. `PROOFCI_EVIDENCE_RETENTION_DAYS`
sets the retention period from completion; it defaults to 30 days. A service
timer deletes expired objects and abandoned uploads independently of webhooks.

To exercise the storage boundary, set `PROOFCI_TEST_DATABASE_URL` to an isolated
PostgreSQL database and `PROOFCI_TEST_S3_ENDPOINT` to an isolated S3-compatible
test server, then run `node --test test/evidence-store.test.ts`. The test creates
and removes its own schema and bucket. To include a real verifier result, run the
packaged `test_service_execute_linux.py` test with `PROOFCI_TEST_PACKAGED=1` and
`PROOFCI_TEST_HOSTED_BUNDLE` set to an output path. Set the same path when running
the storage test. It downloads the persisted bundle and replays it with the
pinned verifier image.

Configure the GitHub App and service as described above, subscribe the App webhook to
push events, and enroll the repository. Reconciliation checks configured
branches every five minutes and recovers missed push events. A missing active
baseline or revoked installation cannot schedule a run.

Inspect runs and deliveries, or cancel a run, using the enrollment scope:

```sh
node src/run-inspect.ts INSTALLATION_ID REPOSITORY_ID
node src/run-inspect.ts INSTALLATION_ID REPOSITORY_ID RUN_ID
node src/run-cancel.ts INSTALLATION_ID REPOSITORY_ID RUN_ID
```

An operator with access to the service database can also admit an immutable
candidate without a webhook:

```sh
node src/run-dispatch.ts INSTALLATION_ID REPOSITORY_ID HEAD BASE BASELINE_SHA256 LANE
```

Use full commit IDs and the active baseline SHA-256. The command prints the run
ID. The worker rechecks the selected installation, repository access, and active
baseline before executing. This command does not publish a GitHub check.

These commands use `DATABASE_URL`. Limit access to the database and pilot
configuration to trusted operators. Cancellation persists, and duplicate
notifications do not restart a cancelled candidate.
