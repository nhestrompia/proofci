<img src="assets/icon.svg" width="64" height="64" alt="">

# proofci

ProofCI aims to preserve approved correctness contracts across code changes through AI-assisted proof construction and Lean 4 validation.

The verifier supports a restricted Lean source language and approved contracts.

- [Feasibility, architecture, and CI integration](docs/research/ci-and-architecture.md)
- [Verification trust model and language support](docs/research/verification-feasibility.md)
- [MVP implementation spec](docs/specs/proofci-mvp.md)
- [Pull request lifecycle and merge policy](docs/pull-request-lifecycle.md)

## GitHub enrollment

The Node.js 24 control service stores selected installation and repository IDs in PostgreSQL. The scheduler checks the stored selection and live App access before dispatch. Maintainers select a repository after signing in; enrollment, removal, and policy inspection recheck their current repository authority. GitHub App and user tokens remain in the control process. Sessions are held in memory and expire on restart.

Register a GitHub App with repository permissions for contents read, pull requests read, checks write, and metadata read. The service rejects contents or pull-request write access. Administration read is optional and is intended only for policy inspection. Install it on the selected repository. Configure an OAuth callback at `https://YOUR-ORIGIN/oauth/callback`. A pilot App was installed on `nhestrompia/proofci` and tested for repository-scoped token issuance, OAuth maintainer enrollment, rejection of an unselected public repository, and denial during an actual suspension followed by successful restoration.

Set `DATABASE_URL`, `GITHUB_APP_ID`, `GITHUB_CLIENT_ID`, `GITHUB_CLIENT_SECRET`, `GITHUB_PRIVATE_KEY_FILE`, and `PROOFCI_ORIGIN`. Set `GITHUB_WEBHOOK_SECRET` to the same high-entropy secret configured on the App webhook and route the public HTTPS webhook URL to `/webhooks/github`. GitHub delivers installation and installation-repository events automatically when the App webhook is active. The origin must use HTTPS, except `http://127.0.0.1:3000` may be used for a local pilot. Run `npm ci`, then `npm start`. The service listens on localhost port 3000, or `PORT`. Remote use requires an HTTPS reverse proxy with request rate limits. Keep the private key file and environment secrets accessible only to the control service.

Run `npm test` and `npm run typecheck`. Set `PROOFCI_TEST_DATABASE_URL` to an isolated PostgreSQL database to run the persistence test. The test creates a `proofci_repository_selections` table and writes test IDs. Set `PROOFCI_TEST_SERVICE_URL` to a separately running test service to run the HTTP boundary test. Set `PROOFCI_TEST_WEBHOOK_SECRET` to its webhook secret to include the signed-webhook HTTP test. To run the live GitHub test, set `PROOFCI_TEST_GITHUB_KEY_FILE`, `PROOFCI_TEST_GITHUB_APP_ID`, `PROOFCI_TEST_GITHUB_INSTALLATION_ID`, `PROOFCI_TEST_GITHUB_REPOSITORY_ID`, and `PROOFCI_TEST_GITHUB_UNSELECTED_REPOSITORY_ID`.

Enrollment does not activate contracts or protect merges. Policy inspection checks available default-branch protection and active rules. Missing permissions and unsupported rulesets leave the required-check configuration unconfirmed. A confirmed configuration means GitHub reports the expected App check, strict freshness, and administrator enforcement; it does not establish that checks are published or that any contract is active. Live repository removal, uninstall, and merge-enforcement tests have not yet been completed. Access checks fail closed while a repository is unavailable. A verified installation deletion, suspension, or repository-removal webhook clears the affected enrollment; an unambiguous revocation observed during an access check also clears it. Configure and monitor webhook delivery and redeliver failures: a removal and restoration between checks cannot be detected if its webhook is missed. The local pilot App webhook is currently disabled and needs a publicly reachable HTTPS endpoint before these events can be received. Configure a required check restricted to the expected App and require fresh merge results or a merge queue. Administration read may be needed to inspect branch protection.

## Run the verification pilot

The pilot schedules nonenforcing head-snapshot runs for configured branches and
publishes a `ProofCI` check for pull requests on GitHub's test-merge commit. It
does not yet support merge queue candidates or enable hosted AI. Use a Linux ARM64 host with KVM,
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

Before enrolling, initialize the authority in the same protected store. Use the
exact current managed branch head and the GitHub numeric user ID of an initial
trusted maintainer. Bootstrap only after reviewing both values:

```sh
python3 portable/authority.py bootstrap --store /absolute/protected/baselines.db \
  --repository https://github.com/OWNER/REPOSITORY.git --ref refs/heads/main \
  --head FULL_COMMIT_SHA --actor NUMERIC_GITHUB_USER_ID
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

Set `PROOFCI_LOCAL_PILOT_CONFIG` to the absolute path of this file. Configure
the GitHub App and service as described above, subscribe the App webhook to
push, pull request, check run, and check suite events, and enroll the repository. Reconciliation checks
configured branches and open pull requests every five minutes. A missing active
baseline or revoked installation cannot schedule a run. The check stays pending
or fails unless the final validator accepts every required obligation. Configure
the required `ProofCI` check from this App and require up-to-date branches before
relying on it as a gate. Merge queues are not supported yet. See
[Pull request lifecycle](docs/pull-request-lifecycle.md) for how updates,
retargeting, closure, reruns, and cancellation affect runs, and for the required
merge policy and its administrator bypass limitations.

The check links to `/runs/INSTALLATION_ID/REPOSITORY_ID/RUN_ID`. A signed-in
maintainer can read the full report there and download its immutable replay
bundle from the same URL with `/evidence` appended. The report records the bundle
SHA-256; pass that digest to the replay command in the portable verifier guide.
Snapshot fetching includes the history needed for replay and rejects a staged
repository larger than 256 MiB. Evidence export rejects shallow repositories.
Unresolved merge candidates are visible to maintainers at
`/pulls/INSTALLATION_ID/REPOSITORY_ID/PULL_NUMBER`. Check publication retries
from the database without rerunning proof work. Newly hosted bundles are stored
in the configured S3-compatible bucket. Older database-stored bundles remain
available through their existing links until the configured retention deadline;
the cleanup timer also removes expired database-stored bundles.

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

Use full commit IDs and the active baseline SHA-256. Set `PROOFCI_LOCAL_PILOT_CONFIG`
for managed repositories so the run binds the authority revision. The command prints the run ID. The worker rechecks the selected installation, repository access, and active
baseline before executing. This command does not publish a GitHub check.

These commands use `DATABASE_URL`. Set `PROOFCI_LOCAL_PILOT_CONFIG` when
inspecting managed runs so their authority revision can be checked. Without it,
managed completed runs are reported as inapplicable. Limit access to the database
and pilot configuration to trusted operators. Cancellation persists, and duplicate
notifications do not restart a cancelled candidate. A rerun of the `ProofCI`
check by an actor with current write access starts a new attempt for the PR's
current inputs.

## Model attempt recovery

Hosted model calls remain disabled. The control service records every model
attempt in PostgreSQL before contacting a provider so that a restart cannot
lose usage or silently repeat a paid call. No provider adapter is wired into the
service yet. A repository has no model policy until an operator stores one, and
a stored policy is disabled unless it sets `enabled`.

Each logical attempt is identified by its run, obligation, and attempt number,
and its request ID is derived from those values. A duplicate or concurrent
dispatch of the same attempt converges on the same record. The broker moves an
attempt through these states, committing each one before the next step:

- `reserved`: the worst-case tokens and cost are held, and the provider has not been contacted.
- `sending`: recorded immediately before the request. From here the provider may have received it.
- `settled`: the exact usage and response are recorded.
- `failed`: the call finished without a usable response. Usage is exact only when the provider confirmed it did not process the request.
- `uncertain`: no outcome was recorded after `sending`, for example after a timeout, a lost response, or a crash.
- `reconciled`: an operator recorded the provider's real outcome for an uncertain attempt.
- `released`: the reservation was never sent.

When a run generation is reclaimed after a restart, every attempt that the
previous generation left in `sending` becomes `uncertain`. An uncertain attempt
is resent only if the provider adapter declares idempotency for the same request
ID, meaning a retry returns the original outcome without a second charge. The
OpenAI Chat Completions request used by the portable adapter has no such
guarantee, so it must be treated as non-idempotent. A response stored before a
crash is validated again by the next generation, not requested again.

Run and repository ceilings are calculated from the durable attempt rows, not
from process memory. Recovery, reruns, and new runs therefore cannot reset them.
Settled attempts count at their exact usage. Reserved, in-flight, uncertain, and
failed attempts without known usage count at their full reservation. A new
reservation is refused when that conservative total would exceed a ceiling. The
final run report includes `usage.model`, which lists each attempt with exact
usage where known, its upper-bound charge, and counts of uncertain, failed, and
unknown-usage attempts.

The send transition takes a lock on the leased run, the repository selection, and
the model policy. Cancellation, a superseding candidate, removed repository
access, disabled assistance, and revoked source consent are all durable, and
each prevents any later send. A response that arrives after its generation lost
the run is recorded for accounting and marked late. It can never satisfy a newer
generation. Publication retries reuse the persisted report and make no model
calls.

Manage the policy and inspect or reconcile attempts with the operator command:

```sh
node src/model-attempts.ts policy INSTALLATION_ID REPOSITORY_ID policy.json
node src/model-attempts.ts revoke-consent INSTALLATION_ID REPOSITORY_ID
node src/model-attempts.ts disable INSTALLATION_ID REPOSITORY_ID
node src/model-attempts.ts inspect INSTALLATION_ID REPOSITORY_ID RUN_ID
node src/model-attempts.ts reconcile INSTALLATION_ID REPOSITORY_ID REQUEST_ID charged INPUT_TOKENS OUTPUT_TOKENS
node src/model-attempts.ts reconcile INSTALLATION_ID REPOSITORY_ID REQUEST_ID not-processed
```

A policy file has this shape. Rates are microdollars per million tokens, and
`maxAttemptsPerObligation` is at most 5:

```json
{"enabled": false, "private": true, "sourceConsent": false, "limits": {
  "contextBytes": 65536, "maxOutputPerCall": 2048,
  "inputMicrosPerMillion": 150000, "outputMicrosPerMillion": 600000,
  "maxAttemptsPerObligation": 5,
  "run": {"inputTokens": 200000, "outputTokens": 20000, "costMicros": 100000},
  "repository": {"inputTokens": 2000000, "outputTokens": 200000, "costMicros": 1000000}}}
```

Reconcile an uncertain attempt only from the provider's own usage records.
Reconciliation never imports a response. The recovery and fault-injection tests
in `test/model-recovery.test.ts` use `PROOFCI_TEST_DATABASE_URL` and a
deterministic model stub. They cover reservation, send, response persistence,
validation, and publication handoff.

## Migrate a baseline

The protected SQLite store is the authority for migration grants, the managed
branch head, enrollment fences, and baseline activation. Grant or revoke a
maintainer through this authority using their numeric GitHub user ID:

```sh
python3 portable/authority.py grant --store STORE --repository REPOSITORY --actor USER_ID
python3 portable/authority.py revoke --store STORE --repository REPOSITORY --actor USER_ID
```

Grant and revoke operations must be restricted to trusted operators. Revoke in
the authority before removing GitHub access. An authority revision changes on
revocation, enrollment changes, managed head changes, and activation. In-flight
migration approvals and completed run results from an older revision are no
longer applicable, even if the original values are later restored.

All changes to the managed GitHub ref must go through the gateway. Configure
GitHub branch restrictions so only its dedicated credential can update the ref,
and give no other actor bypass permission. Restrict administration of those
rules, repository membership, the gateway credential, the SQLite store and its
parent directories to trusted operators. All service instances must share this
single protected store and the same pilot configuration. GitHub administrators
and anyone who can write the protected store remain trusted. An out-of-band
GitHub permission change or branch push is not serialized by the local store;
without these restrictions the activation guarantee does not hold.

The gateway uses a protected local Git object store containing both commits.
Provide its credential through `PROOFCI_GATEWAY_TOKEN`, using a secret manager or
another protected environment. Advance only a fast-forward commit:

```sh
python3 portable/authority_gateway.py advance --store STORE --repository REPOSITORY \
  --git-dir /absolute/protected/repository.git --ref refs/heads/main \
  --expected CURRENT_COMMIT_SHA --head NEW_COMMIT_SHA
```

The gateway records a pending change before contacting GitHub. Pending changes
block activation and managed runs. After an interruption, `recover` finishes a
change only when GitHub reports its target head. If the old head remains, the
push may still be in flight, so the authority stays blocked. An unexpected head
quarantines the authority. Do not clear either state by editing the database;
restoring service requires an operator to establish an external fence against
all uncertain writes and re-provision the authority from verified state.

Sign in as a current repository maintainer and enroll the repository. Configure
it in the local pilot and activate its initial baseline first. On the enrollment
page, select the repository and enter the exact configured branch head, the
current reviewed manifest SHA-256, and the replacement manifest SHA-256. The
replacement manifest must be committed at the active manifest path in that head.
The form authorizes a policy change and starts isolated verification. Obtain the
current manifest digest from `python3 portable/baselines.py lookup --store STORE`
and calculate the replacement digest from the committed manifest bytes. Review
the replacement and the retired guarantees before submitting the form.

The service checks maintainer access and enrollment again after verification.
It activates the replacement only if the configured branch head, enrollment,
maintainer, and previous baseline still match. The protected SQLite store keeps
the authorization, the verification report, and the list of guarantee changes.
The report identifies removed guarantees as retired and states that policy
changed. An unsuccessful or interrupted migration does not activate the
replacement. Ordinary runs continue using the active baseline until activation.
The service must have the same isolated VM prerequisites as the head-snapshot
pilot. This operation does not publish a GitHub check or protect merges.

GitHub access and head are checked again immediately before activation. The
transaction also checks the authority's grant, head, enrollment state, and
revision. The authority controls those values only under the operator and GitHub
restrictions above. This pilot has not configured those restrictions on the
live demo branch and does not claim production merge enforcement.
## Fork verification and assistance

Subscribe the App to pull request events as well as push events. The service
queues signed pull request observations for enrolled pilot repositories, then
resolves the PR through the destination installation. It records the source and
destination repository IDs and immutable head and base. It fetches the snapshot
from the destination and runs the existing isolated verifier with no provider,
installation, or signing credentials in the worker. Results are nonenforcing;
this pilot does not publish a GitHub check. Reconciliation lists open PRs and
revisits applicable runs every five minutes. Configure webhook redelivery for
failures.

Fork proof assistance is off. Hosted provider calls must remain disabled until
durable request recovery and accounting have passed their release gate. The
service never sends candidate source to a model provider. An operator can set
`assistanceQuotaMicros` in the protected pilot configuration, in microdollars;
it defaults to zero. With a positive quota, a signed-in current maintainer can
review a fork run at `/fork-assistance?repository=INSTALLATION_ID:REPOSITORY_ID&number=PR_NUMBER`.
The approval form shows the exact inputs and requests explicit source-transmission
consent. Approval records are scoped to the selection, source and destination,
head, base, baseline revision, resource policy and quota. For an existing store,
run `python3 portable/baselines.py initialize --store /absolute/protected/baselines.db`
as its trusted owner before recording approvals. Without revision tracking,
fork assistance remains denied. A new PR notification or destination push,
superseding candidate, explicit revocation or selection removal invalidates the
record. A changed policy or current input does not match an old record. Approval
only produces a deferred decision while the hosted provider gate is closed; it
is not a broker reservation or a claim that quota accounting is ready.

The dispatch boundary is the database transaction that checks the active run and
selection and starts the isolated process. Cancellation, removal, and accepted
PR updates lock or invalidate those records, so an update ordered before that
boundary prevents process start. Work already started is aborted when its lease
renewal notices cancellation or removal, and cannot publish a late completion.
A GitHub change not yet observed by a webhook or reconciliation cannot be acted
on; the executor also rechecks GitHub and the baseline before dispatch and
before accepting a result. There are no in-flight hosted model calls in this
pilot. The durable model ledger described in
[Model attempt recovery](#model-attempt-recovery) defines the reservation and
in-flight revocation boundary that a hosted broker must use; the provider gate
remains closed until a provider adapter is reviewed and wired to it.

The opt-in fork acceptance tests require the pinned verifier image and a working
VM runtime. Build the separate probe image with
`docker buildx build --platform linux/arm64 -t proofci-ticket16-probe --load worker-probe`, then run
`PROOFCI_TEST_FORK_ISOLATION=1 node --test test/fork-isolation-linux.test.ts`.
The test submits an educational local Git fork containing proof code that
attempts to read host, credential and other-repository cache sentinels and to
reach 1.1.1.1 on port 443. The test first checks that endpoint from the host.
The proof's checks run in the worker's construction sandbox, then intentionally
fail with a test marker. The test also runs a separate fixed-guest probe that
checks those access categories and the container socket. It is a different
guest from the verifier.

`PROOFCI_TEST_LIVE_FORK=1 node --test test/fork-live.test.ts` fetches a public
GitHub fork PR and runs it against a temporary fixture baseline. The current
fixture binds a JSON file, so the expected result is `unsupported_semantics` and
the public result blocks. Set `PROOFCI_TEST_DATABASE_URL` to an isolated test
database. The test signs a local webhook and uses the local `gh` authentication
only for snapshot staging. It requires network access and an open test PR; its
installation authorization is a test fixture, so it does not establish GitHub
App installation authorization or merge-check enforcement.

The GitHub check publisher rechecks the local authority revision before a check
update and reconciliation marks older revisions for revalidation. These checks
are not atomic with a GitHub API request: an in-flight or previously published
success can remain visible after a revision change. Do not rely on the published
check as an enforcing merge gate for managed migrations until the merge path
itself is fenced by the authority and existing checks have been invalidated.
