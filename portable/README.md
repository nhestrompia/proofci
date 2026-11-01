# Portable verification

The CLI checks every required and advisory obligation in a protected baseline.
It uses the fixed source-binding validator. Model assistance is optional. The
supported Lean language and trust assumptions are documented in
[the validator README](../experiments/source-binding/README.md). The baseline,
the verifier checkout, the Docker host and the supplied toolchain must be
protected from the candidate being checked. This local distribution is not
licensed for public distribution; a maintainer license decision is still needed.

The input is a clean Git checkout at the exact full commit named by `head`.
The origin URL must equal `repository`; `base` must be a full commit ID present
in the repository. Candidate and submitted evidence files must be committed, and their
bytes must match the commit. Keep the baseline outside the candidate checkout.
The baseline digest in the envelope identifies the exact approved baseline.
Approval and protected delivery of that digest are the caller's responsibility.

A version 1 baseline has this shape:

```json
{
  "version": 1,
  "candidate": "src/candidate.lean",
  "obligations": [
    {
      "id": "increment",
      "policy": "required",
      "contract": "contracts/increment.json",
      "contract_sha256": "<sha256 of contract bytes>",
      "evidence": "proofs/increment",
      "refutation": "proofs/increment-refutation"
    }
  ]
}
```

Contract paths are relative to the baseline directory; candidate and evidence
paths are relative to the checkout. Evidence uses the
[bundle format](../experiments/source-binding/evidence-format.md). IDs must be
unique and at least one obligation must be required. The optional `refutation`
path supplies a second independent evidence bundle. Both submissions are
validated, and contradictory accepted evidence is an error with both references
retained. Required violations block; advisory violations remain visible.

A version 1 envelope contains `version`, `repository`, `head`, `base`,
`candidate_sha256`, `baseline_sha256`, `dependency`, `toolchain`,
`trust_policy`, and `resource_policy`. The resource policy has positive
integer `timeout_seconds`, `cpu_seconds`, `memory_bytes`, `file_bytes`,
and `processes`. The pinned identity values can be printed from this checkout:

```sh
python3 -c 'import sys; sys.path.insert(0,"portable"); import proofci; print("dependency", proofci.digest(proofci.VALIDATOR / "core-dependencies.json")); print("toolchain", proofci.TOOLCHAIN_SHA256); print("trust_policy", proofci.policy_digest())'
```

Build the local-only Linux image using the pinned ARM64 Lean distribution and
extracted bubblewrap package from the
[source-binding setup](../experiments/source-binding/README.md):

```sh
docker buildx build --provenance=false --build-arg SOURCE_DATE_EPOCH=0 \
  --output type=docker,dest=proofci-validator.tar,rewrite-timestamp=true --platform linux/arm64 \
  --build-context lean=/path/to/lean-4.35.0-linux_aarch64 \
  --build-context bubblewrap=/path/to/extracted-bubblewrap \
  -f portable/Dockerfile -t proofci-validator-local .
docker load -i proofci-validator.tar
```

The build checks the tool digests. The launcher rejects an image whose ID does
not match the pinned distribution. Run as an unprivileged user with Docker:

```sh
python3 portable/container.py --envelope run.json --baseline protected/baseline.json \
  --snapshot checkout --report report.json
```

The trusted operator dispatch command adds the worker boundary and a separate
final-validation pass. It never accepts the worker's claimed JSON as the
result; the final pass rechecks the immutable snapshot and protected baseline:

```sh
python3 portable/dispatch.py --envelope run.json --baseline protected/baseline.json \
  --snapshot checkout --report report.json
```

Dispatch is evidence-only: both the worker and final-validation phases use
`--validator-only` and never turn uncommitted proof suggestions into accepted
evidence. Use `assist.py` separately for bounded proof construction; its output
must still be independently validated before it can be committed or used by a
later run.

An optional dependency manifest stages only operator-approved content from a
local content-addressed cache. Each cache file is named by its SHA-256 digest;
the manifest has no URL, command, hook, or toolchain fields:

```json
{"version":1,"dependencies":[
  {"name":"core/library.bin","sha256":"<digest>","size_bytes":1234}
]}
```

Pass it with `--dependency-manifest manifest.json --dependency-cache cache/`.
The staged directory is read-only in the worker and every file is checked by
identity and size again inside the image. Submodules are rejected, Git hooks
and external configuration are disabled for trusted Git reads, and the image,
toolchain, validator policy, network, credentials, and container socket are
fixed by the protected launcher. The worker receives no host home directory or
provider credentials.

If a separate worker adapter produces raw files, supply its stopped output
directory and an operator-owned allowlist such as
`{"version":1,"files":{"solution.lean":"<digest>"}}` with
`--artifacts WORKER_DIR --artifact-manifest artifacts.json`. The verifier does
not mount this directory into the candidate container; after the worker has
stopped, the handoff accepts only named private regular files with matching
digests and bounded size/count. It does not parse archives; archive export and
replay remain the separate evidence interface below.

Docker runs the CLI and validator offline, unprivileged, with CPU, memory,
process and temporary-storage limits. The tighter of memory and file limits
bounds container memory, including nested tmpfs. This conservative bound may
stop a run before either individual limit would be reached. The smaller of the
CPU and wall-time budgets is a wall deadline while the container is capped at
one CPU. Docker and the host remain trusted. The verifier refuses to accept a
proof outside a container with the required limits.

Exit 0 means all required obligations were verified; exit 1 means a completed
blocking result; exit 2 means configuration, timeout, cancellation or execution
failure. Advisory failures are reported but do not block a completed gate.
A JSON report is written on nonzero results when its destination is writable.
It records the envelope, per-obligation results, evidence digests, timestamps,
and model usage.

## Optional proof repair

Run the control-process launcher to retain generated proof artifacts:

```sh
python3 portable/assist.py --envelope run.json --baseline protected/baseline.json \
  --snapshot checkout --report report.json --artifacts /path/to/artifacts
```

The artifact directory must be outside the snapshot and baseline directory.
The launcher checks committed evidence and tries a fixed deterministic tactic.
Without `--model-config`, it does not make model requests. Each generated
bundle must pass the same independent validator as committed evidence.

To enable the OpenAI adapter, store the following JSON outside the snapshot
and pass its path as `--model-config`. Replace the placeholder identities and
set the limits for the selected model. `head` and `baseline_sha256` must match
the run envelope. Use a new `run_id` for each run.

```json
{
  "repository": "https://example.invalid/project.git",
  "run_id": "unique-run-id",
  "head": "full-commit-id",
  "baseline_sha256": "approved-baseline-digest",
  "authorized": true,
  "private": true,
  "private_source_consent": true,
  "model": "gpt-4o-mini",
  "limits": {
    "context_bytes": 32768,
    "input_tokens": 100000,
    "output_tokens": 5000,
    "cost_micros": 1000000,
    "input_micros_per_million": 10000000,
    "output_micros_per_million": 30000000,
    "max_output_per_call": 1000
  }
}
```

Set `PROOFCI_OPENAI_API_KEY` in the control process. The proof container does
not receive the key or network access. Private source consent defaults to false.
The built-in adapter accepts `gpt-4o-mini`, `gpt-4o`, `gpt-4.1-mini`, and
`gpt-4.1`; it does not expose model tools.
The config must be protected from candidate changes. The configured token rates
must be upper bounds for the selected model and service tier. The broker reserves
the worst-case token cost before each call and retains that reservation when a
provider response is unavailable. It limits each obligation to five requests
and 120 seconds, and the run to 15 minutes. Lower resource limits still apply.

The report contains request IDs, reservation and settlement transitions, usage,
and paths relative to the artifact directory. The broker writes each transition
to an append-only journal before continuing. A failed request with unknown
usage remains marked `uncertain`. A reserved request without a later transition
also has an unknown outcome. The journal does not guarantee exactly-once
provider charging after a crash.
The launcher does not commit artifacts or publish comments.

Run unit checks with `python3 -m unittest discover -s portable`. The real
passing and obsolete-proof scenarios require the pinned dependencies and Docker:

```sh
PROOFCI_TEST_PACKAGED=1 python3 portable/test_cli_linux.py
PROOFCI_TEST_PACKAGED=1 python3 portable/test_assist_linux.py
PROOFCI_TEST_PACKAGED=1 python3 portable/test_dispatch_linux.py
```

A conditional contract may add `"precondition": {"lhs": "x", "op": "<", "rhs": "3"}`.
Each side uses the restricted natural-number expression language; operators are
`=`, `<`, and `≤`. The property holds only where the precondition holds. A
concrete witness must independently establish the precondition and failure.

To report a completed external search without accepting it as proof, pass
`--search-results search.json` to the launcher. Its version 1 format is
`{"version": 1, "exhausted": ["obligation-id"]}`. Only unresolved obligations
receive `search_exhausted`; accepted evidence still determines the result. The
report includes the SHA-256 of this input. The result’s `search.status` records
exhaustion; its nested validation retains the reason the evidence was unresolved.
This option does not run a search. When exporting that report for replay, pass
the same `--search-results` file to `replay.py export`; its digest is checked.

## Reviewed local baselines

`baselines.py` is a local lifecycle adapter around the same pinned container
CLI. Its SQLite store, the verifier, the operator identity, and the invocation
must be protected from candidate changes. The `--approver` value is an assertion
by the trusted caller; it is not authentication. A hosted adapter must obtain a
maintainer identity from its own authentication and authorization boundary and
must not accept it from repository content. An attacker who can invoke the
command as the trusted caller or edit the store can replace policy. Protect the
store, including its directory and SQLite sidecar files, and back it up.

A committed manifest has the following shape (the only currently supported
assumptions and specification closure are empty, and the only binding is
`target`; see the validator README for the exact statement language):

```json
{"version":1,"candidate":"candidate.lean","contracts":[{"id":"increment","explanation":"Adds one","owner":"maintainer","formal_statement":"x + 1","assumptions":[],"specification_closure":[],"implementation_bindings":["target"],"policy":"required","evidence":"evidence"}]}
```

For a local initialization and follow-up demonstration, commit that manifest,
`candidate.lean`, and the matching proof bundle in a clean checkout. Prepare the
version 1 envelope described above for that exact commit and repository. The
baseline digest in that input is replaced by the adapter with the digest of the
protected baseline it constructs. The reviewer examines the committed manifest
and explicitly supplies its SHA-256 and their authenticated identity:

```sh
sha256sum checkout/contracts.json
python3 portable/baselines.py activate --store protected/baselines.db \
  --snapshot checkout --envelope initial-envelope.json --report activation.json \
  --manifest-path contracts.json --reviewed-sha256 REVIEWED_SHA256 --approver MAINTAINER_ID
python3 portable/baselines.py lookup --store protected/baselines.db
```

The first command requiring verification is `activate`: it invokes the pinned
container and changes the active pointer only when every required obligation
passes. Keep the store outside the checkout. `lookup --digest DIGEST` returns a
specific historical reviewed manifest and its approval and validation record;
without a digest it returns the active one. The digest printed in lookup is the
hash of the exact reviewed manifest bytes, distinct from the verifier's baseline
digest. Both are recorded.

Now commit a follow-up candidate, update the envelope's head and candidate hash,
and run:

```sh
python3 portable/baselines.py run --store protected/baselines.db \
  --snapshot checkout --envelope followup-envelope.json --report followup.json
```

The run checks the original obligations and reports proposed changes from the
committed manifest. Deleted or malformed manifests and changed guarantees block
the gate; changing candidate configuration cannot select a new baseline.
Exit codes retain the CLI convention: 0 pass, 1 blocked, 2 execution or
configuration error. A replacement baseline cannot be activated by this local
command; an authorized migration and retirement workflow is separate and is not
implemented here. No draft or model output activates itself.

## Scope and change diagnostics

The report's `support` section names the fixed adapter policy version and
validator digest, trusted tools, assumptions, exclusions and source-level
boundary. The protected verifier determines this policy; files in the candidate
checkout cannot extend it. Each result states the admitted `target` and its
approved equation. A required candidate rejected by the adapter is `unproven`
with `unsupported_semantics`, even when evidence is missing or obsolete.

`coverage.changes` lists the complete base-to-head Git tree diff, including
object IDs, modes and paths. Git filenames and file contents are untrusted data.
`unsupported_changed_code` and `uncovered_supported_symbols` are separate from
`property_counts`. Foreign-language code with a recognized source suffix is listed as unsupported.
Other paths remain visible as outside scope in the full diff; filenames alone
cannot reliably identify all code. Their presence
alone does not block the gate. Every registered obligation is still checked.
Proof evidence files are identified separately from target code. The adapter
accepts only the single declaration described in the validator README, so an
independently admitted `target` in another changed Lean file is uncovered.

A passing gate establishes only the listed approved properties of that admitted
source definition, under the reported assumptions. It does not verify the whole
repository, compiled binaries, deployment, or foreign-language code. Rust and
Aeneas are deferred experimental work and are not supported frontends.

## Export and replay evidence

Export a completed run with its original inputs and report:

```sh
python3 portable/replay.py export --envelope run.json --baseline protected/baseline.json \
  --snapshot checkout --report report.json --output evidence.tar
```

Record the printed SHA-256 in a trusted channel separate from the archive. The
archive contains a Git bundle with both commits, the protected baseline and
contracts, the envelope, and the original report. The commit contains the
candidate and proof evidence. Toolchain, dependencies, and policy are identified
by the envelope and checked by the pinned verifier image. The bundle can contain
repository history and should be handled accordingly.

On a fresh Linux host with the pinned local image and Docker installed, run:

```sh
python3 portable/replay.py replay --bundle evidence.tar --sha256 <trusted-sha256> \
  --output replay-report.json
```

Replay validates the archive before extraction, reconstructs a fresh checkout,
and runs the same verifier without model calls or a proof-result cache. For a
generated proof, it reconstructs the recorded suggestion and validates it
against the archived candidate and contract. Replay compares fresh obligation
outcomes and evidence digests to the original
report. Exit 0 means a passing result was reproduced, 1 means a blocking result
was reproduced, and 2 means replay failed or did not reproduce the result.
The report explicitly says that historical CI publication was not reproduced.
A digest supplied alongside an untrusted archive does not authenticate its
origin; protect the digest separately. Missing inputs or the pinned image cause
a nonpassing result. Archive limits are 256 MiB total and 128 MiB per member. The expanded
repository is limited to 256 MiB total, 128 MiB per file, and 100,000 files;
export checks these limits before creating the bundle.

On Linux, Git reconstruction runs with CPU, address-space, and file-size limits,
plus wall-clock deadlines. macOS does not support the address-space limit;
use a Linux host for the fully resource-bounded replay boundary.

## GitHub Actions

[The fixture workflow](../.github/workflows/portable-fixtures.yml) builds the
pinned ARM64 image and runs the public container launcher for a passing proof,
a missing proof, and an execution failure. It checks the expected public exit
codes, retains each available report and evidence archive, and uploads artifacts
even after a failed step. These are acceptance fixtures, not a gate on the
repository's own properties. The workflow loads the fixture code from the GitHub test-merge commit on
`pull_request` and the merge-group commit on `merge_group`. The verifier checks
the generated fixture commits, not those event commits. It requires no model or
publishing credentials.

For a repository gate, a trusted operator must supply the pinned verifier,
image, envelope, and approved baseline outside the candidate checkout. The
baseline and contracts must come from a protected source at an independently
approved immutable revision, not the pull request. Set the envelope's `head`
to the exact checked-out commit and `base` to the intended base commit, and
calculate the candidate digest from the committed snapshot. The CLI validates
these identities and the protected baseline digest. Keep the checkout clean;
write the envelope, baseline, report and evidence outside it. Follow the input
and image instructions above. Do not construct a baseline from candidate files.

Run verification in an unprivileged `pull_request` job with `contents: read`,
`persist-credentials: false`, and no model or publishing secrets. Include
`merge_group` when using a merge queue. The example below assumes the trusted
setup has already placed the verifier, image, envelope and baseline on the
runner. `snapshot` is the checkout at GitHub's test-merge or merge-group commit.
Do not run candidate code in `pull_request_target` to gain access to secrets.

```yaml
- name: Verify
  id: proofci
  shell: bash
  run: |
    set +e
    python3 "$RUNNER_TEMP/verifier/portable/container.py" \
      --envelope "$RUNNER_TEMP/protected/envelope.json" \
      --baseline "$RUNNER_TEMP/protected/baseline.json" \
      --snapshot "$GITHUB_WORKSPACE" --report "$RUNNER_TEMP/report.json" \
      --image proofci-validator-local --validator-only
    status=$?
    echo "$status" > "$RUNNER_TEMP/exit-code.txt"
    exit "$status"
- name: Export evidence
  if: always()
  shell: bash
  run: |
    if [ -s "$RUNNER_TEMP/report.json" ]; then
      python3 "$RUNNER_TEMP/verifier/portable/replay.py" export \
        --envelope "$RUNNER_TEMP/protected/envelope.json" \
        --baseline "$RUNNER_TEMP/protected/baseline.json" \
        --snapshot "$GITHUB_WORKSPACE" --report "$RUNNER_TEMP/report.json" \
        --output "$RUNNER_TEMP/evidence.tar"
    fi
- name: Upload available results
  if: always()
  uses: actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02
  with:
    name: proofci-results
    path: |
      ${{ runner.temp }}/report.json
      ${{ runner.temp }}/exit-code.txt
      ${{ runner.temp }}/evidence.tar
    if-no-files-found: warn
```

Export evidence with `replay.py export` as described above when the required
inputs and report are available. Run export in a separate `if: always()` step;
it must not replace or mask the verification step's exit status. Evidence
export may fail for an execution failure, so upload whatever is available.

A workflow editable by the candidate can be changed to report success. It is
not an authoritative required gate on its own. Protect the workflow and its
setup through a trusted external enforcement mechanism, and configure the
repository's required check and fresh-merge or merge-queue policy. A portable
job inherits the host CI's isolation and trust configuration; this example does
not establish those protections.
