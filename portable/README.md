# Portable verification

The CLI checks every required and advisory obligation in a protected baseline.
It uses the fixed source-binding validator and does not call a model. The
supported Lean language and trust assumptions are documented in
[the validator README](../experiments/source-binding/README.md). The baseline,
the verifier checkout, the Docker host and the supplied toolchain must be
protected from the candidate being checked. This local distribution is not
licensed for public distribution; a maintainer license decision is still needed.

The input is a clean Git checkout at the exact full commit named by `head`.
The origin URL must equal `repository`; `base` must be a full commit ID present
in the repository. Candidate and evidence files must be committed, and their
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
      "evidence": "proofs/increment"
    }
  ]
}
```

Contract paths are relative to the baseline directory; candidate and evidence
paths are relative to the checkout. Evidence uses the
[bundle format](../experiments/source-binding/evidence-format.md). IDs must be
unique and at least one obligation must be required.

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
and zero model calls.

Run unit checks with `python3 -m unittest discover -s portable`. The real
passing and obsolete-proof scenarios require the pinned dependencies and Docker:

```sh
PROOFCI_TEST_PACKAGED=1 python3 portable/test_cli_linux.py
```

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
and runs the same verifier without model calls or a proof-result cache. It
compares the fresh obligation outcomes and evidence digests to the original
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
