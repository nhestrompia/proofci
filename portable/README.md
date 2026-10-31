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
