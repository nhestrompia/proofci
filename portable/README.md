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

Run with Docker and the pinned Linux ARM64 Lean distribution and bubblewrap
binary from the [source-binding setup](../experiments/source-binding/README.md):

```sh
python3 portable/proofci.py --envelope run.json --baseline protected/baseline.json \
  --snapshot checkout --toolchain /path/to/lean-4.35.0-linux_aarch64 \
  --bwrap /path/to/bubblewrap --report report.json
```

Docker runs the digest-pinned Python image offline, unprivileged, with CPU,
memory, process and temporary-storage limits. The validator checks the Lean
tree and bubblewrap against pinned digests. The tighter of memory and file
limits bounds the container memory, including nested tmpfs. This conservative
bound may stop a run before either individual limit would be reached. The
smaller of the CPU and wall-time budgets is applied as a wall deadline while
the container is capped at one CPU. Docker and the host remain trusted.

To build the local-only image containing the pinned validator and tools, use
the extracted Lean directory and the extracted bubblewrap package directory
as named build contexts:

```sh
docker buildx build --load --platform linux/arm64 \
  --build-context lean=/path/to/lean-4.35.0-linux_aarch64 \
  --build-context bubblewrap=/path/to/extracted-bubblewrap \
  -f portable/Dockerfile -t proofci-validator-local .
```

The build checks both tool digests. The CLI currently mounts those same pinned
tools into the digest-pinned base image; it does not require the local image.

Exit 0 means all required obligations were verified; exit 1 means a completed
blocking result; exit 2 means configuration, timeout, cancellation or execution
failure. Advisory failures are reported but do not block a completed gate.
A JSON report is written on nonzero results when its destination is writable.
It records the envelope, per-obligation results, evidence digests, timestamps,
and zero model calls.

Run unit checks with `python3 -m unittest discover -s portable`. The real
passing and obsolete-proof scenarios require the pinned dependencies and Docker:

```sh
PROOFCI_TEST_TOOLCHAIN=/path/to/lean PROOFCI_TEST_BWRAP=/path/to/bwrap \
  python3 portable/test_cli_linux.py
```
