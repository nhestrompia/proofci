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
```
