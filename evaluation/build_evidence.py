#!/usr/bin/env python3
"""Construct evaluation evidence bundles inside the pinned validator image.

This is corpus preparation, not verification. It plays the part of a pull
request author who produces evidence. Every bundle it writes is submitted to the
unchanged public verifier, which decides independently whether it is accepted.

Forgery jobs may bypass the construction-time syntax filter so that hostile
bundles carry real Lean exports. That bypass exists only here; the verifier
still applies its own fixed policy.

Usage inside the image (see evaluate.py for the container invocation):

    python3 build_evidence.py JOBS.json OUTPUT_DIR
"""
import dataclasses
import hashlib
import json
from pathlib import Path
import sys
import time

sys.path.insert(0, "/app/experiments/source-binding")
sys.path.insert(0, "/app/portable")

PREFIX = "import CandidateCheck\nimport Std.Tactic\n"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def build(job, toolchain, output):
    """Build the first proof body that Lean accepts; return the body used."""
    import evidence

    candidate = job["candidate"].encode()
    contract = job["contract"].encode()
    claim = job.get("claim", "verified")
    witness = job.get("witness")
    bundle = evidence.EvidenceBundle(candidate, contract, b"", b"", b"", sha(candidate), sha(contract),
                                     claim, witness)
    _, statement, _, _ = evidence._sources(bundle)
    if "solution" in job:
        candidates = [job["solution"].replace("{statement}", statement)]
    else:
        candidates = []
        for body in job["bodies"]:
            if not job.get("allow_forbidden") and evidence.FORBIDDEN_SOLUTION.search(body):
                raise ValueError("proof body contains forbidden syntax")
            candidates.append(PREFIX + statement + body + "\n")
    failures = []
    for text in candidates:
        try:
            _build_one(evidence, dataclasses.replace(bundle, solution=text.encode()), job, toolchain, output)
        except evidence.BuildFailure as error:
            failures.append(str(error)[-600:])
            continue
        if job.get("validate"):
            # Keep only evidence the fixed validator accepts, as an author would
            # check before committing. The verifier still re-validates it.
            inputs = Path("/tmp/proofci-eval-inputs")
            inputs.mkdir(exist_ok=True)
            (inputs / "candidate").write_bytes(candidate)
            (inputs / "contract").write_bytes(contract)
            result = evidence.validate_bundle(output, inputs / "candidate", inputs / "contract", toolchain)
            if result.get("decision") != claim:
                failures.append(f"validator: {result.get('reason')}: {str(result.get('detail'))[-300:]}")
                import shutil
                shutil.rmtree(output)
                continue
        return text
    raise RuntimeError("no proof body accepted: " + " | ".join(failures))


def _build_one(evidence, bundle, job, toolchain, output):
    candidate, contract, solution = bundle.candidate, bundle.contract, bundle.solution
    claim, witness = bundle.claimed_decision, bundle.witness
    deadline = time.monotonic() + job.get("timeout_seconds", 120)
    root = Path("/tmp/proofci-eval-build")
    if root.exists():
        import shutil
        shutil.rmtree(root)
    root.mkdir()
    evidence._write_workspace(root, bundle)
    exports = []
    for script, marker in ((evidence.CHALLENGE_SCRIPT, evidence.CHALLENGE_MARKER),
                           (evidence.SOLUTION_SCRIPT, evidence.SOLUTION_MARKER)):
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("construction timed out")
        _, result = evidence._run(toolchain, root, root / "comparator.json", (), timeout=remaining,
                                  read_only_sources=True, entrypoint=("/bin/sh", f"/workspace/{script}"))
        exports.append(evidence._extract_export(result, marker))
    challenge, solved = exports
    manifest = {"version": 1, "candidate_sha256": sha(candidate), "contract_sha256": sha(contract),
                "solution_sha256": sha(solution), "challenge_export_sha256": sha(challenge),
                "solution_export_sha256": sha(solved), "claimed_decision": claim}
    if witness is not None:
        manifest["witness"] = witness
    output.mkdir()
    for name, data in (("solution.lean", solution), ("challenge.ndjson", challenge),
                       ("solution.ndjson", solved),
                       ("manifest.json", json.dumps(manifest, sort_keys=True).encode())):
        (output / name).write_bytes(data)


def main():
    import evidence

    jobs = json.loads(Path(sys.argv[1]).read_text())
    output = Path(sys.argv[2])
    toolchain = evidence._verify_toolchain(Path("/lean"))
    results = {}
    for key, job in jobs.items():
        started = time.monotonic()
        try:
            solution = build(job, toolchain, output / key)
            results[key] = {"status": "built", "seconds": time.monotonic() - started,
                            "solution_sha256": sha(solution.encode())}
        except Exception as error:  # Report every failure; the caller decides.
            results[key] = {"status": "failed", "error": f"{type(error).__name__}: {str(error)[-1500:]}",
                            "seconds": time.monotonic() - started}
        print(json.dumps({key: results[key]}), flush=True)
    (output / "build-results.json").write_text(json.dumps(results, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
