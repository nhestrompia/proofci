"""Build an evidence bundle from a proof body in the offline Lean sandbox.

Construction does not establish validity. The caller must submit the bundle
to the independent validator before using it as evidence.
"""
import json
from pathlib import Path
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "experiments/source-binding"))
import binding
import evidence


def construct(candidate, contract, body, toolchain, output, deadline):
    if not isinstance(body, str) or not body.strip():
        raise ValueError("empty proof body")
    if len(body.encode()) > evidence.MAX_SOLUTION_BYTES:
        raise ValueError("proof body exceeds size limit")
    if evidence.FORBIDDEN_SOLUTION.search(body):
        raise ValueError("proof body contains forbidden syntax")
    _, _, _, statement, _ = binding.build_sources(candidate, contract)
    solution = ("import CandidateCheck\nimport Std.Tactic\n" + statement + body + "\n").encode()
    bundle = evidence.EvidenceBundle(candidate, contract, solution, b"", b"",
                                     evidence.sha(candidate), evidence.sha(contract), "verified", None)
    toolchain = evidence._verify_toolchain(toolchain)
    with tempfile.TemporaryDirectory(prefix="proofci-repair-") as temp:
        root = Path(temp)
        evidence._write_workspace(root, bundle)
        exports = []
        for script, marker in ((evidence.CHALLENGE_SCRIPT, evidence.CHALLENGE_MARKER),
                               (evidence.SOLUTION_SCRIPT, evidence.SOLUTION_MARKER)):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("proof construction timed out")
            _, result = evidence._run(toolchain, root, root / "comparator.json", (),
                timeout=remaining, read_only_sources=True,
                entrypoint=("/bin/sh", f"/workspace/{script}"))
            exports.append(evidence._extract_export(result, marker))
    challenge, solved = exports
    manifest = {"version": 1, "candidate_sha256": evidence.sha(candidate),
                "contract_sha256": evidence.sha(contract), "solution_sha256": evidence.sha(solution),
                "challenge_export_sha256": evidence.sha(challenge),
                "solution_export_sha256": evidence.sha(solved), "claimed_decision": "verified"}
    output.mkdir(mode=0o700)
    for name, data in (("solution.lean", solution), ("challenge.ndjson", challenge),
                       ("solution.ndjson", solved),
                       ("manifest.json", json.dumps(manifest, sort_keys=True).encode())):
        (output / name).write_bytes(data)
