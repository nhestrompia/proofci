#!/usr/bin/env python3
"""Demonstrate why a Lean proof alone does not bind to candidate source."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


BASE = "def target (x : Nat) : Nat := x + 1\n"
BROKEN = "def target (x : Nat) : Nat := x + 2\n"
THEOREM = "theorem contract (x : Nat) : target x = x + 1 := by simp [target]\n"
SHADOW = "namespace Shadow\n" + BASE + THEOREM + "end Shadow\n"


def digest(value):
    return hashlib.sha256(value).hexdigest()


def main():
    lean = os.environ.get("LEAN", "lean")
    version = subprocess.run([lean, "--version"], check=True, capture_output=True, text=True).stdout.strip()
    if not version.startswith("Lean (version 4.35.0,") or "commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc" not in version:
        raise SystemExit(f"expected Lean 4.35.0, got {version}")

    cases = {
        "base": (BASE + THEOREM, True),
        "changed_candidate": (BROKEN + THEOREM, False),
        "shadow": (BROKEN + SHADOW, True),
    }
    observations = {}
    with tempfile.TemporaryDirectory(prefix="proofci-binding-") as tmp:
        for name, (source, expected) in cases.items():
            path = Path(tmp) / f"{name}.lean"
            path.write_text(source, encoding="utf-8")
            result = subprocess.run([lean, str(path)], capture_output=True, text=True)
            accepted = result.returncode == 0
            output = (result.stdout + result.stderr).replace(str(path), path.name).strip()
            observations[name] = {
                "source_sha256": digest(source.encode()),
                "accepted": accepted,
                "expected_accepted": expected,
                "output": output,
            }
    report = {
        "lean_version": version,
        "contract_sha256": digest(THEOREM.encode()),
        "base_candidate_sha256": digest(BASE.encode()),
        "changed_candidate_sha256": digest(BROKEN.encode()),
        "cases": observations,
        "binding_decision": "no-go: no source-binding adapter or independent validation has been demonstrated",
    }
    print(json.dumps(report, indent=2))
    mismatch = any(case["accepted"] != case["expected_accepted"] for case in observations.values())
    # A failed compiler invocation is not necessarily a rejected proof.
    mismatch |= "error: unsolved goals" not in observations["changed_candidate"]["output"]
    return int(mismatch)


if __name__ == "__main__":
    sys.exit(main())
