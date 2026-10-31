#!/usr/bin/env python3
"""Exercise rejected input through the adapter's command-line boundary."""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


BASE = "def target (x : Nat) : Nat := x + 1\n"
CASES = {
    "shadow": (BASE + "namespace Other\ndef target (x : Nat) : Nat := x\nend Other\n", "unexpected token 'namespace'"),
    "import": ("import Std\n" + BASE, "candidate must be exactly one target definition"),
    "macro": ("macro \"m\" : term => `(0)\n" + BASE, "unsupported character"),
    "instance": ("instance : Inhabited Nat := ⟨0⟩\n" + BASE, "unsupported character"),
    "runtime_replacement": ("@[implemented_by other]\n" + BASE, "unsupported character"),
    "source_substitution": ("def target (x : Nat) : Nat := replacement x\n", "unsupported expression token 'replacement'"),
    "comment": (BASE + "-- another declaration\n", "unsupported character"),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--lake", required=True)
    args = parser.parse_args()
    failed = False
    with tempfile.TemporaryDirectory(prefix="proofci-admission-") as tmp:
        candidate = Path(tmp) / "candidate.lean"
        contract = Path(tmp) / "contract.json"
        contract.write_text('{"rhs":"x + 1"}')
        def invoke():
            return subprocess.run([sys.executable, str(Path(__file__).with_name("binding.py")),
                                   str(candidate), str(contract), "--lean", args.lean,
                                   "--lake", args.lake], capture_output=True, text=True)

        candidate.write_text(BASE)
        positive = invoke()
        report = json.loads(positive.stdout)
        accepted = positive.returncode == 1 and report.get("comparator_exit") == 0
        failed |= not accepted
        print(json.dumps({"case": "positive_control", "comparator_accepted": accepted}))
        for name, (source, expected_error) in CASES.items():
            candidate.write_text(source)
            result = invoke()
            report = json.loads(result.stdout)
            rejected = (result.returncode == 1 and expected_error in report.get("error", "")
                        and "comparator_exit" not in report)
            failed |= not rejected
            print(json.dumps({"case": name, "rejected": rejected, "error": report.get("error")}))
        candidate.write_text(BASE)
        for name, data, expected_error in (
            ("contract_shadow", '{"rhs":"target x"}', "unsupported expression token 'target'"),
            ("contract_helper", '{"rhs":"helper x"}', "unsupported expression token 'helper'"),
            ("contract_duplicate", '{"rhs":"x", "rhs":"x + 1"}', "duplicate contract field"),
        ):
            contract.write_text(data)
            result = invoke()
            report = json.loads(result.stdout)
            rejected = (result.returncode == 1 and expected_error in report.get("error", "")
                        and "comparator_exit" not in report)
            failed |= not rejected
            print(json.dumps({"case": name, "rejected": rejected, "error": report.get("error")}))
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
