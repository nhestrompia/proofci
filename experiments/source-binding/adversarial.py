#!/usr/bin/env python3
"""Try hostile solutions against the trusted challenge in an isolated validator."""

import argparse
import json
from pathlib import Path
import tempfile

import binding


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--unsafe-no-sandbox", action="store_true")
    args = parser.parse_args()
    cases = {
        "shadow_implementation": (
            "import CandidateCheck\nnamespace Shadow\ndef target (x : Nat) : Nat := x + 1\nend Shadow\n"
            "theorem contract (x : Nat) : Shadow.target x = x + 1 := by simp [Shadow.target]\n"
        ),
        "weakened_statement": (
            "import CandidateCheck\ntheorem contract (x : Nat) : target x = target x := by rfl\n"
        ),
        "substituted_spec_helper": (
            "import CandidateCheck\nnamespace Spec\ndef expected (x : Nat) : Nat := x + 2\nend Spec\n"
            "theorem contract (x : Nat) : target x = Spec.expected x := by simp [target, Spec.expected]\n"
        ),
        "custom_axiom": (
            "import CandidateCheck\naxiom cheat (x : Nat) : target x = x + 1\n"
            "theorem contract (x : Nat) : target x = x + 1 := by exact cheat x\n"
        ),
        "sorry": (
            "import CandidateCheck\ntheorem contract (x : Nat) : target x = x + 1 := by sorry\n"
        ),
    }
    cases["identical_shadow_implementation"] = cases["shadow_implementation"]
    with tempfile.TemporaryDirectory(prefix="proofci-adversarial-") as tmp:
        candidate = Path(tmp) / "candidate.lean"
        contract = Path(tmp) / "contract.json"
        contract.write_text('{"rhs":"x + 1"}')
        candidate.write_text("def target (x : Nat) : Nat := x + 1\n")
        positive = binding.run(candidate, contract, args.lake, args.lean, args.unsafe_no_sandbox)
        if positive["comparator_exit"] != 0:
            print(json.dumps({"case": "positive_control", "report": positive}))
            return 1
        print(json.dumps({"case": "positive_control", "report": positive}), flush=True)
        candidate.write_text("def target (x : Nat) : Nat := x + 2\n")
        failed = False
        for name, solution in cases.items():
            if name == "identical_shadow_implementation":
                candidate.write_text("def target (x : Nat) : Nat := x + 1\n")
            report = binding.run(candidate, contract, args.lake, args.lean,
                                 args.unsafe_no_sandbox, _test_solution=solution)
            output = report["comparator_output"]
            rejected = report["comparator_exit"] == 1 and (
                (name in {"custom_axiom", "sorry"} and "Illegal axiom" in output)
                or (name in {"shadow_implementation", "identical_shadow_implementation", "weakened_statement", "substituted_spec_helper"} and
                    ("not definitionally equal" in output or "not equivalent" in output or
                     "does not match" in output or "do not match" in output or "mismatch" in output.lower()))
            )
            failed |= not rejected
            print(json.dumps({"case": name, "expected_rejection": rejected, "report": report}), flush=True)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
