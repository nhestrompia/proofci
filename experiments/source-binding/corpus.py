#!/usr/bin/env python3
"""Run bounded candidate mutations through the experimental adapter."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import tempfile

import binding

CONTRACTS = [
    ("x", "x", "x + 0", "x + 1"),
    ("0", "0", "x * 0", "1"),
    ("x + 1", "x + 1", "1 + x", "x + 2"),
    ("x + x", "x + x", "2 * x", "x + x + 1"),
    ("x * 3", "x * 3", "x + x + x", "3 * x + 1"),
    ("7", "7", "3 + 4", "8"),
    ("(x + 1) * 2", "(x + 1) * 2", "2 * x + 2", "2 * x + 3"),
    ("(x + 2) + 3", "(x + 2) + 3", "x + 5", "x + 6"),
    ("x * 0 + 3", "x * 0 + 3", "3", "4"),
    ("x + 2 * x", "x + 2 * x", "3 * x", "4 * x"),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--unsafe-no-sandbox", action="store_true")
    args = parser.parse_args()
    results = []
    with tempfile.TemporaryDirectory(prefix="proofci-corpus-") as tmp:
        root = Path(tmp)
        cases = []
        for n, (rhs, base, equivalent, defective) in enumerate(CONTRACTS, 1):
            contract = root / f"contract-{n}.json"
            contract.write_text(json.dumps({"rhs": rhs}))
            for label, body, expected in (
                ("base", base, 0),
                ("equivalent", equivalent, 0),
                ("defective", defective, 1),
            ):
                candidate = root / f"candidate-{n}-{label}.lean"
                candidate.write_text(f"def target (x : Nat) : Nat := {body}\n")
                cases.append((n, label, expected, candidate, contract))

        precedence_contract = root / "contract-precedence.json"
        precedence_contract.write_text(json.dumps({"rhs": "x + 2"}))
        for label, body, expected in (
            ("precedence", "x + 1 * 2", 0),
            ("defective", "(x + 1) * 2", 1),
        ):
            candidate = root / f"candidate-precedence-{label}.lean"
            candidate.write_text(f"def target (x : Nat) : Nat := {body}\n")
            cases.append(("precedence", label, expected, candidate, precedence_contract))

        def evaluate(case):
            n, label, expected, candidate, contract = case
            result = binding.run(candidate, contract, args.lake, args.lean, args.unsafe_no_sandbox)
            return {"contract": n, "mutation": label, "expected_exit": expected,
                    "observed_exit": result["comparator_exit"], "report": result,
                    "expected_proof_failure": label != "defective" or
                        "omega could not prove the goal" in result["comparator_output"]}

        with ThreadPoolExecutor(max_workers=3) as pool:
            for result in pool.map(evaluate, cases):
                results.append(result)
                print(json.dumps(result), flush=True)
    return int(any(r["expected_exit"] != r["observed_exit"] or not r["expected_proof_failure"] for r in results))


if __name__ == "__main__":
    raise SystemExit(main())
