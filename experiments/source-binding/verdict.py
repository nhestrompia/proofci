"""Run the pinned validator and report its narrowly scoped result."""

import argparse
import json
from pathlib import Path
import subprocess

import binding


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("contract", type=Path)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--lake", required=True)
    args = parser.parse_args()
    try:
        report = binding.run(args.candidate, args.contract, args.lake, args.lean)
        report["verdict_source_sha256"] = binding.sha(Path(__file__).read_bytes())
        report["runner_source_sha256"] = binding.sha(Path(__file__).with_name("linux.sh").read_bytes())
        output = report["comparator_output"]
        accepted = (
            report["comparator_exit"] == 0
            and report["lake_sandbox_disabled"] is False
            and report["lean_distribution_sha256"] == binding.LINUX_ARM64_TOOLCHAIN
            and "nanoda kernel accepts the solution" in output
            and "Lean default kernel accepts the solution" in output
            and "Your solution is okay!" in output
        )
        if accepted:
            report["decision"] = "verified"
            report["scope"] = "pinned Linux source-binding spike; admitted Nat expression and supplied contract only"
            print(json.dumps(report, indent=2))
            return 0
        report["decision"] = "unproven"
        report["reason"] = "a required binding or validator check did not pass"
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        report = {"decision": "unproven", "reason": str(error)}
    print(json.dumps(report, indent=2))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
