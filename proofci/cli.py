"""`python -m proofci check --base BASE --head HEAD`

Exit status: 0 every required guarantee is verified and the policy is
unchanged (or approved); 1 a guarantee is not verified or the policy changed
without approval; 2 configuration or infrastructure error.
"""

import argparse
import json
import sys
from pathlib import Path

from . import check as check_mod
from . import manifest, sandbox
from .summary import markdown


def main(argv=None):
    parser = argparse.ArgumentParser(prog="proofci")
    sub = parser.add_subparsers(dest="command", required=True)
    c = sub.add_parser("check", help="verify guarantees of a candidate commit")
    c.add_argument("--base", type=Path, required=True, help="checkout holding the protected policy")
    c.add_argument("--head", type=Path, required=True, help="checkout of the candidate commit")
    c.add_argument("--policy", choices=("base", "head"), default="base",
                   help="use the candidate's own policy (only after a maintainer approved it)")
    c.add_argument("--report", type=Path, help="write the JSON report here")
    c.add_argument("--summary", type=Path, help="write a Markdown summary here")
    c.add_argument("--work-dir", type=Path)
    args = parser.parse_args(argv)

    try:
        report = check_mod.check(args.base.resolve(), args.head.resolve(), args.policy, args.work_dir)
    except (check_mod.ConfigError, manifest.ManifestError, sandbox.SandboxUnavailable,
            FileNotFoundError, ValueError) as error:
        print(f"proofci: {error}", file=sys.stderr)
        if args.summary:
            args.summary.write_text(f"## ProofCI\n\n**Error:** {error}\n")
        return 2
    data = report.to_json()
    if args.report:
        args.report.write_text(json.dumps(data, indent=2) + "\n")
    text = markdown(data)
    if args.summary:
        args.summary.write_text(text)
    print(text)
    if any(o.status == check_mod.ERROR for o in report.outcomes):
        return 2
    return 0 if report.passed else 1
