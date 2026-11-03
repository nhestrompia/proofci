"""`python -m proofci check --base BASE --head HEAD`

Exit status: 0 every required guarantee is verified and the policy is
unchanged (or approved); 1 a guarantee is not verified or the policy changed
without approval; 2 configuration or infrastructure error.
"""

import argparse
import json
import sys
import tempfile
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
    c.add_argument("--vendor", type=Path, help="crates.io dependencies downloaded by `proofci fetch`")
    c.add_argument("--fetch", action="store_true",
                   help="download crates.io dependencies first (needs network; for local use)")
    f = sub.add_parser("fetch", help="download the candidate's crates.io dependencies (needs network)")
    f.add_argument("--base", type=Path, required=True)
    f.add_argument("--head", type=Path, required=True)
    f.add_argument("--policy", choices=("base", "head"), default="base")
    f.add_argument("--out", type=Path, required=True, help="directory to vendor the dependencies into")
    d = sub.add_parser("dev", help="rebuild the proofs quickly and show Lean's messages (for authors)")
    d.add_argument("--repo", type=Path, default=Path("."), help="checkout with proofci.yaml")
    d.add_argument("--work-dir", type=Path, default=Path("/tmp/proofci-dev"))
    d.add_argument("--vendor", type=Path, help="crates.io dependencies downloaded by `proofci fetch`")
    d.add_argument("--judge", action="store_true", help="also run the comparator on each guarantee")
    args = parser.parse_args(argv)

    if args.command == "dev":
        from . import dev
        try:
            return dev.run(args.repo, args.work_dir.resolve(),
                           args.vendor.resolve() if args.vendor else None, args.judge)
        except (check_mod.ConfigError, manifest.ManifestError, sandbox.SandboxUnavailable,
                FileNotFoundError, ValueError) as error:
            print(f"proofci: {error}", file=sys.stderr)
            return 2

    if args.command == "fetch":
        try:
            check_mod.fetch(args.base.resolve(), args.head.resolve(), args.out.resolve(), args.policy)
        except (check_mod.ConfigError, manifest.ManifestError, sandbox.SandboxUnavailable,
                FileNotFoundError, ValueError) as error:
            print(f"proofci: {error}", file=sys.stderr)
            return 2
        except check_mod.extract.Unsupported as error:
            # Reported by `check`, which marks the guarantees unsupported.
            print(f"proofci: {error}", file=sys.stderr)
        return 0

    try:
        vendor = args.vendor.resolve() if args.vendor else None
        if args.fetch:
            vendor = Path(tempfile.mkdtemp(prefix="proofci-vendor-"))
            try:
                check_mod.fetch(args.base.resolve(), args.head.resolve(), vendor, args.policy)
            except check_mod.extract.Unsupported as error:
                print(f"proofci: {error}", file=sys.stderr)
        report = check_mod.check(args.base.resolve(), args.head.resolve(), args.policy, args.work_dir,
                                 vendor_dir=vendor)
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
