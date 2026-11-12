"""Runner-side driver for the ProofCI GitHub Action.

Runs the pinned toolchain image offline against the base and candidate
checkouts. If the candidate changes the policy (proofci.yaml or the contract),
the check stays blocked unless a repository owner, member or collaborator
other than the author approved a review on the exact candidate commit; only
then is the candidate's own policy used.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import urllib.request
from pathlib import Path

WORK = Path(".proofci").resolve()
TRUSTED_ASSOCIATIONS = {"OWNER", "MEMBER", "COLLABORATOR"}


def subdir(root, rel):
    path = (root / rel).resolve()
    if root.resolve() not in (path, *path.parents):
        sys.exit(f"proofci: path {rel!r} leaves the repository")
    return path


SECCOMP = Path(__file__).resolve().parent / "seccomp.json"
SANDBOX_OPTS = [
    # No capabilities, no privilege escalation, read-only filesystem except /tmp.
    "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
    "--read-only", "--tmpfs", "/tmp:exec,mode=1777",
    # Docker's default seccomp profile plus only the namespace syscalls that
    # bubblewrap needs to build the inner sandboxes (see SECURITY.md).
    "--security-opt", f"seccomp={SECCOMP}",
    # Docker's AppArmor profile forbids the mounts bubblewrap makes, and the
    # masked /proc paths stop it mounting a fresh /proc for each sandbox.
    "--security-opt", "apparmor=unconfined", "--security-opt", "systempaths=unconfined",
]


def fetch(base, head, policy, vendor):
    """Download crates.io dependencies, or install a TypeScript project's packages.
    The only step with network access: `cargo vendor` downloads and checksums
    sources but runs none of them, and the package install runs with scripts off
    and only the public registry allowed (see `proofci/typescript.py`)."""
    if vendor.exists():
        shutil.rmtree(vendor)
    vendor.mkdir(parents=True)
    os.chmod(vendor, 0o777)
    command = [
        "docker", "run", "--rm", *SANDBOX_OPTS, "--memory", "4g", "--pids-limit", "1024",
        "-v", f"{base}:/base:ro", "-v", f"{head}:/head:ro", "-v", f"{vendor}:/vendor",
        os.environ["IMAGE"], "fetch", "--base", "/base", "--head", "/head", "--policy", policy, "--out", "/vendor",
    ]
    status = subprocess.run(command).returncode
    if status != 0:
        reason = ("the dependencies pinned by the lockfile (Cargo.lock, package-lock.json, pnpm-lock.yaml or "
                  "yarn.lock) could not be downloaded"
                  if status == 3 else f"the dependency download step failed (exit {status})")
        fail(f"{reason}. This is a download problem, not a verdict about the code; re-run the job.")


def fail(message):
    """Stop with an error that is not a verdict about the code."""
    print(f"::error::ProofCI: {message}")
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as handle:
            handle.write(f"## ProofCI\n\n**Error:** {message}\n")
    sys.exit(2)


def bridge_limits():
    """`docker run` options that hand the TypeScript bridge's time limits to the check."""
    names = ("PROOFCI_BRIDGE_TIMEOUT", "PROOFCI_BRIDGE_BUDGET")
    return [option for name in names if os.environ.get(name) for option in ("-e", f"{name}={os.environ[name]}")]


def run_image(base, head, policy, out):
    out.mkdir(parents=True, exist_ok=True)
    os.chmod(out, 0o777)
    vendor = WORK / f"vendor-{policy}"
    fetch(base, head, policy, vendor)
    command = [
        "docker", "run", "--rm", "--network", "none", *SANDBOX_OPTS,
        "--cpus", str(os.cpu_count() or 2), "--memory", "8g", "--pids-limit", "4096",
        "-v", f"{base}:/base:ro", "-v", f"{head}:/head:ro", "-v", f"{out}:/out",
        "-v", f"{vendor}:/vendor:ro",
        *bridge_limits(),
        os.environ["IMAGE"], "check", "--base", "/base", "--head", "/head", "--vendor", "/vendor",
        "--policy", policy, "--report", "/out/report.json", "--summary", "/out/summary.md",
    ]
    status = subprocess.run(command).returncode
    report = out / "report.json"
    return status, (json.loads(report.read_text()) if report.exists() else None)


MAX_REVIEW_PAGES = 50


def fetch_reviews(number, token):
    """Every review of the pull request, oldest first (follows pagination).
    None if they cannot all be read, in which case nothing counts as approved."""
    url = f"{os.environ['API_URL']}/repos/{os.environ['REPOSITORY']}/pulls/{number}/reviews?per_page=100"
    reviews = []
    for _ in range(MAX_REVIEW_PAGES):
        request = urllib.request.Request(url, headers={
            "Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json"})
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                reviews += json.load(response)
                links = response.headers.get("Link", "") if hasattr(response, "headers") else ""
        except OSError as error:
            print(f"::warning::could not read reviews: {error}")
            return None
        match = re.search(r'<([^>]+)>;\s*rel="next"', links or "")
        if not match:
            return reviews
        url = match.group(1)
    print("::warning::too many reviews to read; not treating any as an approval")
    return None


def approved_on(head_sha, approvers):
    """Login of a reviewer who may approve policy changes and approved
    exactly `head_sha`, or None. `approvers` comes from the protected base
    policy: None means any owner, member or collaborator other than the
    author; an empty list means policy changes cannot be approved in a PR."""
    if approvers is not None and not approvers:
        return None
    number, token = os.environ.get("PR_NUMBER"), os.environ.get("GH_TOKEN")
    if not number or not token:
        return None
    reviews = fetch_reviews(number, token)
    if reviews is None:
        return None
    latest = {}
    for review in reviews:  # chronological; keep each reviewer's latest decision
        if review.get("state") in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
            latest[review["user"]["login"]] = review
    author = (os.environ.get("PR_AUTHOR") or "").lower()
    for login, review in latest.items():
        if review["state"] != "APPROVED" or review.get("commit_id") != head_sha or login.lower() == author:
            continue
        if approvers is None:
            if review.get("author_association") in TRUSTED_ASSOCIATIONS:
                return login
        elif login.lower() in approvers:
            return login
    return None


def main():
    rel = os.environ.get("PROOFCI_PATH") or "."
    base = subdir(WORK / "base", rel)
    head = subdir(WORK / "head", rel)
    out = WORK / "out"
    status, report = run_image(base, head, "base", out)
    approver = None
    if report and report["policy_changes"]:
        approver = approved_on(os.environ["HEAD_SHA"], report.get("policy_approvers"))
        if approver:
            print(f"Policy change approved by {approver} on {os.environ['HEAD_SHA']}; "
                  "checking the candidate against its own policy.")
            status, report = run_image(base, head, "head", out)
    summary = out / "summary.md"
    text = summary.read_text() if summary.exists() else "## ProofCI\n\nNo report was produced.\n"
    if report and report["policy_changes"] and not approver:
        allowed = report.get("policy_approvers")
        if allowed is not None and not allowed:
            text += ("\nThis repository's policy cannot be changed in a pull request (`policy.approvers` is "
                     "empty); change it with a commit to the protected branch.\n")
        else:
            who = ", ".join(f"@{a}" for a in allowed) if allowed else "a maintainer other than the author"
            text += (f"\nTo accept the policy change, {who} approves this pull request on the "
                     "current commit and someone re-runs this job.\n")
    if approver:
        text += f"\nPolicy change approved by @{approver} on `{os.environ['HEAD_SHA'][:12]}`.\n"
    step_summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if step_summary:
        with open(step_summary, "a") as handle:
            handle.write(text)
    with open(os.environ["GITHUB_OUTPUT"], "a") as handle:
        handle.write(f"passed={'true' if status == 0 else 'false'}\n")
    sys.exit(status)


if __name__ == "__main__":
    main()
