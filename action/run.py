"""Runner-side driver for the ProofCI GitHub Action.

Runs the pinned toolchain image offline against the base and candidate
checkouts. If the candidate changes the policy (proofci.yaml or the contract),
the check stays blocked unless a repository owner, member or collaborator
other than the author approved a review on the exact candidate commit; only
then is the candidate's own policy used.
"""

import json
import os
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


def run_image(base, head, policy, out):
    out.mkdir(parents=True, exist_ok=True)
    os.chmod(out, 0o777)
    command = [
        "docker", "run", "--rm", "--network", "none",
        # bubblewrap inside the container needs these to create its sandboxes
        "--security-opt", "seccomp=unconfined", "--security-opt", "apparmor=unconfined",
        "--security-opt", "systempaths=unconfined",
        "--cpus", str(os.cpu_count() or 2), "--memory", "8g", "--pids-limit", "4096",
        "-v", f"{base}:/base:ro", "-v", f"{head}:/head:ro", "-v", f"{out}:/out",
        os.environ["IMAGE"], "check", "--base", "/base", "--head", "/head",
        "--policy", policy, "--report", "/out/report.json", "--summary", "/out/summary.md",
    ]
    status = subprocess.run(command).returncode
    report = out / "report.json"
    return status, (json.loads(report.read_text()) if report.exists() else None)


def approved_on(head_sha):
    number, token = os.environ.get("PR_NUMBER"), os.environ.get("GH_TOKEN")
    if not number or not token:
        return None
    url = f"{os.environ['API_URL']}/repos/{os.environ['REPOSITORY']}/pulls/{number}/reviews?per_page=100"
    request = urllib.request.Request(url, headers={
        "Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json"})
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            reviews = json.load(response)
    except OSError as error:
        print(f"::warning::could not read reviews: {error}")
        return None
    latest = {}
    for review in reviews:  # chronological; keep each reviewer's latest decision
        if review.get("state") in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
            latest[review["user"]["login"]] = review
    for login, review in latest.items():
        if (review["state"] == "APPROVED" and review.get("commit_id") == head_sha
                and login != os.environ.get("PR_AUTHOR")
                and review.get("author_association") in TRUSTED_ASSOCIATIONS):
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
        approver = approved_on(os.environ["HEAD_SHA"])
        if approver:
            print(f"Policy change approved by {approver} on {os.environ['HEAD_SHA']}; "
                  "checking the candidate against its own policy.")
            status, report = run_image(base, head, "head", out)
    summary = out / "summary.md"
    text = summary.read_text() if summary.exists() else "## ProofCI\n\nNo report was produced.\n"
    if report and report["policy_changes"] and not approver:
        text += ("\nTo accept the policy change, a maintainer approves this pull request on the "
                 "current commit and re-runs this job.\n")
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
