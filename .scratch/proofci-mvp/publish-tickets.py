#!/usr/bin/env python3
"""Publish the explicitly approved plan, preserving issue IDs across retries."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
PLAN = ROOT / "plan.json"
LEDGER = ROOT / "publication.json"
REPO = "nhestrompia/proofci"
LABEL = "ready-for-agent"
MARKER = "proofci-mvp-ticket"
plan = json.loads(PLAN.read_text())
digest = hashlib.sha256(PLAN.read_bytes()).hexdigest()
assert plan["tracker"] == f"https://github.com/{REPO}"
assert plan["publicationLabel"] == LABEL
assert len(plan["tickets"]) == 24

parser = argparse.ArgumentParser()
parser.add_argument("--verify-only", action="store_true")
args = parser.parse_args()

def now():
    return datetime.now(timezone.utc).isoformat()

def save():
    temp = LEDGER.with_suffix(".tmp")
    temp.write_text(json.dumps(ledger, indent=2) + "\n")
    temp.replace(LEDGER)

def gh_api(endpoint, method="GET", payload=None, paginate=False):
    command = ["gh", "api", endpoint, "--method", method,
               "-H", "Accept: application/vnd.github+json",
               "-H", "X-GitHub-Api-Version: 2026-03-10"]
    if paginate:
        command += ["--paginate", "--slurp"]
    if payload is not None:
        command += ["--input", "-"]
    result = subprocess.run(command, input=json.dumps(payload) if payload is not None else None,
                            capture_output=True, text=True, timeout=60)
    if result.returncode:
        raise RuntimeError(f"{method} {endpoint}: {result.stderr.strip() or result.stdout.strip()}")
    if method != "GET":
        time.sleep(1)
    return json.loads(result.stdout) if result.stdout.strip() else None

def issue_list():
    pages = gh_api(f"repos/{REPO}/issues?state=all&per_page=100", paginate=True)
    return [issue for page in pages for issue in page if "pull_request" not in issue]

def marker(ticket_id):
    return f"<!-- {MARKER}:{ticket_id:02d} -->"

def remember(ticket_id, issue):
    ledger["issues"][str(ticket_id)] = {
        "number": issue["number"], "id": issue["id"],
        "url": issue["html_url"], "title": issue["title"]
    }
    save()

def body_for(ticket):
    blockers = "\n".join(
        f"- {ledger['issues'][str(blocker)]['url']}"
        for blocker in ticket["blockedBy"]
    ) or "None (can start immediately)."
    criteria = "\n".join(f"- [ ] {criterion}" for criterion in ticket["acceptance"])
    ownership = re.sub(r"ticket (\d{1,2})", lambda match:
        ledger["issues"].get(str(int(match.group(1))), {}).get("url", match.group(0)),
        ticket["ownership"])
    return (f"## What to build\n\n{ticket['delivers']}\n\n"
            f"## Acceptance criteria\n\n{criteria}\n\n"
            f"## Blocked by\n\n{blockers}\n\n"
            f"## Agent ownership\n\n{ownership}\n\n"
            f"## Specification coverage\n\nApproved ProofCI MVP spec, user stories "
            f"{', '.join(map(str, ticket['stories']))}. "
            "Test through the repository-snapshot and approved-contract input, "
            "authoritative report, public exit status, and applicable CI result, "
            "with real Lean validation where relevant.\n\n"
            f"{marker(ticket['id'])}\n")

if LEDGER.exists():
    ledger = json.loads(LEDGER.read_text())
    assert ledger["approvedPlanSha256"] == digest, "Approved plan changed; stop publication"
else:
    assert not args.verify_only, "No publication ledger to verify"
    ledger = {"state": "publishing", "repository": REPO,
              "approvedPlanSha256": digest,
              "approval": {"userMessage": "I approve", "recordedAt": now(),
                           "scope": "Publish the 24 reviewed tickets, ready-for-agent label, and approved blocking edges to GitHub."},
              "issues": {}, "nativeEdges": []}
    save()

if not args.verify_only:
    # Recover accepted requests whose response was lost before the local write.
    existing = issue_list()
    for ticket in plan["tickets"]:
        matches = [issue for issue in existing if marker(ticket["id"]) in (issue["body"] or "")]
        assert len(matches) <= 1, f"Duplicate marker for ticket {ticket['id']}"
        if matches:
            assert matches[0]["title"] == ticket["title"], "Existing issue title differs from approved plan"
            remember(ticket["id"], matches[0])
        elif str(ticket["id"]) in ledger["issues"]:
            raise RuntimeError(f"Recorded issue for {ticket['id']} is missing; do not recreate blindly")

    labels = gh_api(f"repos/{REPO}/labels?per_page=100")
    if not any(label["name"] == LABEL for label in labels):
        gh_api(f"repos/{REPO}/labels", "POST", {
            "name": LABEL, "color": "0E8A16",
            "description": "Approved implementation ticket; start when its blockers are complete."
        })
        print(f"Created label {LABEL}", flush=True)

    bodies = ROOT / "published-bodies"
    bodies.mkdir(exist_ok=True)
    for ticket in plan["tickets"]:
        key = str(ticket["id"])
        body = body_for(ticket)
        (bodies / f"{ticket['id']:02d}-{ticket['slug']}.md").write_text(body)
        if key not in ledger["issues"]:
            # No automatic retry on uncertain creation. A rerun reconciles markers first.
            issue = gh_api(f"repos/{REPO}/issues", "POST", {
                "title": ticket["title"], "body": body, "labels": [LABEL]
            })
            remember(ticket["id"], issue)
            print(f"Published {ticket['id']:02d}: {issue['html_url']}", flush=True)

        issue = ledger["issues"][key]
        remote_blockers = gh_api(f"repos/{REPO}/issues/{issue['number']}/dependencies/blocked_by?per_page=100")
        present = {item["id"] for item in remote_blockers}
        for blocker in ticket["blockedBy"]:
            blocking_issue = ledger["issues"][str(blocker)]
            if blocking_issue["id"] not in present:
                gh_api(f"repos/{REPO}/issues/{issue['number']}/dependencies/blocked_by", "POST", {
                    "issue_id": blocking_issue["id"]
                })
                print(f"Linked #{issue['number']} blocked by #{blocking_issue['number']}", flush=True)
            edge = [ticket["id"], blocker]
            if edge not in ledger["nativeEdges"]:
                ledger["nativeEdges"].append(edge)
                save()

# Verify actual remote bodies, labels, state, uniqueness, and native dependencies.
remote = issue_list()
verified_edges = 0
for ticket in plan["tickets"]:
    matches = [issue for issue in remote if marker(ticket["id"]) in (issue["body"] or "")]
    assert len(matches) == 1, f"Missing or duplicate issue for ticket {ticket['id']}"
    issue = matches[0]
    assert issue["number"] == ledger["issues"][str(ticket["id"])]["number"]
    assert issue["title"] == ticket["title"]
    assert issue["body"] == body_for(ticket), f"Issue body mismatch: {issue['number']}"
    assert issue["state"] == "open"
    assert LABEL in {label["name"] for label in issue["labels"]}
    actual = gh_api(f"repos/{REPO}/issues/{issue['number']}/dependencies/blocked_by?per_page=100")
    expected_ids = {ledger["issues"][str(blocker)]["id"] for blocker in ticket["blockedBy"]}
    assert {item["id"] for item in actual} == expected_ids, f"Native blockers differ for {issue['number']}"
    verified_edges += len(actual)

assert verified_edges == 43
ledger["state"] = "published-verified"
ledger["verifiedAt"] = now()
ledger["verification"] = {"tickets": len(plan["tickets"]), "nativeBlockingEdges": verified_edges,
                          "bodiesMatchApprovedPlan": True, "labelsVerified": True}
save()
index = ["# Published ProofCI MVP tickets", "", f"Repository: https://github.com/{REPO}", "",
         f"User-approved plan published and verified: {len(plan['tickets'])} issues, {verified_edges} native blocking edges, all labeled `{LABEL}`.", "", "## Tickets", ""]
for ticket in plan["tickets"]:
    issue = ledger["issues"][str(ticket["id"])]
    blockers = ", ".join(f"#{ledger['issues'][str(i)]['number']}" for i in ticket["blockedBy"]) or "None (can start immediately)"
    index.append(f"{ticket['id']}. [#{issue['number']}: {ticket['title']}]({issue['url']}). Blocked by: {blockers}.")
index += ["", "## Initial frontier", ""]
index += [f"- [#{ledger['issues'][str(t['id'])]['number']}: {t['title']}]({ledger['issues'][str(t['id'])]['url']})" for t in plan["tickets"] if not t["blockedBy"]]
index += ["", "Work any ticket whose blockers are complete. Publishing does not mark acceptance criteria complete or start implementation agents.", ""]
(ROOT / "published.md").write_text("\n".join(index))
print(f"Verified {len(plan['tickets'])} published issues and {verified_edges} native blocking edges.", flush=True)
