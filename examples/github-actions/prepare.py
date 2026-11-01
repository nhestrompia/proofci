#!/usr/bin/env python3
"""Create a ProofCI envelope for a GitHub pull request source commit."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

VERIFIER = Path(os.environ.get("PROOFCI_VERIFIER", "/opt/proofci"))
sys.path.insert(0, str(VERIFIER / "portable"))
import proofci


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(event, snapshot, baseline, output, event_name):
    if event.get("action") not in ("opened", "reopened", "synchronize", "ready_for_review", "labeled"):
        raise ValueError("unsupported pull request event")
    pr = event["pull_request"]
    head, base = pr["head"]["sha"], pr["base"]["sha"]
    if any(not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value) for value in (head, base)):
        raise ValueError("invalid pull request commit")
    snapshot = snapshot.resolve(strict=True)
    baseline = baseline.resolve(strict=True)
    if baseline.is_relative_to(snapshot):
        raise ValueError("baseline must be outside the candidate checkout")
    def git(*args):
        return subprocess.check_output(["git", "-C", str(snapshot), *args], text=True).strip()
    if git("rev-parse", "HEAD") != head or git("rev-parse", "--verify", base + "^{commit}") != base:
        raise ValueError("checkout does not contain the requested head and base")
    policy = json.loads(baseline.read_bytes())
    candidate = proofci.path_in(snapshot, policy["candidate"])
    envelope = {
        "version": 1, "repository": git("remote", "get-url", "origin"),
        "head": head, "base": base, "candidate_sha256": sha(candidate),
        "baseline_sha256": sha(baseline),
        "dependency": proofci.digest(proofci.VALIDATOR / "core-dependencies.json"),
        "toolchain": proofci.TOOLCHAIN_SHA256, "trust_policy": proofci.policy_digest(),
        "resource_policy": {"timeout_seconds": 180, "cpu_seconds": 180,
            "memory_bytes": 2147483648, "file_bytes": 2147483648, "processes": 256},
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "envelope.json").write_text(json.dumps(envelope, indent=2) + "\n")
    (output / "github.json").write_text(json.dumps({"platform": "github", "event": event_name,
        "pull_request": pr["number"], "head": head, "base": base,
        "scope": "source-head-only"}, indent=2) + "\n")


if __name__ == "__main__":
    try:
        event_name = os.environ.get("GITHUB_EVENT_NAME")
        if event_name not in ("pull_request", "pull_request_target"):
            raise ValueError("expected a pull request event")
        prepare(json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_bytes()),
                Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), event_name)
    except (OSError, ValueError, KeyError, IndexError, TypeError, subprocess.SubprocessError) as error:
        print(f"proofci GitHub preparation failed: {error}", file=sys.stderr)
        sys.exit(2)
