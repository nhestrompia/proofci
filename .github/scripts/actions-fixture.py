#!/usr/bin/env python3
"""Create one committed snapshot and run the public portable CLI."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / "portable"))
import proofci

case, destination = sys.argv[1:]
output = Path(destination).resolve()
output.mkdir(parents=True, exist_ok=True)
snapshot = output / "snapshot"
snapshot.mkdir()
fixtures = root / "experiments/source-binding/fixtures"
shutil.copy(fixtures / "candidate.lean", snapshot / "candidate.lean")
shutil.copytree(fixtures / "verified", snapshot / "evidence")
shutil.copy(fixtures / "contract.json", output / "contract.json")
def git(*args):
    return subprocess.check_output(["git", "-C", str(snapshot), *args], text=True).strip()
git("init", "-q")
git("config", "user.name", "ProofCI fixture")
git("config", "user.email", "fixture@example.invalid")
git("remote", "add", "origin", "https://example.invalid/fixture.git")
if case == "unproven":
    shutil.rmtree(snapshot / "evidence")
git("add", ".")
git("commit", "-qm", case)
head = git("rev-parse", "HEAD")
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
baseline = {"version": 1, "candidate": "candidate.lean", "obligations": [
    {"id": "increment", "policy": "required", "contract": "contract.json",
     "contract_sha256": digest(output / "contract.json"), "evidence": "evidence"}]}
(output / "baseline.json").write_text(json.dumps(baseline))
envelope = {"version": 1, "repository": "https://example.invalid/fixture.git", "head": head, "base": head,
    "candidate_sha256": digest(snapshot / "candidate.lean"), "baseline_sha256": digest(output / "baseline.json"),
    "dependency": digest(proofci.VALIDATOR / "core-dependencies.json"), "toolchain": proofci.TOOLCHAIN_SHA256,
    "trust_policy": proofci.policy_digest(), "resource_policy": {"timeout_seconds": 180, "cpu_seconds": 180,
    "memory_bytes": 2147483648, "file_bytes": 2147483648, "processes": 256}}
if case == "execution-failure":
    envelope["baseline_sha256"] = "0" * 64
(output / "envelope.json").write_text(json.dumps(envelope))
command = [sys.executable, str(root / "portable/container.py"), "--envelope", str(output / "envelope.json"),
           "--baseline", str(output / "baseline.json"), "--snapshot", str(snapshot), "--report", str(output / "report.json")]
status = subprocess.run(command, check=False).returncode
(output / "exit-code.txt").write_text(f"{status}\n")
if (output / "report.json").exists():
    subprocess.run([sys.executable, str(root / "portable/replay.py"), "export", "--envelope", str(output / "envelope.json"),
                    "--baseline", str(output / "baseline.json"), "--snapshot", str(snapshot), "--report", str(output / "report.json"),
                    "--output", str(output / "evidence.tar")], check=False)
raise SystemExit(status)
