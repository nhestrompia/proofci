#!/usr/bin/env python3
"""Verify a protected baseline against a candidate using the fixed validator."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import signal
import sys
import time

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate field: " + key)
            result[key] = value
        return result
    return json.loads(path.read_bytes(), object_pairs_hook=unique)


def fields(value, expected):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise ValueError("unexpected or missing fields")


def path_in(root, name):
    if not isinstance(name, str) or not name or Path(name).is_absolute():
        raise ValueError("expected relative path")
    path = (root / name).resolve()
    if not path.is_relative_to(root):
        raise ValueError("path outside input root")
    return path


def validate(envelope, baseline, snapshot, baseline_root):
    fields(envelope, ("version", "repository", "head", "base", "candidate_sha256",
                      "baseline_sha256", "dependency", "toolchain", "trust_policy", "resource_policy"))
    if type(envelope["version"]) is not int or envelope["version"] != 1:
        raise ValueError("unsupported envelope version")
    for key in ("repository", "head", "base", "dependency", "toolchain", "trust_policy"):
        if not isinstance(envelope[key], str) or not envelope[key].strip():
            raise ValueError("missing " + key)
    for key in ("candidate_sha256", "baseline_sha256"):
        if not isinstance(envelope[key], str) or not re.fullmatch("[0-9a-f]{64}", envelope[key]):
            raise ValueError("invalid " + key)
    limits = envelope["resource_policy"]
    fields(limits, ("timeout_seconds", "cpu_seconds", "memory_bytes", "file_bytes", "processes"))
    if any(type(value) is not int or value <= 0 for value in limits.values()):
        raise ValueError("resource limits must be positive integers")
    fields(baseline, ("version", "candidate", "obligations"))
    if type(baseline["version"]) is not int or baseline["version"] != 1:
        raise ValueError("unsupported baseline version")
    candidate = path_in(snapshot, baseline["candidate"])
    if digest(candidate) != envelope["candidate_sha256"]:
        raise ValueError("candidate digest mismatch")
    obligations = baseline["obligations"]
    if not isinstance(obligations, list) or not obligations:
        raise ValueError("empty baseline")
    seen = set()
    required = False
    for item in obligations:
        fields(item, ("id", "policy", "contract", "contract_sha256", "evidence"))
        if not isinstance(item["id"], str) or not item["id"].strip() or item["id"] in seen:
            raise ValueError("invalid or duplicate obligation id")
        seen.add(item["id"])
        if item["policy"] not in ("required", "advisory"):
            raise ValueError("invalid policy")
        required |= item["policy"] == "required"
        if digest(path_in(baseline_root, item["contract"])) != item["contract_sha256"]:
            raise ValueError("contract digest mismatch")
        path_in(snapshot, item["evidence"])
    if not required:
        raise ValueError("baseline has no required obligations")
    return candidate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("envelope", "baseline", "snapshot", "toolchain", "report"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    report = {"version": 1, "status": "error", "results": [], "started_at": time.time()}
    status = 2
    try:
        envelope = read_json(args.envelope)
        baseline = read_json(args.baseline)
        report["envelope"] = envelope
        if digest(args.baseline) != envelope["baseline_sha256"]:
            raise ValueError("baseline digest mismatch")
        snapshot = args.snapshot.resolve(strict=True)
        baseline_root = args.baseline.resolve(strict=True).parent
        candidate = validate(envelope, baseline, snapshot, baseline_root)
        for item in baseline["obligations"]:
            proof = path_in(snapshot, item["evidence"])
            result = {"id": item["id"], "policy": item["policy"], "evidence": item["evidence"]}
            if not proof.exists():
                result.update(decision="unproven", reason="missing_evidence")
            else:
                result.update(decision="unproven", reason="validation_unavailable")
            report["results"].append(result)
        failures = {"validation_unavailable", "build_failure", "checker_disagreement", "contradictory_evidence"}
        if any(r["reason"] in failures for r in report["results"]):
            raise ValueError("validator execution failed")
        passed = all(r["decision"] == "verified" for r in report["results"] if r["policy"] == "required")
        if passed:
            raise ValueError("snapshot and policy identities are not yet independently verified")
        report["status"] = "blocked"
        status = 1
    except KeyboardInterrupt:
        report["reason"] = "cancelled"
    except (OSError, ValueError, KeyError, TypeError, RecursionError, UnicodeError) as error:
        report["reason"] = str(error)
    report["finished_at"] = time.time()
    report["usage"] = {"model_calls": 0}
    try:
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    except OSError as error:
        print("cannot write report: " + str(error), file=sys.stderr)
        return 2
    return status


if __name__ == "__main__":
    def cancel(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, cancel)
    raise SystemExit(main())
