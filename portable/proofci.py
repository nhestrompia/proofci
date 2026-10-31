#!/usr/bin/env python3
"""Verify a protected baseline against a candidate using the fixed validator."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import scope

ROOT = Path(__file__).resolve().parent.parent
VALIDATOR = ROOT / "experiments/source-binding"
IMAGE = "python@sha256:6a9220edda062e9223ea0784740a535987299420b96fbfd520b89bbd3e772485"
BWRAP_SHA256 = "b3b829e18a7d43ee589dc37e351cb9480ff7301b493d8227b8c754294638b976"
TOOLCHAIN_SHA256 = "ad4f844f85ce90b22e30efee3a1028ea99d15724fe72de7dc4e16ceda971da00"


class RunTimeout(BaseException):
    pass


def timeout_signal(_signal, _frame):
    signal.setitimer(signal.ITIMER_REAL, 0)
    raise RunTimeout


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def bounded_read(path, limit):
    with path.open("rb") as source:
        data = source.read(limit + 1)
    if len(data) > limit:
        raise ValueError(f"{path.name} exceeds {limit} bytes")
    return data


def parse_json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate field: " + key)
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=unique)


def fields(value, expected):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise ValueError("unexpected or missing fields")


def path_in(root, name):
    if not isinstance(name, str) or not name or Path(name).is_absolute():
        raise ValueError("expected relative path")
    current = root
    for part in Path(name).parts:
        if part in (".", ".."):
            raise ValueError("invalid path component")
        current = current / part
        if current.is_symlink():
            raise ValueError("symbolic links are not allowed in input paths")
    path = (root / name).resolve()
    if not path.is_relative_to(root):
        raise ValueError("path outside input root")
    return path


def verify_snapshot(snapshot, envelope, baseline, deadline):
    def git(*args):
        return subprocess.check_output(["git", "-c", "safe.directory=*", "-c", "core.fsmonitor=false", "-C", str(snapshot), *args],
                                       stderr=subprocess.PIPE, text=True, timeout=max(0, deadline - time.monotonic())).strip()
    if git("rev-parse", "--show-toplevel") != str(snapshot):
        raise ValueError("snapshot must be the repository root")
    if git("rev-parse", "HEAD") != envelope["head"]:
        raise ValueError("snapshot head mismatch")
    if git("rev-parse", "--verify", envelope["base"] + "^{commit}") != envelope["base"]:
        raise ValueError("invalid base commit")
    if git("remote", "get-url", "origin") != envelope["repository"]:
        raise ValueError("repository identity mismatch")
    if git("status", "--porcelain", "--untracked-files=all"):
        raise ValueError("snapshot has uncommitted changes")
    paths = [baseline["candidate"]]
    for item in baseline["obligations"]:
        for name in (item["evidence"], item.get("refutation")):
            if name is None:
                continue
            evidence = path_in(snapshot, name)
            if evidence.is_dir():
                entries = list(evidence.iterdir())
                if len(entries) > 4:
                    raise ValueError("evidence contains too many files")
                if sum(entry.stat().st_size for entry in entries if entry.is_file()) > envelope["resource_policy"]["file_bytes"]:
                    raise ValueError("evidence exceeds file resource limit")
                for item_path in entries:
                    if not item_path.is_file() or item_path.is_symlink():
                        raise ValueError("evidence must contain regular files")
                    if item_path.stat().st_size > 8 * 1024 * 1024:
                        raise ValueError("evidence file exceeds size limit")
                    paths.append(str(item_path.relative_to(snapshot)))
    hashes = {}
    for name in paths:
        if git("ls-files", "--error-unmatch", "--", name) != name:
            raise ValueError("candidate and evidence must be committed")
        committed = subprocess.check_output(["git", "-c", "safe.directory=*", "-C", str(snapshot), "show", envelope["head"] + ":" + name],
                                            stderr=subprocess.PIPE, timeout=max(0, deadline - time.monotonic()))
        if (snapshot / name).read_bytes() != committed:
            raise ValueError("snapshot bytes differ from committed content")
        hashes[name] = hashlib.sha256(committed).hexdigest()
    return hashes


def policy_digest():
    h = hashlib.sha256()
    for name in ("evidence.py", "binding.py", "admission.py", "toolchain.py", "core-dependencies.json"):
        h.update(name.encode() + b"\0" + (VALIDATOR / name).read_bytes())
    return h.hexdigest()


def check_container_limits(limits):
    cgroup = Path("/sys/fs/cgroup")
    def number(name):
        value = (cgroup / name).read_text().strip()
        if not value.isdecimal():
            raise ValueError("container resource limit is not set: " + name)
        return int(value)
    if number("memory.max") > min(limits["memory_bytes"], limits["file_bytes"]):
        raise ValueError("container memory limit exceeds policy")
    if number("memory.swap.max") != 0 or number("pids.max") > limits["processes"]:
        raise ValueError("container swap or process limit exceeds policy")
    cpu = (cgroup / "cpu.max").read_text().split()
    if len(cpu) != 2 or not all(part.isdecimal() for part in cpu) or int(cpu[0]) > int(cpu[1]):
        raise ValueError("container CPU quota exceeds one CPU")


def finish_unchecked(report, baseline, reason):
    if isinstance(baseline, dict) and isinstance(baseline.get("obligations"), list):
        completed = {result["id"] for result in report["results"]}
        for item in baseline["obligations"]:
            if isinstance(item, dict) and isinstance(item.get("id"), str) and item["id"] not in completed and all(k in item for k in ("policy", "evidence")):
                report["results"].append({"id": item["id"], "policy": item["policy"], "evidence": item["evidence"],
                                          "decision": "unproven", "reason": reason})


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
    if hashlib.sha256(bounded_read(candidate, limits["file_bytes"])).hexdigest() != envelope["candidate_sha256"]:
        raise ValueError("candidate digest mismatch")
    obligations = baseline["obligations"]
    if not isinstance(obligations, list) or not obligations:
        raise ValueError("empty baseline")
    seen = set()
    required = False
    for item in obligations:
        if set(item) not in ({"id", "policy", "contract", "contract_sha256", "evidence"},
                             {"id", "policy", "contract", "contract_sha256", "evidence", "refutation"}):
            raise ValueError("unexpected or missing fields")
        if not isinstance(item["id"], str) or not item["id"].strip() or item["id"] in seen:
            raise ValueError("invalid or duplicate obligation id")
        seen.add(item["id"])
        if item["policy"] not in ("required", "advisory"):
            raise ValueError("invalid policy")
        required |= item["policy"] == "required"
        if hashlib.sha256(bounded_read(path_in(baseline_root, item["contract"]), 16384)).hexdigest() != item["contract_sha256"]:
            raise ValueError("contract digest mismatch")
        path_in(snapshot, item["evidence"])
        if "refutation" in item:
            path_in(snapshot, item["refutation"])
    if not required:
        raise ValueError("baseline has no required obligations")
    return candidate


def run_validator(proof, candidate, contract, toolchain, bwrap, limits, deadline, candidate_hash, contract_hash, expected_evidence):
    if digest(bwrap) != BWRAP_SHA256:
        raise ValueError("bubblewrap digest mismatch")
    with tempfile.TemporaryDirectory(prefix="proofci-input-") as temp:
        root = Path(temp)
        (root / "candidate").write_bytes(bounded_read(candidate, 16384))
        (root / "contract").write_bytes(bounded_read(contract, 16384))
        (root / "evidence").mkdir()
        for filename in expected_evidence:
            (root / "evidence" / filename).write_bytes(bounded_read(proof / filename, 8 * 1024 * 1024))
        os.chmod(root / "evidence", 0o755)
        for staged in (root / "candidate", root / "contract", *(root / "evidence" / filename for filename in expected_evidence)):
            os.chmod(staged, 0o644)
        if digest(root / "candidate") != candidate_hash or digest(root / "contract") != contract_hash:
            raise ValueError("staged candidate or contract digest mismatch")
        evidence_hashes = {p.name: digest(p) for p in sorted((root / "evidence").iterdir())}
        if evidence_hashes != expected_evidence:
            raise ValueError("staged evidence differs from committed content")
        os.chmod(root, 0o755)
        if os.environ.get("PROOFCI_CONTAINER") == "1":
            command = [sys.executable, str(VALIDATOR / "evidence.py"), str(root / "evidence"),
                       str(root / "candidate"), str(root / "contract"), "--toolchain", str(toolchain)]
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            try:
                stdout, stderr = process.communicate(timeout=max(0, deadline - time.monotonic()))
            except BaseException:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.communicate(timeout=15)
                raise
            if process.returncode not in (0, 1):
                raise RuntimeError("validator failed: " + stderr.decode(errors="replace")[-1000:])
            result = json.loads(stdout)
            if result.get("decision") not in ("verified", "violated", "unproven") or (process.returncode == 0) != (result["decision"] in ("verified", "violated")):
                raise RuntimeError("validator output and exit status disagree")
            return result, evidence_hashes
        raise RuntimeError("run verification through the resource-limited Linux distribution")



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("envelope", "baseline", "snapshot", "toolchain", "report"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--bwrap", type=Path)
    parser.add_argument("--search-results", type=Path)
    args = parser.parse_args()
    start_monotonic = time.monotonic()
    report = {"version": 1, "status": "error", "results": [], "started_at": time.time()}
    status = 2
    baseline = None
    try:
        report["execution"] = {"image": os.environ.get("PROOFCI_IMAGE_ID", IMAGE), "bubblewrap_sha256": BWRAP_SHA256,
                               "validator_policy_sha256": policy_digest()}
        envelope = parse_json(bounded_read(args.envelope, 1024 * 1024))
        baseline_bytes = bounded_read(args.baseline, 1024 * 1024)
        baseline = parse_json(baseline_bytes)
        report["envelope"] = envelope
        limits = envelope["resource_policy"]
        fields(limits, ("timeout_seconds", "cpu_seconds", "memory_bytes", "file_bytes", "processes"))
        if any(type(value) is not int or value <= 0 for value in limits.values()):
            raise ValueError("resource limits must be positive integers")
        if os.environ.get("PROOFCI_CONTAINER") == "1":
            check_container_limits(limits)
        deadline = time.monotonic() + min(limits["timeout_seconds"], limits["cpu_seconds"])
        signal.signal(signal.SIGALRM, timeout_signal)
        signal.setitimer(signal.ITIMER_REAL, max(0.000001, deadline - time.monotonic()))
        if hashlib.sha256(baseline_bytes).hexdigest() != envelope["baseline_sha256"]:
            raise ValueError("baseline digest mismatch")
        snapshot = args.snapshot.resolve(strict=True)
        baseline_root = args.baseline.resolve(strict=True).parent
        candidate = validate(envelope, baseline, snapshot, baseline_root)
        if envelope["toolchain"] != TOOLCHAIN_SHA256:
            raise ValueError("toolchain identity mismatch")
        if envelope["dependency"] != digest(VALIDATOR / "core-dependencies.json"):
            raise ValueError("dependency identity mismatch")
        if envelope["trust_policy"] != policy_digest():
            raise ValueError("trust policy identity mismatch")
        verify_snapshot(snapshot, envelope, baseline, deadline)
        exhausted = set()
        if args.search_results:
            search_bytes = bounded_read(args.search_results, 1024 * 1024)
            search = parse_json(search_bytes)
            fields(search, ("version", "exhausted"))
            ids = {item["id"] for item in baseline["obligations"]}
            if (type(search["version"]) is not int or search["version"] != 1
                    or not isinstance(search["exhausted"], list)
                    or any(not isinstance(name, str) or name not in ids for name in search["exhausted"])
                    or len(set(search["exhausted"])) != len(search["exhausted"])):
                raise ValueError("invalid search results")
            exhausted = set(search["exhausted"])
            report["search_results_sha256"] = hashlib.sha256(search_bytes).hexdigest()
        candidate_bytes = bounded_read(candidate, limits["file_bytes"])
        candidate_reason = ("source exceeds adapter input limit" if len(candidate_bytes) > 16384
                            else scope.admission(candidate_bytes))
        report["support"] = {
            "policy_version": scope.SUPPORT_VERSION,
            "policy_sha256": policy_digest(),
            "admitted_candidate": baseline["candidate"],
            "symbol": "target" if candidate_reason is None else None,
            "admission_reason": candidate_reason,
            "assumptions": ["protected baseline and verifier", "pinned Lean toolchain and trusted host"],
            "permitted_foundational_axioms": sorted(scope.binding.PERMITTED_AXIOMS),
            "exclusions": ["imports, additional declarations, macros, instances, attributes and runtime replacements",
                           "compiled binaries, deployment, foreign languages and all other repository code"],
            "guarantee": "Named approved properties of the admitted source-level target only",
            "trusted_tools": ["Lean kernel", "Lean exporter", "Nanoda", "Comparator", "source adapter"],
            "lean_commit": scope.binding.LEAN_COMMIT,
            "toolchain_sha256": TOOLCHAIN_SHA256,
            "deferred_frontends": ["Rust/Aeneas"],
        }
        report["coverage"] = scope.describe(snapshot, envelope["base"], envelope["head"], baseline, deadline)
        if candidate_reason is not None:
            report["support"]["unsupported_dependency"] = {"path": baseline["candidate"], "reason": candidate_reason}
            if any(change["path"] == baseline["candidate"] for change in report["coverage"]["changes"]):
                report["coverage"]["unsupported_changed_code"].append(
                    {"path": baseline["candidate"], "reason": candidate_reason, "required_dependency": True})
        for item in baseline["obligations"]:
            result = {"id": item["id"], "policy": item["policy"], "evidence": item["evidence"]}
            (contract, _), precondition = scope.binding.load_contract(bounded_read(path_in(baseline_root, item["contract"]), 16384))
            result["symbol"] = "target"
            result["property"] = (f"({precondition}) → " if precondition else "") + "target x = " + contract
            if candidate_reason is not None:
                result.update(decision="unproven", reason="unsupported_semantics", detail=candidate_reason)
                report["results"].append(result)
                continue
            submissions = []
            for name in (item["evidence"], item.get("refutation")):
                if name is None:
                    continue
                proof = path_in(snapshot, name)
                checked = {"decision": "unproven", "reason": "missing_evidence"}
                evidence_hashes = {}
                if proof.exists():
                    if deadline - time.monotonic() <= 0:
                        checked["reason"] = "timeout"
                    elif args.bwrap is None:
                        checked["reason"] = "validation_unavailable"
                    else:
                        try:
                            committed = verify_snapshot(snapshot, envelope, baseline, deadline)
                            expected_evidence = {p.name: committed[str(p.relative_to(snapshot))] for p in proof.iterdir()}
                            checked, evidence_hashes = run_validator(proof, candidate, path_in(baseline_root, item["contract"]),
                                                    args.toolchain.resolve(strict=True), args.bwrap.resolve(strict=True),
                                                    envelope["resource_policy"], deadline, envelope["candidate_sha256"], item["contract_sha256"], expected_evidence)
                            verify_snapshot(snapshot, envelope, baseline, deadline)
                            if time.monotonic() >= deadline:
                                raise subprocess.TimeoutExpired("verification", envelope["resource_policy"]["timeout_seconds"])
                            if evidence_hashes != {p.name: digest(p) for p in sorted(proof.iterdir())}:
                                raise ValueError("evidence changed during validation")
                        except (subprocess.TimeoutExpired, RunTimeout):
                            checked = {"decision": "unproven", "reason": "timeout"}
                        except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
                            checked = {"decision": "unproven", "reason": "validation_unavailable", "detail": str(error)}
                submissions.append({"evidence": name, "validation": checked, "evidence_sha256": evidence_hashes})
            accepted = [entry for entry in submissions if entry["validation"]["decision"] in ("verified", "violated")]
            execution_errors = {"validation_unavailable", "build_failure", "checker_disagreement", "contradictory_evidence", "timeout"}
            error_entry = next((entry for entry in submissions if entry["validation"]["reason"] in execution_errors), None)
            if len({entry["validation"]["decision"] for entry in accepted}) > 1:
                result.update(decision="unproven", reason="contradictory_evidence")
            else:
                selected = error_entry or (accepted[0] if accepted else next((entry for entry in submissions if entry["validation"]["reason"] != "missing_evidence"), submissions[0]))
                result.update(evidence=selected["evidence"], decision=selected["validation"]["decision"], reason=selected["validation"]["reason"],
                              validation=selected["validation"], evidence_sha256=selected["evidence_sha256"])
            if result["decision"] == "unproven" and result["reason"] in ("missing_evidence", "proof_failed", "unproven") and item["id"] in exhausted:
                result["reason"] = "search_exhausted"
                result["search"] = {"status": "exhausted"}
            if len(submissions) > 1:
                result["submissions"] = submissions
            report["results"].append(result)
        report["property_counts"] = {
            decision: sum(result["decision"] == decision for result in report["results"])
            for decision in ("verified", "violated", "unproven")
        }
        failures = {"validation_unavailable", "build_failure", "checker_disagreement", "contradictory_evidence", "timeout"}
        if any(r["reason"] in failures for r in report["results"]):
            raise ValueError("validator execution failed")
        if time.monotonic() >= deadline:
            raise ValueError("verification timeout")
        passed = all(r["decision"] == "verified" for r in report["results"] if r["policy"] == "required")
        report["status"] = "passed" if passed else "blocked"
        status = 0 if passed else 1
    except KeyboardInterrupt:
        report["reason"] = "cancelled"
        finish_unchecked(report, baseline, "cancelled")
    except (subprocess.TimeoutExpired, RunTimeout):
        report["reason"] = "timeout"
        finish_unchecked(report, baseline, "timeout")
    except (OSError, ValueError, KeyError, TypeError, RecursionError, UnicodeError, subprocess.CalledProcessError) as error:
        report["reason"] = str(error)
    signal.setitimer(signal.ITIMER_REAL, 0)
    report["finished_at"] = time.time()
    report["usage"] = {"model_calls": 0, "elapsed_seconds": time.monotonic() - start_monotonic}
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
