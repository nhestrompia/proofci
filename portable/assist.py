"""Control-process orchestration for optional proof repair.

The caller supplies a broker configured by the deployment. Candidate code cannot
choose the provider, credentials, authorization policy, or limits.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

import proofci
from broker import AuthorizationDenied, BudgetExhausted


def _run(command, deadline):
    process = subprocess.Popen(command, start_new_session=True)
    try:
        return process.wait(timeout=max(0, deadline - time.monotonic()))
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait(timeout=20)
        except ProcessLookupError:
            pass
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        raise


def run(*, envelope_path, baseline_path, snapshot, report_path, artifacts, broker=None):
    """Run deterministic checks and, if configured, authorized bounded repairs."""
    started = time.monotonic()
    envelope_path, baseline_path = Path(envelope_path).resolve(), Path(baseline_path).resolve()
    snapshot, report_path, artifacts = Path(snapshot).resolve(), Path(report_path).resolve(), Path(artifacts).resolve()
    if artifacts.is_relative_to(snapshot) or artifacts.is_relative_to(baseline_path.parent):
        raise ValueError("artifacts must be outside the snapshot and protected baseline")
    artifacts.mkdir(parents=True, exist_ok=True)
    envelope = proofci.parse_json(proofci.bounded_read(envelope_path, 1024 * 1024))
    baseline_bytes = proofci.bounded_read(baseline_path, 1024 * 1024)
    baseline = proofci.parse_json(baseline_bytes)
    if hashlib.sha256(baseline_bytes).hexdigest() != envelope["baseline_sha256"]:
        raise ValueError("baseline digest mismatch")
    deadline = started + min(900, envelope["resource_policy"]["timeout_seconds"],
                             envelope["resource_policy"]["cpu_seconds"])
    candidate = proofci.validate(envelope, baseline, snapshot, baseline_path.parent)
    command = [sys.executable, str(Path(__file__).with_name("container.py")),
               "--envelope", str(envelope_path), "--baseline", str(baseline_path),
               "--snapshot", str(snapshot), "--artifacts", str(artifacts)]
    with tempfile.TemporaryDirectory(prefix="proofci-assist-") as temp:
        root = Path(temp)
        attempt_report = root / "report.json"
        def execute(extra, until):
            status = _run(command + ["--report", str(attempt_report)] + extra, until)
            result = proofci.parse_json(proofci.bounded_read(attempt_report, 4 * 1024 * 1024))
            if (not isinstance(result, dict) or type(result.get("version")) is not int or result["version"] != 1
                    or status not in (0, 1, 2) or (status == 0) != (result.get("status") == "passed")
                    or (status == 2 and result.get("status") != "error")):
                raise ValueError("verification report and exit status disagree")
            if status in (0, 1):
                expected_ids = [extra[1]] if extra else [item["id"] for item in baseline["obligations"]]
                expected_statuses = {"attempt"} if extra else {"passed", "blocked"}
                results = result.get("results")
                usage = result.get("usage")
                policies = {item["id"]: item["policy"] for item in baseline["obligations"]}
                if (result.get("status") not in expected_statuses or result.get("envelope") != envelope
                        or not isinstance(usage, dict) or type(usage.get("model_calls")) is not int
                        or usage["model_calls"] != 0
                        or not isinstance(results, list) or len(results) != len(expected_ids)
                        or any(not isinstance(item, dict) for item in results)
                        or [item.get("id") for item in results] != expected_ids
                        or any(item.get("policy") != policies[item["id"]]
                               or item.get("decision") not in ("verified", "violated", "unproven")
                               or not isinstance(item.get("reason"), str) for item in results)):
                    raise ValueError("malformed verification report")
                obligations_by_id = {item["id"]: item for item in baseline["obligations"]}
                for item in results:
                    approved = obligations_by_id[item["id"]]
                    if item.get("evidence") not in (approved["evidence"], approved.get("refutation")):
                        raise ValueError("verification evidence identity mismatch")
                    if item["decision"] in ("verified", "violated"):
                        validation = item.get("validation")
                        if (not isinstance(validation, dict) or validation.get("decision") != item["decision"]
                                or validation.get("candidate_sha256") != envelope["candidate_sha256"]
                                or validation.get("contract_sha256") != obligations_by_id[item["id"]]["contract_sha256"]):
                            raise ValueError("verified result lacks matching independent validation")
                if not extra and (result["status"] == "passed") != all(
                        item["decision"] == "verified" for item in results if item["policy"] == "required"):
                    raise ValueError("verification gate and results disagree")
            return status, result
        status, report = execute([], deadline)
        if status == 2 or broker is None:
            report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
            return status
        best = {item["id"]: item for item in report["results"]}
        journal_name = None
        if any(item["decision"] != "verified" for item in best.values()):
            journal_name = "requests-" + hashlib.sha256(broker.run_id.encode()).hexdigest() + ".jsonl"
            journal_path = artifacts / journal_name
            descriptor = os.open(journal_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            os.close(descriptor)
            directory_fd = os.open(artifacts, os.O_RDONLY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
            def record_transition(event):
                data = (json.dumps(event, sort_keys=True, separators=(",", ":")) + "\n").encode()
                descriptor = os.open(journal_path, os.O_WRONLY | os.O_APPEND | os.O_NOFOLLOW)
                with os.fdopen(descriptor, "ab") as journal:
                    journal.write(data)
                    journal.flush()
                    os.fsync(journal.fileno())
            broker.set_transition_sink(record_transition)
        obligations = {item["id"]: item for item in baseline["obligations"]}
        execution_error = None
        for obligation, result in list(best.items()):
            if result["decision"] != "unproven":
                continue
            if result.get("reason") == "obligation_budget_exhausted":
                result["repair_reason"] = "timeout"
                continue
            if result.get("reason") not in ("missing_evidence", "invalid_evidence", "proof_failed", "unproven", "search_exhausted"):
                continue
            elapsed = result.get("elapsed_seconds", 120)
            obligation_deadline = min(deadline, time.monotonic() + max(0, 120 - elapsed))
            for _ in range(5):
                if time.monotonic() >= obligation_deadline:
                    result["repair_reason"] = "timeout"
                    break
                try:
                    proofci.verify_snapshot(snapshot, envelope, baseline, obligation_deadline)
                    contract = proofci.path_in(baseline_path.parent, obligations[obligation]["contract"])
                    if proofci.digest(candidate) != envelope["candidate_sha256"] or proofci.digest(contract) != obligations[obligation]["contract_sha256"]:
                        raise ValueError("run inputs changed")
                    identity, body = broker.request(repository=envelope["repository"], obligation=obligation,
                        candidate=proofci.bounded_read(candidate, 16384).decode(),
                        contract=proofci.bounded_read(contract, 16384).decode(),
                        diagnostic=result.get("reason", "unproven"), deadline=obligation_deadline)
                    suggestion = artifacts / (identity + ".lean")
                    with suggestion.open("x") as target:
                        target.write(body)
                    broker.events[-1]["artifact"] = suggestion.name
                    status, current = execute(["--repair-id", obligation, "--proof-body", str(suggestion)], obligation_deadline)
                    if status == 2:
                        result["repair_reason"] = "validation_unavailable"
                        execution_error = current.get("reason", "repair validation failed")
                        break
                    checked = next(item for item in current["results"] if item["id"] == obligation)
                    if checked["decision"] == "verified":
                        best[obligation] = checked
                        break
                except AuthorizationDenied:
                    result["repair_reason"] = "not_authorized"
                    break
                except TimeoutError:
                    result["repair_reason"] = "timeout"
                    break
                except BudgetExhausted:
                    result["repair_reason"] = "budget_or_context_exhausted"
                    break
                except ValueError:
                    result["repair_reason"] = "execution_unavailable"
                    execution_error = "repair execution returned invalid data"
                    break
                except RuntimeError:
                    result["repair_reason"] = "provider_unavailable"
                    break
                except subprocess.TimeoutExpired:
                    result["repair_reason"] = "timeout"
                    if time.monotonic() < obligation_deadline:
                        execution_error = "repair execution timed out unexpectedly"
                    break
                except (OSError, subprocess.SubprocessError):
                    result["repair_reason"] = "execution_unavailable"
                    execution_error = "repair execution failed"
                    break
            else:
                result["repair_reason"] = "attempts_exhausted"
            if execution_error is not None:
                break
        report["results"] = [best[item["id"]] for item in baseline["obligations"]]
        report["property_counts"] = {decision: sum(item["decision"] == decision for item in report["results"])
                                     for decision in ("verified", "violated", "unproven")}
        try:
            if hashlib.sha256(proofci.bounded_read(baseline_path, 1024 * 1024)).hexdigest() != envelope["baseline_sha256"]:
                raise ValueError("baseline changed during run")
            proofci.validate(envelope, baseline, snapshot, baseline_path.parent)
            proofci.verify_snapshot(snapshot, envelope, baseline, deadline)
            if time.monotonic() >= deadline:
                raise TimeoutError("run timed out")
            if execution_error is not None:
                raise ValueError(execution_error)
            passed = all(item["decision"] == "verified" for item in report["results"] if item["policy"] == "required")
            report["status"] = "passed" if passed else "blocked"
            status = 0 if passed else 1
        except (OSError, ValueError, subprocess.SubprocessError, TimeoutError) as error:
            report["status"] = "error"
            report["reason"] = str(error)
            status = 2
        report["usage"].update(model_calls=len([event for event in broker.events if event["state"] == "reserved"]),
                               input_tokens=broker.input_tokens, output_tokens=broker.output_tokens,
                               cost_micros=broker.cost_micros, requests=broker.events,
                               elapsed_seconds=time.monotonic() - started)
        if journal_name is not None:
            report["usage"]["journal"] = journal_name
        report["finished_at"] = time.time()
        report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        return status


def main():
    import argparse
    from broker import Broker, Limits
    from openai_provider import OpenAIProvider

    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("envelope", "baseline", "snapshot", "report", "artifacts"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--model-config", type=Path)
    args = parser.parse_args()
    broker = None
    try:
        if args.model_config is not None:
            config_path = args.model_config.resolve(strict=True)
            if config_path.is_relative_to(args.snapshot.resolve()):
                raise ValueError("model configuration must be outside the snapshot")
            config = proofci.parse_json(proofci.bounded_read(config_path, 65536))
            required = {"repository", "run_id", "head", "baseline_sha256", "authorized", "model", "limits"}
            if not required.issubset(config) or set(config) - required - {"private", "private_source_consent"}:
                raise ValueError("invalid model configuration")
            if type(config["authorized"]) is not bool:
                raise ValueError("invalid model authorization")
            private = config.get("private", True)
            consent = config.get("private_source_consent", False)
            if type(private) is not bool or type(consent) is not bool:
                raise ValueError("invalid source consent")
            if any(not isinstance(config[key], str) or not config[key] for key in
                   ("repository", "run_id", "head", "baseline_sha256", "model")):
                raise ValueError("invalid model configuration identity")
            limits = Limits(**config["limits"])
            provider = OpenAIProvider(api_key=os.environ.get("PROOFCI_OPENAI_API_KEY"), model=config["model"])
            envelope = proofci.parse_json(proofci.bounded_read(args.envelope, 1024 * 1024))
            baseline_raw = proofci.bounded_read(args.baseline, 1024 * 1024)
            baseline = proofci.parse_json(baseline_raw)
            run_matches = (config["authorized"] and envelope["repository"] == config["repository"]
                           and envelope["head"] == config["head"]
                           and envelope["baseline_sha256"] == config["baseline_sha256"]
                           and hashlib.sha256(baseline_raw).hexdigest() == config["baseline_sha256"])
            snapshot = args.snapshot.resolve(strict=True)
            baseline_root = args.baseline.resolve(strict=True).parent
            candidate_path = proofci.validate(envelope, baseline, snapshot, baseline_root)
            obligations = {item["id"]: item for item in baseline["obligations"]}
            def authorize(repository, run_id, obligation, candidate, contract, deadline):
                if not run_matches or repository != config["repository"] or run_id != config["run_id"] or obligation not in obligations:
                    return False
                item = obligations[obligation]
                proofci.verify_snapshot(snapshot, envelope, baseline, deadline)
                return (proofci.bounded_read(candidate_path, 16384).decode() == candidate
                        and hashlib.sha256(candidate.encode()).hexdigest() == envelope["candidate_sha256"]
                        and proofci.bounded_read(proofci.path_in(baseline_root, item["contract"]), 16384).decode() == contract
                        and hashlib.sha256(contract.encode()).hexdigest() == item["contract_sha256"])
            broker = Broker(run_id=config["run_id"], repository=config["repository"], private=private,
                            consent=lambda repository: consent and repository == config["repository"],
                            authorize=authorize,
                            limits=limits, provider=provider, run_deadline=time.monotonic() + 900)
        return run(envelope_path=args.envelope, baseline_path=args.baseline, snapshot=args.snapshot,
                   report_path=args.report, artifacts=args.artifacts, broker=broker)
    except KeyboardInterrupt:
        report = {"version": 1, "status": "error", "reason": "cancelled"}
        if broker is not None:
            report["usage"] = {"input_tokens": broker.input_tokens, "output_tokens": broker.output_tokens,
                               "cost_micros": broker.cost_micros, "requests": broker.events}
        try:
            args.report.write_text(json.dumps(report) + "\n")
        except OSError:
            print("cannot write report", file=sys.stderr)
        return 2
    except (OSError, ValueError, TypeError, KeyError, PermissionError, subprocess.SubprocessError) as error:
        try:
            args.report.write_text(json.dumps({"version": 1, "status": "error", "reason": str(error)}) + "\n")
        except OSError:
            print("cannot write report", file=sys.stderr)
        return 2


if __name__ == "__main__":
    def cancel(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, cancel)
    raise SystemExit(main())
