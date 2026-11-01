#!/usr/bin/env python3
"""Dispatch one immutable verification snapshot to the isolated worker.

This is the trusted operator boundary.  It stages only content-addressed
dependencies, passes no caller environment through to the worker, and treats
the worker's JSON as a claim that must satisfy the public report contract.
The worker's proof result is accepted only when its report contains the
independent validation identity for every accepted property.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

import dependencies
import proofci
import report as report_contract
from worker_artifacts import collect_artifacts, read_identities


MAX_REPORT_BYTES = 8 * 1024 * 1024


def _read_json(path, limit):
    data = proofci.bounded_read(Path(path), limit)
    return proofci.parse_json(data), data


def _write_error(path, reason):
    Path(path).write_text(json.dumps({"version": 1, "status": "error", "reason": str(reason)},
                                     sort_keys=True) + "\n")


def _run_process(command, deadline):
    process = subprocess.Popen(command, start_new_session=True)
    try:
        return process.wait(timeout=max(0, deadline - time.monotonic()))
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGTERM)
            process.wait(timeout=10)
        except ProcessLookupError:
            pass
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        raise


def _preflight(envelope, baseline, snapshot, baseline_root, deadline):
    if baseline_root.is_relative_to(snapshot):
        raise ValueError("protected baseline must be outside the candidate snapshot")
    if envelope["toolchain"] != proofci.TOOLCHAIN_SHA256:
        raise ValueError("toolchain identity mismatch")
    if envelope["dependency"] != proofci.digest(proofci.VALIDATOR / "core-dependencies.json"):
        raise ValueError("dependency identity mismatch")
    if envelope["trust_policy"] != proofci.policy_digest():
        raise ValueError("trust policy identity mismatch")
    proofci.verify_snapshot(snapshot, envelope, baseline, deadline)


def run(*, envelope_path, baseline_path, snapshot, report_path, dependency_manifest=None,
        dependency_cache=None, artifacts=None, artifact_manifest=None, image=None, launcher=None):
    """Run a deterministic worker dispatch and write the public report.

    ``launcher`` is a test seam accepting ``(command, deadline)``.  Production
    calls use the resource-limited container launcher as a child process.
    """
    started = time.monotonic()
    envelope_path = Path(envelope_path).resolve(strict=True)
    baseline_input = Path(baseline_path)
    snapshot_input = Path(snapshot)
    if baseline_input.is_symlink() or snapshot_input.is_symlink():
        _write_error(report_path, "snapshot and protected baseline must not be symbolic links")
        return 2
    baseline_path = baseline_input.resolve(strict=True)
    snapshot = snapshot_input.resolve(strict=True)
    report_path = Path(report_path).resolve()
    try:
        envelope, _ = _read_json(envelope_path, 1024 * 1024)
        baseline, baseline_bytes = _read_json(baseline_path, 1024 * 1024)
        if hashlib.sha256(baseline_bytes).hexdigest() != envelope.get("baseline_sha256"):
            raise ValueError("baseline digest mismatch")
        if dependency_manifest is not None and dependency_cache is None:
            raise ValueError("dependency cache is required with a dependency manifest")
        if dependency_manifest is None and dependency_cache is not None:
            raise ValueError("dependency manifest is required with a dependency cache")
        for protected_input in (dependency_manifest, dependency_cache, artifact_manifest):
            if protected_input is not None:
                input_input = Path(protected_input)
                if input_input.is_symlink():
                    raise ValueError("dispatch metadata must not be symbolic links")
                input_path = input_input.resolve(strict=True)
                if input_path.is_relative_to(snapshot) or input_path.is_relative_to(baseline_path.parent):
                    raise ValueError("dispatch metadata must be outside the snapshot and protected baseline")
        deadline = started + min(900, envelope["resource_policy"]["timeout_seconds"],
                                envelope["resource_policy"]["cpu_seconds"])
        candidate = proofci.validate(envelope, baseline, snapshot, baseline_path.parent)
        _preflight(envelope, baseline, snapshot, baseline_path.parent, deadline)
        if (artifact_manifest is None) != (artifacts is None):
            raise ValueError("worker artifact directory and manifest must be supplied together")
        if artifacts is not None:
            artifact_input = Path(artifacts)
            if artifact_input.is_symlink():
                raise ValueError("worker artifact directory must not be a symbolic link")
            artifacts = artifact_input.resolve(strict=True)
            if artifacts.is_relative_to(snapshot) or artifacts.is_relative_to(baseline_path.parent):
                raise ValueError("worker artifacts must be outside the snapshot and protected baseline")

        with tempfile.TemporaryDirectory(prefix="proofci-dispatch-") as temporary:
            staged = None
            dependency_info = None
            if dependency_manifest is not None:
                staged = Path(temporary) / "dependencies"
                dependency_info = dependencies.stage(dependency_manifest, dependency_cache, staged)
            command = [sys.executable, str(Path(__file__).with_name("container.py")),
                       "--envelope", str(envelope_path), "--baseline", str(baseline_path),
                       "--snapshot", str(snapshot)]
            if image is not None:
                command.extend(["--image", image])
            if staged is not None:
                command.extend(["--dependencies", str(staged)])
            worker_report_path = Path(temporary) / "worker-report.json"
            worker_status = (launcher or _run_process)(
                command + ["--report", str(worker_report_path), "--phase", "worker",
                           "--validator-only"], deadline)
            worker_report = proofci.parse_json(proofci.bounded_read(worker_report_path, MAX_REPORT_BYTES))
            if worker_status in (0, 1):
                report_contract.validate(worker_report, envelope, baseline)
            elif worker_status == 2:
                if worker_report.get("version") != 1 or worker_report.get("status") != "error":
                    raise ValueError("worker status and report disagree")
                raise ValueError("isolated worker failed: " + worker_report.get("reason", "unknown error"))
            else:
                raise ValueError("worker returned an invalid exit status")
            final_report_path = Path(temporary) / "final-report.json"
            final_status = (launcher or _run_process)(
                command + ["--report", str(final_report_path), "--phase", "final-validation",
                           "--validator-only"], deadline)
            final_report = proofci.parse_json(proofci.bounded_read(final_report_path, MAX_REPORT_BYTES))
            if final_status in (0, 1):
                report_contract.validate(final_report, envelope, baseline)
            elif final_status == 2:
                if final_report.get("version") != 1 or final_report.get("status") != "error":
                    raise ValueError("final validator status and report disagree")
            else:
                raise ValueError("final validator returned an invalid exit status")
            worker_report_digest = hashlib.sha256(
                json.dumps(worker_report, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
            worker_report = final_report
            if artifact_manifest is not None:
                identities = read_identities(artifact_manifest)
                collected = collect_artifacts(artifacts, identities, envelope["resource_policy"]["file_bytes"])
                worker_report["worker_artifacts"] = {
                    "files": {name: hashlib.sha256(data).hexdigest() for name, data in collected.items()},
                    "bytes": sum(len(data) for data in collected.values()),
                }
            worker_report["dispatch"] = {
                "mode": "isolated-worker",
                "worker_status": worker_status,
                "final_status": final_status,
                "worker_report_sha256": worker_report_digest,
                "elapsed_seconds": time.monotonic() - started,
                "dependencies": dependency_info or {"mode": "pinned-image"},
            }
            report_path.write_text(json.dumps(worker_report, indent=2, sort_keys=True) + "\n")
            return final_status
    except KeyboardInterrupt:
        _write_error(report_path, "cancelled")
        return 2
    except (OSError, ValueError, KeyError, TypeError, RecursionError, UnicodeError,
            subprocess.SubprocessError) as error:
        _write_error(report_path, error)
        return 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("envelope", "baseline", "snapshot", "report"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--dependency-manifest", type=Path)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--artifacts", type=Path)
    parser.add_argument("--artifact-manifest", type=Path)
    parser.add_argument("--image")
    args = parser.parse_args()
    try:
        return run(envelope_path=args.envelope, baseline_path=args.baseline,
                   snapshot=args.snapshot, report_path=args.report,
                   dependency_manifest=args.dependency_manifest,
                   dependency_cache=args.dependency_cache, artifacts=args.artifacts,
                   artifact_manifest=args.artifact_manifest, image=args.image)
    except KeyboardInterrupt:
        _write_error(args.report, "cancelled")
        return 2


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, lambda _signum, _frame: (_ for _ in ()).throw(KeyboardInterrupt()))
    raise SystemExit(main())
