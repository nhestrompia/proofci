#!/usr/bin/env python3
"""Run the portable CLI inside its resource-limited Linux image."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import time
import uuid

import report as report_contract
import proofci

IMAGE_ID = "sha256:0768934aa3f0d7d40edb6bbe879c97ef66f2fd825549861ee8bc2598adda4054"
IMAGE_CONFIG_ID = "sha256:0fed6287e0b5723db99852e9aad1c45d35e284c5f1891c42c90240444793a594"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("envelope", "baseline", "snapshot", "report"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--image", default=IMAGE_ID)
    parser.add_argument("--repair-id")
    parser.add_argument("--proof-body", type=Path)
    parser.add_argument("--artifacts", type=Path)
    parser.add_argument("--search-results", type=Path)
    parser.add_argument("--dependencies", type=Path)
    parser.add_argument("--phase", choices=("worker", "final-validation"), default="worker")
    parser.add_argument("--validator-only", action="store_true")
    args = parser.parse_args()
    report = args.report.resolve()
    try:
        if os.getuid() == 0:
            raise ValueError("run the launcher as an unprivileged user")
        if (args.repair_id is None) != (args.proof_body is None):
            raise ValueError("repair identity and proof body must be supplied together")
        with args.envelope.open("rb") as source:
            raw = source.read(1024 * 1024 + 1)
        if len(raw) > 1024 * 1024:
            raise ValueError("envelope exceeds size limit")
        envelope = json.loads(raw)
        with args.baseline.open("rb") as source:
            baseline_raw = source.read(1024 * 1024 + 1)
        if len(baseline_raw) > 1024 * 1024:
            raise ValueError("baseline exceeds size limit")
        limits = envelope["resource_policy"]
        expected = {"timeout_seconds", "cpu_seconds", "memory_bytes", "file_bytes", "processes"}
        if set(limits) != expected or any(type(v) is not int or v <= 0 for v in limits.values()):
            raise ValueError("invalid resource policy")
        deadline = time.monotonic() + min(900, limits["timeout_seconds"], limits["cpu_seconds"])
        if args.baseline.is_symlink() or args.snapshot.is_symlink():
            raise ValueError("snapshot and protected baseline must not be symbolic links")
        snapshot = args.snapshot.resolve(strict=True)
        baseline = args.baseline.resolve(strict=True)
        if not snapshot.is_dir() or not baseline.is_file():
            raise ValueError("invalid snapshot or baseline")
        if args.artifacts is not None:
            artifacts = args.artifacts.resolve(strict=True)
            if artifacts.is_relative_to(snapshot) or artifacts.is_relative_to(baseline.parent):
                raise ValueError("artifact destination must be outside the snapshot and protected baseline")
        if args.dependencies is not None:
            if args.dependencies.is_symlink():
                raise ValueError("dependency staging directory must not be a symbolic link")
            dependency_root = args.dependencies.resolve(strict=True)
            if not dependency_root.is_dir() or dependency_root.is_relative_to(snapshot) or dependency_root.is_relative_to(baseline.parent):
                raise ValueError("dependency staging directory is invalid")
        try:
            image_id = subprocess.check_output(["docker", "image", "inspect", "--format", "{{.Id}}", args.image],
                                               text=True, timeout=max(0, deadline - time.monotonic())).strip()
        except subprocess.CalledProcessError:
            if args.image != IMAGE_ID:
                raise
            image_id = subprocess.check_output(["docker", "image", "inspect", "--format", "{{.Id}}", IMAGE_CONFIG_ID],
                                               text=True, timeout=max(0, deadline - time.monotonic())).strip()
        if image_id not in (IMAGE_ID, IMAGE_CONFIG_ID):
            raise ValueError("local image identity does not match the pinned distribution")
        if baseline.parent.is_relative_to(snapshot):
            raise ValueError("protected baseline must be outside the candidate snapshot")
        git_env = os.environ.copy()
        git_env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
                       GIT_CONFIG_SYSTEM=os.devnull, GIT_NO_REPLACE_OBJECTS="1",
                       GIT_OPTIONAL_LOCKS="0", GIT_TERMINAL_PROMPT="0")
        common = subprocess.check_output(
            ["git", "-c", "core.fsmonitor=false", "-c", "core.hooksPath=/dev/null",
             "-c", "submodule.recurse=false", "-C", str(snapshot),
             "rev-parse", "--git-common-dir"], env=git_env, text=True,
            timeout=max(0, deadline - time.monotonic())).strip()
        common = (snapshot / common).resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix="proofci-launch-") as tmp:
            temp = Path(tmp)
            os.chmod(temp, 0o755)
            protected = temp / "protected"
            protected.mkdir(mode=0o755)
            baseline_copy = protected / "baseline.json"
            baseline_copy.write_bytes(baseline_raw)
            os.chmod(baseline_copy, 0o444)
            baseline_value = json.loads(baseline_raw)
            if not isinstance(baseline_value, dict) or not isinstance(baseline_value.get("obligations"), list):
                raise ValueError("baseline obligations are invalid")
            for item in baseline_value["obligations"]:
                if not isinstance(item, dict) or not isinstance(item.get("contract"), str):
                    raise ValueError("baseline contract path is invalid")
                contract = proofci.path_in(baseline.parent, item["contract"])
                if not contract.is_file() or Path(item["contract"]) == Path("baseline.json"):
                    raise ValueError("baseline contract cannot be staged")
                contract_target = protected / item["contract"]
                contract_target.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
                contract_bytes = proofci.bounded_read(contract, 16384)
                if hashlib.sha256(contract_bytes).hexdigest() != item.get("contract_sha256"):
                    raise ValueError("protected contract digest mismatch")
                contract_target.write_bytes(contract_bytes)
                os.chmod(contract_target, 0o444)
            envelope_path = temp / "envelope.json"
            envelope_path.write_bytes(raw)
            os.chmod(envelope_path, 0o644)
            result_path = temp / "report.json"
            result_path.write_text("")
            os.chmod(result_path, 0o666)
            name = "proofci-" + uuid.uuid4().hex
            stop_reason = None
            guard = None
            command = ["docker", "create", "--name", name, "--label", f"proofci.run={os.getpid()}", "--rm", "--network", "none",
                "--platform", "linux/arm64", "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
                "--security-opt", "seccomp=unconfined", "--security-opt", "systempaths=unconfined",
                "--security-opt", "apparmor=unconfined",
                "--user", f"{os.getuid()}:{os.getgid()}",
                "--read-only", "--memory", str(min(limits["memory_bytes"], limits["file_bytes"])),
                "--memory-swap", str(min(limits["memory_bytes"], limits["file_bytes"])),
                "--pids-limit", str(limits["processes"]), "--cpus", "1", "--log-driver", "none",
                "--tmpfs", f"/tmp:rw,size={limits['file_bytes']},mode=1777",
                "--tmpfs", "/run:rw,size=1m,mode=1777",
                "--mount", f"type=bind,src={snapshot},dst=/snapshot,readonly",
                "--mount", f"type=bind,src={common},dst={common},readonly",
                "--mount", f"type=bind,src={protected},dst=/baseline,readonly",
                "--mount", f"type=bind,src={envelope_path},dst=/runinput/envelope.json,readonly",
                "--mount", f"type=bind,src={result_path},dst=/result/report.json",
                "-e", f"PROOFCI_IMAGE_ID={image_id}", image_id, "--envelope", "/runinput/envelope.json", "--baseline", "/baseline/baseline.json",
                "--snapshot", "/snapshot", "--toolchain", "/lean", "--bwrap", "/usr/bin/bwrap",
                "--report", "/result/report.json"]
            if args.validator_only:
                command.append("--validator-only")
            if args.artifacts is not None:
                if not artifacts.is_dir():
                    raise ValueError("artifact destination must be a directory")
                command[command.index("-e"):command.index("-e")] = [
                    "--mount", f"type=bind,src={artifacts},dst=/artifacts"]
                command.extend(["--artifacts", "/artifacts"])
            if args.dependencies is not None:
                command[command.index("-e"):command.index("-e")] = [
                    "--mount", f"type=bind,src={dependency_root},dst=/dependencies,readonly"]
                command.extend(["--dependencies", "/dependencies"])
            if args.proof_body is not None:
                body = args.proof_body.read_bytes()
                if len(body) > 65536:
                    raise ValueError("proof body exceeds size limit")
                body_path = temp / "body"
                body_path.write_bytes(body)
                os.chmod(body_path, 0o644)
                command[command.index("-e"):command.index("-e")] = [
                    "--mount", f"type=bind,src={body_path},dst=/runinput/body,readonly"]
                command.extend(["--repair-id", args.repair_id, "--proof-body", "/runinput/body", "--attempt-only"])
            if args.search_results:
                with args.search_results.open("rb") as source:
                    search_bytes = source.read(1024 * 1024 + 1)
                if len(search_bytes) > 1024 * 1024:
                    raise ValueError("search results exceed size limit")
                search_path = temp / "search.json"
                search_path.write_bytes(search_bytes)
                os.chmod(search_path, 0o644)
                image_index = command.index(image_id)
                command[image_index:image_index] = ["--mount", f"type=bind,src={search_path},dst=/runinput/search.json,readonly"]
                command.extend(["--search-results", "/runinput/search.json"])
            try:
                guard = subprocess.Popen([sys.executable, str(Path(__file__).with_name("create_guard.py")),
                                          name, json.dumps(command)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.DEVNULL, start_new_session=True)
                try:
                    ready, _, _ = select.select([guard.stdout], [], [], max(0, deadline - time.monotonic()))
                    if not ready:
                        raise subprocess.TimeoutExpired("docker create", min(limits["timeout_seconds"], limits["cpu_seconds"]))
                    if guard.stdout.readline() != b"created\n":
                        raise RuntimeError("container creation failed")
                    guard.stdin.write(b"S")
                    guard.stdin.flush()
                except BaseException:
                    guard.stdin.close()
                    guard.stdout.close()
                    guard = None
                    raise
                process = subprocess.Popen(["docker", "start", "-a", name])
                try:
                    status = process.wait(timeout=max(0, deadline - time.monotonic()))
                except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
                    stop_reason = "cancelled" if isinstance(error, KeyboardInterrupt) else "timeout"
                    subprocess.run(["docker", "kill", "--signal", "TERM", name], stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL, timeout=10, check=False)
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        subprocess.run(["docker", "rm", "-f", name], stdout=subprocess.DEVNULL,
                                       stderr=subprocess.DEVNULL, timeout=10, check=False)
                        process.wait(timeout=10)
                    status = 2
            finally:
                if guard is not None:
                    guard.stdin.close()
                    guard.stdout.close()
                    try:
                        guard.wait(timeout=15)
                    except subprocess.TimeoutExpired:
                        pass
                subprocess.run(["docker", "rm", "-f", name], stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL, timeout=15, check=False)
                inspection = subprocess.run(["docker", "inspect", name], stdout=subprocess.DEVNULL,
                                            stderr=subprocess.PIPE, timeout=15, check=False)
                if inspection.returncode == 0 or b"no such object" not in inspection.stderr.lower():
                    raise RuntimeError("container cleanup could not be confirmed")
            if result_path.stat().st_size:
                data = result_path.read_bytes()
                parsed = json.loads(data)
                if not isinstance(parsed, dict) or parsed.get("version") != 1:
                    raise ValueError("container status and report disagree")
                if status in (0, 1):
                    report_contract.validate(parsed, envelope, json.loads(baseline_raw),
                                             attempt=args.repair_id is not None, attempt_id=args.repair_id)
                    if (status == 0) != (parsed.get("status") == "passed"):
                        raise ValueError("container status and report disagree")
                elif parsed.get("status") != "error":
                    raise ValueError("container status and report disagree")
                parsed.setdefault("execution", {})["dispatch_phase"] = args.phase
                if stop_reason == "timeout":
                    parsed["reason"] = "timeout"
                    for result in parsed.get("results", []):
                        if result.get("reason") == "cancelled":
                            result["reason"] = "timeout"
                    data = (json.dumps(parsed, indent=2, sort_keys=True) + "\n").encode()
                report.write_bytes(data)
            else:
                report.write_text(json.dumps({"version": 1, "status": "error",
                                              "reason": stop_reason or "container failed before writing a report"}) + "\n")
                status = 2
            return status
    except KeyboardInterrupt:
        try:
            report.write_text(json.dumps({"version": 1, "status": "error", "reason": "cancelled"}) + "\n")
        except OSError:
            print("cannot write report", file=sys.stderr)
        return 2
    except subprocess.TimeoutExpired:
        try:
            report.write_text(json.dumps({"version": 1, "status": "error", "reason": "timeout"}) + "\n")
        except OSError:
            print("cannot write report", file=sys.stderr)
        return 2
    except (OSError, ValueError, KeyError, TypeError, RuntimeError, subprocess.SubprocessError) as error:
        try:
            report.write_text(json.dumps({"version": 1, "status": "error", "reason": str(error)}) + "\n")
        except OSError:
            print("cannot write report", file=sys.stderr)
        return 2


if __name__ == "__main__":
    def cancel(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, cancel)
    raise SystemExit(main())
