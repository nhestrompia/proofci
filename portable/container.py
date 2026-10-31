#!/usr/bin/env python3
"""Run the portable CLI inside its resource-limited Linux image."""
import argparse
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

IMAGE_ID = "sha256:83fc8d3f7b4936f7410c70cee37de6d99177757f38e843ea96195a3fcc82ff39"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("envelope", "baseline", "snapshot", "report"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--image", default="proofci-validator-local")
    args = parser.parse_args()
    report = args.report.resolve()
    try:
        if os.getuid() == 0:
            raise ValueError("run the launcher as an unprivileged user")
        with args.envelope.open("rb") as source:
            raw = source.read(1024 * 1024 + 1)
        if len(raw) > 1024 * 1024:
            raise ValueError("envelope exceeds size limit")
        envelope = json.loads(raw)
        limits = envelope["resource_policy"]
        expected = {"timeout_seconds", "cpu_seconds", "memory_bytes", "file_bytes", "processes"}
        if set(limits) != expected or any(type(v) is not int or v <= 0 for v in limits.values()):
            raise ValueError("invalid resource policy")
        deadline = time.monotonic() + min(limits["timeout_seconds"], limits["cpu_seconds"])
        snapshot = args.snapshot.resolve(strict=True)
        baseline = args.baseline.resolve(strict=True)
        if not snapshot.is_dir() or not baseline.is_file():
            raise ValueError("invalid snapshot or baseline")
        image_id = subprocess.check_output(["docker", "image", "inspect", "--format", "{{.Id}}", args.image],
                                           text=True, timeout=max(0, deadline - time.monotonic())).strip()
        if image_id != IMAGE_ID:
            raise ValueError("local image identity does not match the pinned distribution")
        common = subprocess.check_output(["git", "-c", "core.fsmonitor=false", "-C", str(snapshot),
                                          "rev-parse", "--git-common-dir"], text=True,
                                         timeout=max(0, deadline - time.monotonic())).strip()
        common = (snapshot / common).resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix="proofci-launch-") as tmp:
            temp = Path(tmp)
            os.chmod(temp, 0o755)
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
                "--user", f"{os.getuid()}:{os.getgid()}",
                "--read-only", "--memory", str(min(limits["memory_bytes"], limits["file_bytes"])),
                "--memory-swap", str(min(limits["memory_bytes"], limits["file_bytes"])),
                "--pids-limit", str(limits["processes"]), "--cpus", "1", "--log-driver", "none",
                "--tmpfs", f"/tmp:rw,size={limits['file_bytes']},mode=1777",
                "--tmpfs", "/run:rw,size=1m,mode=1777",
                "--mount", f"type=bind,src={snapshot},dst=/snapshot,readonly",
                "--mount", f"type=bind,src={common},dst={common},readonly",
                "--mount", f"type=bind,src={baseline.parent},dst=/baseline,readonly",
                "--mount", f"type=bind,src={envelope_path},dst=/runinput/envelope.json,readonly",
                "--mount", f"type=bind,src={result_path},dst=/result/report.json",
                "-e", f"PROOFCI_IMAGE_ID={image_id}", image_id, "--envelope", "/runinput/envelope.json", "--baseline", "/baseline/" + baseline.name,
                "--snapshot", "/snapshot", "--toolchain", "/lean", "--bwrap", "/usr/bin/bwrap",
                "--report", "/result/report.json"]
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
                if not isinstance(parsed, dict) or parsed.get("version") != 1 or (status == 0) != (parsed.get("status") == "passed"):
                    raise ValueError("container status and report disagree")
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
