#!/usr/bin/env python3
"""Run the fixed worker isolation probe inside disposable QEMU guests."""
import argparse
import json
import os
import platform
import re
import selectors
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time

TIME_LIMIT_SECONDS = 60
LOG_LIMIT_BYTES = 256 * 1024


def stop_guest(process):
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


class ProbeCancellation(Exception):
    pass


def collect_guest(command, timeout=None, cancel_marker=None, start_marker=None):
    if timeout is None:
        timeout = TIME_LIMIT_SECONDS
    blocked = {signal.SIGTERM, signal.SIGINT}
    previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, blocked)
    try:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True,
                                   preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask))
    except BaseException:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        raise
    output = bytearray()
    deadline = time.monotonic() + (TIME_LIMIT_SECONDS if start_marker else timeout)
    started = start_marker is None
    reason = None
    try:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        with selectors.DefaultSelector() as selector:
            selector.register(process.stdout, selectors.EVENT_READ)
            while selector.get_map():
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    reason = "guest_timeout"
                    break
                for key, _ in selector.select(remaining):
                    chunk = os.read(key.fd, 8192)
                    if not chunk:
                        selector.unregister(key.fileobj)
                    elif len(output) + len(chunk) > LOG_LIMIT_BYTES:
                        reason = "guest_log_limit"
                        break
                    else:
                        output.extend(chunk)
                        if not started and start_marker in output:
                            deadline = time.monotonic() + timeout
                            started = True
                        if cancel_marker and cancel_marker in output:
                            raise ProbeCancellation
                if reason:
                    break
            if not reason:
                while os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOWAIT | os.WNOHANG) is None:
                    if time.monotonic() >= deadline:
                        reason = "guest_timeout"
                        break
                    time.sleep(0.01)
    except (KeyboardInterrupt, subprocess.TimeoutExpired, ProbeCancellation) as error:
        if isinstance(error, KeyboardInterrupt):
            reason = "cancelled"
        elif isinstance(error, ProbeCancellation):
            reason = "probe_cancelled"
        else:
            reason = "guest_timeout"
    finally:
        stop_guest(process)
        process.stdout.close()
    return process.returncode, bytes(output).decode("utf-8", errors="replace"), reason


def cancel_on_sigterm(_signum, _frame):
    raise KeyboardInterrupt


def main():
    signal.signal(signal.SIGTERM, cancel_on_sigterm)
    parser = argparse.ArgumentParser(description="Run the fixed hostile-worker probe")
    parser.add_argument("--job", choices=["probe"], default="probe")
    parser.add_argument("--challenge", default="probe", help="alphanumeric probe challenge (up to 64 characters)")
    parser.add_argument("--report", help="write the JSON report to this file")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", args.challenge):
        parser.error("--challenge must contain 1 to 64 letters, digits, underscores or hyphens")
    try:
        return run(args)
    except KeyboardInterrupt:
        report = {"status": "cancelled", "reason": "operator_cancelled"}
        return 130 if emit_report(report, args.report) else 2
    except OSError as error:
        emit_report({"status": "incomplete", "reason": "worker_prerequisite_or_execution_error", "detail": str(error)}, args.report)
        return 2


def emit_report(report, path):
    report_json = json.dumps(report, indent=2) + "\n"
    if path:
        try:
            with open(path, "w", encoding="utf-8") as report_file:
                report_file.write(report_json)
        except OSError as error:
            print(f"Cannot write report: {error}", file=sys.stderr)
            return False
    print(report_json, end="")
    return True


def run(args):
    required = ("qemu-system-aarch64", "cpio", "find", "cp")
    missing = [name for name in required if shutil.which(name) is None]
    files = ("/bin/busybox.static", "/connect", "/limits", "/workload", "/guest-init", "/boot/vmlinuz-virt")
    missing.extend(path for path in files if not os.path.isfile(path))
    if platform.system() != "Linux" or platform.machine() not in ("aarch64", "arm64") or missing:
        emit_report({"status": "incomplete", "reason": "unsupported_prerequisites", "required": "Linux aarch64 with QEMU, cpio, find and cp", "missing": missing}, args.report)
        return 2
    with tempfile.TemporaryDirectory(prefix="proofci-probe-") as tmp, tempfile.TemporaryDirectory(prefix="proofci-probe-home-", dir=os.path.expanduser("~")) as host_home:
        if not all(re.fullmatch(r"/[A-Za-z0-9_./-]+", path) for path in (tmp, host_home)):
            emit_report({"status": "incomplete", "reason": "unsupported_temporary_path"}, args.report)
            return 2
        os.makedirs(f"{tmp}/root/bin")
        for directory in ("proc", "sys", "dev", "tmp"):
            os.mkdir(f"{tmp}/root/{directory}")
        subprocess.run(["cp", "/bin/busybox.static", f"{tmp}/root/bin/busybox"], check=True)
        subprocess.run(["cp", "/connect", f"{tmp}/root/bin/connect"], check=True)
        subprocess.run(["cp", "/limits", f"{tmp}/root/bin/limits"], check=True)
        subprocess.run(["cp", "/workload", f"{tmp}/root/bin/workload"], check=True)
        os.chmod(f"{tmp}/root/tmp", 0o1777)
        with open(f"{host_home}/sentinel", "w", encoding="utf-8") as sentinel:
            sentinel.write("dummy host home sentinel")
        for name in ("credentials", "other-workspace", "other-repository-cache"):
            os.mkdir(f"{tmp}/{name}")
            with open(f"{tmp}/{name}/sentinel", "w", encoding="utf-8") as sentinel:
                sentinel.write("dummy sentinel; no real credential")
        socket_path = f"{tmp}/docker.sock"
        sentinel_socket = socket.socket(socket.AF_UNIX)
        sentinel_socket.bind(socket_path)
        sentinel_socket.listen()
        with open("/guest-init", encoding="utf-8") as source:
            guest_init = source.read().replace("@HOST_TMP@", tmp).replace("@HOST_HOME@", host_home)
        with open(f"{tmp}/root/init", "w", encoding="utf-8") as target:
            target.write(guest_init)
        os.chmod(f"{tmp}/root/init", 0o755)
        with open(f"{tmp}/initramfs", "wb") as archive:
            find = subprocess.Popen(["find", "."], cwd=f"{tmp}/root", stdout=subprocess.PIPE)
            subprocess.run(["cpio", "-o", "-H", "newc"], cwd=f"{tmp}/root", stdin=find.stdout, stdout=archive, stderr=subprocess.DEVNULL, check=True)
            find.stdout.close()
            if find.wait() != 0:
                raise RuntimeError("Could not enumerate guest files")
        command = ["qemu-system-aarch64", "-machine", "virt", "-accel", "tcg", "-cpu", "max", "-m", "256", "-nographic", "-no-reboot", "-nic", "none", "-kernel", "/boot/vmlinuz-virt", "-initrd", f"{tmp}/initramfs", "-append", "console=ttyAMA0 rdinit=/init panic=-1 quiet"]
        def run_mode(mode, timeout=TIME_LIMIT_SECONDS, cancel_marker=None, start_marker=None):
            return collect_guest(command[:-1] + [command[-1] + " proofci.mode=" + mode + " proofci.challenge=" + args.challenge], timeout, cancel_marker, start_marker)

        try:
            exit_code, output, reason = run_mode("probe")
            if reason == "cancelled":
                raise KeyboardInterrupt
            cancel_code, cancel_output, cancel_reason = run_mode("cancel", cancel_marker=b"PROOFCI_CANCEL_READY")
            if cancel_reason == "cancelled":
                raise KeyboardInterrupt
            fresh_code, fresh_output, fresh_reason = run_mode("fresh")
            if fresh_reason == "cancelled":
                raise KeyboardInterrupt
            flood_code, flood_output, flood_reason = run_mode("flood")
            if flood_reason == "cancelled":
                raise KeyboardInterrupt
            timeout_code, timeout_output, timeout_reason = run_mode("timeout", timeout=5, start_marker=b"PROOFCI_TIMEOUT_READY")
            if timeout_reason == "cancelled":
                raise KeyboardInterrupt
        finally:
            sentinel_socket.close()
        results = []
        for line in (output + "\n" + fresh_output).splitlines():
            match = re.search(r"PROOFCI_RESULT (\{.*\})", line)
            if match:
                try:
                    result = json.loads(match.group(1))
                    if not isinstance(result, dict) or set(result) != {"probe", "status"}:
                        raise ValueError("invalid guest result")
                    results.append(result)
                except (ValueError, TypeError):
                    reason = "malformed_guest_result"
        artifact_matches = re.findall(r"PROOFCI_ARTIFACT (\{.*\})", output)
        try:
            artifact = json.loads(artifact_matches[0]) if len(artifact_matches) == 1 else None
        except ValueError:
            artifact = None
        expected = {
            "guest_boot": "passed", "cgroup_cpu": "available", "cgroup_memory": "available", "cgroup_pids": "available",
            "host-home": "denied", "credentials": "denied", "other-workspace": "denied", "other-repository-cache": "denied", "container_socket": "denied", "network": "denied",
            "cgroup_memory_limit": "observed", "cgroup_pids_limit": "observed", "cgroup_cpu_budget": "observed", "tmpfs_disk_limit": "observed",
            "limit_cpu": "observed", "limit_memory": "observed", "limit_disk": "observed", "limit_processes": "observed", "fresh_state": "absent",
        }
        actual = {entry["probe"]: entry["status"] for entry in results}
        complete = (reason is None and exit_code == 0 and "PROOFCI_DONE" in output and len(results) == len(expected) and actual == expected
                    and cancel_reason == "probe_cancelled" and b"PROOFCI_CANCEL_READY" in cancel_output.encode() and cancel_code != 0
                    and fresh_reason is None and fresh_code == 0 and "PROOFCI_DONE" in fresh_output
                    and flood_reason == "guest_log_limit" and "PROOFCI_FLOOD_READY" in flood_output and flood_code != 0
                    and artifact == {"type": "probe_receipt", "challenge": args.challenge}
                    and timeout_reason == "guest_timeout" and "PROOFCI_TIMEOUT_READY" in timeout_output and timeout_code != 0)
        report = {"status": "passed" if complete else "failed", "reason": reason or (None if complete else "one or more required probe checks failed"),
                  "scope": "fixed probe only; not formal verification or public-job admission",
                  "host": platform.uname()._asdict(),
                  "configuration": {"hypervisor": "qemu", "acceleration": "tcg", "network": "none", "guest_memory_mib": 256,
                                    "time_limit_seconds": TIME_LIMIT_SECONDS, "log_limit_bytes": LOG_LIMIT_BYTES,
                                    "cgroup_memory_bytes": 16777216, "cgroup_pids": 8, "cpu_budget_usec": 500000, "tmpfs_bytes": 1048576},
                  "guest_artifact": artifact, "guest_exit_code": exit_code, "guest_completed": "PROOFCI_DONE" in output, "results": results,
                  "cancel_diagnostics": cancel_output[-2000:] if cancel_reason != "probe_cancelled" else None,
                  "lifecycle": {"cancellation": cancel_reason, "fresh_guest": fresh_reason or "completed", "log_limit": flood_reason, "time_limit": timeout_reason}}
    cleanup_complete = not os.path.exists(tmp) and not os.path.exists(host_home)
    report["lifecycle"]["temporary_cleanup"] = "completed" if cleanup_complete else "failed"
    if not cleanup_complete:
        report["status"] = "failed"
        report["reason"] = "temporary_cleanup_failed"
        complete = False
    if not emit_report(report, args.report):
        return 2
    return 0 if complete else 2



if __name__ == "__main__":
    sys.exit(main())
