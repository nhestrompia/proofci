"""Run untrusted-input tools inside a bubblewrap sandbox.

The verifier process itself never executes code derived from the pull request.
Charon/rustc, Aeneas and Lean see the candidate only inside a sandbox with no
network, a read-only root, a fresh /tmp, and write access to one directory.
"""

import os
import shutil
import signal
import subprocess
from dataclasses import dataclass

MAX_OUTPUT = 4 * 1024 * 1024


class SandboxUnavailable(RuntimeError):
    pass


@dataclass
class Result:
    status: int
    output: str
    timed_out: bool = False


def bwrap():
    path = os.environ.get("PROOFCI_BWRAP") or shutil.which("bwrap")
    if not path:
        raise SandboxUnavailable("bubblewrap (bwrap) is required")
    return path


def run(argv, *, writable, cwd, readable=(), env=None, timeout=600, network=False):
    """Run `argv` with only `writable` directories writable and no network.

    `readable` paths are re-bound read-only (needed for paths under /tmp,
    which the sandbox replaces with an empty tmpfs). `network` keeps the
    host network (only for downloading dependencies)."""
    base_env = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "HOME": "/tmp/home",
        "LC_ALL": "C.UTF-8",
        "RUSTUP_HOME": os.environ.get("RUSTUP_HOME", ""),
        "RUSTUP_TOOLCHAIN": os.environ.get("RUSTUP_TOOLCHAIN", ""),
    }
    base_env.update(env or {})
    args = [
        bwrap(), "--die-with-parent", "--new-session", "--unshare-all",
        *(["--share-net"] if network else []),
        "--ro-bind", "/", "/",
        "--tmpfs", "/tmp", "--dir", "/tmp/home",
        "--dev", "/dev", "--proc", "/proc",
        "--clearenv",
    ]
    for path in readable:
        args += ["--ro-bind", str(path), str(path)]
    for path in writable:
        args += ["--bind", str(path), str(path)]
    for key, value in base_env.items():
        if value:
            args += ["--setenv", key, value]
    args += ["--chdir", str(cwd), "--", *map(str, argv)]
    process = subprocess.Popen(
        args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
        start_new_session=True,
    )
    try:
        out, _ = process.communicate(timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        out, _ = process.communicate()
        timed_out = True
    text = out[-MAX_OUTPUT:].decode("utf-8", "replace")
    return Result(process.returncode if not timed_out else 124, text, timed_out)
