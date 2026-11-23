"""`proofci local`: the CI check on a working tree, inside the toolchain image.

For coding agents. One command runs exactly what CI runs -- the same image,
the same container restrictions -- and prints the machine-readable report on
stdout. The Docker flags that isolate the run (no network, dropped
capabilities, read-only mounts) are the ones the action uses
(`action/run.py`); they are baked in here so callers can't weaken them.

    python -m proofci local --repo .                 # check against HEAD's policy
    python -m proofci local --scan                   # only translate: which functions are supported

The check's own code and sandbox do not change for local use; an error or a
timeout exits non-zero and never prints a passing report.
"""

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from . import check as check_mod
from . import manifest

SECCOMP = Path(__file__).resolve().parent.parent / "action" / "seccomp.json"


def sandbox_opts():
    """The container restrictions from action/run.py. The seccomp profile is
    shipped with the action; where it isn't installed (a bare `proofci`
    package), fall back to no profile the way docs/development.md does."""
    return [
        "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
        "--read-only", "--tmpfs", "/tmp:exec,mode=1777",
        "--security-opt", f"seccomp={SECCOMP}" if SECCOMP.is_file() else "seccomp=unconfined",
        "--security-opt", "apparmor=unconfined", "--security-opt", "systempaths=unconfined",
    ]


def checkout_ref(repo: Path, ref: str, dest: Path):
    """Materialize `ref` as a plain directory, like the action's `actions/checkout`.

    `repo` may be a directory inside a git checkout; only its subtree is archived."""
    inside = subprocess.run(["git", "-C", str(repo), "rev-parse", "--show-prefix"], capture_output=True)
    if inside.returncode != 0:
        raise check_mod.ConfigError(f"{repo} is not inside a git checkout")
    # `git archive` run inside a subdirectory archives just that subtree.
    archive = subprocess.run(["git", "-C", str(repo), "archive", "--format=tar", ref],
                             capture_output=True)
    if archive.returncode != 0:
        raise check_mod.ConfigError(f"git could not read `{ref}` in {repo} ({_text(archive.stderr).strip()})")
    dest.mkdir()
    done = subprocess.run(["tar", "-x", "-C", str(dest)], input=archive.stdout, capture_output=True)
    if done.returncode != 0:
        raise check_mod.ConfigError(f"could not unpack `{ref}`: {_text(done.stderr).strip()}")
    return dest


def _text(value):
    return value if isinstance(value, str) else value.decode(errors="replace")


def _docker(image, mounts, extra, inner):
    return ["docker", "run", "--rm", "--user", f"{os.getuid()}:{os.getgid()}", *extra, *sandbox_opts(),
            *(x for pair in mounts for x in ("-v", pair)),
            image, *inner]


def run(repo: Path, base_ref, policy, image, scan=False, fetch_deps=False, err=lambda t: print(t, file=sys.stderr)):
    repo = repo.resolve()
    if not repo.is_dir():
        raise check_mod.ConfigError(f"{repo} is not a directory")
    if scan:
        try:
            active = check_mod.load_manifest(repo)
        except (check_mod.ConfigError, manifest.ManifestError):
            active = None
        if active and active.language != "typescript":
            raise check_mod.ConfigError("--scan lists supported functions of a TypeScript package; "
                                      "this repository's proofci.yaml is for Rust")
        inner = ["scan", "--repo", "/head", "--report", "/out/report.json"]
    else:
        inner = ["check", "--base", "/base", "--head", "/head", "--vendor", "/vendor",
                 "--policy", policy, "--report", "/out/report.json", "--summary", "/out/summary.md"]
    work = Path(tempfile.mkdtemp(prefix="proofci-local-"))
    try:
        out_dir = work / "out"
        out_dir.mkdir()
        out_dir.chmod(0o777)
        vendor = work / "vendor"
        vendor.mkdir()
        vendor.chmod(0o777)
        mounts = [f"{repo}:/head:ro", f"{out_dir}:/out", f"{vendor}:/vendor:ro"]
        if not scan:
            base = checkout_ref(repo, base_ref, work / "base")
            mounts.insert(0, f"{base}:/base:ro")
        if fetch_deps:
            # fetch needs a --base even for a scan; the head checkout serves.
            fetch_mounts = [f"{repo}:/head:ro", f"{vendor}:/vendor"]
            base_args = ["--base", "/head"]
            if not scan:
                fetch_mounts.insert(0, mounts[0])
                base_args = ["--base", "/base"]
            command = _docker(image, fetch_mounts, ["--memory", "4g", "--pids-limit", "1024"],
                              ["fetch", *base_args, "--head", "/head", "--policy", policy, "--out", "/vendor"])
            done = subprocess.run(command)
            if done.returncode != 0:
                err(f"proofci: the dependency install failed (exit {done.returncode})")
                return 2
        done = subprocess.run(_docker(image, mounts, ["--network", "none", "--cpus", str(os.cpu_count() or 2),
                                                    "--memory", "8g", "--pids-limit", "4096"], inner),
                              capture_output=True, text=True)
        if scan:
            # The in-image command's stdout is the JSON document itself.
            sys.stdout.write(done.stdout)
            if done.stderr:
                err(done.stderr)
            return 0 if done.returncode == 0 else (1 if done.returncode == 1 else 2)
        if done.stdout:
            err(done.stdout)          # the human summary; JSON goes to stdout only
        if done.stderr:
            err(done.stderr)
        report = out_dir / "report.json"
        if not report.exists():
            err(f"proofci: no report was produced (exit {done.returncode})")
            return 2
        print(report.read_text(), end="")
        return 0 if done.returncode == 0 else (1 if done.returncode == 1 else 2)
    finally:
        shutil.rmtree(work, ignore_errors=True)   # container-owned files may not be removable


__all__ = ["run"]
