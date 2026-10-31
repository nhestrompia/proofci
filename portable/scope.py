"""Explain a Git tree diff using the fixed source adapter's admission decision."""
import os
import subprocess
import sys
from pathlib import Path

VALIDATOR = Path(__file__).resolve().parent.parent / "experiments/source-binding"
sys.path.insert(0, str(VALIDATOR))
import binding

SUPPORT_VERSION = "lean-target-v1"


def admission(data):
    try:
        binding.candidate_body(data.decode("utf-8"))
        return None
    except (UnicodeDecodeError, ValueError, RecursionError) as error:
        return str(error)


def describe(snapshot, base, head, baseline, deadline):
    import time
    env = os.environ.copy()
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_NO_REPLACE_OBJECTS="1", GIT_OPTIONAL_LOCKS="0")
    def git(*args):
        return subprocess.check_output(
            ["git", "-c", "safe.directory=*", "-c", "core.fsmonitor=false",
             "-C", str(snapshot), *args], env=env, stderr=subprocess.PIPE,
            timeout=max(0, deadline - time.monotonic()))
    raw = git("diff-tree", "--no-commit-id", "--raw", "-r", "-z", "--no-abbrev",
              "--no-renames", "--no-ext-diff", "--no-textconv", base, head)
    parts = raw.split(b"\0")
    changes, unsupported, uncovered = [], [], []
    evidence_roots = [item[key].rstrip("/") for item in baseline["obligations"]
                      for key in ("evidence", "refutation") if key in item]
    for index in range(0, len(parts) - 1, 2):
        metadata, name_bytes = parts[index:index + 2]
        old_mode, new_mode, old_oid, new_oid, status = metadata.decode("ascii").split()
        name = os.fsdecode(name_bytes)
        entry = {"path": name, "status": status, "old_mode": old_mode[1:],
                 "new_mode": new_mode, "old_object": old_oid, "new_object": new_oid}
        changes.append(entry)
        deleted = new_mode == "000000"
        mode = old_mode[1:] if deleted else new_mode
        oid = old_oid if deleted else new_oid
        if name == baseline["candidate"]:
            entry["scope"] = "bound_candidate"
        elif any(name == root or name.startswith(root + "/") for root in evidence_roots):
            entry["scope"] = "proof_evidence"
        elif name.endswith(".lean") and mode in ("100644", "100755"):
            size = int(git("cat-file", "-s", oid))
            reason = "source exceeds adapter input limit" if size > 16384 else admission(git("cat-file", "blob", oid))
            if reason is None:
                entry["scope"] = "deleted_supported_symbol" if deleted else "uncovered_supported_symbol"
                if not deleted:
                    uncovered.append({"path": name, "symbol": "target"})
            else:
                entry["scope"] = "unsupported_code"
                unsupported.append({"path": name, "reason": reason})
        else:
            entry["scope"] = "outside_supported_scope"
            if Path(name).suffix.lower() in {".rs", ".c", ".h", ".cc", ".cpp", ".hpp", ".py", ".rb", ".js", ".jsx", ".ts", ".tsx", ".java", ".go", ".sh"}:
                unsupported.append({"path": name, "reason": "language outside the admitted Lean candidate scope"})
    return {"changes": changes, "unsupported_changed_code": unsupported,
            "uncovered_supported_symbols": uncovered}
