"""Identify a complete extracted Lean distribution, including symbolic links."""

import hashlib
import json
import os
from pathlib import Path
import stat
import sys


def tree_digest(root):
    root = Path(root).resolve(strict=True)
    digest = hashlib.sha256()
    for directory, subdirs, files in os.walk(root, followlinks=False):
        subdirs.sort()
        for name in sorted(subdirs + files):
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode):
                target = os.readlink(path)
                if not path.resolve().is_relative_to(root):
                    raise ValueError(f"toolchain link escapes its root: {relative}")
                record = [relative, "link", target]
            elif stat.S_ISDIR(mode):
                record = [relative, "dir"]
            elif stat.S_ISREG(mode):
                content = hashlib.sha256()
                with path.open("rb") as source:
                    while chunk := source.read(1024 * 1024):
                        content.update(chunk)
                record = [relative, "file", content.hexdigest(), bool(mode & 0o111)]
            else:
                raise ValueError(f"unsupported toolchain file: {relative}")
            digest.update(json.dumps(record, ensure_ascii=True, separators=(",", ":")).encode() + b"\n")
    return digest.hexdigest()


if __name__ == "__main__":
    print(tree_digest(sys.argv[1]))
