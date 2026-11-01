"""Validate and stage immutable dependency inputs for an isolated worker.

The dependency cache is an operator-owned content-addressed directory.  The
manifest deliberately has no URL, command, or destination fields: a
candidate cannot turn it into a network fetch, a hook, or a toolchain
substitution.  Staged files are copied into a fresh directory and mounted
read-only by the worker launcher.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import stat


MAX_MANIFEST_BYTES = 1024 * 1024
MAX_DEPENDENCIES = 128
MAX_DEPENDENCY_BYTES = 128 * 1024 * 1024
SHA256 = re.compile(r"[0-9a-f]{64}")


def _json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate field: " + key)
            result[key] = value
        return result

    return json.loads(data, object_pairs_hook=unique)


def _safe_name(name):
    if not isinstance(name, str) or not name or name.startswith("/"):
        raise ValueError("dependency name must be relative")
    parts = Path(name).parts
    if not parts or any(part in ("", ".", "..") for part in parts):
        raise ValueError("invalid dependency name")
    if any("\\" in part or "\x00" in part for part in parts):
        raise ValueError("invalid dependency name")
    return name


def read_manifest(path):
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        raise ValueError("dependency manifest must be a regular file")
    path = path.resolve(strict=True)
    data = path.read_bytes()
    if len(data) > MAX_MANIFEST_BYTES:
        raise ValueError("dependency manifest exceeds size limit")
    manifest = _json(data)
    if set(manifest) != {"version", "dependencies"} or manifest["version"] != 1:
        raise ValueError("unsupported dependency manifest")
    entries = manifest["dependencies"]
    if not isinstance(entries, list) or len(entries) > MAX_DEPENDENCIES:
        raise ValueError("invalid dependency list")
    seen = set()
    total = 0
    normalized = []
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"name", "sha256", "size_bytes"}:
            raise ValueError("dependency entries must contain only name, sha256, and size_bytes")
        name = _safe_name(entry["name"])
        checksum = entry["sha256"]
        size = entry["size_bytes"]
        if not isinstance(checksum, str) or not SHA256.fullmatch(checksum):
            raise ValueError("invalid dependency digest")
        if type(size) is not int or size < 0 or size > MAX_DEPENDENCY_BYTES:
            raise ValueError("invalid dependency size")
        if name in seen:
            raise ValueError("duplicate dependency name")
        seen.add(name)
        total += size
        if total > MAX_DEPENDENCY_BYTES:
            raise ValueError("dependency set exceeds size limit")
        normalized.append({"name": name, "sha256": checksum, "size_bytes": size})
    return {"version": 1, "dependencies": normalized}, data


def _open_regular(root_fd, name, flags):
    try:
        fd = os.open(name, flags | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=root_fd)
    except OSError as error:
        raise ValueError("dependency cache entry is unavailable") from error
    info = os.fstat(fd)
    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
        os.close(fd)
        raise ValueError("dependency cache entry is not a private regular file")
    return fd, info


def _read_cache_entry(cache_fd, checksum, expected_size):
    fd, initial = _open_regular(cache_fd, checksum, os.O_RDONLY)
    try:
        if initial.st_size != expected_size or initial.st_size > MAX_DEPENDENCY_BYTES:
            raise ValueError("dependency size does not match manifest")
        chunks = []
        remaining = expected_size
        while remaining:
            chunk = os.read(fd, min(1024 * 1024, remaining))
            if not chunk:
                raise ValueError("dependency changed while being read")
            chunks.append(chunk)
            remaining -= len(chunk)
        data = b"".join(chunks)
        final = os.fstat(fd)
        if ((initial.st_dev, initial.st_ino, initial.st_size, initial.st_mtime_ns, initial.st_nlink)
                != (final.st_dev, final.st_ino, final.st_size, final.st_mtime_ns, final.st_nlink)):
            raise ValueError("dependency changed while being read")
        if hashlib.sha256(data).hexdigest() != checksum:
            raise ValueError("dependency digest mismatch")
        return data
    finally:
        os.close(fd)


def stage(manifest_path, cache_path, destination):
    """Stage the manifest's content-addressed files into *destination*.

    The returned manifest is safe to include in an execution report.  This
    function performs no network access and does not run any repository code.
    """
    manifest, raw_manifest = read_manifest(manifest_path)
    cache = Path(cache_path)
    if cache.is_symlink():
        raise ValueError("dependency cache must not be a symbolic link")
    cache = cache.resolve(strict=True)
    destination = Path(destination).resolve()
    if not cache.is_dir():
        raise ValueError("dependency cache must be a directory")
    destination.mkdir(mode=0o700, parents=True, exist_ok=False)
    cache_fd = os.open(cache, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for entry in manifest["dependencies"]:
            data = _read_cache_entry(cache_fd, entry["sha256"], entry["size_bytes"])
            target = destination / entry["name"]
            target.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
            with target.open("xb") as output:
                output.write(data)
            os.chmod(target, 0o644)
        (destination / "_proofci-manifest.json").write_bytes(raw_manifest)
        os.chmod(destination / "_proofci-manifest.json", 0o644)
    finally:
        os.close(cache_fd)
    return manifest


def verify_staged(root):
    """Verify a read-only staged dependency root inside the worker."""
    root = Path(root)
    if root.is_symlink():
        raise ValueError("staged dependency root must not be a symbolic link")
    root = root.resolve(strict=True)
    manifest, _ = read_manifest(root / "_proofci-manifest.json")
    expected = {entry["name"] for entry in manifest["dependencies"]} | {"_proofci-manifest.json"}
    actual = {str(path.relative_to(root)) for path in root.rglob("*") if path.is_file()}
    if any(path.is_symlink() for path in root.rglob("*")):
        raise ValueError("staged dependency tree contains a symbolic link")
    if actual != expected:
        raise ValueError("staged dependency set differs from manifest")
    for entry in manifest["dependencies"]:
        path = root / entry["name"]
        if not path.is_file() or path.is_symlink():
            raise ValueError("staged dependency is not a regular file")
        data = path.read_bytes()
        if len(data) != entry["size_bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError("staged dependency digest mismatch")
    return manifest
