"""Strict parser for `proofci.yaml`.

The manifest names which guarantees are required. Their exact meaning lives in
Lean: every guarantee names a theorem whose statement is in the protected
`<lean>/Contract.lean`. Proofs live in `<lean>/Proofs.lean` (plus optional
helper modules under `<lean>/Proofs/`). The manifest never contains formulas.
"""

import re
from dataclasses import dataclass
from pathlib import PurePosixPath

import yaml

MANIFEST_NAME = "proofci.yaml"
CONTRACT_MODULE = "Contract"
PROOFS_MODULE = "Proofs"
MAX_MANIFEST_BYTES = 64 * 1024
ID = re.compile(r"^[a-z][a-z0-9_-]{0,63}$")
RUST_PATH = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)+$")
LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")


class ManifestError(ValueError):
    """The manifest is missing, malformed, or outside the supported schema."""


@dataclass(frozen=True)
class Guarantee:
    id: str
    theorem: str
    required: bool


@dataclass(frozen=True)
class Target:
    id: str
    function: str
    guarantees: tuple


@dataclass(frozen=True)
class Manifest:
    crate: str
    lean: str
    targets: tuple

    @property
    def contract(self):
        return f"{self.lean}/{CONTRACT_MODULE}.lean"

    @property
    def proofs(self):
        return f"{self.lean}/{PROOFS_MODULE}.lean"

    def guarantees(self):
        for target in self.targets:
            for guarantee in target.guarantees:
                yield target, guarantee

    def summary(self):
        """Comparable view used to detect policy changes between commits."""
        return {
            "crate": self.crate,
            "lean": self.lean,
            "guarantees": {
                f"{t.id}/{g.id}": {"function": t.function, "theorem": g.theorem, "required": g.required}
                for t, g in self.guarantees()
            },
        }


def _relative_path(value, field):
    if not isinstance(value, str) or not value:
        raise ManifestError(f"{field} must be a non-empty relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "\\" in value:
        raise ManifestError(f"{field} must stay inside the repository: {value!r}")
    return str(path)


def _keys(mapping, allowed, required, where):
    if not isinstance(mapping, dict):
        raise ManifestError(f"{where} must be a mapping")
    unknown = set(mapping) - set(allowed)
    if unknown:
        raise ManifestError(f"{where} has unknown keys: {', '.join(sorted(map(str, unknown)))}")
    missing = set(required) - set(mapping)
    if missing:
        raise ManifestError(f"{where} is missing: {', '.join(sorted(missing))}")


class _UniqueKeyLoader(yaml.SafeLoader):
    pass


def _construct_mapping(loader, node, deep=False):
    seen = set()
    for key_node, _ in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in seen:
            raise ManifestError(f"duplicate key {key!r} in manifest")
        seen.add(key)
    return loader.construct_mapping(node, deep=deep)


_UniqueKeyLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _construct_mapping)


def parse(data: bytes) -> Manifest:
    if len(data) > MAX_MANIFEST_BYTES:
        raise ManifestError("manifest is larger than 64 KiB")
    try:
        raw = yaml.load(data.decode("utf-8"), Loader=_UniqueKeyLoader)
    except (UnicodeDecodeError, yaml.YAMLError) as error:
        raise ManifestError(f"manifest is not valid YAML: {error}") from None
    _keys(raw, ("version", "crate", "lean", "targets"), ("version", "targets"), "manifest")
    if raw["version"] != 1:
        raise ManifestError("only manifest version 1 is supported")
    crate = _relative_path(raw.get("crate", "."), "crate")
    lean = _relative_path(raw.get("lean", "proofci"), "lean")
    if not isinstance(raw["targets"], list) or not raw["targets"]:
        raise ManifestError("targets must be a non-empty list")
    targets, target_ids, guarantee_ids, theorems = [], set(), set(), set()
    for index, entry in enumerate(raw["targets"]):
        where = f"targets[{index}]"
        _keys(entry, ("id", "function", "guarantees"), ("id", "function", "guarantees"), where)
        if not isinstance(entry["id"], str) or not ID.match(entry["id"]):
            raise ManifestError(f"{where}.id must match {ID.pattern}")
        if entry["id"] in target_ids:
            raise ManifestError(f"duplicate target id {entry['id']!r}")
        target_ids.add(entry["id"])
        if not isinstance(entry["function"], str) or not RUST_PATH.match(entry["function"]):
            raise ManifestError(f"{where}.function must be a Rust path such as crate_name::function")
        if not isinstance(entry["guarantees"], list) or not entry["guarantees"]:
            raise ManifestError(f"{where}.guarantees must be a non-empty list")
        guarantees = []
        for g_index, item in enumerate(entry["guarantees"]):
            g_where = f"{where}.guarantees[{g_index}]"
            _keys(item, ("id", "theorem", "required"), ("id", "theorem"), g_where)
            if not isinstance(item["id"], str) or not ID.match(item["id"]):
                raise ManifestError(f"{g_where}.id must match {ID.pattern}")
            key = f"{entry['id']}/{item['id']}"
            if key in guarantee_ids:
                raise ManifestError(f"duplicate guarantee {key!r}")
            guarantee_ids.add(key)
            if not isinstance(item["theorem"], str) or not LEAN_NAME.match(item["theorem"]):
                raise ManifestError(f"{g_where}.theorem must be a Lean declaration name")
            if item["theorem"] in theorems:
                raise ManifestError(f"theorem {item['theorem']!r} is used by two guarantees")
            theorems.add(item["theorem"])
            required = item.get("required", True)
            if not isinstance(required, bool):
                raise ManifestError(f"{g_where}.required must be true or false")
            guarantees.append(Guarantee(item["id"], item["theorem"], required))
        targets.append(Target(entry["id"], entry["function"], tuple(guarantees)))
    if not any(g.required for t in targets for g in t.guarantees):
        raise ManifestError("at least one guarantee must be required")
    return Manifest(crate, lean, tuple(targets))
