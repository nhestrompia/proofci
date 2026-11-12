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
TS_PATH = re.compile(r"^(?!/)(?!.*\.\.)[A-Za-z0-9_./-]+\.ts::[A-Za-z_$][A-Za-z0-9_$]*$")
LANGUAGES = ("rust", "typescript")
ASSUMED_CALL = re.compile(r"^(@[\w.-]+/)?[\w.-]+(/[\w.-]+)*::[A-Za-z_][A-Za-z0-9_]*$")
LOGIN = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$")
LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$")
EFFECT_ID = re.compile(r"^[a-z][A-Za-z0-9_]{0,63}$")
EFFECT_KINDS = ("read", "write")
EFFECT_METHOD = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*#[A-Za-z_][A-Za-z0-9_]*$")
EFFECT_PARAM = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)+$")
# `(a: string, b: number): Promise<Link | null>`: the return type has to be written out.
EFFECT_SIGNATURE = re.compile(r"^\(.*\)\s*:\s*Promise<.+>$", re.S)


class ManifestError(ValueError):
    """The manifest is missing, malformed, or outside the supported schema."""


@dataclass(frozen=True)
class Effect:
    """An outside operation an `async` function may await, with the world's answer unknown.

    Exactly one of `call`, `method` and `param` names it: `call` is `module::name` (a package
    function, or a project function by its file, used as an opaque boundary), `method` is
    `Class#method` on an injected object, `param` is `parameter.field` on a function-typed
    parameter. `kind` says whether it changes what later calls answer."""
    id: str
    form: str        # "call" | "method" | "param"
    target: str
    signature: str
    kind: str
    # What the proof assumes the call answers where `signature` says `any` (see typescript/narrow.mjs).
    narrowed: str = ""

    def entry(self):
        return {"id": self.id, self.form: self.target, "signature": self.signature, "kind": self.kind,
                **({"narrowed": self.narrowed} if self.narrowed else {})}


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
    # GitHub logins allowed to approve policy changes. None: any repository
    # owner, member or collaborator other than the author; (): nobody, so the
    # policy can only change through a commit to the protected branch.
    approvers: tuple = None
    language: str = "rust"
    # Outside calls a proof may rely on, as (`module::name`, signature). They
    # are part of the policy, so a pull request can't add one for itself.
    assumes: tuple = ()
    # Outside operations `async` code may await. They extend `assumes` and are protected the same
    # way: a pull request can't add or change one for itself.
    effects: tuple = ()

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
            "language": self.language,
            "lean": self.lean,
            "approvers": None if self.approvers is None else sorted(self.approvers),
            "guarantees": {
                f"{t.id}/{g.id}": {"function": t.function, "theorem": g.theorem, "required": g.required}
                for t, g in self.guarantees()
            },
            "assumes": dict(self.assumes),
            "effects": {e.id: e.entry() for e in self.effects},
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


def _assumes(entries, language):
    if entries and language != "typescript":
        raise ManifestError("assumes is only available for TypeScript")
    if not isinstance(entries, list):
        raise ManifestError("assumes must be a list")
    assumptions = {}
    for index, entry in enumerate(entries):
        where = f"assumes[{index}]"
        _keys(entry, ("call", "signature"), ("call", "signature"), where)
        if not isinstance(entry["call"], str) or not ASSUMED_CALL.match(entry["call"]):
            raise ManifestError(f"{where}.call must look like `package::function`")
        if not isinstance(entry["signature"], str) or not entry["signature"].strip():
            raise ManifestError(f"{where}.signature must be the function's TypeScript signature")
        if entry["call"] in assumptions:
            raise ManifestError(f"{entry['call']} is assumed twice")
        assumptions[entry["call"]] = entry["signature"]
    return tuple(sorted(assumptions.items()))


def _effects(entries, language):
    if entries and language != "typescript":
        raise ManifestError("effects is only available for TypeScript")
    if not isinstance(entries, list):
        raise ManifestError("effects must be a list")
    found, ids, targets = [], set(), set()
    for index, entry in enumerate(entries):
        where = f"effects[{index}]"
        _keys(entry, ("id", "call", "method", "param", "signature", "narrowed", "kind"), ("id", "signature", "kind"), where)
        if not isinstance(entry["id"], str) or not EFFECT_ID.match(entry["id"]):
            raise ManifestError(f"{where}.id must match {EFFECT_ID.pattern}")
        if entry["id"] in ids:
            raise ManifestError(f"duplicate effect id {entry['id']!r}")
        ids.add(entry["id"])
        forms = [f for f in ("call", "method", "param") if f in entry]
        if len(forms) != 1:
            raise ManifestError(f"{where} must name the operation with exactly one of `call`, `method` and `param`")
        form = forms[0]
        target = entry[form]
        pattern = {"call": ASSUMED_CALL, "method": EFFECT_METHOD, "param": EFFECT_PARAM}[form]
        shape = {"call": "`module::function` or `path/file.ts::function`", "method": "`Class#method`",
                 "param": "`parameter.field`"}[form]
        if not isinstance(target, str) or not pattern.match(target):
            raise ManifestError(f"{where}.{form} must look like {shape}")
        if (form, target) in targets:
            raise ManifestError(f"{target} is listed as an effect twice")
        targets.add((form, target))
        signature = entry["signature"]
        if not isinstance(signature, str) or not EFFECT_SIGNATURE.match(signature.strip()):
            raise ManifestError(f"{where}.signature must be the TypeScript signature with a written "
                                "`Promise<T>` return type, for example `(id: string): Promise<Link | null>`")
        if entry["kind"] not in EFFECT_KINDS:
            raise ManifestError(f"{where}.kind must be one of: {', '.join(EFFECT_KINDS)}")
        narrowed = entry.get("narrowed", "")
        if narrowed != "" and (not isinstance(narrowed, str) or not EFFECT_SIGNATURE.match(narrowed.strip())):
            raise ManifestError(f"{where}.narrowed must be a TypeScript signature with a written `Promise<T>` return type, "
                                "the same as `signature` except where that says `any`")
        found.append(Effect(entry["id"], form, target, signature.strip(), entry["kind"], narrowed.strip()))
    return tuple(sorted(found, key=lambda e: e.id))


def parse(data: bytes) -> Manifest:
    if len(data) > MAX_MANIFEST_BYTES:
        raise ManifestError("manifest is larger than 64 KiB")
    try:
        raw = yaml.load(data.decode("utf-8"), Loader=_UniqueKeyLoader)
    except (UnicodeDecodeError, yaml.YAMLError) as error:
        raise ManifestError(f"manifest is not valid YAML: {error}") from None
    _keys(raw, ("version", "language", "crate", "package", "lean", "targets", "policy", "assumes", "effects"), ("version", "targets"), "manifest")
    if raw["version"] != 1:
        raise ManifestError("only manifest version 1 is supported")
    language = raw.get("language", "rust")
    if language not in LANGUAGES:
        raise ManifestError(f"language must be one of: {', '.join(LANGUAGES)}")
    if language == "typescript" and "crate" in raw:
        raise ManifestError("a TypeScript manifest names its directory with `package`")
    if language == "rust" and "package" in raw:
        raise ManifestError("a Rust manifest names its directory with `crate`")
    crate = _relative_path(raw.get("crate", raw.get("package", ".")), "package" if language == "typescript" else "crate")
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
        pattern = TS_PATH if language == "typescript" else RUST_PATH
        if not isinstance(entry["function"], str) or not pattern.match(entry["function"]):
            expected = "a path such as src/ledger.ts::transfer" if language == "typescript" \
                else "a Rust path such as crate_name::function"
            raise ManifestError(f"{where}.function must be {expected}")
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
    approvers = None
    if "policy" in raw:
        _keys(raw["policy"], ("approvers",), ("approvers",), "policy")
        logins = raw["policy"]["approvers"]
        if not isinstance(logins, list) or not all(isinstance(x, str) and LOGIN.match(x) for x in logins):
            raise ManifestError("policy.approvers must be a list of GitHub logins (may be empty)")
        approvers = tuple(sorted({x.lower() for x in logins}))
    return Manifest(crate, lean, tuple(targets), approvers, language, _assumes(raw.get("assumes", []), language),
                    _effects(raw.get("effects", []), language))
