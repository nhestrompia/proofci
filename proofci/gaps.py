"""Aggregate ProofCI gap logs (`proofci/gaps.jsonl`) into a ranked table.

Adopting repositories keep one JSON object per line recording each refusal,
workaround or stuck proof an agent hit (see docs/skills/proofci). This command
reads any number of those files and prints which constructs cost the most time,
ranked by total minutes then occurrences.
"""

import json
import sys
from collections import defaultdict
from pathlib import Path

FIELDS = ("function", "construct", "code", "refusal", "workaround", "minutes", "resolved")

# Gap codes for everything the translator's refusal codes don't cover — proof,
# bridge, setup and report problems. A fixed, documented set (also listed in
# docs/skills/proofci/SKILL.md): like the refusal codes, these are an interface —
# add new codes, never rename or repurpose existing ones.
GAP_CODES = {
    "setup-cli": "invoking the CLI itself: packaging, PYTHONPATH, a flag the CLI rejects",
    "setup-env": "the environment fights you: docker volume ownership, a missing sandbox tool",
    "setup-deps": "dependency install/fetch fails (lockfile format, workspace link:, private registry)",
    "scan-crash": "a scan aborts on one file or function instead of reporting it",
    "contract-shape": "the contract checker rejects a statement shape",
    "proof-bind": "bind/spec friction: Bind.bind vs Std.bind, WP.spec_bind, missing Js.* step lemmas",
    "proof-tactic": "other Lean dead-ends: simp/split/cases/omega, unsolvable metavariables",
    "proof-view": "the emitted view is hard to reason about (opaque defs, _proof_ numerals)",
    "bridge-stuck": "a bridge proof times out or comes back STUCK",
    "bridge-refusal": "bridge generation refuses or crashes",
    "node-crash": "the Node comparison crashes, runs out of memory, or times out",
    "report-gap": "the report misleads or omits something a reader needs",
    "docs-gap": "the skill or other docs were wrong or missing the needed step",
}

# Refusal codes the translator emits (typescript/hints.mjs): the named ones,
# plus the `type-`, `unsupported-` and `method-` families and kebab-case
# construct codes. A `code` not in this list and not in GAP_CODES was invented
# by the agent — `proofci gaps` groups such entries by normalized construct
# text instead of trusting the ad hoc name.
REFUSAL_CODES = frozenset({
    "compile-error", "outside-package", "missing-types", "null-check",
    "optional-chain", "in-place-mutation", "mixed-number-modes",
    "unassigned-on-path", "returns-nothing", "type-named",
    "rest-parameters", "module-level-mutable", "index-non-array",
    "no-lean-spelling", "not-plain-field", "unknown-callee", "math-member",
    "record-literal", "translator-crash",
})
REFUSAL_PREFIXES = ("type-", "unsupported-", "method-")


def _code_key(code):
    """The grouping code, or None when `code` should fall back to the
    construct text: empty, `other`, or an invented code that matches neither
    the refusal list nor the fixed gap codes."""
    code = code.strip()
    if not code or code == "other":
        return None
    if code in GAP_CODES or code in REFUSAL_CODES:
        return code
    if any(code.startswith(prefix) for prefix in REFUSAL_PREFIXES):
        return code
    return None


def _repo_name(path):
    """A display name for the repo a gap file came from: the directory holding
    gaps.jsonl, or its parent when the log sits in `proofci/`."""
    name = path.resolve().parent.name
    if name == "proofci":
        name = path.resolve().parent.parent.name
    return name or str(path)


def _read_entries(files):
    entries = []
    for path in files:
        try:
            text = path.read_text()
        except OSError as error:
            print(f"proofci: could not read {path}: {error.strerror}", file=sys.stderr)
            return None
        # Split on "\n" only: splitlines() also breaks on U+2028/U+2029, which a
        # refusal message may contain inside a JSON string.
        for lineno, line in enumerate(text.split("\n"), 1):
            if not line.strip():
                continue
            try:
                entry = json.loads(line)
            except json.JSONDecodeError as error:
                print(f"proofci: {path}:{lineno}: {error}", file=sys.stderr)
                return None
            if not isinstance(entry, dict):
                print(f"proofci: {path}:{lineno}: not a JSON object", file=sys.stderr)
                return None
            entries.append((_repo_name(path), entry))
    return entries


def _normalize(construct):
    """The grouping key for free-text constructs: lowercase, whitespace collapsed,
    so "typeof guard" and "typeof  guard" don't split into separate rows."""
    return " ".join(str(construct).lower().split())


def _grouped(entries):
    """Rank entries by group: a known stable `code` when present, else the
    normalized construct text (which is also where `other`, empty and invented
    codes land). Returns rows sorted by minutes then count."""
    groups = defaultdict(lambda: {"count": 0, "minutes": 0, "unresolved": 0,
                                  "functions": set(), "repos": set(),
                                  "texts": defaultdict(int)})
    for repo, entry in entries:
        construct = entry.get("construct") or "(unclassified)"
        key = _code_key(str(entry.get("code") or ""))
        key = f"code:{key}" if key else f"construct:{_normalize(construct)}"
        row = groups[key]
        row["count"] += 1
        try:
            row["minutes"] += int(entry.get("minutes") or 0)
        except (TypeError, ValueError):
            pass
        if not entry.get("resolved", False):
            row["unresolved"] += 1
        function = entry.get("function")
        if function:
            row["functions"].add(function)
        row["repos"].add(repo)
        row["texts"][str(construct)] += 1
    rows = []
    for key, row in groups.items():
        # Code groups are named by the code (stable across repos); construct
        # groups show the most common construct spelling.
        label = (key.split(":", 1)[1] if key.startswith("code:")
                 else max(row["texts"].items(), key=lambda item: item[1])[0])
        rows.append({"key": key, "construct": label, "count": row["count"],
                     "minutes": row["minutes"], "unresolved": row["unresolved"],
                     "repos": sorted(row["repos"]),
                     "functions": sorted(row["functions"])})
    rows.sort(key=lambda r: (-r["minutes"], -r["count"], r["key"]))
    return rows


def run(files, as_json=False):
    """Print the ranked gap table for the given files; exit code."""
    if not files:
        files = [Path("proofci/gaps.jsonl")]
    files = [Path(f) for f in files]
    existing = [f for f in files if f.exists()]
    if not existing:
        print("proofci: no gap logs found "
              f"(looked for {', '.join(str(f) for f in files)})", file=sys.stderr)
        return 2
    entries = _read_entries(existing)
    if entries is None:
        return 2

    missing = len(files) - len(existing)
    if missing:
        print(f"{missing} file(s) not found and skipped.", file=sys.stderr)

    rows = _grouped(entries)
    if as_json:
        print(json.dumps({"version": 1, "rows": rows, "missing": missing}, indent=2))
        return 0

    def cell(text):
        return str(text).replace("|", "\\|").replace("\n", " ")

    print("| Construct | Repos | Hits | Unresolved | Minutes | Examples |")
    print("|---|---:|---:|---:|---:|---|")
    for row in rows:
        examples = ", ".join(row["functions"][:3])
        print(f"| {cell(row['construct'])} | {len(row['repos'])} | {row['count']} | "
              f"{row['unresolved']} | {row['minutes']} | {cell(examples)} |")
    return 0
