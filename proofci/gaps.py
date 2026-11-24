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
            entries.append(entry)
    return entries


def _normalize(construct):
    """The grouping key for free-text constructs: lowercase, whitespace collapsed,
    so "typeof guard" and "typeof  guard" don't split into separate rows."""
    return " ".join(str(construct).lower().split())


def _grouped(entries):
    """Rank entries by group: the stable refusal `code` when present, else the
    normalized construct text. Returns rows sorted by minutes then count."""
    groups = defaultdict(lambda: {"count": 0, "minutes": 0, "unresolved": 0,
                                  "functions": set(), "texts": defaultdict(int)})
    for entry in entries:
        construct = entry.get("construct") or "(unclassified)"
        code = (entry.get("code") or "").strip()
        key = f"code:{code}" if code else f"construct:{_normalize(construct)}"
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
        row["texts"][str(construct)] += 1
    rows = []
    for key, row in groups.items():
        # The most common construct text becomes the row's display name.
        label = max(row["texts"].items(), key=lambda item: item[1])[0]
        rows.append({"key": key, "construct": label, "count": row["count"],
                     "minutes": row["minutes"], "unresolved": row["unresolved"],
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

    rows = _grouped(entries)
    if as_json:
        print(json.dumps({"version": 1, "rows": rows}, indent=2))
        return 0

    def cell(text):
        return str(text).replace("|", "\\|").replace("\n", " ")

    print("| Construct | Hits | Unresolved | Minutes | Examples |")
    print("|---|---:|---:|---:|---|")
    for row in rows:
        examples = ", ".join(row["functions"][:3])
        print(f"| {cell(row['construct'])} | {row['count']} | {row['unresolved']} | {row['minutes']} | {cell(examples)} |")
    missing = len(files) - len(existing)
    if missing:
        print(f"\n{missing} file(s) not found and skipped.", file=sys.stderr)
    return 0
