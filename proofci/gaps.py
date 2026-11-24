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
            lines = path.read_text().splitlines()
        except OSError as error:
            print(f"proofci: could not read {path}: {error.strerror}", file=sys.stderr)
            return None
        for lineno, line in enumerate(lines, 1):
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


def run(files):
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

    ranked = defaultdict(lambda: {"count": 0, "minutes": 0, "unresolved": 0, "functions": set()})
    for entry in entries:
        key = entry.get("construct") or "(unclassified)"
        row = ranked[key]
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

    rows = sorted(ranked.items(), key=lambda item: (-item[1]["minutes"], -item[1]["count"], item[0]))
    print("| Construct | Hits | Unresolved | Minutes | Examples |")
    print("|---|---:|---:|---:|---|")
    for construct, row in rows:
        examples = ", ".join(sorted(row["functions"])[:3])
        print(f"| {construct} | {row['count']} | {row['unresolved']} | {row['minutes']} | {examples} |")
    missing = len(files) - len(existing)
    if missing:
        print(f"\n{missing} file(s) not found and skipped.", file=sys.stderr)
    return 0
