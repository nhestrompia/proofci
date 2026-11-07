#!/usr/bin/env python3
"""Combine the per-repository survey results into one Markdown report."""
import collections
import json
import sys
from pathlib import Path

rows, total, sole, blockers, order = [], collections.Counter(), collections.Counter(), collections.Counter(), []
logic = []
for path in sorted(Path(sys.argv[1]).glob("*.json")):
    data = json.loads(path.read_text())
    s = data["summary"]
    rows.append(s)
    for key in ("functions", "logic", "m2", "m3", "models", "pure", "pureM2", "pureM3"):
        total[key] += s[key]
    sole.update(s["sole"])
    blockers.update(s["blockers"])
    logic += [r for r in data["results"] if r["logic"]]


def pct(part, whole):
    return f"{100 * part / whole:.0f}%" if whole else "-"


print("| Repository | Logic functions | Milestone 2 | Milestone 3 | With models | Pure functions | Pure, milestone 2 | Pure, milestone 3 |")
print("|---|---:|---:|---:|---:|---:|---:|---:|")
for s in sorted(rows, key=lambda r: -r["logic"]):
    print(f"| {s['repo']} | {s['logic']} | {pct(s['m2'], s['logic'])} | {pct(s['m3'], s['logic'])} | {pct(s['models'], s['logic'])} | {s['pure']} | {pct(s['pureM2'], s['pure'])} | {pct(s['pureM3'], s['pure'])} |")
print(f"| **All** | **{total['logic']}** | **{pct(total['m2'], total['logic'])}** | "
      f"**{pct(total['m3'], total['logic'])}** | **{pct(total['models'], total['logic'])}** | **{total['pure']}** | "
      f"**{pct(total['pureM2'], total['pure'])}** | **{pct(total['pureM3'], total['pure'])}** |")
print()
print("| Blocker outside the plan | Functions reaching it | Only blocker |")
print("|---|---:|---:|")
for name, count in blockers.most_common():
    print(f"| {name} | {pct(count, total['logic'])} | {pct(sole[name], total['logic'])} |")
print()
print("| Added next | Coverage after |")
print("|---|---:|")
remaining = [{f for f in r["features"] if r["tier"] == 9 and f in blockers} for r in logic]
print(f"| (plan with library models) | {pct(sum(not s for s in remaining), len(remaining))} |")
for _ in range(8):
    choices = {f for s in remaining for f in s}
    if not choices:
        break
    best = max(sorted(choices), key=lambda f: sum(s <= {f} for s in remaining))
    remaining = [s - {best} for s in remaining]
    print(f"| {best} | {pct(sum(not s for s in remaining), len(remaining))} |")
