"""Markdown summary for CI job pages and pull request comments."""

ICON = {"verified": "✅", "unproven": "❌", "unsupported": "⛔", "contract-stale": "⚠️", "error": "💥"}


def _translator(report):
    return ("ProofCI's TypeScript translator" if report.get("language") == "typescript"
            else "the pinned Charon/Aeneas toolchain")


def markdown(report):
    lines = ["## ProofCI", ""]
    lines.append("**Result: passed**" if report["passed"] else "**Result: blocked**")
    lines.append("")
    if report["policy_changes"]:
        approved = report["policy_source"] == "head"
        lines.append("### Policy changes " + ("(approved)" if approved else "(need maintainer approval)"))
        lines.append("")
        lines += [f"- {change}" for change in report["policy_changes"]]
        lines.append("")
        if not approved:
            lines.append("Guarantees below were checked against the protected policy of the base branch.")
            lines.append("")
    lines += ["| | Guarantee | Function | Theorem | Required | Status |",
              "|---|---|---|---|---|---|"]
    for g in report["guarantees"]:
        lines.append(
            f"| {ICON.get(g['status'], '')} | `{g['target']}/{g['guarantee']}` | `{g['function']}` | "
            f"`{g['theorem']}` | {'yes' if g['required'] else 'no'} | {g['status']} |")
    details = [g for g in report["guarantees"] if g["reason"]]
    reasons = {g["reason"] for g in details}
    if details and len(reasons) == 1 and len(details) == len(report["guarantees"]):
        lines += ["", "### Details", "", "All guarantees: " + details[0]["status"], "",
                  "```", details[0]["reason"].strip()[:4000], "```"]
    elif details:
        lines += ["", "### Details", ""]
        for g in details:
            lines.append(f"<details><summary><code>{g['target']}/{g['guarantee']}</code>: {g['status']}</summary>")
            lines += ["", "```", g["reason"].strip()[:4000], "```", "", "</details>"]
    assumed = sorted({m for g in report["guarantees"] if g["status"] == "verified" for m in g.get("assumes", [])})
    if assumed:
        lines += ["", "### Trusted models", "",
                  "Some verified guarantees rely on ProofCI's models of these library functions "
                  "(checked against `rustc`, see SECURITY.md):", ""]
        lines += [f"- `{m}`" for m in assumed]
    warned = [g for g in report["guarantees"] if g.get("warnings")]
    if warned:
        lines += ["", "### Contract warnings", "",
                  "These statements may not constrain the code as intended. Review the contract:", ""]
        for g in warned:
            lines += [f"- `{g['target']}/{g['guarantee']}`: {w}" for w in g["warnings"]]
    lines += ["", "Verified means the Lean kernel (and nanoda) accepted a proof of the exact protected "
              f"statement about the code as translated by {_translator(report)}. "
              "It covers only the listed guarantees."]
    timings = report.get("timings_seconds") or {}
    if timings:
        lines += ["", "Timings: " + ", ".join(f"{k} {v}s" for k, v in timings.items())]
    return "\n".join(lines) + "\n"
