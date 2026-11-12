"""Markdown summary for CI job pages and pull request comments."""

ICON = {"verified": "✅", "unproven": "❌", "unsupported": "⛔", "contract-stale": "⚠️", "error": "💥"}


def _translator(report):
    return ("ProofCI's TypeScript translator" if report.get("language") == "typescript"
            else "the pinned Charon/Aeneas toolchain")


BRIDGE_ICON = {"proved": "✅", "tested": "🧪", "failed": "❌"}
BRIDGE_WORDS = {"proved": "proved", "tested": "tested, not proved", "failed": "failed"}


def _functions(report):
    """TypeScript: how each function's Lean view relates to JavaScript."""
    functions = report.get("functions") or []
    if not functions:
        return []
    count = {s: sum(f["status"] == s for f in functions) for s in BRIDGE_WORDS}
    lines = ["", "### Does the Lean view match JavaScript?", "",
             f"{count['proved']} proved, {count['tested']} tested but not proved, {count['failed']} failed, "
             f"of {len(functions)} function{'s' if len(functions) != 1 else ''}.", "",
             "| | Function | Status | Why | Seconds |", "|---|---|---|---|---|"]
    for f in functions:
        why = (f["reason"] or "").replace("|", "\\|").replace("\n", " ")[:300]
        seconds = "" if f.get("seconds") is None else f["seconds"]
        lines.append(f"| {BRIDGE_ICON[f['status']]} | `{f['function']}` | {BRIDGE_WORDS[f['status']]} | {why} | {seconds} |")
    if count["tested"]:
        lines += ["", "**Tested, not proved** means the guarantee holds of the Lean view, and that the view matches what "
                  "JavaScript does has been tested on generated inputs but not proved for that function. A repository can "
                  "refuse such functions with `require_bridge` in `proofci.yaml`."]
    return lines


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
    lines += _functions(report)
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
    outside = sorted({c for g in report["guarantees"] if g["status"] == "verified" for c in g.get("assumed", [])})
    if outside:
        lines += ["", "### Assumed outside calls", "",
                  "These proofs hold only if each function below has this type and gives the same "
                  "result for the same arguments. ProofCI didn't check that code:", ""]
        lines += [f"- `{c}`" for c in outside]
    awaited = [g for g in report["guarantees"] if g["status"] == "verified" and g.get("effects") is not None]
    if awaited:
        lines += ["", "### Outside effects", "",
                  "These guarantees are about `async` code. Each holds for every answer the listed outside "
                  "calls could give, and for every history of them, and no answer is assumed unless the "
                  "contract states it as a hypothesis. ProofCI didn't check the code behind these calls:", ""]
        for g in awaited:
            lines.append(f"- `{g['target']}/{g['guarantee']}`: "
                         + (", ".join(f"`{e}`" for e in g["effects"]) if g["effects"] else "no outside calls"))
            narrowed = [e for e in g["effects"] if ", assumed to answer " in e]
            if narrowed:
                lines.append("  - the published types of these calls say `any`; the policy narrows them, and the proof "
                             "**assumes** each answers with the narrowed type: "
                             + ", ".join(f"`{e.split(': ', 1)[0]}` ({e.split(', assumed to answer ', 1)[1]})" for e in narrowed))
            lines.append("  - " + (
                "relied on arguments not being changed by other code while a call is pending, "
                "through: " + ", ".join(f"`{a}`" for a in g["arguments_stable"])
                if g["arguments_stable"] else
                "did not rely on arguments staying unchanged while a call is pending"))
            if g.get("constants_stable"):
                lines.append("  - read these exported module-level tables after an `await`; nothing in the program changes "
                             "them, and the proof assumes no code outside it does: "
                             + ", ".join(f"`{c}`" for c in g["constants_stable"]))
    warned = [g for g in report["guarantees"] if g.get("warnings")]
    if warned:
        lines += ["", "### Contract warnings", "",
                  "These statements may not constrain the code as intended. Review the contract:", ""]
        for g in warned:
            lines += [f"- `{g['target']}/{g['guarantee']}`: {w}" for w in g["warnings"]]
    if report.get("notes"):
        lines += ["", "### Notes", ""]
        lines += [f"- {note}" for note in report["notes"]]
    lines += ["", "Verified means the Lean kernel (and nanoda) accepted a proof of the exact protected "
              f"statement about the code as translated by {_translator(report)}. "
              "It covers only the listed guarantees."]
    if report.get("functions"):
        lines += ["", "For TypeScript, the table above says how far that translation is trusted: *proved* functions "
                  "have a checked theorem that the Lean view means what the code means under ProofCI's model of "
                  "JavaScript; *tested, not proved* ones are only compared with Node."]
    timings = report.get("timings_seconds") or {}
    if timings:
        lines += ["", "Timings: " + ", ".join(f"{k} {v}s" for k, v in timings.items())]
    return "\n".join(lines) + "\n"
