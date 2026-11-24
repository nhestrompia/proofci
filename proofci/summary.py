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
    for f in functions:
        for w in f.get("warnings") or []:
            lines.append(f"> ⚠️ {w}")
    if count["tested"]:
        lines += ["", "**Tested, not proved** means the guarantee holds of the Lean view, and that the view matches what "
                  "JavaScript does has been tested on generated inputs but not proved for that function. A repository can "
                  "refuse such functions with `require_bridge` in `proofci.yaml`."]
    return lines


def _downgrades(report):
    """Functions proved on the base branch that are not proved in this pull request."""
    downgrades = report.get("downgrades") or []
    stale = report.get("stale_accepts") or []
    if not downgrades:
        return (["", "Accepted under `accept_downgrades` but not a downgrade here — stale entries a "
                 "maintainer may want to remove: " + ", ".join(f"`{f}`" for f in stale)] if stale else [])
    lines = ["", "### Proved on the base branch, not proved now", "",
             "| | Function | On the base | In this pull request | Accepted | Why |",
             "|---|---|---|---|---|---|"]
    for d in downgrades:
        now = "tested, not proved" if d["now"] == "tested" else d["now"]
        why = (d["reason"] or "").replace("|", "\\|").replace("\n", " ")[:300]
        lines.append(f"| {'✅' if d['accepted'] else '⛔'} | `{d['function']}` | {d['was']} | {now} | "
                     f"{'yes' if d['accepted'] else 'no'} | {why} |")
    if stale:
        lines += ["", "Accepted under `accept_downgrades` but not a downgrade here — stale entries a "
                  "maintainer may want to remove: " + ", ".join(f"`{f}`" for f in stale)]
    unaccepted = [d for d in downgrades if not d["accepted"]]
    if unaccepted:
        lines += ["", "A maintainer accepts a downgrade by listing the function under `accept_downgrades` in "
                  "`proofci.yaml`; that is a policy change and is approved the same way. The pull request's "
                  "own `accept_downgrades` does not count."]
    return lines


def _reason(g):
    lines = ["```", g["reason"].strip()[:4000], "```"]
    if g.get("hint"):
        lines += ["", "**How to fix:** " + g["hint"].strip()[:1000]]
    return lines


def _status(g):
    """How a guarantee's status reads in the report: an unjudged guarantee
    caused by a tool failure is an infrastructure failure, not unsupported
    code."""
    return "infrastructure failure" if g.get("infrastructure") else g["status"]


def _claims(report):
    """Per guarantee: the claim in plain words, what it rests on, and -- when an
    approved change reworded it -- the claim it replaces."""
    lines = ["", "### What each guarantee says", ""]
    for g in report["guarantees"]:
        claim = g.get("claim") or "*(the contract gives this theorem no `/--` doc comment)*"
        lines.append(f"- {ICON.get(g['status'], '')} `{g['target']}/{g['guarantee']}` — **{_status(g)}**: {claim}")
        if g.get("previous_claim") is not None and g["previous_claim"] != claim:
            lines.append(f"  - before this change it claimed: {g['previous_claim'] or '*(nothing)*'}")
        if g.get("scope") == "example":
            lines.append("  - scope: **example** — checks one fixed input only, not the general case")
        rests = []
        if g.get("hypotheses"):
            rests.append("it holds only when " + ", ".join(f"`{h}`" for h in g["hypotheses"]))
        for m in g.get("assumes") or []:
            rests.append(f"the trusted model of `{m}`")
        for c in g.get("assumed") or []:
            rests.append(f"the outside call `{c}`")
        if g.get("effects"):
            rests.append("the outside calls listed below")
        if g.get("bridge") == "tested":
            rests.append("a Lean view tested against Node but not proved to match JavaScript")
        if rests:
            lines.append("  - relies on " + "; ".join(rests))
        for w in g.get("strength") or []:
            lines.append(f"  - strength: {w}")
    return lines


def _weak(report):
    """Verified guarantees that let a planted defect through."""
    return [e["guarantee"] for e in report.get("escapes") or []]


def _verdict(report):
    required = [g for g in report["guarantees"] if g["required"]]
    weak = _weak(report)
    if report["passed"]:
        verdict = f"**Result: passed** — all {len(required)} required guarantees verified."
        if report.get("first_adoption"):
            verdict += " (First adoption approved.)"
        if weak:
            plural = len(weak) > 1
            verdict += (f" But {len(weak)} verified guarantee{'s' if plural else ''} let a planted bug "
                        f"through ({', '.join(f'`{g}`' for g in weak)}): see the strength notes — "
                        "set `require_strength` in `proofci.yaml` to block on this.")
        example = [g for g in report["guarantees"] if g.get("scope") == "example"]
        if example:
            plural = len(example) > 1
            verdict += (f" {len(example)} guarantee{'s' if plural else ''} "
                        f"({', '.join(f'`{g['target']}/{g['guarantee']}`' for g in example)}) check "
                        "one fixed input only: see the scope labels — set `require_general` in "
                        "`proofci.yaml` to block on this.")
        stale = report.get("stale_accepts") or []
        if stale:
            verdict += (" `accept_downgrades` lists " + ", ".join(f"`{f}`" for f in stale)
                        + ", not a downgrade here — a stale entry a maintainer may remove.")
        return verdict
    reasons = []
    if report["policy_changes"] and report["policy_source"] != "head":
        reasons.append("this is a first adoption — the whole contract needs maintainer approval"
                       if report.get("first_adoption")
                       else "the policy change waits for maintainer approval")
    if report.get("invalid_contract"):
        reasons.append("the approved contract is missing `/--` doc comments on new guarantees")
    bad = sum(g["status"] != "verified" for g in required)
    if bad:
        reasons.append(f"{bad} of {len(required)} required guarantees not verified")
    if not required:
        reasons.append("the policy lists no required guarantees")
    if weak:
        plural = len(weak) > 1
        reasons.append(f"{len(weak)} verified guarantee{'s' if plural else ''} "
                       f"({', '.join(f'`{g}`' for g in weak)}) let a planted bug through"
                       + (" — `require_strength` is set" if report.get("require_strength") else ""))
    example = [g for g in report["guarantees"] if g.get("scope") == "example"]
    if example and report.get("require_general"):
        plural = len(example) > 1
        reasons.append(f"{len(example)} guarantee{'s' if plural else ''} "
                       f"({', '.join(f'`{g['target']}/{g['guarantee']}`' for g in example)}) check "
                       "one fixed input only — `require_general` is set")
    proved = [d["function"] for d in report.get("downgrades") or []
              if not d["accepted"] and d["was"] == "proved"]
    unknown = [d["function"] for d in report.get("downgrades") or []
               if not d["accepted"] and d["was"] != "proved"]
    if proved:
        plural = len(proved) > 1
        reasons.append(" and ".join(f"`{f}`" for f in proved)
                       + (" were" if plural else " was")
                       + " proved on the base branch and "
                       + ("are" if plural else "is") + " not now")
    if unknown:
        plural = len(unknown) > 1
        reasons.append(" and ".join(f"`{f}`" for f in unknown)
                       + " may have been proved on the base branch — the base could not be checked — and "
                       + ("are" if plural else "is") + " not proved now")
    verdict = "**Result: blocked** — " + "; ".join(reasons) + "."
    stale = report.get("stale_accepts") or []
    if stale:
        verdict += (" `accept_downgrades` lists " + ", ".join(f"`{f}`" for f in stale)
                    + ", not a downgrade here — a stale entry a maintainer may remove.")
    return verdict


def markdown(report):
    lines = ["## ProofCI", "", _verdict(report), ""]
    if report.get("first_adoption"):
        approved = report["policy_source"] == "head"
        lines.append("### First adoption " + ("(approved)" if approved else "(needs maintainer approval)"))
        lines.append("")
        lines.append("The base branch has no `proofci.yaml`: this pull request introduces ProofCI. Every "
                     "target and guarantee was checked as new — the contract needs a /-- doc comment on "
                     "each and all of them were tested against planted defects. Approving this pull "
                     "request accepts the whole contract, after which re-running the job uses it.")
        lines.append("")
    if report["policy_changes"]:
        approved = report["policy_source"] == "head"
        lines.append("### Policy changes " + ("(approved)" if approved else "(need maintainer approval)"))
        lines.append("")
        lines += [f"- {change}" for change in report["policy_changes"]]
        lines.append("")
        if not approved and not report.get("first_adoption"):
            lines.append("Guarantees below were checked against the protected policy of the base branch.")
            lines.append("")
    lines += ["| | Guarantee | Function | Theorem | Required | Status |",
              "|---|---|---|---|---|---|"]
    for g in report["guarantees"]:
        lines.append(
            f"| {ICON.get(g['status'], '')} | `{g['target']}/{g['guarantee']}` | `{g['function']}` | "
            f"`{g['theorem']}` | {'yes' if g['required'] else 'no'} | {_status(g)} |")
    lines += _claims(report)
    lines += _functions(report)
    lines += _downgrades(report)
    details = [g for g in report["guarantees"] if g["reason"]]
    reasons = {(g["reason"], g.get("hint")) for g in details}
    if details and len(reasons) == 1 and len(details) == len(report["guarantees"]):
        lines += ["", "### Details", "", "All guarantees: " + details[0]["status"], ""] + _reason(details[0])
    elif details:
        lines += ["", "### Details", ""]
        for g in details:
            lines.append(f"<details><summary><code>{g['target']}/{g['guarantee']}</code>: {_status(g)}</summary>")
            if g.get("statement"):
                lines += ["", "The protected statement:", "", "```lean", g["statement"], "```"]
            lines += [""] + _reason(g) + ["", "</details>"]
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
