"""Aggregate scenario runs into evaluation metrics and human-readable text.

Inputs are the per-run records written by evaluate.py. Nothing here runs the
verifier. False acceptances are carried into every summary; no option removes
them from the aggregate.
"""
import math
import statistics

LATENCY_TARGETS = {"median_seconds": 60, "p95_seconds": 300}
FIXED_TACTICS = {"rfl", "simp [target] <;> omega"}
DECISIONS = ("verified", "violated", "unproven")


def percentile(values, fraction):
    """Nearest-rank percentile; None for an empty sample."""
    if not values:
        return None
    ordered = sorted(values)
    rank = max(1, math.ceil(fraction * len(ordered)))
    return ordered[rank - 1]


def latency(values):
    if not values:
        return {"count": 0, "median_seconds": None, "p95_seconds": None, "min_seconds": None, "max_seconds": None}
    return {"count": len(values), "median_seconds": statistics.median(values), "p95_seconds": percentile(values, 0.95),
            "min_seconds": min(values), "max_seconds": max(values)}


def _count(items):
    result = {}
    for item in items:
        result[item] = result.get(item, 0) + 1
    return dict(sorted(result.items()))


def mode_summary(runs):
    """Summarize all runs of one mode."""
    results = [r for run in runs for r in run["results"]]
    unproven = [r for r in results if r["decision"] == "unproven"]
    usage = {"model_calls": 0, "input_tokens": 0, "output_tokens": 0, "settled_cost_micros": 0,
             "uncertain_requests": 0, "uncertain_reserved_cost_micros": 0, "wall_seconds": 0.0}
    for run in runs:
        u = run.get("usage", {})
        usage["wall_seconds"] += run["wall_seconds"]
        usage["model_calls"] += u.get("model_calls", 0)
        usage["input_tokens"] += u.get("input_tokens", 0)
        usage["output_tokens"] += u.get("output_tokens", 0)
        usage["settled_cost_micros"] += u.get("settled_cost_micros", 0)
        usage["uncertain_requests"] += u.get("uncertain_requests", 0)
        usage["uncertain_reserved_cost_micros"] += u.get("uncertain_reserved_cost_micros", 0)
    repairs = _count(r["repaired_by"] for r in results if r.get("repaired_by"))
    failed_attempts = sum(1 for r in results if r.get("repair_attempted") and r["decision"] != "verified")
    model_failures = _count(r["repair_reason"] for r in results if r.get("repair_reason"))
    run_errors = [run for run in runs if run["exit"] == 2]
    invalid = [r for r in results if r["reason"] == "invalid_evidence"]
    invalid_runs = [run for run in runs if run["category"] == "invalid_submission" and run["exit"] == 2]
    unsupported_results = [r for r in results if r["reason"] == "unsupported_semantics"]
    unsupported_paths = sum(run.get("coverage", {}).get("unsupported_changed_code", 0) for run in runs)
    timeouts = [r for r in results if r["reason"] in ("timeout", "obligation_budget_exhausted")]
    timeout_runs = [run for run in runs if run.get("run_reason") == "timeout"]
    return {
        "runs": len(runs),
        "scenarios": len({run["scenario"] for run in runs}),
        "obligation_results": len(results),
        "decisions": {d: sum(r["decision"] == d for r in results) for d in DECISIONS},
        "unproven_reasons": _count(r["reason"] for r in unproven),
        "unsupported_inputs": {"unsupported_target_results": len(unsupported_results),
                               "unsupported_changed_paths": unsupported_paths},
        "invalid_submissions": {"invalid_evidence_results": len(invalid),
                                "rejected_runs": len(invalid_runs)},
        "timeouts": {"obligation_results": len(timeouts), "runs": len(timeout_runs)},
        "execution_errors": _count(run.get("run_reason") or "unknown" for run in run_errors),
        "repairs": repairs,
        "failed_repair_attempts": failed_attempts,
        "repair_failure_reasons": model_failures,
        "usage": usage,
        "cost": {"model_micros_settled": usage["settled_cost_micros"],
                 "model_micros_unknown_upper_bound": usage["uncertain_reserved_cost_micros"],
                 "cost_known": usage["uncertain_requests"] == 0},
        "expectations": {"met": sum(run["expectation"]["met"] for run in runs),
                         "not_met": [{"scenario": run["scenario"], "repetition": run["repetition"],
                                      "failures": run["expectation"]["failures"]}
                                     for run in runs if not run["expectation"]["met"]]},
        "by_category": {category: {
            "runs": len(items),
            "decisions": {d: sum(r["decision"] == d for run in items for r in run["results"]) for d in DECISIONS},
            "exits": _count(run["exit"] for run in items),
            "false_acceptances": sum(len(run["false_acceptances"]) for run in items),
        } for category, items in sorted(_group(runs, "category").items())},
    }


def _group(runs, key):
    groups = {}
    for run in runs:
        groups.setdefault(run[key], []).append(run)
    return groups


def latency_summary(runs):
    deterministic = [run for run in runs if run["mode"] == "deterministic"]
    cold = [run["wall_seconds"] for run in deterministic if run["temperature"] == "cold"]
    warm = [run["wall_seconds"] for run in deterministic if run["temperature"] == "warm"]
    warm_stats = latency(warm)
    if warm_stats["count"]:
        assessment = {
            "median_below_60_seconds": warm_stats["median_seconds"] < LATENCY_TARGETS["median_seconds"],
            "p95_below_300_seconds": warm_stats["p95_seconds"] < LATENCY_TARGETS["p95_seconds"],
        }
        assessment["met"] = all(assessment.values())
    else:
        assessment = {"met": None, "reason": "no warm deterministic runs"}
    by_category = {}
    for category, items in sorted(_group(deterministic, "category").items()):
        by_category[category] = {
            "cold": latency([r["wall_seconds"] for r in items if r["temperature"] == "cold"]),
            "warm": latency([r["wall_seconds"] for r in items if r["temperature"] == "warm"]),
        }
    per_obligation = [r["elapsed_seconds"] for run in deterministic if run["temperature"] == "warm"
                      for r in run["results"] if isinstance(r.get("elapsed_seconds"), (int, float))]
    assisted = [run["wall_seconds"] for run in runs if run["mode"] == "assisted"]
    return {"targets": LATENCY_TARGETS, "deterministic_cold": latency(cold), "deterministic_warm": warm_stats,
            "assessment": assessment, "deterministic_by_category": by_category,
            "deterministic_warm_per_obligation": latency(per_obligation), "assisted": latency(assisted),
            "policy": "Measured with the unchanged pinned verifier and resource policy; no proof policy is relaxed."}


def stability(runs):
    """Outcome variation across repetitions, separated by mode."""
    outcomes = {}
    for run in runs:
        for r in run["results"]:
            key = (run["mode"], run["scenario"], r["id"])
            outcomes.setdefault(key, set()).add((r["decision"], r["reason"]))
        outcomes.setdefault((run["mode"], run["scenario"], "<exit>"), set()).add(("exit", str(run["exit"])))
    unstable = {"deterministic": [], "assisted": []}
    for (mode, scenario, obligation), seen in sorted(outcomes.items()):
        if len(seen) > 1:
            unstable[mode].append({"scenario": scenario, "obligation": obligation,
                                   "outcomes": sorted("/".join(item) for item in seen)})
    return {"deterministic_instability": unstable["deterministic"],
            "model_nondeterminism": unstable["assisted"]}


def utility(runs):
    """Measured contribution of assistance relative to deterministic runs."""
    deterministic = {(run["scenario"], run["repetition"]): run for run in runs if run["mode"] == "deterministic"}
    assisted = [run for run in runs if run["mode"] == "assisted"]
    if not assisted:
        return {"measured": False, "reason": "no assisted runs", "additional_verified": 0,
                "pairs": 0, "regressions": 0, "model_repairs": 0}
    gained, lost, pairs = [], [], 0
    for run in assisted:
        base = deterministic.get((run["scenario"], run["repetition"]))
        if base is None:
            continue
        pairs += 1
        before = {r["id"]: r for r in base["results"]}
        for r in run["results"]:
            prior = before.get(r["id"])
            if prior is None:
                continue
            if r["decision"] == "verified" and prior["decision"] != "verified":
                gained.append({"scenario": run["scenario"], "repetition": run["repetition"], "obligation": r["id"]})
            if prior["decision"] == "verified" and r["decision"] != "verified":
                lost.append({"scenario": run["scenario"], "repetition": run["repetition"], "obligation": r["id"]})
    model_repairs = sum(1 for run in assisted for r in run["results"] if r.get("repaired_by") == "model")
    settled = sum(run.get("usage", {}).get("settled_cost_micros", 0) for run in assisted)
    unknown = sum(run.get("usage", {}).get("uncertain_reserved_cost_micros", 0) for run in assisted)
    return {"measured": pairs > 0, "pairs": pairs, "additional_verified": len(gained), "gains": gained,
            "regressions": len(lost), "regression_details": lost, "model_repairs": model_repairs,
            "settled_cost_micros": settled, "unknown_cost_upper_bound_micros": unknown,
            "settled_cost_micros_per_additional_verified": (settled / len(gained)) if gained else None}


def paid_assistance(util, false_acceptances, cost_known, complete):
    """Paid assistance may become a default only with measured, sound, costed utility."""
    reasons = []
    if not util["measured"]:
        reasons.append("assistance was not measured on this corpus")
    elif util["additional_verified"] == 0:
        reasons.append("assistance verified no obligation that deterministic runs left unverified")
    if util.get("regressions"):
        reasons.append("assisted runs lost results that deterministic runs verified")
    if false_acceptances:
        reasons.append("false acceptances were recorded")
    if not cost_known:
        reasons.append("some model cost is unknown")
    if not complete:
        reasons.append("the evaluation did not cover the complete frozen corpus")
    return {"eligible_for_default": not reasons, "reasons": reasons,
            "note": "Eligibility only permits a maintainer decision; it never enables paid assistance automatically."}


def summarize(runs, *, complete, modes, assisted_status, soundness, persistence):
    false_acceptances = [dict(item, scenario=run["scenario"], mode=run["mode"], repetition=run["repetition"],
                              category=run["category"])
                         for run in runs for item in run["false_acceptances"]]
    false_rejections = [dict(item, scenario=run["scenario"], mode=run["mode"], repetition=run["repetition"])
                        for run in runs for item in run["false_rejections"]]
    by_mode = {mode: mode_summary([run for run in runs if run["mode"] == mode]) for mode in modes}
    util = utility(runs)
    assisted = by_mode.get("assisted")
    cost_known = assisted["cost"]["cost_known"] if assisted else True
    sound = {category_set: sum(1 for item in false_acceptances if item["category"] in members)
             for category_set, members in (("soundness", soundness), ("persistence", persistence))}
    expectations_met = all(run["expectation"]["met"] for run in runs if run["mode"] == "deterministic")
    lat = latency_summary(runs)
    return {
        "release": {
            "blocked": bool(false_acceptances) or not expectations_met,
            "false_acceptances": len(false_acceptances),
            "false_acceptances_in_soundness_scenarios": sound["soundness"],
            "false_acceptances_in_persistence_scenarios": sound["persistence"],
            "deterministic_expectations_met": expectations_met,
            "complete_corpus": complete,
            "latency_target_met": lat["assessment"]["met"],
            "statement": "Any false acceptance blocks release. This aggregate always lists every false acceptance.",
        },
        "false_acceptances": false_acceptances,
        "false_rejections": false_rejections,
        "modes": by_mode,
        "assisted_status": assisted_status,
        "latency": lat,
        "stability": stability(runs),
        "assistance_utility": util,
        "default_paid_assistance": paid_assistance(util, false_acceptances, cost_known, complete),
    }


def _fmt(value, digits=1):
    if value is None:
        return "n/a"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return str(value)


def markdown(evaluation):
    s = evaluation["summary"]
    release = s["release"]
    env = evaluation["environment"]
    lines = ["# ProofCI evaluation", ""]
    lines += [f"Corpus `{evaluation['corpus']['corpus_sha256'][:16]}` frozen {evaluation['corpus']['frozen_at']}; "
              f"{evaluation['corpus']['properties']} properties in {len(evaluation['corpus']['packages'])} packages; "
              f"{evaluation['corpus']['scenarios_run']} of {evaluation['corpus']['scenarios_total']} scenarios; "
              f"{evaluation['repetitions']} repetitions. Started {evaluation['started_at']}.", ""]
    lines += ["## Release gate", ""]
    lines.append(f"- **{'BLOCKED' if release['blocked'] else 'Not blocked'}** by soundness or expectations.")
    lines.append(f"- False acceptances: **{release['false_acceptances']}** "
                 f"(soundness scenarios {release['false_acceptances_in_soundness_scenarios']}, "
                 f"persistence scenarios {release['false_acceptances_in_persistence_scenarios']}).")
    lines.append(f"- Deterministic expectations met: {release['deterministic_expectations_met']}.")
    lines.append(f"- Complete frozen corpus: {release['complete_corpus']}.")
    lines.append(f"- Warm latency target met: {release['latency_target_met']}.")
    if s["false_acceptances"]:
        lines += ["", "| Mode | Scenario | Rep | Obligation | Kind | Detail |", "| --- | --- | --- | --- | --- | --- |"]
        for item in s["false_acceptances"]:
            lines.append(f"| {item['mode']} | {item['scenario']} | {item['repetition']} | {item.get('obligation', '-')} "
                         f"| {item['kind']} | {item.get('detail', '')} |")
    lines += ["", "## Outcomes by mode", ""]
    lines += ["| Mode | Runs | Verified | Violated | Unproven | Repairs | Failed repairs | Run errors |",
              "| --- | --- | --- | --- | --- | --- | --- | --- |"]
    for mode, m in s["modes"].items():
        lines.append(f"| {mode} | {m['runs']} | {m['decisions']['verified']} | {m['decisions']['violated']} | "
                     f"{m['decisions']['unproven']} | {sum(m['repairs'].values())} | {m['failed_repair_attempts']} | "
                     f"{sum(m['execution_errors'].values())} |")
    for mode, m in s["modes"].items():
        lines += ["", f"### {mode.capitalize()}", ""]
        lines.append("Unproven reasons: " + (", ".join(f"`{k}` {v}" for k, v in m["unproven_reasons"].items()) or "none") + ".")
        lines.append(f"Unsupported inputs: {m['unsupported_inputs']['unsupported_target_results']} unsupported target results, "
                     f"{m['unsupported_inputs']['unsupported_changed_paths']} unsupported changed paths.")
        lines.append(f"Invalid submissions: {m['invalid_submissions']['invalid_evidence_results']} invalid evidence results, "
                     f"{m['invalid_submissions']['rejected_runs']} rejected runs.")
        lines.append(f"Timeouts: {m['timeouts']['obligation_results']} obligation results, {m['timeouts']['runs']} runs.")
        lines.append("Execution errors: " + (", ".join(f"`{k}` {v}" for k, v in m["execution_errors"].items()) or "none") + ".")
        lines.append("Repairs: " + (", ".join(f"{k} {v}" for k, v in m["repairs"].items()) or "none")
                     + f"; failed repair attempts {m['failed_repair_attempts']}"
                     + ("; repair failures " + ", ".join(f"`{k}` {v}" for k, v in m["repair_failure_reasons"].items())
                        if m["repair_failure_reasons"] else "") + ".")
        u = m["usage"]
        lines.append(f"Usage: {u['model_calls']} model calls, {u['input_tokens']} input and {u['output_tokens']} output tokens, "
                     f"{_fmt(u['wall_seconds'])} s wall time. Model cost: {m['cost']['model_micros_settled']} micros settled, "
                     f"{m['cost']['model_micros_unknown_upper_bound']} micros unknown (upper bound); cost known: {m['cost']['cost_known']}.")
        if m["expectations"]["not_met"]:
            lines.append("Expectations not met: " + "; ".join(
                f"{item['scenario']} (rep {item['repetition']}): {', '.join(item['failures'])}"
                for item in m["expectations"]["not_met"]) + ".")
        lines += ["", "| Category | Runs | Verified | Violated | Unproven | Exit codes | False acceptances |",
                  "| --- | --- | --- | --- | --- | --- | --- |"]
        for category, c in m["by_category"].items():
            lines.append(f"| {category} | {c['runs']} | {c['decisions']['verified']} | {c['decisions']['violated']} | "
                         f"{c['decisions']['unproven']} | {', '.join(f'{k}:{v}' for k, v in c['exits'].items())} | "
                         f"{c['false_acceptances']} |")
    if not s["modes"].get("assisted"):
        lines += ["", f"Assisted mode: {s['assisted_status']['status']} ({s['assisted_status']['reason']})."]
    lat = s["latency"]
    lines += ["", "## Latency", "",
              "Wall time of the public command per scenario run, deterministic mode.", "",
              "| Sample | Runs | Median s | p95 s | Min s | Max s |", "| --- | --- | --- | --- | --- | --- |"]
    for label, value in (("cold", lat["deterministic_cold"]), ("warm", lat["deterministic_warm"]),
                         ("warm per obligation", lat["deterministic_warm_per_obligation"]),
                         ("assisted (all)", lat["assisted"])):
        lines.append(f"| {label} | {value['count']} | {_fmt(value['median_seconds'])} | {_fmt(value['p95_seconds'])} | "
                     f"{_fmt(value['min_seconds'])} | {_fmt(value['max_seconds'])} |")
    a = lat["assessment"]
    lines += ["", f"Assessment against a warm median below 60 s and p95 below 300 s: "
              f"median {_fmt(a.get('median_below_60_seconds'))}, p95 {_fmt(a.get('p95_below_300_seconds'))}, "
              f"met {_fmt(a.get('met'))}. {lat['policy']}", "",
              "| Category | Cold median s | Warm median s | Warm p95 s |", "| --- | --- | --- | --- |"]
    for category, c in lat["deterministic_by_category"].items():
        lines.append(f"| {category} | {_fmt(c['cold']['median_seconds'])} | {_fmt(c['warm']['median_seconds'])} | "
                     f"{_fmt(c['warm']['p95_seconds'])} |")
    st = s["stability"]
    lines += ["", "## Stability", "",
              f"Deterministic outcomes that changed between repetitions: {len(st['deterministic_instability'])}.",
              f"Assisted outcomes that changed between repetitions (model nondeterminism, reported separately): "
              f"{len(st['model_nondeterminism'])}."]
    for item in st["deterministic_instability"] + st["model_nondeterminism"]:
        lines.append(f"- {item['scenario']} / {item['obligation']}: {', '.join(item['outcomes'])}")
    util, paid = s["assistance_utility"], s["default_paid_assistance"]
    lines += ["", "## Assistance utility", ""]
    if util["measured"]:
        lines.append(f"Paired runs: {util['pairs']}. Additional verified obligations: {util['additional_verified']}. "
                     f"Regressions: {util['regressions']}. Settled cost per additional verified obligation: "
                     f"{_fmt(util['settled_cost_micros_per_additional_verified'])} micros. Unknown cost upper bound: "
                     f"{util['unknown_cost_upper_bound_micros']} micros.")
    else:
        lines.append(f"Not measured: {util['reason']}.")
    lines.append(f"Default paid assistance eligible: **{paid['eligible_for_default']}**. "
                 + ("Reasons: " + "; ".join(paid["reasons"]) + ". " if paid["reasons"] else "") + paid["note"])
    lines += ["", "## Environment", ""]
    for key in ("platform", "machine", "cpu_count", "memory_bytes", "python", "docker", "git"):
        lines.append(f"- {key}: {env.get(key)}")
    ident = env["verifier"]
    for key in ("commit", "dirty", "image_id", "toolchain_sha256", "dependency_sha256", "trust_policy_sha256",
                "bubblewrap_sha256", "lean_commit", "builder_sha256"):
        lines.append(f"- {key}: {ident.get(key)}")
    cache = env["cache"]
    lines.append(f"- evidence cache: {cache['bundles_reused']} bundles reused, {cache['bundles_built']} built "
                 f"({_fmt(cache['build_seconds'])} s); {cache['note']}")
    lines.append(f"- cold/warm: {env['temperature_definition']}")
    lines += ["", "## Scenario runs", "", "| Scenario | Category | Mode | Rep | Exit | Wall s | Results | Expectation |",
              "| --- | --- | --- | --- | --- | --- | --- | --- |"]
    for run in evaluation["runs"]:
        counts = _count(r["decision"] for r in run["results"])
        lines.append(f"| {run['scenario']} | {run['category']} | {run['mode']} | {run['repetition']} | {run['exit']} | "
                     f"{_fmt(run['wall_seconds'])} | {', '.join(f'{k} {v}' for k, v in counts.items()) or run.get('run_reason', '')} | "
                     f"{'met' if run['expectation']['met'] else 'NOT MET'} |")
    return "\n".join(lines) + "\n"
