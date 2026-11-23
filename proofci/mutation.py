"""Does a verified guarantee constrain the function it names? Plant small
defects in the Lean view; a mutant is only interesting when it changes what the
view computes on a generated input (an equivalent mutant proves nothing).
A guarantee that rejects none of those behavioural mutants may hold for any
version of the function: warn, don't fail — it may sit on paths the guarantee
never meant to cover.

Costs: one #eval pass over the original view, then per effective mutant one
#eval pass and one `lake build Proofs`, all in disposable clones of the
workspace, capped by PROOFCI_MUTANTS (per function) and PROOFCI_MUTATION_BUDGET
(seconds)."""

import re
import os
import time
from concurrent.futures import ThreadPoolExecutor

from . import claims, lean

MAX_MUTANTS = int(os.environ.get("PROOFCI_MUTANTS", 3))
BUDGET = int(os.environ.get("PROOFCI_MUTATION_BUDGET", 600))
# The default checks only guarantees whose statement is new or changed in the
# PR; PROOFCI_MUTATION_FULL=1 sweeps every verified guarantee.
FULL = os.environ.get("PROOFCI_MUTATION_FULL", "") not in ("", "0", "false")
MAX_INPUTS = 40

TOP_LEVEL = re.compile(r"^\S")

# Small plausible defects inside a translated function body. Each is (kind,
# pattern, replacement) applied to the first matching line of the `def`.
KINDS = {
    "lt-to-le": (r"\.val < ", ".val ≤ "),
    "le-to-lt": (r"\.val ≤ ", ".val < "),
    "gt-to-ge": (r"\.val > ", ".val ≥ "),
    "ge-to-gt": (r"\.val ≥ ", ".val > "),
    "add-to-sub": (r"\.val \+ ", ".val - "),
    "sub-to-add": (r"\.val - ", ".val + "),
    "eq-to-ne": (r"\.val = ", ".val ≠ "),
    "and-to-or": (r" && ", " || "),
    "or-to-and": (r" \|\| ", " && "),
}


def _def_block(lines, name):
    start = next((i for i, line in enumerate(lines)
                  if re.match(rf"def {re.escape(name)}\b", line)), None)
    if start is None:
        return None
    end = next((i for i in range(start + 1, len(lines)) if TOP_LEVEL.match(lines[i])),
               len(lines))
    return start, end


def plant(text, name, limit=MAX_MUTANTS):
    """Mutate `def name` inside the module text; returns [(kind, line, mutated_line, mutant_text)]."""
    lines = text.splitlines(keepends=True)
    block = _def_block(lines, name)
    if not block:
        return []
    mutants = []
    for kind, (pattern, replacement) in KINDS.items():
        if len(mutants) >= limit:
            break
        for i in range(*block):
            if re.search(pattern, lines[i]):
                mutated = lines[:]
                mutated[i] = re.sub(pattern, replacement, lines[i], count=1)
                mutants.append((kind, i + 1, mutated[i].strip(), "".join(mutated)))
                break
    return mutants


OUT_MARKER = "PROOFCI_MUTANT_OUT "


def _eval_outputs(ws, calls, module_text, timeout):
    """Evaluate each call (`_root_.f arg …`) by interpreting the module text
    itself (an `import` would load the prebuilt olean, mutants included or
    not); returns the repr of each result, or None on failure."""
    path = ws.root / "MutantCheck.lean"
    defs = "\n".join(f"def proofciOut{i} := {call}" for i, call in enumerate(calls))
    evals = "\n".join(f'#eval IO.println s!"{OUT_MARKER}{i} {{repr proofciOut{i}}}"'
                      for i in range(len(calls)))
    path.write_text(f"{module_text}\n\n{defs}\n\n{evals}\n")
    done = lean._lake(ws, ["env", "lean", "MutantCheck.lean"], timeout=timeout)
    try:
        path.unlink()
    except OSError:
        pass
    if done.status != 0:
        return None
    out = {}
    for line in done.output.splitlines():
        if line.startswith(OUT_MARKER):
            i, _, rep = line[len(OUT_MARKER):].partition(" ")
            out[int(i)] = rep
    return out if len(out) == len(calls) else None


ERROR_LINE_ANY = re.compile(r"(Proofs(?:/[\w.-]+)*\.lean):(\d+)")


def _failed_declarations(root, output):
    """Map error locations in the judge's output back to declaration names."""
    files = {}
    for match in ERROR_LINE_ANY.finditer(output):
        files.setdefault(match.group(1), []).append(int(match.group(2)))
    failed = set()
    for name, lines in files.items():
        try:
            text = (root / name).read_text()
        except OSError:
            continue
        file_lines = text.splitlines()
        source = text.splitlines(keepends=True)
        masked = claims._mask(text)
        for start, end, _ in lean._blocks(source):
            if any(start < line <= end for line in lines):  # error lines are 1-based
                m = lean.DECL_NAME.match(file_lines[start])
                if m:
                    pos = sum(len(l) for l in source[:start])
                    failed.add(".".join([*claims._scope_at(masked, pos), m.group(1)]))
    return failed


def check(ws, work, module_text, inputs, names, jobs, candidates, all_outcomes):
    """`inputs`: {function: [arg terms]} from the comparison with Node;
    `names`: {function: lean def name}; `candidates`: the guarantees under
    test; `all_outcomes`: every verified guarantee (a mutant is rejected when
    any guarantee of the function fails it, not only those under test).
    Returns (escaped, planted): escaped maps each theorem that rejected no
    behavioural mutant to the mutant descriptions it let through."""
    pending = {}
    for o in candidates:
        if o.function in pending or not inputs.get(o.function) or o.function not in names:
            continue
        mutants = plant(module_text, names[o.function])
        if mutants:
            pending[o.function] = mutants
    if not pending:
        return {}, 0
    deadline = time.monotonic() + BUDGET

    # Evaluate the original view on every input once; a mutant that produces
    # the same repr on all of them changes no observable behaviour.
    calls = {f: [f"_root_.{names[f]} {' '.join(args)}" for args in inputs[f][:MAX_INPUTS]]
             for f in pending}
    original = _eval_outputs(ws, [c for f in pending for c in calls[f]], module_text,
                             min(120, max(30, int(deadline - time.monotonic()))))
    if original is None:
        return {}, 0

    base, n = {}, 0
    for f in pending:
        base[f], n = n, n + len(calls[f])
    todo = [(i, f, kind, line, src, mutant)
            for i, (f, (kind, line, src, mutant)) in enumerate(
                (f, m) for f in pending for m in pending[f])]

    def one(entry):
        i, f, kind, line, src, mutant = entry
        left = deadline - time.monotonic()
        if left <= 0:
            return None
        copy = lean.clone(ws, work / f"mutant-{i}")
        (copy.root / f"{copy.crate_module}.lean").write_text(mutant)
        offset = base[f]
        out = _eval_outputs(copy, calls[f], mutant, min(120, max(30, int(left))))
        if out is None:
            return ("unknown", f)
        if all(out.get(k) == original.get(offset + k) for k in range(len(calls[f]))):
            return None  # equivalent mutant: changes no observable behaviour
        done = lean._lake(copy, ["build", "Proofs"], timeout=max(30, int(left)))
        failed = set() if done.status == 0 else _failed_declarations(copy.root, done.output)
        # A failure we cannot attribute to a declaration (timeout, sandbox
        # error, error outside Proofs*) is not evidence of escape: don't judge.
        if done.timed_out or (done.status != 0 and not failed):
            return ("unknown", f)
        return ("done", f, kind, line, src, failed)

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = [r for r in pool.map(one, todo) if r]

    # A point-wise guarantee legitimately ignores mutants on paths it never
    # meant to cover, so judge the function's guarantees together: warn each
    # only when no guarantee rejects any behavioural mutant of the function.
    # A failure in a declaration that is no guarantee's theorem (a proof
    # helper, support code) means modules were never built, so the mutant is
    # inconclusive and dropped; a failure attributed only to another
    # guarantee's theorem counts as an escape.
    theorems = {}
    for o in all_outcomes:
        theorems.setdefault(o.function, set()).add(o.theorem)
    known = {o.theorem for o in all_outcomes}
    escaped = {}
    for o in candidates:
        own = theorems.get(o.function, set())
        done = [(kind, line, src, failed) for _, f, kind, line, src, failed in
                (r for r in results if r[0] == "done") if f == o.function]
        # A failure in a declaration that is no guarantee's theorem (a proof
        # helper, support code) means modules were never built: inconclusive.
        # But a theorem of this function failing is a rejection either way.
        conclusive = [t for t in done if not (t[3] - known)]
        rejected = any(failed & own for _, _, _, failed in done)
        if conclusive and not rejected:
            escaped[o.theorem] = [f"{kind} at `{o.function}` line {line}: `{src}`"
                                  for kind, line, src, _ in conclusive]
    return escaped, sum(len(m) for m in pending.values())
