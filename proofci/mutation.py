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

MAX_MUTANTS = int(os.environ.get("PROOFCI_MUTANTS", 6))
BUDGET = int(os.environ.get("PROOFCI_MUTATION_BUDGET", 600))
# The default checks only guarantees whose statement is new or changed in the
# PR; PROOFCI_MUTATION_FULL=1 sweeps every verified guarantee.
FULL = os.environ.get("PROOFCI_MUTATION_FULL", "") not in ("", "0", "false")
MAX_INPUTS = 40

TOP_LEVEL = re.compile(r"^\S")

def _num_literal_bump(match):
    return f"{match.group(1)}{int(match.group(2)) + 1}{match.group(3)}"


def _dbl_literal_bump(match):
    return f"{match.group(1)}{int(match.group(2), 16) + 1:x}"


def _f64_op(match):
    return "Core.F64." + {"add": "sub", "sub": "add", "mul": "div", "div": "mul", "rem": "sub",
                         "floor": "ceil", "ceil": "floor", "trunc": "jsround", "jsround": "trunc",
                         "abs": "neg", "neg": "abs"}[match.group(1)]


# Small plausible defects inside a translated function body. Each is (kind,
# pattern, replacement) applied to the first matching line of the `def`; the
# replacement may be a string or a callable taking the match. Patterns come in
# two families: the `.val`-based Aeneas shapes Rust code translates to, and the
# `decide`, `if`, `Js.*` and literal shapes the TypeScript translator emits.
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
    # TypeScript-generated shapes: branch conditions, `decide`, and the
    # unicode operators conditions emit.
    "negate-branch": (r"\bif (.+?) then", lambda m: f"if ¬({m.group(1)}) then"),
    "negate-decide": (r"decide \((.*)\)", r"decide (¬(\1))"),
    "and-to-or-lean": (r" ∧ ", " ∨ "),
    "or-to-and-lean": (r" ∨ ", " ∧ "),
    "eq-to-ne-lean": (r" = ", " ≠ "),
    "ne-to-eq-lean": (r" ≠ ", " = "),
    # Comparisons the `.val` patterns above miss (Int, Dbl via `.f`, locals).
    "lt-to-le-lean": (r"(?<!\.val) < ", " ≤ "),
    "le-to-lt-lean": (r"(?<!\.val) ≤ ", " < "),
    "gt-to-ge-lean": (r"(?<!\.val) > ", " ≥ "),
    "ge-to-gt-lean": (r"(?<!\.val) ≥ ", " > "),
    # Option results: drop a produced `some` value.
    "some-to-none": (r"\(some [^()]*\)", "(none)"),
    # Boolean results.
    "true-to-false": (r"Result\.ok true", "Result.ok false"),
    "false-to-true": (r"Result\.ok false", "Result.ok true"),
    # Literals: an off-by-one in a baked-in constant.
    "num-literal": (r"(Js\.lit \()(-?\d+)(\))", _num_literal_bump),
    "int-literal": (r"\((-?\d+)( : Int\))", lambda m: f"({int(m.group(1)) + 1}{m.group(2)})"),
    "dbl-literal": (r"(Js\.Dbl\.lit 0x)([0-9a-fA-F]+)", _dbl_literal_bump),
    # The `Js.*` operations a translated body binds.
    "js-add-to-sub": (r"\bJs\.add\b", "Js.sub"),
    "js-sub-to-add": (r"\bJs\.sub\b", "Js.add"),
    "js-mul-to-div": (r"\bJs\.mul\b", "Js.div"),
    "js-rem-to-sub": (r"\bJs\.rem\b", "Js.sub"),
    "js-min-to-max": (r"\bJs\.min\b", "Js.max"),
    "js-max-to-min": (r"\bJs\.max\b", "Js.min"),
    "bdiv-to-brem": (r"\bJs\.bdiv\b", "Js.brem"),
    "brem-to-bdiv": (r"\bJs\.brem\b", "Js.bdiv"),
    "dbl-add-to-sub": (r"\bJs\.Dbl\.add\b", "Js.Dbl.sub"),
    "dbl-sub-to-add": (r"\bJs\.Dbl\.sub\b", "Js.Dbl.add"),
    "dbl-mul-to-div": (r"\bJs\.Dbl\.mul\b", "Js.Dbl.div"),
    "dbl-div-to-mul": (r"\bJs\.Dbl\.div\b", "Js.Dbl.mul"),
    "dbl-rem-to-sub": (r"\bJs\.Dbl\.rem\b", "Js.Dbl.sub"),
    "dbl-min-to-max": (r"\bJs\.Dbl\.min\b", "Js.Dbl.max"),
    "dbl-max-to-min": (r"\bJs\.Dbl\.max\b", "Js.Dbl.min"),
    "f64-op": (r"Core\.F64\.(add|sub|mul|div|rem|floor|ceil|trunc|jsround|abs|neg)\b", _f64_op),
}


def _def_block(lines, name):
    start = next((i for i, line in enumerate(lines)
                  if re.match(rf"def {re.escape(name)}\b", line)), None)
    if start is None:
        return None
    end = next((i for i in range(start + 1, len(lines)) if TOP_LEVEL.match(lines[i])),
               len(lines))
    return start, end


def _binders(header):
    """(name, type) for each `(name : type)` binder of the def header."""
    binders, i = [], 0
    while True:
        open_ = header.find("(", i)
        if open_ < 0:
            return binders
        depth, j = 0, open_
        while j < len(header):
            if header[j] == "(":
                depth += 1
            elif header[j] == ")":
                depth -= 1
                if not depth:
                    break
            j += 1
        inner = header[open_ + 1:j]
        if " : " in inner:
            name, type_ = inner.split(" : ", 1)
            if re.fullmatch(r"\w+", name):
                binders.append((name, type_.strip()))
        i = j + 1


def _unparen(text):
    """Strip redundant outer parentheses so `List α` and `(List α)` compare equal."""
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth, balanced = 0, True
        for k, c in enumerate(text):
            depth += c == "("
            depth -= c == ")"
            if not depth and k != len(text) - 1:
                balanced = False
                break
        if not balanced or depth:
            return text
        text = text[1:-1].strip()
    return text


def _trivial_constants(result):
    """Wrong-but-type-checking constants of a result type."""
    if result == "Bool":
        return ["true", "false"]
    if result.startswith("Option"):
        return ["none"]
    if result.startswith("List"):
        return ["[]"]
    if result == "Js.Num":
        return ["(Js.lit (0))"]
    if result == "Js.Dbl":
        return ["(Js.Dbl.lit 0x0)"]
    if result == "Int":
        return ["(0 : Int)"]
    if result == "Js.Str":
        return ["([] : Js.Str)"]
    if result == "String":
        return ['""']
    return []


def _trivial_mutants(lines, block):
    """Trivial wrong implementations of the whole `def`, derived from its Lean
    signature: return a same-typed argument unchanged, a constant of the result
    type, or always fail. A guarantee that still holds for one constrains
    little of the function's behaviour."""
    header = lines[block[0]]
    result = re.search(r": (Result|(?:Proofci\.Effects\.)?Eff) (.+?) := do\s*$", header)
    if not result:
        return []
    monad, result_type = result.group(1), _unparen(result.group(2))
    ok = "Result.ok" if monad == "Result" else f"{monad}.pure"
    body = []
    for name, type_ in _binders(header):
        if _unparen(type_) == result_type:
            body.append(("trivial-arg", f"{ok} {name}", name))
    body += [("trivial-constant", f"{ok} {expr}", expr)
             for expr in _trivial_constants(result_type)]
    if monad == "Result":
        body.append(("trivial-fail", "Result.fail .undef", "Result.fail .undef"))
    indent = "  "
    return [(kind, block[0] + 2, src,
             "".join(lines[:block[0] + 1] + [f"{indent}{term}\n"] + lines[block[1]:]))
            for kind, term, src in body]


def _filter_mutants(lines, block):
    """A `.filter` that drops nothing: the call the translator emits spans
    `let x ← Js.filter (fun … => do` … `  ) xs`; returning `xs` keeps every
    element. Returns one mutant per multi-line call, or none."""
    mutants = []
    start = next((i for i in range(*block) if "← Js.filter " in lines[i]), None)
    if start is None or re.search(r"← Js\.filter \S+ \S+\s*$", lines[start]):
        return []  # a single-line call (bound name) has no span to rewrite
    end = next((i for i in range(start + 1, block[1]) if re.match(r"\s*\) \S+\s*$", lines[i])), None)
    if end is None:
        return []
    bound = re.search(r"let (\S+) ←", lines[start])
    if not bound:
        return []
    keep = lines[end].strip()[2:]
    indent = lines[start][:len(lines[start]) - len(lines[start].lstrip())]
    name = bound.group(1)
    mutated = lines[:start] + [f"{indent}let {name} ← Result.ok {keep}\n"] + lines[end + 1:]
    mutants.append(("filter-keeps-all", end + 1, f"let {name} ← Result.ok {keep}", "".join(mutated)))
    return mutants


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
            if lines[i].lstrip().startswith("--"):
                continue  # `-- src:` source-map comments, not code
            if re.search(pattern, lines[i]):
                mutated = lines[:]
                mutated[i] = re.sub(pattern, replacement, lines[i], count=1)
                mutants.append((kind, i + 1, mutated[i].strip(), "".join(mutated)))
                break
    # Several kinds can produce the same text (e.g. `.val < ` and ` < ` on the
    # same spot); keep one of each. Compare without the `-- src:` comments:
    # a mutant that only removes one of them is the original implementation,
    # not a defect.
    seen, unique = {_unmarked(text)}, []
    for mutant in mutants:
        if _unmarked(mutant[3]) not in seen:
            seen.add(_unmarked(mutant[3]))
            unique.append(mutant)
    # Whole-result, call-span and trivial-implementation mutants don't fit a
    # one-line substitution; they get their own slots so the line-mutation
    # limit can't crowd them out.
    for extra in _filter_mutants(lines, block) + _trivial_mutants(lines, block):
        if _unmarked(extra[3]) not in seen:
            seen.add(_unmarked(extra[3]))
            unique.append(extra)
    return unique


TS_OP = {"add": "`+`", "sub": "`-`", "mul": "`*`", "div": "`/`", "rem": "`%`",
         "min": "`Math.min`", "max": "`Math.max`"}

SRC_MARK = re.compile(r"^\s*-- src:(\S+):(\d+)")


def _unmarked(text):
    """Module text minus the `-- src:` source-map comments. Two texts that
    differ only in those comments are the same implementation."""
    return "".join(l for l in text.splitlines(keepends=True) if not SRC_MARK.match(l))


def source_map(module_text):
    """Lean line -> `tsfile:line`, from the `-- src:` markers the translator
    emits before each def and each statement. A mutation on generated line N
    maps to the nearest marker at or above N."""
    marks = {}
    for i, text in enumerate(module_text.splitlines()):
        m = SRC_MARK.match(text)
        if m:
            marks[i + 1] = f"{m.group(1)}:{m.group(2)}"
    return marks


def ts_at(marks, line):
    """The TS `file:line` a generated line maps back to, or None."""
    nearest = max((mark for mark in marks if mark <= line), default=0)
    return marks.get(nearest) if nearest else None


def _ts_literal(line):
    """The TypeScript literal a Lean expression in `line` stands for."""
    for pattern, render in (
            (r"Js\.lit \((-?\d+)\)", lambda m: m.group(1)),
            (r"\((-?\d+) : Int\)", lambda m: f"{m.group(1)}n"),
            (r"Js\.Dbl\.lit 0x([0-9a-fA-F]+)", lambda m: str(int(m.group(1), 16))),
            (r"\[\] : Js\.Str", lambda m: '""')):
        found = re.search(pattern, line)
        if found:
            return render(found)
    return None


def _ts_value(expr, sig=None):
    """A planted return value as the TypeScript the reviewer reads. `sig` is
    the function's signature entry — its `result.nothing` says whether `none`
    means `null` or `undefined`. None when the value can't be named."""
    expr = re.sub(r"^(?:Result\.ok|(?:Proofci\.Effects\.)?Eff\.pure)\s+", "", expr.strip()).strip()
    if expr == "none":
        nothing = ((sig or {}).get("result") or {}).get("nothing")
        return nothing if nothing in ("null", "undefined") else None
    if expr in ("true", "false", '""', "[]"):
        return expr
    if re.fullmatch(r"[A-Za-z_$][\w$]*", expr):
        return expr
    return _ts_literal(expr)


def _loc(ts):
    """`src/ledger.ts:16` -> `src/ledger.ts line 16`, the report's phrasing."""
    if not ts:
        return ""
    file, _, n = ts.rpartition(":")
    return f"{file} line {n}"


# Mutation kinds phrased as the TypeScript operators they swap: kind ->
# (what the mutant uses, what the code uses).
_SWAPPED = {
    "lt-to-le": ("<=", "<"), "le-to-lt": ("<", "<="),
    "gt-to-ge": (">=", ">"), "ge-to-gt": (">", ">="),
    "lt-to-le-lean": ("<=", "<"), "le-to-lt-lean": ("<", "<="),
    "gt-to-ge-lean": (">=", ">"), "ge-to-gt-lean": (">", ">="),
    "add-to-sub": ("-", "+"), "sub-to-add": ("+", "-"),
    "eq-to-ne": ("!==", "==="), "eq-to-ne-lean": ("!==", "==="),
    "ne-to-eq-lean": ("===", "!=="),
    "and-to-or": ("||", "&&"), "and-to-or-lean": ("||", "&&"),
    "or-to-and": ("&&", "||"), "or-to-and-lean": ("&&", "||"),
}


def describe(kind, line, src, original, ts=None, sig=None):
    """One plain fragment completing `if <function> ...`, in the TypeScript
    the reviewer reads — never generated Lean. `src` is the mutated line,
    `original` the line it replaced on generated line `line`; `ts` is the
    TypeScript `file:line` that generated line maps back to and `sig` the
    function's declared signature for telling `null` and `undefined` apart."""
    loc = _loc(ts)
    on = f" on {loc}" if loc else ""
    at = f" ({loc})" if loc else ""
    if kind == "trivial-arg":
        arg = src.removeprefix("Result.ok ").strip()
        return f"returned `{arg}` unchanged"
    if kind == "trivial-constant":
        value = _ts_value(src, sig)
        if value is None:
            return "always returned no value (`null`/`undefined`)"
        return f"always returned `{value}`"
    if kind == "trivial-fail":
        return "always threw"
    if kind == "filter-keeps-all":
        kept = src.rsplit(" ", 1)[-1]
        return f"returned `{kept}` without filtering it"
    if kind == "negate-branch":
        return f"the `if`{on} were negated" if on else "the condition were negated"
    if kind == "negate-decide":
        return f"the condition{on} were negated" if on else "the condition were negated"
    if kind in ("true-to-false", "false-to-true"):
        new, old = ("false", "true") if kind == "true-to-false" else ("true", "false")
        return f"returned `{new}`{at} where the code returns `{old}`"
    if kind in _SWAPPED:
        new, old = _SWAPPED[kind]
        return f"used `{new}`{at} where the code uses `{old}`"
    if "-to-" in kind and kind.startswith(("js-", "dbl-", "bdiv-", "brem-")):
        pair = kind.split("-to-")
        if pair[0] in ("bdiv", "brem"):
            return (f"used `{'%' if pair[0] == 'bdiv' else '/'}`{at} on the bigint "
                    f"where the code uses `{'/' if pair[0] == 'bdiv' else '%'}`")
        op_from = pair[0].removeprefix("js-").removeprefix("dbl-")
        return (f"used {TS_OP.get(pair[1], pair[1])}{at} where the code uses "
                f"{TS_OP.get(op_from, op_from)}")
    if kind == "f64-op":
        new = re.search(r"Core\.F64\.(\w+)", src)
        old = re.search(r"Core\.F64\.(\w+)", original)
        if new and old:
            return f"used `Math.{new.group(1)}`{at} where the code uses `Math.{old.group(1)}`"
    elif kind in ("num-literal", "int-literal", "dbl-literal"):
        old_v, new_v = _ts_literal(original), _ts_literal(src)
        if old_v and new_v:
            return f"`{old_v}`{on} were `{new_v}`" if on else f"a literal `{old_v}` were `{new_v}`"
        return f"a literal{on} were off by one" if on else "a literal were off by one"
    elif kind == "some-to-none":
        value = _ts_value("none", sig)
        return (f"returned `{value}` instead of a value" if value
                else "returned no value (`null`/`undefined`)")
    return (f"a small change to the code{on} still passes" if on
            else "a small change to the code still passes")


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


# Lake prints `error: Proofs.lean:L:C: msg`; plain lean `Proofs.lean:L:C: error: msg`.
# `warning:`-level diagnostics are not build failures and must not be attributed.
ERROR_LINE_ANY = re.compile(r"(?:error: (Proofs(?:/[\w.-]+)*\.lean):(\d+):|(Proofs(?:/[\w.-]+)*\.lean):(\d+):(\d+): error)")


def _failed_declarations(root, output):
    """Map error locations in the judge's output back to declaration names."""
    files = {}
    for match in ERROR_LINE_ANY.finditer(output):
        files.setdefault(match.group(1) or match.group(3), []).append(int(match.group(2) or match.group(4)))
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


def check(ws, work, module_text, inputs, names, jobs, candidates, all_outcomes, sigs=None):
    """`inputs`: {function: [arg terms]} from the comparison with Node;
    `names`: {function: lean def name}; `candidates`: the guarantees under
    test; `all_outcomes`: every verified guarantee (a mutant is rejected when
    any guarantee of the function fails it, not only those under test).
    Returns (escaped, planted): escaped maps each theorem that rejected no
    behavioural mutant to the mutant descriptions it let through; planted maps
    each candidate function to how many mutants were planted in it."""
    pending = {}
    for o in candidates:
        if o.function in pending or not inputs.get(o.function) or o.function not in names:
            continue
        mutants = plant(module_text, names[o.function])
        if mutants:
            pending[o.function] = mutants
    if not pending:
        return {}, {}
    deadline = time.monotonic() + BUDGET

    # Evaluate the original view on every input once; a mutant that produces
    # the same repr on all of them changes no observable behaviour.
    calls = {f: [f"_root_.{names[f]} {' '.join(args)}" for args in inputs[f][:MAX_INPUTS]]
             for f in pending}
    original = _eval_outputs(ws, [c for f in pending for c in calls[f]], module_text,
                             min(120, max(30, int(deadline - time.monotonic()))))
    if original is None:
        return {}, {}

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
        # A behavioural mutant that changes no sampled output is skipped; a
        # trivial implementation is judged anyway — its still verifying is
        # itself the evidence the guarantee constrains little.
        if (all(out.get(k) == original.get(offset + k) for k in range(len(calls[f])))
                and not kind.startswith("trivial-")):
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

    # A mutant escapes a guarantee only when the mutant's proof build came out
    # clean: any failure — this function's theorems rejecting it, another
    # guarantee's theorem erroring, or support code — means the mutant did not
    # plainly verify, so it is no evidence of weakness. Per mutant, so one
    # rejected mutant never hides a sibling that slipped through.
    escaped = {}
    for o in candidates:
        conclusive = [(kind, line, src) for _, f, kind, line, src, failed in
                      (r for r in results if r[0] == "done")
                      if f == o.function and not failed]
        if conclusive:
            lines = module_text.splitlines()
            marks = source_map(module_text)
            escaped[o.theorem] = [
                {"kind": kind, "line": line, "src": src,
                 "ts": ts_at(marks, line),
                 "desc": (f"{kind} at `{o.function}`"
                          + (f" on {ts_at(marks, line)}" if ts_at(marks, line) else "")
                          + f": `{src}`"),
                 "plain": describe(kind, line, src,
                                   lines[line - 1].strip() if line <= len(lines) else src,
                                   ts=ts_at(marks, line),
                                   sig=(sigs or {}).get(o.function))}
                for kind, line, src in conclusive]
    return escaped, {f: len(m) for f, m in pending.items()}
