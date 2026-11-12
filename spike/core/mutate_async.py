#!/usr/bin/env python3
"""Plants mistranslations in the Lean view of async functions and checks that the comparison
with Node (asynccheck.sh) rejects each one: a case must disagree, or the file must not compile.
usage: mutate_async.py <dir with Check.lean from asynccheck.sh> <out dir>
Mutants are written to <out>/M<i>.lean, run by `run`, and judged by `judge`."""
import json, os, re, sys
src, out = sys.argv[1], sys.argv[2]
mode = sys.argv[3] if len(sys.argv) > 3 else "make"
text = open(f"{src}/Check.lean").read()
head, replay = text.split("\n#eval", 1)[0], "#eval" + text.split("\n#eval", 1)[1]
# only function bodies, from the first `def <file>.<function>` that is not the world
start = head.index("\ndef async.")

def swap_calls(m):
    return f"{m.group(2)}\n{m.group(1)}"

def flip(m):
    return m.group(1) + ("Result.ok true" if m.group(2) == "false" else "Result.ok false")

def second_arm_as_first(m):
    return f"{m.group(1)}{m.group(4)}{m.group(5)}{m.group(6)}"

KINDS = {
    # control flow
    "true-false": (r"Result\.ok true\b", "Result.ok false"),
    "false-true": (r"Result\.ok false\b", "Result.ok true"),
    "negate-if": (r"\bif (.+?) then$", r"if ¬(\1) then"),
    "drop-await-branch": (r"(\| none =>\n)(\s+)([^\n]*)\n(\s+\| some \w+ =>\n)(\s+)[^\n]*\n", lambda m: f"{m.group(1)}{m.group(2)}{m.group(3)}\n{m.group(4)}{m.group(5)}{m.group(3)}\n"),
    "drop-throw": (r"Js\.Eff\.throw \(.*\)$", "Result.ok ()"),
    "throw-message": (r'message := \(js!"([^"]*)"\)', r'message := (js!"\1!")'),
    "throw-name": (r'«name» := \(js!"Error"\)', '«name» := (js!"TypeError")'),
    "rethrow-swallowed": (r"Js\.Eff\.throw e$", "Result.ok ()"),
    # effects
    "swap-effects": (r"( +let tmp\d+ ← Proofci\.Effects\.call [^\n]*)\n( +let tmp\d+ ← Proofci\.Effects\.call [^\n]*)", swap_calls),
    "drop-effect": (r"  +let tmp\d+ ← Proofci\.Effects\.call [^\n]*\n", ""),
    # try / catch / finally
    "catch-skipped": (r"Js\.Eff\.tryCatch", "Js.Eff.tryFinally"),
    "catch-result": (r"(\(fun e => do\n\s+)Result\.ok (false|true)", flip),
    "message-dropped": (r"\(\(js!\"failed: \"\) \+\+ e\.message\)", r'((js!"failed: ") ++ [])'),
    "instanceof-false": (r"if True then", "if False then"),
    # loops
    "loop-continue": (r"Result\.ok \(\.cont (\w+)\)", r"Result.ok (.done (.inr \1))"),
    "loop-bound": (r"(\w+)\.val < (\w+)\.val", r"\1.val ≤ \2.val"),
    "counter": (r"Js\.add (\w+) \(Js\.Num\.mk \(1\)", r"Js.add \1 (Js.Num.mk (2)"),
    "await-result": (r"Result\.ok \(\.inl \(some (\w+)\.owner\)\)", r"Result.ok (.inl none)"),
    "truthy": (r"Js\.truthyStr (\S+) = true", r"Option.isSome \1 = true"),
}
mutants = []
body = head[start:]
for kind, (pattern, repl) in KINDS.items():
    if repl is None:
        continue
    for m in re.finditer(pattern, body, re.M):
        new = body[:m.start()] + m.expand(repl) if isinstance(repl, str) else body[:m.start()] + repl(m)
        new += body[m.end():]
        if new == body:
            continue
        mutants.append((kind, m.start(), head[:start] + new))
os.makedirs(out, exist_ok=True)
index = []
for i, (kind, at, mutated) in enumerate(mutants):
    open(f"{out}/M{i}.lean", "w").write(mutated + "\n" + replay)
    index.append({"i": i, "kind": kind, "at": at, "line": mutated[:start + at].count("\n") + 1})
json.dump(index, open(f"{out}/index.json", "w"))
print(f"{len(mutants)} mutants")
