#!/usr/bin/env python3
"""Plants mistranslations in the typed view of functions that have a bridge. Each mutant
keeps the same Core and the same proof, so a sound bridge must fail to check.
usage: mutate.py <dir with F*.lean, F*.res, index.json> <out dir> [per kind]"""
import json, os, re, sys, random
src, out, per = sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 8
only = len(sys.argv) > 4
os.makedirs(out, exist_ok=True)
index = [x for x in json.load(open(f"{src}/index.json")) if x["ok"]]
good = []
for x in index:
    n = f"F{x['i']}"
    r = open(f"{src}/{n}.res").read().split()[0] if os.path.exists(f"{src}/{n}.res") else "1"
    if r == "0" and "sorryAx" not in open(f"{src}/{n}.out").read():
        good.append(n)
def numbump(m):
    return f"Js.Num.mk ({int(m.group(1)) + 1}) (of_decide_eq_true rfl) (of_decide_eq_true rfl)"
KINDS = {
    "lt-le": (r"\.val < ", ".val ≤ "),
    "le-lt": (r"\.val ≤ ", ".val < "),
    "gt-ge": (r"\.val > ", ".val ≥ "),
    "add-sub": (r"\bJs\.add\b", "Js.sub"),
    "sub-add": (r"\bJs\.sub\b", "Js.add"),
    "string": (r'js!"([^"]*)"', r'js!"\1q"'),
    "number": (r"Js\.Num\.mk \((\d+)\) \(of_decide_eq_true rfl\) \(of_decide_eq_true rfl\)", numbump),
    "last-first": (r"\bJs\.strLastIndexOf\b", "Js.strIndexOf"),
    "first-last": (r"\bJs\.strIndexOf\b", "Js.strLastIndexOf"),
    "code-trim": (r"\bJs\.charCodeAt (\S+)", r"Js.charCodeAt (Js.trim \1)"),
    "show-null": (r"\bJs\.showUndef\b", "Js.showNull"),
    "show-undef": (r"\bJs\.showNull\b", "Js.showUndef"),
    "show-trim": (r"(Js\.show(?:Undef|Null)) id\b", r"\1 Js.trim"),
    "bool-negate": (r"\bJs\.boolStr (\S+)\)", r"Js.boolStr (!\1))"),
    "set-no-dedupe": (r"\bJs\.setOf ", "id "),
    "set-has-not": (r"\(Js\.setHas ", "(!Js.setHas "),
    "parse-auto": (r"\bJs\.parseIntStr true\b", "Js.parseIntStr false"),
    "parse-radix": (r"\bJs\.parseIntStr false\b", "Js.parseIntStr true"),
    "trim-start": (r"\bJs\.trim\b", "Js.trimStart"),
    "fixed-str": (r"\bJs\.toFixed (\S+) (\S+)$", r"Js.toFixed \1 (Js.lit 3)"),
    "num-test": (r"Result\.ok true$", "Result.ok false"),
    "set-add-skip": (r"\bJs\.setAdd (\S+) (\S+)\)$", r"\1)"),
    "truthy-str": (r"Js\.truthyStr (\S+) = true", r"Option.isSome \1 = true"),
    "truthy-num": (r"Js\.truthyNum (\S+) = true", r"Option.isSome \1 = true"),
    "truthy-bool": (r"Js\.truthyBool (\S+) = true", r"Option.isSome \1 = true"),
    "none-some": (r"Option\.isNone", "Option.isSome"),
    "some-none": (r"Option\.isSome", "Option.isNone"),
    "and-or": (r" ∧ ", " ∨ "),
    "empty": (r" ≠ \[\]", " = []"),
    "nonzero": (r"\.val ≠ 0", ".val > 0"),
    "opt-eq": (r"decide \((\S+) = some (\S+)\)", r"decide (\1 ≠ some \2)"),
    "negate-if": (r"\bif (.+?) then$", r"if ¬(\1) then"),
    "true-false": (r"Result\.ok true\b", "Result.ok false"),
    "false-true": (r"Result\.ok false\b", "Result.ok true"),
    "starts-ends": (r"\bJs\.startsWith\b", "Js.endsWith"),
    "trim": (r"\bJs\.trim\b", "Js.trimStart"),
    "lower-upper": (r"\bJs\.toLower\b", "Js.toUpper"),
    "append-order": (r"\(js!\"([^\"]*)\"\) \+\+ ", r'(js!"\1 ") ++ '),
    "eq-ne": (r" = true then", " = false then"),
    # Inside loops and callbacks
    "loop-skip": (r"Result\.ok \(\.cont \((\w+), (\w+)\)\)", r"Result.ok (.cont (\1, \2)) >>= fun _ => Result.ok (.done (Sum.inr ()))"),
    "loop-next": (r"\.cont \((\w+)\)\)$", r".cont (\1 ++ \1)))"),
    "done-early": (r"Result\.ok \(\.cont ", "Result.ok (.done "),
    "append-front": (r"(\w+) \+\+ \[(.+)\]\)$", r"[\2] ++ \1)"),
    "filter-not": (r"Result\.ok \(decide \((.*)\)\)$", r"Result.ok (decide (¬(\1)))"),
    
    "guard-rev": (r"\bJs\.unwrapAll (\S+)$", r"Js.unwrapAll (List.reverse \1)"),
    "guard-drop": (r"\bJs\.unwrapAll (\S+)$", r"Js.unwrapAll (List.drop 1 \1)"),
    "narrow-none": (r"\bJs\.unwrap (\S+)$", r"Js.unwrap (Option.filter (fun _ => false) \1)"),
    "some-every": (r"\bJs\.some_\b", "Js.every"),
    "every-some": (r"\bJs\.every\b", "Js.some_"),
    # `%` and rounded division
    "rem-sub": (r"\bJs\.rem\b", "Js.sub"),
    "rem-mul": (r"\bJs\.rem\b", "Js.mul"),
    "floor-trunc": (r"\bJs\.floorDiv\b", "Js.truncDiv"),
    "floor-ceil": (r"\bJs\.floorDiv\b", "Js.ceilDiv"),
    "trunc-floor": (r"\bJs\.truncDiv\b", "Js.floorDiv"),
    "ceil-floor": (r"\bJs\.ceilDiv\b", "Js.floorDiv"),
    "ceil-trunc": (r"\bJs\.ceilDiv\b", "Js.truncDiv"),
    "rem-zero": (r"tmp\d+\.val = 0", "False"),
}
rng = random.Random(20261105)
made = []
for kind, (pat, rep) in KINDS.items():
    names = good[:]
    rng.shuffle(names)
    count = 0
    for n in names:
        if count >= per:
            break
        text = open(f"{src}/{n}.lean").read()
        cut = text.index("set_option maxRecDepth 4000") if "set_option maxRecDepth 4000" in text else None
        head = text.find("def ")
        lines = text[:cut].split("\n")
        body = [i for i, l in enumerate(lines) if re.search(pat, l) and not l.startswith(("structure", "inductive"))]
        if only and not any("Aeneas.Std.loop" in l or re.search(r"\bJs\.(map|filter|some_|every|find)\b", l) for l in lines):
            continue
        if not body:
            continue
        i = rng.choice(body)
        lines[i] = re.sub(pat, rep, lines[i], count=1)
        mutant = "\n".join(lines) + text[cut:]
        if mutant == text:
            continue
        name = f"F{len(made)}"
        open(f"{out}/{name}.lean", "w").write(mutant)
        made.append({"name": name, "kind": kind, "from": n, "line": lines[i].strip()[:110]})
        count += 1
json.dump(made, open(f"{out}/mutants.json", "w"), indent=0)
print(len(good), "bridged functions,", len(made), "mutants")
