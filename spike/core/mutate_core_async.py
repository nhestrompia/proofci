#!/usr/bin/env python3
"""Plants wrong lowerings in the Core of async fixtures (asynccore.sh) and checks that the comparison
with Node rejects each one: some case must disagree, or the file must not compile.
usage: mutate_core_async.py <dir with Core.lean from asynccore.sh> <out dir>"""
import json, os, re, sys
src, out = sys.argv[1], sys.argv[2]
text = open(f"{src}/Core.lean").read()
first = text.index("\n#eval")
head, evals = text[:first], text[first:]
start = head.index("def async_")
body = head[start:]

def matching(s, i):
    """Index just past the bracket or paren that opens at s[i]."""
    pairs = {"(": ")", "[": "]"}
    stack, j, instr = [pairs[s[i]]], i + 1, False
    while stack:
        c = s[j]
        if instr:
            if c == '"': instr = False
        elif c == '"': instr = True
        elif c in pairs: stack.append(pairs[c])
        elif c == stack[-1]: stack.pop()
        j += 1
    return j

mutants = []
def add(kind, at, new):
    if new != body:
        mutants.append((kind, at, head[:start] + new))

# literal results and tests
for m in re.finditer(r"\.ret \(\.lit \(\.bool (true|false)\)\)", body):
    add("ret-flip", m.start(), body[:m.start()] + (".ret (.lit (.bool %s))" % ("false" if m.group(1) == "true" else "true")) + body[m.end():])
# a test negated
for m in re.finditer(r"\.ite \(", body):
    j = matching(body, m.end() - 1)
    add("negate-test", m.start(), body[:m.end()] + ".not (" + body[m.end():j - 1] + "))" + body[j:])
# two awaits swapped
for m in re.finditer(r"(\.await [^\n]*?\]),\n(\s+)(\.await [^\n]*?\]),", body):
    add("swap-awaits", m.start(), body[:m.start()] + m.group(3) + ",\n" + m.group(2) + m.group(1) + "," + body[m.end():])
# an await dropped
for m in re.finditer(r"\.await \"[^\"]*\" \"\w+\" \[[^\n]*?\],\n", body):
    add("drop-await", m.start(), body[:m.start()] + body[m.end():])
# the else side of a test emptied / the then side emptied
for m in re.finditer(r"\.ite \(", body):
    j = matching(body, m.end() - 1)
    k = body.index("[", j)
    e = matching(body, k)
    add("empty-then", m.start(), body[:k] + "[]" + body[e:])
# a try that is not caught, a finally dropped
for m in re.finditer(r"\.tryCatch (\[)", body):
    k = m.end(1) - 1
    e = matching(body, k)
    h = body.index("[", e)
    he = matching(body, h)
    add("catch-dropped", m.start(), body[:m.start()] + body[k + 1:e - 1] + body[he:])
for m in re.finditer(r"\.tryFinally (\[)", body):
    k = m.end(1) - 1
    e = matching(body, k)
    f = body.index("[", e)
    fe = matching(body, f)
    add("finally-dropped", m.start(), body[:m.start()] + body[k + 1:e - 1] + body[fe:])
# a rejection payload changed
for m in re.finditer(r'\("message", ', body):
    j = matching(body, m.start())
    add("message-changed", m.start(), body[:m.end()] + ".bin .add (" + body[m.end():j - 1] + ") (.lit (.str [33]))" + body[j - 1:])
# loops
for m in re.finditer(r"\.bin \.lt \(\.var \"(\w+)\"\) \(\.var \"(\w+)\"\)", body):
    add("loop-bound", m.start(), body[:m.start()] + ".bin .le (.var \"%s\") (.var \"%s\")" % (m.group(1), m.group(2)) + body[m.end():])
for m in re.finditer(r"\.bin \.add \(\.var \"(\w+)\"\) \(\.lit \(\.num \(F64\.ofInt \(1\)\)\)\)", body):
    add("counter", m.start(), body[:m.start()] + ".bin .add (.var \"%s\") (.lit (.num (F64.ofInt (2))))" % m.group(1) + body[m.end():])
# an effect called with another argument
for m in re.finditer(r"(\.await \"[^\"]*\" \"\w+\" \[)(\.[^\]]*?)(\])", body):
    if ".var" in m.group(2):
        add("effect-arg", m.start(), body[:m.start(2)] + ".lit (.str [120])" + body[m.end(2):])

os.makedirs(out, exist_ok=True)
index = []
for i, (kind, at, mutated) in enumerate(mutants):
    open(f"{out}/M{i}.lean", "w").write(mutated + evals)
    index.append({"i": i, "kind": kind, "line": mutated[:start + at].count("\n") + 1})
json.dump(index, open(f"{out}/index.json", "w"))
import collections
print(f"{len(mutants)} mutants", dict(collections.Counter(x["kind"] for x in index)))
