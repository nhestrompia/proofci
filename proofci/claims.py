"""The human-facing claims of a contract.

Every guarantee names a theorem in `<lean>/Contract.lean`. The `/-- ... -/`
doc comment directly above it is the claim the report shows to the human
reading the result: what the guarantee says in plain words. This module reads
the contract as text -- it never evaluates it -- and is trusted the same way:
the contract comes from the protected policy checkout, not the candidate.
"""

import re

# The doc body cannot contain a `-/` of its own: without that guard a block comment
# sitting between the docstring and the theorem would merge both into a fake claim.
DOC_THEOREM = re.compile(
    r"/--(?P<doc>(?:(?!-/).)*)-/\s*(?:@\[.*?\]\s*)*(?:private |protected |noncomputable |partial )*"
    r"theorem\s+(?P<name>[^\s(:{\[]+)", re.S)
# `namespace A.B` opens a scope until `end A.B` (or the file ends); the manifest
# names theorems qualified (`A.B.fee_capped`), so claims are keyed the same way.
SCOPE = re.compile(r"^(namespace|end)\s+([\w.]+)", re.M)
THEOREM = re.compile(
    r"(?<![\w'.])(?:private |protected |noncomputable |partial )*theorem\s+(?P<name>[^\s(:{\[]+)")
BINDER = re.compile(r"\((\w[\w' ]*?)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)")
# Binder types that say something rather than name something: a condition the
# guarantee only holds under. `=` must not start `=>` (a `⦃ _ => ... ⦄` arrow).
PROP = re.compile(r"[≤≥<>≠∈∉∀∃↔¬∧∨]|(?<![\w.])=(?!=)|\bProp\b")


def _open(signature):
    """The signature up to the top-level `:` that starts the result type."""
    depth = 0
    for i, char in enumerate(signature):
        if char in "([{⟨⦃":
            depth += 1
        elif char in ")]}⟩⦄":
            depth -= 1
        elif char == ":" and depth == 0:
            return signature[:i]
    return signature


def _hypotheses(signature):
    """`(name : condition)` binders whose condition is a proposition."""
    found = []
    for names, condition in BINDER.findall(_open(signature)):
        if PROP.search(condition):
            found.append(" ".join(f"{names} : {' '.join(condition.split())}".split()))
    return found


def _scope_at(text, pos):
    """Namespace stack open at `pos` (e.g. ['A', 'B'] inside `namespace A`/`namespace B`)."""
    stack = []
    for m in SCOPE.finditer(text, 0, pos):
        if m.group(1) == "end":
            if m.group(2) in stack:
                stack.remove(m.group(2))
            elif stack:
                stack.pop()
        else:
            stack.append(m.group(2))
    return stack


def theorems(text):
    """{qualified name: {"claim", "statement", "hypotheses"}} for each theorem in a contract."""
    docs = {}
    for m in DOC_THEOREM.finditer(text):
        qualified = ".".join([*_scope_at(text, m.start()), m.group("name")])
        docs[qualified] = " ".join(m.group("doc").split()) or None
    found = {}
    for m in THEOREM.finditer(text):
        name = ".".join([*_scope_at(text, m.start()), m.group("name")])
        end = text.find(":=", m.end())
        statement = text[m.start():end if end != -1 else len(text)].rstrip().rstrip(":").strip()
        signature = text[m.end():end if end != -1 else len(text)]
        found[name] = {
            "claim": docs.get(name),
            "statement": " ".join(statement.split()),
            "hypotheses": _hypotheses(signature),
        }
    return found
