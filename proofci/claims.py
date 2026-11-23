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
# `namespace`/`section` open a scope until `end` (or the file ends); the manifest
# names theorems qualified (`A.B.fee_capped`), so claims are keyed the same way.
SCOPE = re.compile(r"^(namespace|section|end)\b(?:\s+([\w.]+))?", re.M)
THEOREM = re.compile(
    r"(?<![\w'.])(?:private |protected |noncomputable |partial )*theorem\s+(?P<name>[^\s(:{\[]+)")
# Binder types that say something rather than name something: a condition the
# guarantee only holds under. `=` must not start `=>` (a `⦃ _ => ... ⦄` arrow).
PROP = re.compile(r"[≤≥<>≠∈∉∀∃↔¬∧∨]|(?<![\w.])=(?!=)|\bProp\b")
# Block/line comments, string literals (raw `r#"..."#` too) and character literals, in one pass so the
# leftmost match wins: a `"` inside a comment never starts a string and a `--`
# inside a string never starts a comment. Character literals hold exactly one
# character or escape, so an identifier prime (`h'`) is never eaten.
LITERAL = re.compile(r"""/-.*?-/|--[^\n]*|(?<![\w'.])r(#*)".*?"\1|"(?:[^"\\]|\\.)*"|'(?:\\.|[^'\\])'""", re.S)


def _blank(match):
    return re.sub(r"[^\n]", " ", match.group(0))


def _syntax(text):
    """Comments and literals replaced by spaces, keeping length, so their
    brackets and colons are never read as Lean syntax by the depth scans."""
    return LITERAL.sub(_blank, text)


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


def _binder(inner):
    """`(names, condition)` for a binder's contents, split at its top-level `:`."""
    depth = 0
    for i, char in enumerate(_syntax(inner)):
        if char in "([{⟨⦃":
            depth += 1
        elif char in ")]}⟩⦄":
            depth -= 1
        elif char == ":" and depth == 0:
            return inner[:i].strip(), " ".join(inner[i + 1:].split())
    return inner.strip(), None


def _hypotheses(signature):
    """`(name : condition)` binders whose condition is a proposition."""
    found = []
    clean = _open(_syntax(signature))
    raw = signature[:len(clean)]
    depth, start, paren = 0, None, False
    for i, char in enumerate(clean):
        if char in "([{⟨⦃":
            depth += 1
            if depth == 1:
                start, paren = i + 1, char == "("
        elif char in ")]}⟩⦄" and depth > 0:
            depth -= 1
            if depth == 0:
                if paren:
                    names, condition = _binder(raw[start:i])
                    if condition is not None and PROP.search(condition):
                        found.append(" ".join(f"{names} : {condition}".split()))
                paren = False
    return found


def _uncommented(text):
    """Comments replaced by spaces, literals kept: the text a statement is read from."""
    return LITERAL.sub(lambda m: _blank(m) if m.group(0)[0] in "/-" else m.group(0), text)


def _mask(text):
    """Comments replaced by spaces, keeping length and newlines, so positions stay
    valid and keywords inside comments (a `namespace` line in a `/- -/` block, or
    a commented-out theorem) are ignored by the scans that run on the result."""
    return _syntax(text)


def _scope_at(masked, pos):
    """Namespaces open at `pos`. Sections are tracked too (so `end` closes them)
    but they don't qualify declaration names."""
    stack = []  # "ns:Name" | "sec:Name"
    for m in SCOPE.finditer(masked, 0, pos):
        kind, name = m.group(1), m.group(2) or ""
        if kind == "end":
            if stack and (not name or stack[-1].split(":", 1)[1] == name):
                stack.pop()
            else:
                deeper = next((e for e in reversed(stack) if e.split(":", 1)[1] == name), None)
                if deeper is not None:
                    stack.remove(deeper)
        else:
            stack.append(("ns" if kind == "namespace" else "sec") + ":" + name)
    return [e.split(":", 1)[1] for e in stack if e.startswith("ns:")]


def theorems(text):
    """{qualified name: {"claim", "statement", "hypotheses"}} for each theorem in a contract."""
    masked, plain = _mask(text), _uncommented(text)
    docs = {}
    for m in DOC_THEOREM.finditer(text):
        qualified = ".".join([*_scope_at(masked, m.start()), m.group("name")])
        docs[qualified] = " ".join(m.group("doc").split()) or None
    found = {}
    for m in THEOREM.finditer(masked):
        name = ".".join([*_scope_at(masked, m.start()), m.group("name")])
        end = masked.find(":=", m.end())
        statement = plain[m.start():end if end != -1 else len(text)].rstrip().rstrip(":").strip()
        signature = plain[m.end():end if end != -1 else len(text)]
        found[name] = {
            "claim": docs.get(name),
            "statement": " ".join(statement.split()),
            "hypotheses": _hypotheses(signature),
        }
    return found
