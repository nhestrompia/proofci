"""Independent ground truth for the evaluation corpus.

The verifier's restricted language has natural-number literals, `x`, `+`, `*`
and parentheses. Every such expression is a polynomial in `x` with nonnegative
integer coefficients, so two expressions are equal for every `x` exactly when
their normalized coefficients agree. Conditional contracts in this corpus use a
bounded precondition on `x` alone, which this module checks by enumeration.

This module deliberately does not import the verifier's parser. It is the
reference used to label results as false acceptances; it never decides a gate.
"""
import json
import re

TOKEN = re.compile(r"\s*(?:(\d+)|(x)|([+*()]))")
OPERATORS = ("=", "<", "≤")


def _tokens(text):
    position, result = 0, []
    text = text.strip()
    while position < len(text):
        match = TOKEN.match(text, position)
        if not match or match.end() == position:
            raise ValueError(f"unsupported expression {text!r}")
        result.append(match.group(1) or match.group(2) or match.group(3))
        position = match.end()
    return result


def _add(a, b):
    result = dict(a)
    for degree, coefficient in b.items():
        result[degree] = result.get(degree, 0) + coefficient
    return {d: c for d, c in result.items() if c}


def _mul(a, b):
    result = {}
    for da, ca in a.items():
        for db, cb in b.items():
            result[da + db] = result.get(da + db, 0) + ca * cb
    return {d: c for d, c in result.items() if c}


def polynomial(text):
    """Return {degree: coefficient} for a restricted expression."""
    words = _tokens(text)
    position = 0

    def atom():
        nonlocal position
        if position >= len(words):
            raise ValueError("truncated expression")
        word = words[position]
        position += 1
        if word == "(":
            value = term()
            if position >= len(words) or words[position] != ")":
                raise ValueError("unclosed parenthesis")
            position += 1
            return value
        if word == "x":
            return {1: 1}
        if word.isdecimal():
            return {0: int(word)} if int(word) else {}
        raise ValueError(f"unexpected token {word!r}")

    def product():
        nonlocal position
        value = atom()
        while position < len(words) and words[position] == "*":
            position += 1
            value = _mul(value, atom())
        return value

    def term():
        nonlocal position
        value = product()
        while position < len(words) and words[position] == "+":
            position += 1
            value = _add(value, product())
        return value

    value = term()
    if position != len(words):
        raise ValueError(f"unexpected token {words[position]!r}")
    return value


def evaluate(poly, x):
    return sum(c * x ** d for d, c in poly.items())


def candidate_expression(source):
    match = re.fullmatch(r"\s*def target \(x : Nat\) : Nat :=(.*)", source, re.S)
    if not match:
        raise ValueError("candidate is outside the oracle's language")
    return match.group(1).strip()


def precondition_domain(precondition):
    """Return the finite list of x satisfying a corpus precondition."""
    if set(precondition) != {"lhs", "op", "rhs"} or precondition["op"] not in OPERATORS:
        raise ValueError("unsupported precondition")
    if precondition["lhs"].strip() != "x" or not precondition["rhs"].strip().isdecimal():
        raise ValueError("corpus preconditions must compare x with a literal")
    bound = int(precondition["rhs"])
    if precondition["op"] == "=":
        return [bound]
    if precondition["op"] == "<":
        return list(range(bound))
    return list(range(bound + 1))


def judge(candidate_source, contract):
    """Return (holds, smallest counterexample or None) for `target x = rhs`."""
    if isinstance(contract, (str, bytes)):
        contract = json.loads(contract)
    left = polynomial(candidate_expression(candidate_source))
    right = polynomial(contract["rhs"])
    if "precondition" in contract:
        for x in precondition_domain(contract["precondition"]):
            if evaluate(left, x) != evaluate(right, x):
                return False, x
        return True, None
    if left == right:
        return True, None
    degree = max(list(left) + list(right) + [0])
    for x in range(degree + 2):
        if evaluate(left, x) != evaluate(right, x):
            return False, x
    raise AssertionError("distinct polynomials must differ within degree + 1 points")
