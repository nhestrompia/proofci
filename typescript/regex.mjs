// The regular expressions the model covers (`Js.Re` in ProofciJs.lean): a literal whose flags are at
// most `i` and `g`, built from code units, classes, `.`, `^`, `$`, `*`, `+`, `?`, `|` and groups.
// Anything else is refused with the reason thrown here.

const SPACE = [[9, 13], [32, 32], [160, 160], [5760, 5760], [8192, 8202], [8232, 8233], [8239, 8239], [8287, 8287], [12288, 12288], [65279, 65279]];
const DIGIT = [[48, 57]];
const WORD = [[48, 57], [65, 90], [95, 95], [97, 122]];
const complement = ranges => {
  const out = [];
  let next = 0;
  for (const [a, b] of [...ranges].sort((x, y) => x[0] - y[0])) {
    if (a > next) out.push([next, a - 1]);
    next = Math.max(next, b + 1);
  }
  if (next <= 0xffff) out.push([next, 0xffff]);
  return out;
};
const CLASSES = { d: DIGIT, D: complement(DIGIT), w: WORD, W: complement(WORD), s: SPACE, S: complement(SPACE) };
const CONTROL = { n: 10, t: 9, r: 13, f: 12, v: 11 };
const SYNTAX = "^$\\.*+?()[]{}|/";

const refuse = what => { throw new Error(`the regular expression uses ${what}, which has no model`); };

export function parseRegex(source, flags) {
  for (const f of flags) if (!"ig".includes(f)) refuse(`the flag \`${f}\``);
  let i = 0, groups = 0;
  const peek = () => source[i];
  const unit = () => source.charCodeAt(i++);
  const hex = n => {
    const digits = source.slice(i, i + n);
    if (!new RegExp(`^[0-9a-fA-F]{${n}}$`).test(digits)) refuse("an incomplete hexadecimal escape");
    i += n;
    return parseInt(digits, 16);
  };
  // An escape after `\`: a code unit, or a class as ranges.
  const escape = inClass => {
    const c = source[i++];
    if (c === undefined) refuse("a trailing `\\`");
    if (CLASSES[c]) return { ranges: CLASSES[c] };
    if (c in CONTROL) return { unit: CONTROL[c] };
    if (c === "x") return { unit: hex(2) };
    if (c === "u") return { unit: hex(4) };
    if (c === "0" && !/[0-9]/.test(peek() ?? "")) return { unit: 0 };
    if (c === "b" && inClass) return { unit: 8 };
    if (c === "b" || c === "B") refuse("`\\b` or `\\B`");
    if (/[1-9]/.test(c)) refuse("a backreference");
    if (/[A-Za-z0-9]/.test(c)) refuse(`\`\\${c}\``);
    return { unit: c.charCodeAt(0) };
  };
  const cls = () => {
    const neg = peek() === "^";
    if (neg) i++;
    const ranges = [];
    while (peek() !== "]") {
      if (i >= source.length) refuse("an unclosed class");
      const one = () => (peek() === "\\" ? (i++, escape(true)) : { unit: unit() });
      const a = one();
      if (peek() === "-" && source[i + 1] !== "]" && i + 1 < source.length) {
        i++;
        const b = one();
        if (a.ranges || b.ranges) refuse("a range with a class at one end");
        if (a.unit > b.unit) refuse("a range out of order");
        ranges.push([a.unit, b.unit]);
      } else if (a.ranges) ranges.push(...a.ranges);
      else ranges.push([a.unit, a.unit]);
    }
    i++;
    return { kind: "cls", neg, ranges };
  };
  const atom = () => {
    const c = peek();
    if (c === ".") { i++; return { kind: "dot" }; }
    if (c === "[") { i++; return cls(); }
    if (c === "\\") {
      i++;
      const e = escape(false);
      return e.ranges ? { kind: "cls", neg: false, ranges: e.ranges } : { kind: "chr", unit: e.unit };
    }
    if (c === "(") {
      i++;
      if (peek() === "?") {
        if (source[i + 1] !== ":") refuse(source[i + 1] === "<" && !"=!".includes(source[i + 2]) ? "a named group" : "a lookahead or lookbehind");
        i += 2;
      } else groups++;
      const inner = disjunction();
      if (peek() !== ")") refuse("an unclosed group");
      i++;
      return inner;
    }
    if (SYNTAX.includes(c)) refuse(`\`${c}\` where it is not supported`);
    return { kind: "chr", unit: unit() };
  };
  const term = () => {
    const c = peek();
    if (c === "^") { i++; return { kind: "bol" }; }
    if (c === "$") { i++; return { kind: "eol" }; }
    const a = atom();
    const q = peek();
    if (q === "{") refuse("a counted repeat `{...}`");
    if (!"*+?".includes(q ?? "x")) return a;
    i++;
    if (peek() === "?") refuse("a lazy repeat");
    if ("*+?{".includes(peek() ?? "x")) refuse("a repeat of a repeat");
    return q === "*" ? { kind: "star", a } : q === "+" ? { kind: "seq", a, b: { kind: "star", a } } : { kind: "opt", a };
  };
  const alternative = () => {
    const parts = [];
    while (i < source.length && peek() !== "|" && peek() !== ")") parts.push(term());
    return parts.reduceRight((b, a) => (b ? { kind: "seq", a, b } : a), null) ?? { kind: "eps" };
  };
  const disjunction = () => {
    const a = alternative();
    if (peek() !== "|") return a;
    i++;
    return { kind: "alt", a, b: disjunction() };
  };
  const re = disjunction();
  if (i < source.length) refuse(`\`${peek()}\` where it is not supported`);
  return { re, lean: lean(re), ic: flags.includes("i"), global: flags.includes("g"), groups };
}

const lean = r => {
  switch (r.kind) {
    case "eps": case "dot": case "bol": case "eol": return `Js.Re.${r.kind}`;
    case "chr": return `(Js.Re.chr ${r.unit})`;
    case "cls": return `(Js.Re.cls ${r.neg} [${r.ranges.map(([a, b]) => `(${a}, ${b})`).join(", ")}])`;
    case "star": case "opt": return `(Js.Re.${r.kind} ${lean(r.a)})`;
    default: return `(Js.Re.${r.kind} ${lean(r.a)} ${lean(r.b)})`;
  }
};
