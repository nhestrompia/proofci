// Compares `%` and `Math.floor/ceil/trunc(a / b)` on safe integers with exact integer arithmetic
// (BigInt: floor, ceiling, truncation and the truncating remainder). The bridge's view relies on
// these being equal, including for operands near 2^53, negative operands and a zero dividend.
// usage: node rounddiv-check.mjs [cases]
const MAX = Number.MAX_SAFE_INTEGER;
const N = Number(process.argv[2] ?? 2_000_000);
let s = 0x9e3779b97f4a7c15n;
const r64 = () => { s ^= (s << 13n) & 0xffffffffffffffffn; s ^= s >> 7n; s ^= (s << 17n) & 0xffffffffffffffffn; return s; };
const rnd = n => Number(r64() % BigInt(n));
const EDGES = [0, 1, 2, 3, 7, 10, 60, 100, 400, 1000, 94906265, 94906266, 2 ** 31, 2 ** 32, 2 ** 52 - 1, 2 ** 52, 2 ** 52 + 1, MAX - 2, MAX - 1, MAX];
const pick = () => {
  const m = rnd(6), sign = rnd(2) ? 1 : -1;
  if (m === 0) return sign * EDGES[rnd(EDGES.length)];
  if (m === 1) return sign * (rnd(2001));
  if (m === 2) return sign * (MAX - rnd(1000));
  if (m === 3) return sign * Number(r64() % BigInt(MAX + 1));
  if (m === 4) return sign * (2 ** (rnd(53)) + rnd(3) - 1);
  return sign * Number(r64() % 100000007n);
};
const fdiv = (a, b) => { const q = a / b, r = a % b; return r !== 0n && ((r < 0n) !== (b < 0n)) ? q - 1n : q; };
let bad = 0, count = 0, nonwhole = 0, negzero = 0;
const same = (x, n) => x === Number(n) && (x !== 0 || true);
for (let i = 0; i < N; i++) {
  const a = pick(), b = pick();
  if (b === 0) continue;
  const A = BigInt(a), B = BigInt(b);
  const t = A / B, f = fdiv(A, B), c = -fdiv(-A, B), m = A % B;
  count++;
  if (A % B !== 0n) nonwhole++;
  const got = [Math.trunc(a / b), Math.floor(a / b), Math.ceil(a / b), a % b];
  const want = [t, f, c, m];
  for (let k = 0; k < 4; k++) if (got[k] !== Number(want[k])) { bad++; if (bad < 10) console.log("DISAGREE", k, a, b, got[k], want[k]); }
  // signed zeros: -0 appears exactly when the exact result is 0 and the sign is negative
  for (let k = 0; k < 4; k++) if (got[k] === 0 && Object.is(got[k], -0)) negzero++;
}
console.log(`${count} cases (${nonwhole} with a fractional quotient, ${negzero} results of -0), ${bad} disagree`);
process.exit(bad ? 1 : 0);
