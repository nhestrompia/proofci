// Writes `op a b expected` lines from Node's own arithmetic.
import { createWriteStream } from "node:fs";
const out = createWriteStream(process.argv[2]);
const N = Number(process.argv[3] ?? 300000);
const buf = new DataView(new ArrayBuffer(8));
const bits = x => { buf.setFloat64(0, x); return buf.getBigUint64(0); };
const fromBits = b => { buf.setBigUint64(0, b); return buf.getFloat64(0); };
let s = 88172645463325252n;
const r64 = () => { s ^= (s << 13n) & 0xffffffffffffffffn; s ^= s >> 7n; s ^= (s << 17n) & 0xffffffffffffffffn; return s; };
const rnd = n => Number(r64() % BigInt(n));
const special = [0, -0, 1, -1, 0.5, 0.1, 0.2, 0.3, 2 ** 53, 2 ** 53 + 2, 2 ** 53 - 1, -(2 ** 53), Number.MAX_VALUE, Number.MIN_VALUE, -Number.MIN_VALUE,
  2.2250738585072014e-308, 2.225073858507201e-308, Infinity, -Infinity, NaN, 1e308, 1e-308, 1e-320, 4.5, 5.5, 1 + 2 ** -52, 1 - 2 ** -53, 3, 7, 10];
const value = () => {
  switch (rnd(9)) {
    case 0: return special[rnd(special.length)];
    case 1: return fromBits(r64());                                   // any bit pattern
    case 2: return rnd(2001) - 1000;                                  // small integers
    case 3: return (rnd(2 ** 31) * 2 ** 22 + rnd(2 ** 22)) * (rnd(2) ? 1 : -1); // large safe integers
    case 4: return (rnd(2001) - 1000) / 100;                          // money-like fractions
    case 5: return (rnd(2 ** 30) + 1) * 2 ** (rnd(60) - 1074);        // subnormal region
    case 6: return Number.MAX_VALUE / (1 + rnd(8));                   // near overflow
    case 7: return (2 ** 53 + rnd(1000) * 2) * 2 ** (rnd(3));         // spacing above 2^53
    default: return (rnd(1000) + 0.5);                                // exact ties for rounding
  }
};
const two = { add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b, div: (a, b) => a / b, rem: (a, b) => a % b,
  lt: (a, b) => Number(a < b), le: (a, b) => Number(a <= b), eq: (a, b) => Number(a === b) };
const one = { floor: Math.floor, ceil: Math.ceil, trunc: Math.trunc, neg: a => -a };
const names = [...Object.keys(two), ...Object.keys(two), ...Object.keys(one)];
for (let i = 0; i < N; i += 1) {
  const op = names[rnd(names.length)], a = value(), b = value();
  const r = two[op] ? two[op](a, b) : one[op](a);
  out.write(`${op} ${bits(a)} ${bits(b)} ${Number.isNaN(r) ? 9221120237041090560n : bits(r)}\n`);
}
out.end();
