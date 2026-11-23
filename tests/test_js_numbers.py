"""Compares ProofCI's model of JavaScript numbers with Node.

The model promises that when it returns a value, JavaScript computes the same
value, including for `Math.floor(a / b)` near the limits of safe integers.
Run inside the toolchain image:

    PROOFCI_TOOLCHAIN=1 python3 -m unittest tests.test_js_numbers -v
"""

import json
import os
import tempfile
import unittest
from pathlib import Path

from proofci import lean, typescript

OPERATIONS = """
export const add = (a: number, b: number): number => a + b;
export const sub = (a: number, b: number): number => a - b;
export const mul = (a: number, b: number): number => a * b;
export const div = (a: number, b: number): number => a / b;
export const rem = (a: number, b: number): number => a % b;
export const neg = (a: number): number => -a;
export const floor = (a: number, b: number): number => Math.floor(a / b);
export const ceil = (a: number, b: number): number => Math.ceil(a / b);
export const trunc = (a: number, b: number): number => Math.trunc(a / b);
export const abs = (a: number): number => Math.abs(a);
export const min = (a: number, b: number): number => Math.min(a, b);
export const max = (a: number, b: number): number => Math.max(a, b);
export const lt = (a: number, b: number): boolean => a < b;
export const le = (a: number, b: number): boolean => a <= b;
export const eq = (a: number, b: number): boolean => a === b;
export const ne = (a: number, b: number): boolean => a !== b;
export const both = (a: boolean, b: boolean): boolean => a && !b;
export const either = (a: boolean, b: boolean): boolean => a || b;
export const pick = (a: boolean, b: number): number => a ? b : 0;
export const orNull = (a: number | null): number => { if (a === null) return 0; return a; };
export const undefinedIsNotNull = (a: number | undefined): number => { if (a === undefined) return 1; return a; };
export const bigMul = (a: bigint, b: bigint): bigint => a * b - 1n;
export const bigDiv = (a: bigint, b: bigint): bigint => a / b;
export const bigRem = (a: bigint, b: bigint): bigint => a % b;
export const bigLess = (a: bigint, b: bigint): boolean => a < b;
export function check(a: number): void { if (a < 0) throw new RangeError("negative"); }
export function caught(a: number): number { try { check(a); return a; } catch { return 7; } }
export function joined(a: number, b: number): number { let r = a; if (r > b) { r = b; } else { r = r + 1; } return r * 2; }
export function capped(n: number): number { let s = 0; for (let i = 0; i < n && i < 50; i++) { if (i % 3 === 0) continue; if (s > 100) break; s += i; } return s; }
export function search(n: number): number { let i = 0; while (i < 40) { if (i * i >= n) return i; i += 1; } return -1; }
export function fact(n: number): number { if (n <= 0 || n > 25) return 1; return n * fact(n - 1); }
export function sum(xs: number[]): number { let s = 0; for (const x of xs) { s += x; } return s; }
export function evens(xs: number[]): number[] { const out: number[] = []; for (const x of xs) { if (x % 2 === 0) { out.push(x); } } return out; }
export const chain = (xs: number[]): number => xs.filter(x => x > 0).map(x => x * 2).reduce((a, b) => a + b, 0);
export const anyBig = (xs: number[]): boolean => xs.some(x => x > 100);
export const allBig = (xs: number[]): boolean => xs.every(x => x > 100);
export const found = (xs: number[]): number | undefined => xs.find(x => x > 1);
export const at = (xs: number[], i: number): number => xs[i];
export const size = (xs: number[]): number => xs.length;
export const cut = (xs: number[], a: number, b: number): number[] => xs.slice(a, b);
export const cutFrom = (xs: number[], a: number): number[] => xs.slice(a);
export const has = (xs: number[], a: number): boolean => xs.includes(a);
export const where = (xs: number[], a: number): number => xs.indexOf(a);
export const joinAll = (xs: number[], ys: number[]): number[] => [...xs, 1, ...ys].concat(xs);
export const textLength = (a: string): number => a.length;
export const textAt = (a: string, i: number): string => a[i];
export const textChar = (a: string, i: number): string => a.charAt(i);
export const textSlice = (a: string, x: number, y: number): string => a.slice(x, y);
export const textSub = (a: string, x: number, y: number): string => a.substring(x, y);
export const textStarts = (a: string, b: string): boolean => a.startsWith(b);
export const textEnds = (a: string, b: string): boolean => a.endsWith(b);
export const textHas = (a: string, b: string): boolean => a.includes(b);
export const textWhere = (a: string, b: string): number => a.indexOf(b);
export const textTrim = (a: string): string => a.trim();
export const textLower = (a: string): string => a.toLowerCase();
export const textUpper = (a: string): string => a.toUpperCase();
export const textSplit = (a: string, b: string): string[] => a.split(b);
export const textJoin = (xs: string[], b: string): string => xs.join(b);
export const textReplace = (a: string, b: string, c: string): string => a.replace(b, c);
export const textReplaceAll = (a: string, b: string, c: string): string => a.replaceAll(b, c);
export const textLess = (a: string, b: string): boolean => a < b;
export const textEqual = (a: string, b: string): boolean => a === b;
export const textAdd = (a: string, b: string): string => a + "-" + b;
export const textTemplate = (a: string, n: number, b: boolean, c: bigint): string => `${a}=${n},${b},${c}`;
export const textNumber = (n: number): string => String(n);
export const textPadStart = (a: string, n: number, b: string): string => a.padStart(n % 40, b);
export const textPadEnd = (a: string, n: number): string => a.padEnd(n % 40);
export const textToNumber = (a: string): number => Number(a);
export const boolToNumber = (a: boolean, b: boolean): number => Number(a) - Number(b);
export const isList = (xs: number[], ys: string[] | null): boolean => Array.isArray(xs) && !Array.isArray(ys);
export const lastOf = (xs: string[], v: string): number => xs.lastIndexOf(v);
export const atOf = (xs: number[], i: number): number => xs.at(i % 9) ?? -1;
export const charOf = (a: string, i: number): string => a.at(i % 9) ?? "none";
export const repeated = (a: string, n: number): string => a.repeat(n % 6);
export const flattened = (xs: number[], ys: number[]): number[] => [xs, ys, xs].flat();
export const doubled = (xs: number[]): number[] => xs.flatMap(x => [x, x + 1]);
export const firstBig = (xs: number[]): number => xs.findIndex(x => x > 3);
export const scoreIn = (r: Record<string, number>, k: string): number => r[k] ?? -1;
export const hasIn = (r: Record<string, number>, k: string): boolean => k in r;
export const keysOf = (r: Record<string, number>): string[] => Object.keys(r);
export const valuesOf = (r: Record<string, number>): number[] => Object.values(r);
export function tally(xs: string[]): Record<string, number> { const out: Record<string, number> = {}; for (const x of xs) { out[x] = (out[x] ?? 0) + 1; } return out; }
export function tallyKeys(xs: string[]): string[] { const out: Record<string, number> = {}; for (const x of xs) { out[x] = (out[x] ?? 0) + 1; } return Object.keys(out); }
export function bumped(r: Record<string, number>, k: string): Record<string, number> { const c = { ...r }; c[k] = (c[k] ?? 0) + 1; return c; }
export function counted(xs: string[]): Map<string, number> { const m = new Map<string, number>(); for (const x of xs) { const seen = m.get(x); if (seen === undefined) { m.set(x, 1); } else { m.set(x, seen + 1); } } m.delete("a"); return m; }
export const reSlug = (s: string): boolean => /^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(s);
export const reName = (s: string): boolean => /^[A-Z][a-z]*$/i.test(s);
export const reFound = (s: string): boolean => s.match(/a.b|\\d\\d/) !== null;
export const reOpt = (s: string): boolean => /^(?:|a)?b$/.test(s);
export const reSquash = (s: string): string => s.replace(/\\s+/g, " ");
export const reFirst = (s: string): string => s.replace(/[^a-z]/, "#");
export const reEmpty = (s: string): string => s.replaceAll(/x*/g, "-");
export const reHalves = (s: string): string => s.replaceAll(/[\\ud800-\\udbff]|é/g, "?");
export const reCase = (s: string, t: string): string => s.replace(/A|z/gi, t);
export const reWords = (s: string): string[] => s.split(/[,;]\\s*/);
export const reUnits = (s: string): string[] => s.split(/b?/);
export const reNested = (s: string): string[] => s.split(/(?:a*)*/);
export function unique(xs: number[]): Set<number> { const s = new Set<number>(); for (const x of xs) { s.add(x); } s.delete(0); return s; }
export const mapHas = (m: Map<number, string>, k: number): boolean => m.has(k);
export const mapGet = (m: Map<number, string>, k: number): string | undefined => m.get(k);
export const mapSize = (m: Map<string, number>): number => m.size;
export const setHas = (s: Set<string>, k: string): boolean => s.has(k);
export const optional = (a?: number): number => (a === undefined ? 1 : a + 1);
export const defaulted = (a: number = 5, b: number = a + 1): number => a * b;
export const destructured = ({ x, y: z }: { x: number; y: number }): number => x - z;
export const anyNull = (a: number | null | undefined): number => (a == null ? 0 : a);
export const orElse = (a: number | null, b: number): number => (a ?? b) + 1;
export const truthyNumber = (a: number): 1 | 2 => (a ? 1 : 2);
export const truthyText = (a: string): 1 | 2 => (a ? 1 : 2);
export const notText = (a: string): boolean => !a;
export const truthyBig = (a: bigint): 1 | 2 => (a ? 1 : 2);
export function maybeField(a: { x: number } | null): number | undefined { return a?.x; }
export function maybeOptional(a: { x?: number } | null): number | undefined { return a?.x; }
export function truthyObject(a: { x: number } | null): number { if (a) return a.x; return 0; }
export function notObject(a: { x: number } | undefined): number { if (!a) return 0; return a.x; }
export function bothTests(a: { x: number } | null): number { if (a !== null && a.x > 0) { return a.x; } return 0; }
export function eitherTest(a: { x: number } | null): number { if (a === null || a.x > 0) { return 1; } return a.x; }
export function reads(xs: { n: number }[]): number { return xs[0].n + 1; }
export function walk(xs: number[]): number { let s = 0; xs.forEach(x => { s += 1; if (x > 0) return; s += x; }); return s; }

export const dAdd = (): number => 0.1 + 0.2;
export const dSub = (): number => 0.3 - 0.1;
export const dMul = (a: number): number => a * 0.5;
export const dDiv = (a: number, b: number): number => a / b;
export const dRem = (): number => -7 % 3;
export const dRemNeg = (): number => 7 % -3;
export const dNeg = (a: number): number => -a;
export const dZeroEq = (): boolean => -0 === 0;
export const dNan = (): number => NaN;
export const dInf = (): number => Infinity;
export const dDiv0 = (): number => 1 / 0;
export const dDivN0 = (): number => -1 / 0;
export const dSubnormal = (): number => 5e-324 / 2;
export const dBig = (): number => 9007199254740992 + 0.5;
export const dOver53 = (): number => 9007199254740993 + 0.25;
export const dRound = (): number => Math.round(0.5);
export const dRoundNeg = (): number => Math.round(-0.5);
export const dRound25 = (): number => Math.round(2.5) + Math.round(-2.5);
export const dFloor = (): number => Math.floor(-0.5);
export const dCeil = (): number => Math.ceil(-0.5);
export const dTrunc = (): number => Math.trunc(-0.5);
export const dSign = (): number => Math.sign(-0.5);
export const dSign0 = (): number => Math.sign(-0);
export const dAbs = (): number => Math.abs(-0.5);
export const dMinNan = (a: number): number => Math.min(a, NaN);
export const dMax = (a: number, b: number): number => Math.max(a, b) / 1.5;
export const dEq = (): boolean => 0.1 + 0.2 === 0.3;
export const dNanEq = (n: number): boolean => n === n;
export const dLt = (a: number): boolean => a < 0.5;
export const dFin = (): boolean => Number.isFinite(0.1 + 0.2);
export const dFinInf = (): boolean => Number.isFinite(Infinity - Infinity);
export const dIsNaN = (): boolean => Number.isNaN(NaN);
export const dIsInt = (): boolean => Number.isInteger(Infinity);
export const dSafe = (): boolean => Number.isSafeInteger(0.5);
export const dTruth = (): number => { const x = 0.5; if (x) return 1; return 2; }
export const dCond = (a: number): number => a / 2 > 0.1 ? a : -a;
export const dCents = (a: number): number => Math.round(a * 100) / 100;
export const dLen = (xs: number[]): number => xs.length / 3;
export const dLenOpt = (a?: number): boolean => Number.isFinite(a);
const LIMIT = 2 * 3;
const CONFIG = { a: 1, names: ["a", "b"] };
export const limited = (a: number): number => a + LIMIT + CONFIG.a;
export const named = (a: string): boolean => CONFIG.names.includes(a);
export const fieldOptional = (a: { x?: number; y: number }): number => (a.x === undefined ? a.y : a.x + 1);
export function fieldNull(a: { x: number | null }): number { if (a.x !== null) { return a.x; } return 0; }
export function changes(xs: number[], i: number, v: number): number[] { const a = xs.slice(); a[i % 9] = v; a.push(v); a.unshift(1); a.pop(); a.shift(); a.reverse(); return a; }
"""
BATCH = 12
NAMES = [line.split()[2].split("(")[0] for line in OPERATIONS.strip().splitlines()
         if line.startswith("export")]


@unittest.skipUnless(os.environ.get("PROOFCI_TOOLCHAIN"), "needs the ProofCI toolchain image")
class Numbers(unittest.TestCase):
    def test_model_agrees_with_node(self):
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            package = work / "package"
            (package / "src").mkdir(parents=True)
            (package / "package.json").write_text(json.dumps({"name": "numbers"}))
            (package / "src/ops.ts").write_text(OPERATIONS)
            (work / "lean-src").mkdir()
            module = "Numbers"
            (work / "lean-src/Contract.lean").write_text(f"import {module}\n")
            functions = [f"src/ops.ts::{name}" for name in NAMES]
            extraction = typescript.extract(package.parent, "package", work, functions)
            self.assertEqual(extraction.failures, {})
            ws = lean.assemble(work / "lean", extraction.lean_file, extraction.module,
                               work / "lean-src", work / "lean-src")
            self.assertIsNone(lean.build_translation(ws))
            # Lean slows down badly on one huge file, so compare in batches.
            signatures = list(extraction.signatures.items())
            for start in range(0, len(signatures), BATCH):
                extraction.signatures = dict(signatures[start:start + BATCH])
                batch = work / f"batch-{start}"
                batch.mkdir()
                differ, notes = typescript.differential(package.parent, "package", batch, ws, extraction,
                                                        cases=500, timeout=300)
                self.assertEqual(differ[:5], [])
                self.assertIn("compared with Node", notes[-1])
                print(notes[-1])
