// Forms the translator learned late, each shaped like code from date-fns or @types/geojson.
// They go through the bridge: `corpus-gaps.tsv` lists them, with this directory as the repository.
// `%` and rounded division are in `../rem/rem.ts`.

// `let x;` assigned on every path before it is read (date-fns `normalizeTwoDigitYear`).
export function centuryStart(twoDigitYear: number, currentYear: number): number {
  const isCommonEra = currentYear > 0;
  const absCurrentYear = isCommonEra ? currentYear : 1 - currentYear;
  let result;
  if (isCommonEra) {
    const rangeEnd = absCurrentYear + 50;
    const isPreviousCentury = twoDigitYear > rangeEnd;
    result = twoDigitYear + rangeEnd - (isPreviousCentury ? 100 : 0);
  } else {
    const rangeStart = absCurrentYear - 50;
    const isPreviousCentury = twoDigitYear >= rangeStart;
    result = twoDigitYear + rangeStart + (isPreviousCentury ? 100 : 0);
  }
  return isCommonEra ? result : 1 - result;
}

export function sizeName(n: number): string {
  let name: string;
  if (n > 9) {
    name = "big";
  } else if (n > 0) {
    name = "small";
  } else {
    name = "none";
  }
  return name;
}

export function assignedTwice(n: number): number {
  let x;
  x = n + 1;
  x = x * 2;
  return x;
}

export function assignedAfterExit(n: number): number {
  let x;
  if (n > 5) {
    return 0;
  }
  x = n;
  return x;
}

// `||` and `&&` on a call, an index or a conditional (date-fns `validateDate`).
const DAYS_IN_MONTH = [31, null, 31, 30];

export function daysIn(month: number, leap: boolean): number {
  return DAYS_IN_MONTH[month] || (leap ? 29 : 28);
}

export function validDate(month: number, date: number, leap: boolean): boolean {
  return month >= 0 && month <= 3 && date >= 1 && date <= (DAYS_IN_MONTH[month] || (leap ? 29 : 28));
}

export function orCall(a: number, b: number): number {
  return Math.max(a, b) || 7;
}

export function andCall(a: string): string {
  return a.trim() && a.slice(1);
}

export function orIndex(xs: number[], i: number, d: number): number {
  return xs[i] || Math.max(d, 1);
}

export function orConditional(a: number, b: number, c: number): number {
  return (a > b ? a : b) || c;
}

// `null` and `undefined` inside arrays whose elements allow them.
export function withHole(a: number): (number | null)[] {
  return [a, null, 3];
}

export function withUndefined(a: number): (number | undefined)[] {
  return [undefined, a];
}

export function withNulls(a: string): (string | null)[] {
  return [null, a, null];
}

export function nested(a: number): ((number | null)[] | null)[] {
  return [[a, null], null];
}

export function sumPresent(a: number): number {
  const xs: (number | null)[] = [a, null, 3];
  let n = 0;
  for (const x of xs) {
    if (x != null) n += x;
  }
  return n;
}

// Index signatures next to the named fields (@types/geojson, foreign members).
export interface Point {
  type: "Point";
  coordinates: number[];
  [foreignMember: string]: unknown;
}

export interface Counts {
  total: number;
  [name: string]: number;
}

export function pointKind(p: Point): string {
  return p.type;
}

export function pointDimensions(p: Point): number {
  return p.coordinates.length;
}

export function totalPlusOne(c: Counts): number {
  return c.total + 1;
}

export function makeCounts(n: number): Counts {
  return { total: n };
}

export function twoDigits(n: string): string {
  return n.padStart(2, "0");
}

export function column(s: string, width: number): string {
  return s.trim().padEnd(width);
}

export function portOf(s: string): number {
  return Number(s.trim());
}

export function flagCount(a: boolean, b: boolean): number {
  return Number(a) + Number(b);
}

export function listCount(xs: string[] | undefined, ys: number[]): number {
  return (Array.isArray(xs) ? 1 : 0) + (Array.isArray(ys) ? 1 : 0);
}

export function lastTag(tags: string[]): number {
  return tags.lastIndexOf("draft");
}

export function lastScore(scores: number[], i: number): number {
  const s = scores.at(i);
  return s === undefined ? 0 : s;
}

export function lastChar(s: string): string {
  return s.at(-1) ?? "";
}

export function rule(width: number): string {
  return "-".repeat(width);
}

export function allRows(rows: number[][]): number[] {
  return rows.flat();
}

export function pairs(xs: number[]): number[] {
  return xs.flatMap(x => [x, x * 2]);
}

export function firstNegative(xs: number[]): number {
  return xs.findIndex(x => x < 0);
}


export interface Page<T> {
  items: T[];
  total: number;
}

export function pageSize<T>(p: Page<T>): number {
  return p.items.length;
}

export function pageItems<T>(p: Page<T>): T[] {
  return p.total > 0 ? p.items : [];
}

export function onePage<T>(x: T): Page<T> {
  return { items: [x], total: 1 };
}

export function firstOf<T extends {}>(xs: T[]): T | undefined {
  return xs[0];
}

export function orElse<T extends {}>(a: T | undefined, d: T): T {
  return a ?? d;
}

function repeat<T>(x: T, n: number): T[] {
  return n > 0 ? [x, x] : [x];
}

export function repeatCount(n: number): number {
  return repeat(n, n).length;
}

export function numberPage(p: Page<number>): number {
  return pageSize(p) + p.total;
}
