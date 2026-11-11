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
