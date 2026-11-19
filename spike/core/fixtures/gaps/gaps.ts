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

export function scoreOf(scores: Record<string, number>, name: string): number {
  return scores[name] ?? 0;
}

export function isKnown(labels: { [id: string]: string }, id: string): boolean {
  return id in labels;
}

export function fieldNames(row: Record<string, string>): string[] {
  return Object.keys(row);
}

export function weights(row: Record<string, number>): number[] {
  return Object.values(row);
}

export function ownerId(row: Record<string, number>): number {
  return row.owner ?? -1;
}

export function snapshot(row: Record<string, boolean>): Record<string, boolean> {
  return { ...row };
}


// Types that hold themselves (a linked list, a JSON-like union), and recursion over them.
export interface GapItem {
  value: number;
  next: GapItem | null;
}

export function itemTotal(list: GapItem | null): number {
  if (list === null) return 0;
  return list.value + itemTotal(list.next);
}

export type GapJson = { kind: "num"; value: number } | { kind: "list"; items: GapJson[] };

export function jsonLeaves(json: GapJson): number {
  switch (json.kind) {
    case "num": return 1;
    case "list": return json.items.map(item => jsonLeaves(item)).reduce((a, b) => a + b, 0);
  }
}

export function itemSum(list: GapItem | null, acc: number): number {
  if (list === null) return acc;
  return itemSum(list.next, acc + list.value);
}

export function prependItem(list: GapItem | null, value: number): GapItem {
  return { value, next: list };
}

export function countDown(n: number): number {
  if (n <= 0) return 0;
  return 1 + countDown(n - 1);
}

export interface GapTree {
  label: string;
  kids: GapTree[];
}

export function firstKid(t: GapTree): string {
  return t.kids.length > 0 ? t.kids[0].label : t.label;
}

export function treeSize(t: GapTree): number {
  return t.kids.map(k => treeSize(k)).reduce((a, b) => a + b, 1);
}

export type GapShape = { kind: "circle"; r: number } | { kind: "rect"; w: number; h: number };

export function shapeSize(s: GapShape): number {
  switch (s.kind) {
    case "circle": return s.r * 2;
    case "rect": return s.w + s.h;
  }
}

export function shapeArea(s: GapShape): number {
  switch (s.kind) {
    case "circle":
      return s.r * s.r;
    default:
      return s.w * s.h;
  }
}

export function isRect(s: GapShape): boolean {
  switch (s.kind) {
    case "rect": return true;
    default: return false;
  }
}

export function circle(r: number): GapShape {
  return { kind: "circle", r };
}

export type GapNode = { kind: "leaf"; weight: number } | { kind: "pair"; left: GapNode; right: GapNode };

export function nodeWeight(n: GapNode): number {
  switch (n.kind) {
    case "leaf": return n.weight;
    case "pair": return nodeWeight(n.left) + nodeWeight(n.right);
  }
}

export function sumFour(a: number, b: number, c: number, d: number): number {
  return a + b + c + d;
}

export function callFour(x: number): number {
  return sumFour(x, x, 1, 2);
}

export function rotateTotal(list: GapItem | null, a: number, b: number, c: number): number {
  if (list === null) return a + b + c;
  return rotateTotal(list.next, b, c, a + list.value);
}

export function nextValue(item: GapItem): number {
  if (item.next === null) return 0;
  return item.next.value;
}

export type GapMove = { kind: "left"; by: number } | { kind: "right"; by: number };

export function moveX(m: GapMove): number {
  switch (m.kind) {
    case "left": return 0 - m.by;
    case "right": return m.by;
  }
}

export function rectDiff(s: GapShape): number {
  switch (s.kind) {
    case "circle": return s.r;
    case "rect": return s.w - s.h;
  }
}

export type GapResult<T> = { kind: "ok"; value: T } | { kind: "err"; code: number };

export function resultOr(r: GapResult<number>, d: number): number {
  switch (r.kind) {
    case "ok": return r.value;
    case "err": return d + r.code;
  }
}

export interface GapPt {
  x: number;
}

export type GapPick = { kind: "one"; pt: GapPt } | { kind: "none" };

export function pickX(p: GapPick): number {
  switch (p.kind) {
    case "one": return p.pt.x;
    case "none": return 0;
  }
}

export function okNum(v: number): GapResult<number> {
  return { kind: "ok", value: v };
}

export function resultLen(r: GapResult<string>): number {
  switch (r.kind) {
    case "ok": return r.value.length;
    case "err": return r.code;
  }
}

export type GapMaybe = { kind: "some"; v: number | null } | { kind: "none" };

export function maybeOr(m: GapMaybe, d: number): number {
  switch (m.kind) {
    case "some":
      if (m.v === null) return d;
      return m.v;
    case "none": return d;
  }
}

export type GapLink = { kind: "end" } | { kind: "link"; next: GapLink | null; value: number };

export function linkSum(l: GapLink): number {
  switch (l.kind) {
    case "end": return 0;
    case "link":
      if (l.next === null) return l.value;
      return l.value + linkSum(l.next);
  }
}

export function okOr<T>(r: GapResult<T>, d: T): T {
  switch (r.kind) {
    case "ok": return r.value;
    case "err": return d;
  }
}

export type GapOpt = { kind: "has"; v?: number } | { kind: "empty" };

export function optOr(o: GapOpt, d: number): number {
  switch (o.kind) {
    case "has": return o.v ?? d;
    case "empty": return d;
  }
}

export interface GapBox<T> {
  value: T;
}

export function boxOrZero(b: GapBox<number | null>): number {
  if (b.value === null) return 0;
  return b.value;
}

export function boxIsUndef(b: GapBox<number | undefined>): boolean {
  return b.value === undefined;
}

export function resultNull(r: GapResult<string | null>): number {
  switch (r.kind) {
    case "ok":
      if (r.value === null) return 0;
      return r.value.length;
    case "err": return r.code;
  }
}

export interface GapSlot<T> {
  v?: T;
}

export function slotUndef(s: GapSlot<number | undefined>): boolean {
  return s.v === undefined;
}

export function slotOf(x: number | undefined): GapSlot<number | undefined> {
  return { v: x };
}

export function isEven(n: number): boolean {
  if (n <= 0) return true;
  return isOdd(n - 1);
}

export function isOdd(n: number): boolean {
  if (n <= 0) return false;
  return isEven(n - 1);
}

export type GapTerm =
  | { kind: "num"; n: number }
  | { kind: "list"; items: GapTerm[] };

export function jsonSum(j: GapTerm): number {
  switch (j.kind) {
    case "num": return j.n;
    case "list": return itemsSum(j.items, 0);
  }
}

function itemsSum(xs: GapTerm[], i: number): number {
  if (i >= xs.length) return 0;
  return jsonSum(xs[i]) + itemsSum(xs, i + 1);
}
