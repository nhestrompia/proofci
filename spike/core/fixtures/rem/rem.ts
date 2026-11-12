// Functions that use `%` and rounded division, shaped like date-fns and similar code.
// `corpus-rem.tsv` lists them, with this directory as the repository.

// date-fns `isLeapYearIndex`.
export function isLeapYearIndex(year: number): boolean {
  return year % 400 === 0 || (year % 4 === 0 && year % 100 !== 0);
}

export function twoDigits(year: number): number {
  return year % 100;
}

export function isEven(n: number): boolean {
  return n % 2 === 0;
}

// A positive modulus for a possibly negative index (zero modulus: the model stops).
export function wrapIndex(i: number, n: number): number {
  return ((i % n) + n) % n;
}

export function negativeDivisor(a: number, b: number): number {
  return a % -b;
}

export function secondsPart(total: number): number {
  return total % 60;
}

export function minutesOf(total: number): number {
  return Math.floor(total / 60);
}

export function pageCount(total: number, size: number): number {
  return Math.ceil(total / size);
}

export function halve(n: number): number {
  return Math.trunc(n / 2);
}

export function centuryOf(year: number): number {
  return Math.ceil(year / 100);
}

export function floorByAny(a: number, b: number): number {
  return Math.floor(a / b);
}

export function hourOfDay(ms: number): number {
  return Math.floor(ms / 3600000) % 24;
}

export function middle(a: number, b: number): number {
  return Math.floor((a + b) / 2);
}

export function splitClock(total: number): string {
  const hours = Math.floor(total / 3600);
  const minutes = Math.floor((total % 3600) / 60);
  const seconds = total % 60;
  if (hours > 0) return `${hours}:${minutes}:${seconds}`;
  return `${minutes}:${seconds}`;
}

// date-fns `normalizeTwoDigitYear`, with the rounding written out.
export function centuryOffset(twoDigitYear: number, currentYear: number): number {
  const century = currentYear - (currentYear % 100);
  return twoDigitYear + century;
}

// In a loop.
export function digitSum(n: number): number {
  let sum = 0;
  let rest = n < 0 ? -n : n;
  while (rest > 0) {
    sum += rest % 10;
    rest = Math.floor(rest / 10);
  }
  return sum;
}

export function sumOdd(xs: number[]): number {
  let sum = 0;
  for (const x of xs) {
    if (x % 2 !== 0) sum += x;
  }
  return sum;
}

// In callbacks.
export function evens(xs: number[]): number[] {
  return xs.filter(x => x % 2 === 0);
}

export function halves(xs: number[]): number[] {
  return xs.map(x => Math.trunc(x / 2));
}

export function multiplesOf(xs: number[], d: number): number[] {
  return xs.filter(x => x % d === 0);
}

export function pagesFor(sizes: number[], per: number): number {
  return sizes.reduce((acc, s) => acc + Math.ceil(s / per), 0);
}

// date-fns `validateDate`, with the table of month lengths written as conditions.
export function validateDate(year: number, month: number, date: number): boolean {
  if (month < 0 || month > 11) return false;
  const days = month === 1 ? (isLeapYearIndex(year) ? 29 : 28) : month === 3 || month === 5 || month === 8 || month === 10 ? 30 : 31;
  return date >= 1 && date <= days;
}

export function weekOfYear(dayOfYear: number): number {
  return Math.floor((dayOfYear - 1) / 7) + 1;
}

export function roundUpTo(n: number, step: number): number {
  return Math.ceil(n / step) * step;
}

export function remainderIsZero(a: number, b: number): boolean {
  return a % b === 0;
}

export function gcd(a: number, b: number): number {
  let x = a < 0 ? -a : a;
  let y = b < 0 ? -b : b;
  while (y !== 0) {
    const t = y;
    y = x % y;
    x = t;
  }
  return x;
}

export function halfIfEven(n: number): number {
  return n % 2 === 0 ? n / 2 : n;
}

export function powersOfTwo(n: number): number {
  let count = 0;
  let rest = n;
  while (rest !== 0 && rest % 2 === 0) {
    rest = Math.trunc(rest / 2);
    count += 1;
  }
  return count;
}

export function daysBetween(from: number, to: number): number {
  return Math.trunc((to - from) / 86400000);
}

export function negativeLiterals(n: number): number {
  return Math.floor(n / -2) + (n % -3) + Math.ceil(n / -5) + Math.trunc(n / -7);
}

export function residues(xs: number[]): number[] {
  return xs.map(x => x % 7);
}

export function anyMultiple(xs: number[], d: number): boolean {
  return xs.some(x => x % d === 0);
}

export function allOdd(xs: number[]): boolean {
  return xs.every(x => x % 2 !== 0);
}

export function clockHour(hour: number): number {
  const h = hour % 12;
  return h === 0 ? 12 : h;
}

export function isEvenIndex(xs: number[], i: number): boolean {
  return xs.length > 0 && i % 2 === 0 && i < xs.length;
}
