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

// date-fns `validateDate`.
export function validateDate(year: number, month: number, date: number): boolean {
  const daysInMonths = [31, year % 400 === 0 || (year % 4 === 0 && year % 100 !== 0) ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
  if (month < 0 || month > 11) return false;
  return date >= 1 && date <= daysInMonths[month];
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
