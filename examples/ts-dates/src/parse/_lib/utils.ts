// Excerpt of date-fns (MIT, Copyright (c) 2021 Sasha Koss and Lesha Koss), a9739fb, pkgs/core/src/parse/_lib/utils.ts

export function isLeapYearIndex(year: number): boolean {
  return year % 400 === 0 || (year % 4 === 0 && year % 100 !== 0);
}
