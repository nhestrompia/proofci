// Excerpt of date-fns (MIT, Copyright (c) 2021 Sasha Koss and Lesha Koss), a9739fb, pkgs/core/src/parseISO/index.ts

function isLeapYearIndex(year: number): boolean {
  return year % 400 === 0 || (year % 4 === 0 && year % 100 !== 0);
}

function validateDayOfYearDate(year: number, dayOfYear: number): boolean {
  return dayOfYear >= 1 && dayOfYear <= (isLeapYearIndex(year) ? 366 : 365);
}

function validateTime(
  hours: number,
  minutes: number,
  seconds: number,
): boolean {
  if (hours === 24) {
    return minutes === 0 && seconds === 0;
  }

  return (
    seconds >= 0 &&
    seconds < 60 &&
    minutes >= 0 &&
    minutes < 60 &&
    hours >= 0 &&
    hours < 25
  );
}
