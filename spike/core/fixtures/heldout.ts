// Real functions the generator was never tuned on, copied unchanged from public repositories.
export type DataGridCoordinates = { row: number; col: number };
export type IncrementType = "object" | "array";
export type AuctionOutcome = "active" | "graduated" | "failed";
export type LocaleDayPeriod = "am" | "pm" | "morning" | "noon" | "afternoon" | "evening" | "night";
export type RangePosition = 'start' | 'end' | 'middle' | null;
const daysInWeek = 7;

export function isCellMatch(
  cell: DataGridCoordinates,
  coords?: DataGridCoordinates | null
) {
  if (!coords) {
    return false
  }

  return cell.row === coords.row && cell.col === coords.col
}

export function maybeIncrementLevel(
  level: number,
  type: IncrementType
): number {
  if (type !== "object") {
    return level
  }

  return level + 1
}

export function getNextRunningBalance({
  hasBudgetData,
  carryoverToNextMonth,
  runningBalance,
}: {
  hasBudgetData: boolean;
  carryoverToNextMonth: number;
  runningBalance: number;
}): number {
  return hasBudgetData ? carryoverToNextMonth : runningBalance;
}

export function deriveAuctionOutcome(p: {
  isGraduated: boolean
  endBlock: bigint
  currentBlock: bigint
}): AuctionOutcome {
  if (p.currentBlock < p.endBlock) {
    return 'active'
  }
  return p.isGraduated ? 'graduated' : 'failed'
}

export function calculateTrend(
  graphData: Array<{ date: string; ageOfMoney: number }>,
): 'up' | 'down' | 'stable' {
  if (graphData.length < 2) return 'stable';

  const last = graphData[graphData.length - 1].ageOfMoney;
  const secondLast = graphData[graphData.length - 2].ageOfMoney;

  const diff = last - secondLast;
  const threshold = 2; // Days threshold for "stable"

  if (diff > threshold) return 'up';
  if (diff < -threshold) return 'down';
  return 'stable';
}

export function clamp(value: string, min: string, max: string): string {
  if (value < min) return min;
  if (value > max) return max;
  return value;
}

export function rangePosition(
  cell: string,
  start: string,
  end: string,
): RangePosition {
  if (cell < start || cell > end) return null;
  if (cell === start) return 'start';
  if (cell === end) return 'end';
  return 'middle';
}

export function daysToWeeks(days: number): number {
  const result = Math.trunc(days / daysInWeek);
  // Prevent negative zero
  return result === 0 ? 0 : result;
}

export function trimIntervalDataToRange(
  data: { date: string; total: number }[],
  startIndex: number,
  endIndex: number,
): { date: string; total: number }[] {
  // Trim empty interval data from the start and end based on the range
  if (startIndex > endIndex || startIndex < 0 || endIndex >= data.length) {
    return [];
  }
  return data.slice(startIndex, endIndex + 1);
}

export function getV3HopCount(path: string): number | undefined {
  if (!path.startsWith('0x')) return undefined

  const byteLength = (path.length - 2) / 2
  if (byteLength < 43) return undefined

  const variableSegmentLength = byteLength - 20
  if (variableSegmentLength < 23 || variableSegmentLength % 23 !== 0) return undefined

  return variableSegmentLength / 23
}
