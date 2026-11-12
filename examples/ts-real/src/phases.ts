export type MonteCarloSpendingPhase = {
  id: string;
  name: string;
  /** Age the phase begins (inclusive); null = starts immediately */
  fromAge: number | null;
  /** Yearly spending in minor units, in today's money */
  annualWithdrawal: number;
};

/**
 * The phase active at the given age from a resolved (sorted) list: the
 * last phase that has started, or the earliest phase before any has.
 * The engine's planned-spending schedule and the cashflow chart's phase
 * attribution both resolve through here so they can't disagree.
 */
export function getActiveSpendingPhase(
  resolvedPhases: MonteCarloSpendingPhase[],
  age: number,
): MonteCarloSpendingPhase {
  let active = resolvedPhases[0];
  for (const phase of resolvedPhases) {
    if (phase.fromAge == null || phase.fromAge <= age) {
      active = phase;
    } else {
      break;
    }
  }
  return active;
}
