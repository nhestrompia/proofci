import TsReal
open Aeneas Aeneas.Std Result src.config.price src.phases

/-- Tick spacing is always positive, whatever the input. -/
theorem tick_spacing_positive (raw : Int) :
    deriveAuctionTickSpacing raw ⦃ t => 0 < t ⦄ := by sorry

/-- The floor is on a tick boundary and never above the requested price, so the
contract's `floorPrice % tickSpacing == 0` check cannot revert. -/
theorem floor_on_tick (raw : Int) (h : 0 ≤ raw) :
    deriveAuctionPricing raw ⦃ p =>
      0 < p.tickSpacing ∧ p.floorPriceX96 % p.tickSpacing = 0 ∧ p.floorPriceX96 ≤ raw ⦄ := by sorry

/-- The doc comment's claim: the floor drifts by less than 1/100 of the requested price. -/
theorem floor_drift_bounded (raw : Int) (h : 0 < raw) :
    deriveAuctionPricing raw ⦃ p => (raw - p.floorPriceX96) * 100 < raw ⦄ := by sorry

/-- The last phase in the leading run of started phases. A missing `fromAge` means
the phase starts immediately. -/
theorem active_phase_is_last_started (p : MonteCarloSpendingPhase)
    (ps : List MonteCarloSpendingPhase) (age : Js.Num) :
    getActiveSpendingPhase (p :: ps) age ⦃ r =>
      r = ((p :: ps).takeWhile (fun q => q.fromAge.all (fun a => a.val ≤ age.val))).getLast?.getD p ⦄ := by
  sorry

/-- Before any phase has started, the earliest one is active. -/
theorem active_phase_before_any (p : MonteCarloSpendingPhase)
    (ps : List MonteCarloSpendingPhase) (age : Js.Num)
    (h : p.fromAge.all (fun a => a.val ≤ age.val) = false) :
    getActiveSpendingPhase (p :: ps) age ⦃ r => r = p ⦄ := by sorry
