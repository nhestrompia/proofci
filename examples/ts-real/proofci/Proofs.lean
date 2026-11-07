import TsReal
open Aeneas Aeneas.Std Result src.config.price src.phases
open src.constants

@[step] theorem divisor_spec : AUCTION_TICK_DIVISOR ⦃ d => d = 100 ⦄ := by
  simp [AUCTION_TICK_DIVISOR, WP.spec_ok]

theorem tick_spacing_positive (raw : Int) :
    deriveAuctionTickSpacing raw ⦃ t => 0 < t ⦄ := by
  unfold deriveAuctionTickSpacing
  step*
  split
  · simpa [WP.spec_ok]
  · simp [WP.spec_ok]

/-- For a non-negative price, the exact spacing. -/
@[step] theorem spacing_spec (raw : Int) (h : 0 ≤ raw) :
    deriveAuctionTickSpacing raw ⦃ t => t = if raw / 100 > 0 then raw / 100 else 1 ⦄ := by
  unfold deriveAuctionTickSpacing
  have hd : Int.tdiv raw 100 = raw / 100 := Int.tdiv_eq_ediv_of_nonneg h
  step*
  split <;> simp_all [WP.spec_ok]

/-- The shape both pricing theorems need: a floor one remainder below `raw`. -/
@[step] theorem pricing_spec (raw : Int) (h : 0 ≤ raw) :
    deriveAuctionPricing raw ⦃ p =>
      p.tickSpacing = (if raw / 100 > 0 then raw / 100 else 1) ∧
      p.floorPriceX96 = raw - raw % p.tickSpacing ⦄ := by
  unfold deriveAuctionPricing
  step*
  have hpos : 0 < tickSpacing := by rw [tickSpacing_post]; split <;> omega
  have hm : raw.tmod tickSpacing = raw % tickSpacing := Int.tmod_eq_emod_of_nonneg h
  simp_all
  intro h0
  rw [h0] at hpos
  omega

theorem floor_on_tick (raw : Int) (h : 0 ≤ raw) :
    deriveAuctionPricing raw ⦃ p =>
      0 < p.tickSpacing ∧ p.floorPriceX96 % p.tickSpacing = 0 ∧ p.floorPriceX96 ≤ raw ⦄ := by
  apply WP.spec_mono (pricing_spec raw h)
  rintro p ⟨ht, hf⟩
  have hpos : 0 < p.tickSpacing := by rw [ht]; split <;> omega
  have hn := Int.emod_nonneg raw (Int.ne_of_gt hpos)
  refine ⟨hpos, ?_, by omega⟩
  rw [hf, Int.sub_emod, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
  simp

theorem floor_drift_bounded (raw : Int) (h : 0 < raw) :
    deriveAuctionPricing raw ⦃ p => (raw - p.floorPriceX96) * 100 < raw ⦄ := by
  apply WP.spec_mono (pricing_spec raw (by omega))
  rintro p ⟨ht, hf⟩
  have hpos : 0 < p.tickSpacing := by rw [ht]; split <;> omega
  have hn := Int.emod_nonneg raw (Int.ne_of_gt hpos)
  have hl := Int.emod_lt_of_pos raw hpos
  rw [hf]
  generalize raw % p.tickSpacing = r at *
  split at ht <;> omega

theorem last_cons {α} (q : α) (l : List α) (a : α) :
    (q :: l).getLast?.getD a = l.getLast?.getD q := by
  simp [List.getLast?_cons]

theorem active_phase_is_last_started (p : MonteCarloSpendingPhase)
    (ps : List MonteCarloSpendingPhase) (age : Js.Num) :
    getActiveSpendingPhase (p :: ps) age ⦃ r =>
      r = ((p :: ps).takeWhile (fun q => q.fromAge.all (fun a => a.val ≤ age.val))).getLast?.getD p ⦄ := by
  unfold getActiveSpendingPhase
  generalize hst : (fun q : MonteCarloSpendingPhase => q.fromAge.all (fun a => decide (a.val ≤ age.val))) = st
  generalize hT : ((p :: ps).takeWhile st).getLast?.getD p = T
  apply WP.spec_bind (Pₘ := fun a => a = some p) (by simp [WP.spec_ok, Js.at_])
  intro a ha; subst ha
  apply WP.spec_bind (Pₘ := fun l => l = p :: ps) (by simp [WP.spec_ok])
  intro l hl; subst hl
  apply WP.spec_bind (Pₘ := fun r => r = some T)
  · apply loop.spec_decr_nat (fun s => s.1.length)
      (fun s => ∃ a, s.2 = some a ∧ (s.1.takeWhile st).getLast?.getD a = T)
    · rintro ⟨rest, cur⟩ ⟨a, h1, h2⟩
      dsimp only at h1 h2 ⊢
      subst h1
      cases rest with
      | nil =>
        simp_all [WP.spec_ok]
      | cons q r =>
        subst hst
        cases hf : q.fromAge with
        | none =>
          simp [hf, WP.spec_ok]
          rw [List.takeWhile_cons_of_pos (by simp [hf]), last_cons] at h2
          exact h2
        | some v =>
          by_cases hv : v.val ≤ age.val
          · simp [hf, hv, WP.spec_ok]
            rw [List.takeWhile_cons_of_pos (by simp [hf, hv]), last_cons] at h2
            exact h2
          · simp [hf, hv, WP.spec_ok]
            rw [List.takeWhile_cons_of_neg (by simp [hf, hv])] at h2
            simpa using h2
    · exact ⟨p, rfl, hT⟩
  · intro r hr
    subst hr
    simpa using Js.unwrap_spec T

theorem active_phase_before_any (p : MonteCarloSpendingPhase)
    (ps : List MonteCarloSpendingPhase) (age : Js.Num)
    (h : p.fromAge.all (fun a => a.val ≤ age.val) = false) :
    getActiveSpendingPhase (p :: ps) age ⦃ r => r = p ⦄ := by
  apply WP.spec_mono (active_phase_is_last_started p ps age)
  intro r hr
  rw [List.takeWhile_cons_of_neg (by simp [h])] at hr
  simpa using hr
