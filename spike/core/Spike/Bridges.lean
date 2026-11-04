import Spike.WP
open Core Aeneas Aeneas.Std Result Gen

attribute [simp] Gen.src_ledger_transfer
attribute [simp] Gen.src_ledger_sumAmounts
attribute [simp] Gen.src_phases_getActiveSpendingPhase
attribute [simp] Gen.src_config_price_deriveAuctionPricing
attribute [simp] Gen.src_config_price_deriveAuctionTickSpacing
attribute [simp] Gen.prog



instance : Enc src.ledger.Accounts := ⟨fun h a v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.«from» ((fs.lookup "from").getD .undef) ∧
  Enc.enc h a.«to» ((fs.lookup "to").getD .undef)⟩
@[simp] theorem enc_src_ledger_Accounts {h} {a : src.ledger.Accounts} {v} : Enc.enc h a v ↔ ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.«from» ((fs.lookup "from").getD .undef) ∧
  Enc.enc h a.«to» ((fs.lookup "to").getD .undef) := Iff.rfl

instance : Enc src.phases.MonteCarloSpendingPhase := ⟨fun h a v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.id ((fs.lookup "id").getD .undef) ∧
  Enc.enc h a.«name» ((fs.lookup "name").getD .undef) ∧
  Enc.enc h a.fromAge ((fs.lookup "fromAge").getD .undef) ∧
  Enc.enc h a.annualWithdrawal ((fs.lookup "annualWithdrawal").getD .undef)⟩
@[simp] theorem enc_src_phases_MonteCarloSpendingPhase {h} {a : src.phases.MonteCarloSpendingPhase} {v} : Enc.enc h a v ↔ ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.id ((fs.lookup "id").getD .undef) ∧
  Enc.enc h a.«name» ((fs.lookup "name").getD .undef) ∧
  Enc.enc h a.fromAge ((fs.lookup "fromAge").getD .undef) ∧
  Enc.enc h a.annualWithdrawal ((fs.lookup "annualWithdrawal").getD .undef) := Iff.rfl

instance : Enc Proofci.Inline.R9365a59415 := ⟨fun h a v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.floorPriceX96 ((fs.lookup "floorPriceX96").getD .undef) ∧
  Enc.enc h a.tickSpacing ((fs.lookup "tickSpacing").getD .undef)⟩
@[simp] theorem enc_Proofci_Inline_R9365a59415 {h} {a : Proofci.Inline.R9365a59415} {v} : Enc.enc h a v ↔ ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.floorPriceX96 ((fs.lookup "floorPriceX96").getD .undef) ∧
  Enc.enc h a.tickSpacing ((fs.lookup "tickSpacing").getD .undef) := Iff.rfl

theorem src_ledger_transfer_bridge {h p0 p1 v0 v1 r}
    (h0 : Enc.enc h p0 v0)
    (h1 : Enc.enc h p1 v1)
    (hr : src.ledger.transfer p0 p1 = ok r) :
    WpRun prog src_ledger_transfer [v0, v1] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by
  simp only [enc_src_ledger_Accounts] at h0
  obtain ⟨l0, fs0, rfl, hl0, f00, f01⟩ := h0
  simp only [enc_num] at f00
  simp only [enc_num] at f01
  simp only [enc_num] at h1
  subst h1
  all_goals unfold src.ledger.transfer at hr
  all_goals apply wprun
  all_goals simp only [src_ledger_transfer]
  all_goals try simp only [bind_ok, Aeneas.Std.bind_assoc] at hr
  all_goals shallow
  all_goals core_run

theorem src_ledger_sumAmounts_bridge {h p0 v0 r}
    (h0 : Enc.enc h p0 v0)
    (hr : src.ledger.sumAmounts p0 = ok r) :
    WpRun prog src_ledger_sumAmounts [v0] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by
  simp only [enc_list] at h0
  obtain ⟨l0, vs0, rfl, harr0, hf0⟩ := h0
  all_goals unfold src.ledger.sumAmounts at hr
  all_goals apply wprun
  all_goals simp only [src_ledger_sumAmounts]
  all_goals try simp only [bind_ok, Aeneas.Std.bind_assoc] at hr
  revert hr; refine Core.bind_intro ?_; intro res hl hr
  shallow
  all_goals core_run
  refine wp_iter_loop hl hf0 (fun a s => s.heap = h ∧ s.env "amounts" = some (.ref l0) ∧ ∃ w, s.env "total" = some w ∧ Enc.enc h a w) (fun a s => s.heap = h ∧ s.env "amounts" = some (.ref l0) ∧ ∃ w, s.env "total" = some w ∧ Enc.enc h a w) ?_ ?_ (fun _ _ hR => hR.1) harr0 ?_ ?_
  · refine ⟨rfl, ?_⟩
    simp [Env.put, Fn.env0, *]
    first | done | exact enc_at hf0 0
  · rintro s ⟨hh, e0, w, hw, hwe⟩
    try simp only [enc_num] at hwe
    try subst hwe
    try simp only [enc_some] at hwe
    core_run
  · intro a s y hR hb
    simp at hb
    exact ⟨a, hb.symm, hR⟩
  · rintro q rest a s item y ⟨hh, e0, w, hw, hwe⟩ hq hr
    try simp only [enc_num] at hwe
    try subst hwe
    simp only [enc_num] at hq
    subst hq
    dsimp only at hr
    shallow
    all_goals core_run

theorem src_phases_getActiveSpendingPhase_bridge {h p0 p1 v0 v1 r}
    (h0 : Enc.enc h p0 v0)
    (h1 : Enc.enc h p1 v1)
    (hr : src.phases.getActiveSpendingPhase p0 p1 = ok r) :
    WpRun prog src_phases_getActiveSpendingPhase [v0, v1] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by
  simp only [enc_list] at h0
  obtain ⟨l0, vs0, rfl, harr0, hf0⟩ := h0
  simp only [enc_num] at h1
  subst h1
  all_goals unfold src.phases.getActiveSpendingPhase at hr
  all_goals apply wprun
  all_goals simp only [src_phases_getActiveSpendingPhase]
  all_goals try simp only [bind_ok, Aeneas.Std.bind_assoc] at hr
  revert hr; refine Core.bind_intro ?_; intro res hl hr
  shallow
  all_goals core_run
  refine wp_iter_loop hl hf0 (fun a s => s.heap = h ∧ s.env "resolvedPhases" = some (.ref l0) ∧ s.env "age" = some (.num p1.val) ∧ ∃ w, s.env "active" = some w ∧ Enc.enc h a w) (fun a s => s.heap = h ∧ s.env "resolvedPhases" = some (.ref l0) ∧ s.env "age" = some (.num p1.val) ∧ ∃ w, s.env "active" = some w ∧ Enc.enc h a w) ?_ ?_ (fun _ _ hR => hR.1) harr0 ?_ ?_
  · refine ⟨rfl, ?_⟩
    simp [Env.put, Fn.env0, *]
    first | done | exact enc_at hf0 0
  · rintro s ⟨hh, e0, e1, w, hw, hwe⟩
    try simp only [enc_num] at hwe
    try subst hwe
    try simp only [enc_some] at hwe
    simp only [enc_src_phases_MonteCarloSpendingPhase] at hwe
    obtain ⟨lr, fsr, rfl, hlr, fr0, fr1, fr2, fr3⟩ := hwe
    simp only [enc_str] at fr0
    simp only [enc_str] at fr1
    simp only [enc_num] at fr3
    core_run
  · intro a s y hR hb
    simp at hb
    exact ⟨a, hb.symm, hR⟩
  · rintro q rest a s item y ⟨hh, e0, e1, w, hw, hwe⟩ hq hr
    try simp only [enc_num] at hwe
    try subst hwe
    simp only [enc_src_phases_MonteCarloSpendingPhase] at hq
    obtain ⟨lq, fsq, rfl, hlq, fq0, fq1, fq2, fq3⟩ := hq
    simp only [enc_str] at fq0
    simp only [enc_str] at fq1
    simp only [enc_num] at fq3
    dsimp only at hr
    shallow
    all_goals (try simp only [*, enc_none, enc_some, enc_num] at fq2)
    all_goals (try rcases fq2 with fq2 | fq2)
    all_goals core_run

theorem src_config_price_deriveAuctionPricing_bridge {h p0 v0 r}
    (h0 : Enc.enc h p0 v0)
    (hr : src.config.price.deriveAuctionPricing p0 = ok r) :
    WpRun prog src_config_price_deriveAuctionPricing [v0] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by
  simp only [enc_big] at h0
  subst h0
  all_goals unfold src.config.price.deriveAuctionPricing src.config.price.deriveAuctionTickSpacing src.constants.AUCTION_TICK_DIVISOR at hr
  all_goals apply wprun
  all_goals simp only [src_config_price_deriveAuctionPricing]
  all_goals try simp only [bind_ok, Aeneas.Std.bind_assoc] at hr
  all_goals shallow
  all_goals core_run
