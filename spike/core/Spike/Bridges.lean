import Spike.WP
open Core Aeneas Aeneas.Std Result Gen

attribute [simp] Gen.src_heldout_deriveAuctionOutcome
attribute [simp] Gen.prog

instance : Enc Proofci.Inline.R5763cf2dd2 := ⟨fun h a v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.isGraduated ((fs.lookup "isGraduated").getD .undef) ∧
  Enc.enc h a.endBlock ((fs.lookup "endBlock").getD .undef) ∧
  Enc.enc h a.currentBlock ((fs.lookup "currentBlock").getD .undef)⟩
@[simp] theorem enc_Proofci_Inline_R5763cf2dd2 {h} {a : Proofci.Inline.R5763cf2dd2} {v} : Enc.enc h a v ↔ ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.isGraduated ((fs.lookup "isGraduated").getD .undef) ∧
  Enc.enc h a.endBlock ((fs.lookup "endBlock").getD .undef) ∧
  Enc.enc h a.currentBlock ((fs.lookup "currentBlock").getD .undef) := Iff.rfl

theorem src_heldout_deriveAuctionOutcome_bridge {h p0 v0 r}
    (h0 : Enc.enc h p0 v0)
    (hr : src.heldout.deriveAuctionOutcome p0 = ok r) :
    WpRun prog src_heldout_deriveAuctionOutcome [v0] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by
  simp only [enc_Proofci_Inline_R5763cf2dd2] at h0
  obtain ⟨l0, fs0, rfl, hl0, f00, f01, f02⟩ := h0
  unfold src.heldout.deriveAuctionOutcome at hr
  apply wprun
  simp only [src_heldout_deriveAuctionOutcome]
  try simp only [bind_ok, Aeneas.Std.bind_assoc] at hr
  shallow
  all_goals core_run
