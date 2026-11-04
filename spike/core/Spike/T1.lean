import Spike.WP
open Core Aeneas Aeneas.Std Result
open src.ledger Gen

instance : Enc Accounts := ⟨fun h a v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.from ((fs.lookup "from").getD .undef) ∧
  Enc.enc h a.to ((fs.lookup "to").getD .undef)⟩
@[simp] theorem enc_Accounts {h} {a : Accounts} {v} : Enc.enc h a v ↔ ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.from ((fs.lookup "from").getD .undef) ∧ Enc.enc h a.to ((fs.lookup "to").getD .undef) := Iff.rfl

theorem transfer_bridge {h a amt va vamt r} (ha : Enc.enc h a va) (hn : Enc.enc h amt vamt)
    (hr : transfer a amt = ok r) :
    WpRun prog src_ledger_transfer [va, vamt] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by
  simp only [enc_Accounts, enc_num] at ha hn
  obtain ⟨l, fs, rfl, hl, h1, h2⟩ := ha
  subst hn
  unfold transfer at hr
  apply wprun
  simp only [src_ledger_transfer]
  shallow
  all_goals core_debug
  all_goals trace_state
  all_goals sorry
