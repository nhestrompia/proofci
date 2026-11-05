import Spike.WP
set_option maxHeartbeats 0
set_option maxRecDepth 200000
open Core Aeneas Aeneas.Std Result Gen

attribute [simp] Gen.src_scale_joins6
attribute [simp] Gen.prog





theorem src_scale_joins6_bridge {h p0 v0 r}
    (h0 : Enc.enc h p0 v0)
    (hr : src.scale.joins6 p0 = ok r) :
    WpRun prog src_scale_joins6 [v0] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by
  simp only [enc_num] at h0
  subst h0
  all_goals unfold src.scale.joins6 at hr
  all_goals apply wprun
  all_goals simp only [src_scale_joins6]
  all_goals try simp only [bind_ok, Aeneas.Std.bind_assoc] at hr
  all_goals shallow
  all_goals core_run
