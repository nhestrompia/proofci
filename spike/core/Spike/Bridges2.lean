import Spike.Step
open Core Aeneas Aeneas.Std Result Gen
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem src_scale_joins160_bridge {h p0 r} (hr : src.scale.joins160 p0 = ok r) :
    WpRun prog src_scale_joins160 [.num (F64.ofInt p0.val)] h fun v s => s.heap = h ∧ Enc.enc s.heap r v := by
  unfold src.scale.joins160 at hr
  try simp (maxSteps := 50000000) only [bind_ok] at hr
  apply wprun
  have va : VarIs ⟨src_scale_joins160.env0 [.num (F64.ofInt p0.val)], h⟩ "a" p0 := by
    have hp : src_scale_joins160.params = ["a"] := rfl
    simp [VarIs, Fn.env0, hp, Env.put]
  have hh : (St.mk (src_scale_joins160.env0 [.num (F64.ofInt p0.val)]) h).heap = h := rfl
  generalize St.mk (src_scale_joins160.env0 [.num (F64.ofInt p0.val)]) h = s0 at va hh
  refine step_set (a := ⟨0, by decide, by decide⟩) (NumE.lit _ rfl) ?_
  intro s1 vt keeps1
  replace va := VarIs.keep keeps1 (by decide) va
  replace hh := keeps1.1.trans hh
  revert hr; refine Core.bind_intro ?_
  intro tj1 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj1) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s2 vt' keeps2
  replace va := VarIs.keep keeps2 (by decide) va
  replace hh := keeps2.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj2 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj2) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s3 vt' keeps3
  replace va := VarIs.keep keeps3 (by decide) va
  replace hh := keeps3.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj3 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj3) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s4 vt' keeps4
  replace va := VarIs.keep keeps4 (by decide) va
  replace hh := keeps4.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj4 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj4) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s5 vt' keeps5
  replace va := VarIs.keep keeps5 (by decide) va
  replace hh := keeps5.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj5 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj5) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s6 vt' keeps6
  replace va := VarIs.keep keeps6 (by decide) va
  replace hh := keeps6.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj6 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj6) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s7 vt' keeps7
  replace va := VarIs.keep keeps7 (by decide) va
  replace hh := keeps7.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj7 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj7) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s8 vt' keeps8
  replace va := VarIs.keep keeps8 (by decide) va
  replace hh := keeps8.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj8 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj8) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s9 vt' keeps9
  replace va := VarIs.keep keeps9 (by decide) va
  replace hh := keeps9.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj9 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj9) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s10 vt' keeps10
  replace va := VarIs.keep keeps10 (by decide) va
  replace hh := keeps10.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj10 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj10) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s11 vt' keeps11
  replace va := VarIs.keep keeps11 (by decide) va
  replace hh := keeps11.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj11 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj11) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s12 vt' keeps12
  replace va := VarIs.keep keeps12 (by decide) va
  replace hh := keeps12.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj12 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj12) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s13 vt' keeps13
  replace va := VarIs.keep keeps13 (by decide) va
  replace hh := keeps13.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj13 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj13) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s14 vt' keeps14
  replace va := VarIs.keep keeps14 (by decide) va
  replace hh := keeps14.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj14 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj14) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s15 vt' keeps15
  replace va := VarIs.keep keeps15 (by decide) va
  replace hh := keeps15.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj15 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj15) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s16 vt' keeps16
  replace va := VarIs.keep keeps16 (by decide) va
  replace hh := keeps16.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj16 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj16) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s17 vt' keeps17
  replace va := VarIs.keep keeps17 (by decide) va
  replace hh := keeps17.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj17 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj17) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s18 vt' keeps18
  replace va := VarIs.keep keeps18 (by decide) va
  replace hh := keeps18.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj18 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj18) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s19 vt' keeps19
  replace va := VarIs.keep keeps19 (by decide) va
  replace hh := keeps19.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj19 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj19) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s20 vt' keeps20
  replace va := VarIs.keep keeps20 (by decide) va
  replace hh := keeps20.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj20 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj20) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s21 vt' keeps21
  replace va := VarIs.keep keeps21 (by decide) va
  replace hh := keeps21.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj21 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj21) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s22 vt' keeps22
  replace va := VarIs.keep keeps22 (by decide) va
  replace hh := keeps22.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj22 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj22) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s23 vt' keeps23
  replace va := VarIs.keep keeps23 (by decide) va
  replace hh := keeps23.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj23 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj23) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s24 vt' keeps24
  replace va := VarIs.keep keeps24 (by decide) va
  replace hh := keeps24.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj24 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj24) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s25 vt' keeps25
  replace va := VarIs.keep keeps25 (by decide) va
  replace hh := keeps25.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj25 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj25) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s26 vt' keeps26
  replace va := VarIs.keep keeps26 (by decide) va
  replace hh := keeps26.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj26 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj26) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s27 vt' keeps27
  replace va := VarIs.keep keeps27 (by decide) va
  replace hh := keeps27.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj27 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj27) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s28 vt' keeps28
  replace va := VarIs.keep keeps28 (by decide) va
  replace hh := keeps28.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj28 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj28) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s29 vt' keeps29
  replace va := VarIs.keep keeps29 (by decide) va
  replace hh := keeps29.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj29 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj29) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s30 vt' keeps30
  replace va := VarIs.keep keeps30 (by decide) va
  replace hh := keeps30.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj30 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj30) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s31 vt' keeps31
  replace va := VarIs.keep keeps31 (by decide) va
  replace hh := keeps31.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj31 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj31) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s32 vt' keeps32
  replace va := VarIs.keep keeps32 (by decide) va
  replace hh := keeps32.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj32 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj32) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s33 vt' keeps33
  replace va := VarIs.keep keeps33 (by decide) va
  replace hh := keeps33.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj33 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj33) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s34 vt' keeps34
  replace va := VarIs.keep keeps34 (by decide) va
  replace hh := keeps34.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj34 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj34) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s35 vt' keeps35
  replace va := VarIs.keep keeps35 (by decide) va
  replace hh := keeps35.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj35 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj35) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s36 vt' keeps36
  replace va := VarIs.keep keeps36 (by decide) va
  replace hh := keeps36.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj36 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj36) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s37 vt' keeps37
  replace va := VarIs.keep keeps37 (by decide) va
  replace hh := keeps37.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj37 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj37) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s38 vt' keeps38
  replace va := VarIs.keep keeps38 (by decide) va
  replace hh := keeps38.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj38 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj38) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s39 vt' keeps39
  replace va := VarIs.keep keeps39 (by decide) va
  replace hh := keeps39.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj39 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj39) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s40 vt' keeps40
  replace va := VarIs.keep keeps40 (by decide) va
  replace hh := keeps40.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj40 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj40) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s41 vt' keeps41
  replace va := VarIs.keep keeps41 (by decide) va
  replace hh := keeps41.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj41 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj41) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s42 vt' keeps42
  replace va := VarIs.keep keeps42 (by decide) va
  replace hh := keeps42.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj42 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj42) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s43 vt' keeps43
  replace va := VarIs.keep keeps43 (by decide) va
  replace hh := keeps43.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj43 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj43) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s44 vt' keeps44
  replace va := VarIs.keep keeps44 (by decide) va
  replace hh := keeps44.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj44 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj44) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s45 vt' keeps45
  replace va := VarIs.keep keeps45 (by decide) va
  replace hh := keeps45.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj45 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj45) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s46 vt' keeps46
  replace va := VarIs.keep keeps46 (by decide) va
  replace hh := keeps46.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj46 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj46) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s47 vt' keeps47
  replace va := VarIs.keep keeps47 (by decide) va
  replace hh := keeps47.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj47 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj47) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s48 vt' keeps48
  replace va := VarIs.keep keeps48 (by decide) va
  replace hh := keeps48.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj48 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj48) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s49 vt' keeps49
  replace va := VarIs.keep keeps49 (by decide) va
  replace hh := keeps49.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj49 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj49) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s50 vt' keeps50
  replace va := VarIs.keep keeps50 (by decide) va
  replace hh := keeps50.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj50 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj50) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s51 vt' keeps51
  replace va := VarIs.keep keeps51 (by decide) va
  replace hh := keeps51.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj51 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj51) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s52 vt' keeps52
  replace va := VarIs.keep keeps52 (by decide) va
  replace hh := keeps52.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj52 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj52) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s53 vt' keeps53
  replace va := VarIs.keep keeps53 (by decide) va
  replace hh := keeps53.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj53 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj53) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s54 vt' keeps54
  replace va := VarIs.keep keeps54 (by decide) va
  replace hh := keeps54.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj54 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj54) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s55 vt' keeps55
  replace va := VarIs.keep keeps55 (by decide) va
  replace hh := keeps55.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj55 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj55) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s56 vt' keeps56
  replace va := VarIs.keep keeps56 (by decide) va
  replace hh := keeps56.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj56 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj56) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s57 vt' keeps57
  replace va := VarIs.keep keeps57 (by decide) va
  replace hh := keeps57.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj57 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj57) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s58 vt' keeps58
  replace va := VarIs.keep keeps58 (by decide) va
  replace hh := keeps58.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj58 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj58) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s59 vt' keeps59
  replace va := VarIs.keep keeps59 (by decide) va
  replace hh := keeps59.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj59 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj59) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s60 vt' keeps60
  replace va := VarIs.keep keeps60 (by decide) va
  replace hh := keeps60.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj60 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj60) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s61 vt' keeps61
  replace va := VarIs.keep keeps61 (by decide) va
  replace hh := keeps61.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj61 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj61) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s62 vt' keeps62
  replace va := VarIs.keep keeps62 (by decide) va
  replace hh := keeps62.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj62 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj62) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s63 vt' keeps63
  replace va := VarIs.keep keeps63 (by decide) va
  replace hh := keeps63.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj63 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj63) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s64 vt' keeps64
  replace va := VarIs.keep keeps64 (by decide) va
  replace hh := keeps64.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj64 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj64) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s65 vt' keeps65
  replace va := VarIs.keep keeps65 (by decide) va
  replace hh := keeps65.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj65 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj65) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s66 vt' keeps66
  replace va := VarIs.keep keeps66 (by decide) va
  replace hh := keeps66.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj66 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj66) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s67 vt' keeps67
  replace va := VarIs.keep keeps67 (by decide) va
  replace hh := keeps67.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj67 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj67) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s68 vt' keeps68
  replace va := VarIs.keep keeps68 (by decide) va
  replace hh := keeps68.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj68 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj68) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s69 vt' keeps69
  replace va := VarIs.keep keeps69 (by decide) va
  replace hh := keeps69.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj69 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj69) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s70 vt' keeps70
  replace va := VarIs.keep keeps70 (by decide) va
  replace hh := keeps70.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj70 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj70) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s71 vt' keeps71
  replace va := VarIs.keep keeps71 (by decide) va
  replace hh := keeps71.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj71 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj71) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s72 vt' keeps72
  replace va := VarIs.keep keeps72 (by decide) va
  replace hh := keeps72.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj72 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj72) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s73 vt' keeps73
  replace va := VarIs.keep keeps73 (by decide) va
  replace hh := keeps73.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj73 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj73) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s74 vt' keeps74
  replace va := VarIs.keep keeps74 (by decide) va
  replace hh := keeps74.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj74 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj74) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s75 vt' keeps75
  replace va := VarIs.keep keeps75 (by decide) va
  replace hh := keeps75.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj75 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj75) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s76 vt' keeps76
  replace va := VarIs.keep keeps76 (by decide) va
  replace hh := keeps76.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj76 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj76) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s77 vt' keeps77
  replace va := VarIs.keep keeps77 (by decide) va
  replace hh := keeps77.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj77 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj77) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s78 vt' keeps78
  replace va := VarIs.keep keeps78 (by decide) va
  replace hh := keeps78.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj78 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj78) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s79 vt' keeps79
  replace va := VarIs.keep keeps79 (by decide) va
  replace hh := keeps79.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj79 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj79) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s80 vt' keeps80
  replace va := VarIs.keep keeps80 (by decide) va
  replace hh := keeps80.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj80 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj80) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s81 vt' keeps81
  replace va := VarIs.keep keeps81 (by decide) va
  replace hh := keeps81.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj81 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj81) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s82 vt' keeps82
  replace va := VarIs.keep keeps82 (by decide) va
  replace hh := keeps82.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj82 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj82) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s83 vt' keeps83
  replace va := VarIs.keep keeps83 (by decide) va
  replace hh := keeps83.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj83 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj83) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s84 vt' keeps84
  replace va := VarIs.keep keeps84 (by decide) va
  replace hh := keeps84.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj84 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj84) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s85 vt' keeps85
  replace va := VarIs.keep keeps85 (by decide) va
  replace hh := keeps85.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj85 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj85) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s86 vt' keeps86
  replace va := VarIs.keep keeps86 (by decide) va
  replace hh := keeps86.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj86 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj86) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s87 vt' keeps87
  replace va := VarIs.keep keeps87 (by decide) va
  replace hh := keeps87.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj87 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj87) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s88 vt' keeps88
  replace va := VarIs.keep keeps88 (by decide) va
  replace hh := keeps88.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj88 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj88) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s89 vt' keeps89
  replace va := VarIs.keep keeps89 (by decide) va
  replace hh := keeps89.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj89 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj89) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s90 vt' keeps90
  replace va := VarIs.keep keeps90 (by decide) va
  replace hh := keeps90.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj90 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj90) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s91 vt' keeps91
  replace va := VarIs.keep keeps91 (by decide) va
  replace hh := keeps91.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj91 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj91) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s92 vt' keeps92
  replace va := VarIs.keep keeps92 (by decide) va
  replace hh := keeps92.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj92 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj92) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s93 vt' keeps93
  replace va := VarIs.keep keeps93 (by decide) va
  replace hh := keeps93.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj93 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj93) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s94 vt' keeps94
  replace va := VarIs.keep keeps94 (by decide) va
  replace hh := keeps94.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj94 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj94) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s95 vt' keeps95
  replace va := VarIs.keep keeps95 (by decide) va
  replace hh := keeps95.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj95 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj95) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s96 vt' keeps96
  replace va := VarIs.keep keeps96 (by decide) va
  replace hh := keeps96.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj96 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj96) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s97 vt' keeps97
  replace va := VarIs.keep keeps97 (by decide) va
  replace hh := keeps97.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj97 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj97) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s98 vt' keeps98
  replace va := VarIs.keep keeps98 (by decide) va
  replace hh := keeps98.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj98 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj98) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s99 vt' keeps99
  replace va := VarIs.keep keeps99 (by decide) va
  replace hh := keeps99.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj99 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj99) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s100 vt' keeps100
  replace va := VarIs.keep keeps100 (by decide) va
  replace hh := keeps100.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj100 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj100) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s101 vt' keeps101
  replace va := VarIs.keep keeps101 (by decide) va
  replace hh := keeps101.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj101 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj101) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s102 vt' keeps102
  replace va := VarIs.keep keeps102 (by decide) va
  replace hh := keeps102.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj102 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj102) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s103 vt' keeps103
  replace va := VarIs.keep keeps103 (by decide) va
  replace hh := keeps103.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj103 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj103) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s104 vt' keeps104
  replace va := VarIs.keep keeps104 (by decide) va
  replace hh := keeps104.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj104 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj104) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s105 vt' keeps105
  replace va := VarIs.keep keeps105 (by decide) va
  replace hh := keeps105.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj105 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj105) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s106 vt' keeps106
  replace va := VarIs.keep keeps106 (by decide) va
  replace hh := keeps106.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj106 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj106) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s107 vt' keeps107
  replace va := VarIs.keep keeps107 (by decide) va
  replace hh := keeps107.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj107 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj107) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s108 vt' keeps108
  replace va := VarIs.keep keeps108 (by decide) va
  replace hh := keeps108.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj108 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj108) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s109 vt' keeps109
  replace va := VarIs.keep keeps109 (by decide) va
  replace hh := keeps109.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj109 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj109) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s110 vt' keeps110
  replace va := VarIs.keep keeps110 (by decide) va
  replace hh := keeps110.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj110 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj110) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s111 vt' keeps111
  replace va := VarIs.keep keeps111 (by decide) va
  replace hh := keeps111.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj111 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj111) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s112 vt' keeps112
  replace va := VarIs.keep keeps112 (by decide) va
  replace hh := keeps112.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj112 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj112) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s113 vt' keeps113
  replace va := VarIs.keep keeps113 (by decide) va
  replace hh := keeps113.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj113 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj113) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s114 vt' keeps114
  replace va := VarIs.keep keeps114 (by decide) va
  replace hh := keeps114.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj114 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj114) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s115 vt' keeps115
  replace va := VarIs.keep keeps115 (by decide) va
  replace hh := keeps115.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj115 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj115) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s116 vt' keeps116
  replace va := VarIs.keep keeps116 (by decide) va
  replace hh := keeps116.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj116 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj116) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s117 vt' keeps117
  replace va := VarIs.keep keeps117 (by decide) va
  replace hh := keeps117.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj117 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj117) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s118 vt' keeps118
  replace va := VarIs.keep keeps118 (by decide) va
  replace hh := keeps118.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj118 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj118) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s119 vt' keeps119
  replace va := VarIs.keep keeps119 (by decide) va
  replace hh := keeps119.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj119 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj119) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s120 vt' keeps120
  replace va := VarIs.keep keeps120 (by decide) va
  replace hh := keeps120.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj120 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj120) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s121 vt' keeps121
  replace va := VarIs.keep keeps121 (by decide) va
  replace hh := keeps121.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj121 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj121) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s122 vt' keeps122
  replace va := VarIs.keep keeps122 (by decide) va
  replace hh := keeps122.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj122 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj122) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s123 vt' keeps123
  replace va := VarIs.keep keeps123 (by decide) va
  replace hh := keeps123.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj123 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj123) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s124 vt' keeps124
  replace va := VarIs.keep keeps124 (by decide) va
  replace hh := keeps124.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj124 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj124) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s125 vt' keeps125
  replace va := VarIs.keep keeps125 (by decide) va
  replace hh := keeps125.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj125 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj125) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s126 vt' keeps126
  replace va := VarIs.keep keeps126 (by decide) va
  replace hh := keeps126.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj126 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj126) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s127 vt' keeps127
  replace va := VarIs.keep keeps127 (by decide) va
  replace hh := keeps127.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj127 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj127) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s128 vt' keeps128
  replace va := VarIs.keep keeps128 (by decide) va
  replace hh := keeps128.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj128 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj128) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s129 vt' keeps129
  replace va := VarIs.keep keeps129 (by decide) va
  replace hh := keeps129.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj129 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj129) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s130 vt' keeps130
  replace va := VarIs.keep keeps130 (by decide) va
  replace hh := keeps130.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj130 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj130) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s131 vt' keeps131
  replace va := VarIs.keep keeps131 (by decide) va
  replace hh := keeps131.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj131 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj131) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s132 vt' keeps132
  replace va := VarIs.keep keeps132 (by decide) va
  replace hh := keeps132.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj132 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj132) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s133 vt' keeps133
  replace va := VarIs.keep keeps133 (by decide) va
  replace hh := keeps133.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj133 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj133) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s134 vt' keeps134
  replace va := VarIs.keep keeps134 (by decide) va
  replace hh := keeps134.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj134 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj134) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s135 vt' keeps135
  replace va := VarIs.keep keeps135 (by decide) va
  replace hh := keeps135.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj135 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj135) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s136 vt' keeps136
  replace va := VarIs.keep keeps136 (by decide) va
  replace hh := keeps136.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj136 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj136) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s137 vt' keeps137
  replace va := VarIs.keep keeps137 (by decide) va
  replace hh := keeps137.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj137 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj137) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s138 vt' keeps138
  replace va := VarIs.keep keeps138 (by decide) va
  replace hh := keeps138.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj138 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj138) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s139 vt' keeps139
  replace va := VarIs.keep keeps139 (by decide) va
  replace hh := keeps139.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj139 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj139) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s140 vt' keeps140
  replace va := VarIs.keep keeps140 (by decide) va
  replace hh := keeps140.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj140 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj140) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s141 vt' keeps141
  replace va := VarIs.keep keeps141 (by decide) va
  replace hh := keeps141.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj141 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj141) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s142 vt' keeps142
  replace va := VarIs.keep keeps142 (by decide) va
  replace hh := keeps142.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj142 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj142) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s143 vt' keeps143
  replace va := VarIs.keep keeps143 (by decide) va
  replace hh := keeps143.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj143 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj143) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s144 vt' keeps144
  replace va := VarIs.keep keeps144 (by decide) va
  replace hh := keeps144.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj144 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj144) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s145 vt' keeps145
  replace va := VarIs.keep keeps145 (by decide) va
  replace hh := keeps145.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj145 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj145) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s146 vt' keeps146
  replace va := VarIs.keep keeps146 (by decide) va
  replace hh := keeps146.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj146 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj146) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s147 vt' keeps147
  replace va := VarIs.keep keeps147 (by decide) va
  replace hh := keeps147.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj147 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj147) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s148 vt' keeps148
  replace va := VarIs.keep keeps148 (by decide) va
  replace hh := keeps148.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj148 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj148) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s149 vt' keeps149
  replace va := VarIs.keep keeps149 (by decide) va
  replace hh := keeps149.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj149 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj149) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s150 vt' keeps150
  replace va := VarIs.keep keeps150 (by decide) va
  replace hh := keeps150.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj150 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj150) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s151 vt' keeps151
  replace va := VarIs.keep keeps151 (by decide) va
  replace hh := keeps151.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj151 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj151) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s152 vt' keeps152
  replace va := VarIs.keep keeps152 (by decide) va
  replace hh := keeps152.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj152 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj152) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s153 vt' keeps153
  replace va := VarIs.keep keeps153 (by decide) va
  replace hh := keeps153.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj153 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj153) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s154 vt' keeps154
  replace va := VarIs.keep keeps154 (by decide) va
  replace hh := keeps154.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj154 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj154) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s155 vt' keeps155
  replace va := VarIs.keep keeps155 (by decide) va
  replace hh := keeps155.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj155 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj155) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s156 vt' keeps156
  replace va := VarIs.keep keeps156 (by decide) va
  replace hh := keeps156.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj156 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj156) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s157 vt' keeps157
  replace va := VarIs.keep keeps157 (by decide) va
  replace hh := keeps157.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj157 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj157) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s158 vt' keeps158
  replace va := VarIs.keep keeps158 (by decide) va
  replace hh := keeps158.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj158 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj158) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s159 vt' keeps159
  replace va := VarIs.keep keeps159 (by decide) va
  replace hh := keeps159.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj159 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj159) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s160 vt' keeps160
  replace va := VarIs.keep keeps160 (by decide) va
  replace hh := keeps160.1.trans hh
  clear vt hj
  rename' vt' => vt
  revert hr; refine Core.bind_intro ?_
  intro tj160 hj hr
  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := tj160) ?_ ?_ vt ?_
  · intro hp; rw [if_pos hp] at hj
    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)
  · intro hn; rw [if_neg hn] at hj
    exact (Result.ok_injective hj).symm
  intro s161 vt' keeps161
  replace va := VarIs.keep keeps161 (by decide) va
  replace hh := keeps161.1.trans hh
  clear vt hj
  rename' vt' => vt
  have := Result.ok_injective hr; subst this
  exact step_ret (NumE.var vt) ⟨_, rfl, hh, rfl⟩
