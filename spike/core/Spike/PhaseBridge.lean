import Spike.Phase
open Core Aeneas Aeneas.Std Result
open src.phases Gen

instance : Enc MonteCarloSpendingPhase := ⟨fun h a v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧
  Enc.enc h a.id ((fs.lookup "id").getD .undef) ∧
  Enc.enc h a.name ((fs.lookup "name").getD .undef) ∧
  Enc.enc h a.fromAge ((fs.lookup "fromAge").getD .undef) ∧
  Enc.enc h a.annualWithdrawal ((fs.lookup "annualWithdrawal").getD .undef)⟩

@[simp] theorem put_same (e : Env) (x v) : (e.put x v) x = some v := by simp [Env.put]
theorem put_other (e : Env) {x y} (v) (h : y ≠ x) : (e.put x v) y = e y := by simp [Env.put, h]

theorem phase_bridge {h xs age vxs vage r}
    (hx : Enc.enc h xs vxs) (ha : Enc.enc h age vage)
    (hr : getActiveSpendingPhase xs age = ok r) :
    ∃ v s', Runs prog src_phases_getActiveSpendingPhase [vxs, vage] h v s' ∧ s'.heap = h ∧ Enc.enc h r v := by
  obtain ⟨l, vs, rfl, harr, hf⟩ := hx
  unfold getActiveSpendingPhase at hr
  simp only [bind_ok] at hr
  obtain ⟨a4, hl, hun⟩ := bind_ok_inv hr
  have ha4 : a4 = some r := by
    cases a4 with
    | none => simp [Js.unwrap] at hun
    | some x => simpa [Js.unwrap] using hun
  subst ha4
  let R : Option MonteCarloSpendingPhase → St → Prop := fun a s =>
    s.heap = h ∧ s.env "resolvedPhases" = some (.ref l) ∧ s.env "age" = some vage ∧
      ∃ w, s.env "active" = some w ∧ Enc.enc h a w
  let s0 : St := ⟨src_phases_getActiveSpendingPhase.env0 [.ref l, vage], h⟩
  have e0 : s0.env "resolvedPhases" = some (.ref l) := by
    simp [s0, src_phases_getActiveSpendingPhase, Fn.env0, Env.put]
  have e1 : s0.env "age" = some vage := by
    simp [s0, src_phases_getActiveSpendingPhase, Fn.env0, Env.put]
  -- active = resolvedPhases[0]
  let v0 : Val := if (0 : Int) < 0 then .undef else vs[(0 : Int).toNat]?.getD .undef
  have hset : Execs prog s0 (.set "active" (.index (.var "resolvedPhases") (.lit (.num 0)))) .normal
      { s0 with env := s0.env.put "active" v0 } :=
    Execs.set (Evals.index (xs := vs) (Evals.var e0) (Evals.lit _ _ _) rfl harr)
  let s1 : St := { s0 with env := s0.env.put "active" v0 }
  have hR0 : R (Js.at_ xs ⟨0, by decide, by decide⟩) s1 := by
    refine ⟨rfl, by simp [s1, Env.put, e0], by simp [s1, Env.put, e1], v0, by simp [s1, Env.put], ?_⟩
    simpa [Js.at_, v0] using enc_at hf 0
  -- the loop
  obtain ⟨sf, hit, hQ⟩ := sim_loop' (p := prog) (x := "phase") (l := l) (vs := vs) (i := 0)
    (body := src_phases_getActiveSpendingPhase_loop0) (h := h) hl (by simpa using hf) R R hR0
    (fun _ _ hR => hR.1) harr
    (by
      intro a s y hR hb
      simp at hb
      exact ⟨a, hb.symm, hR⟩)
    (by
      intro q rest a s item y hR hq hb
      obtain ⟨hh, r0, r1, w, hw, hwe⟩ := hR
      obtain ⟨lq, fs, rfl, hq1, hid, hname, hage, hmoney⟩ := hq
      let s2 : St := { s with env := s.env.put "phase" (.ref lq) }
      have hheap : s2.heap = h := hh
      have hphase : Evals prog s2 (.var "phase") (.ref lq) s2 := Evals.var (by simp [s2, Env.put])
      have hfield := Evals.field (k := "fromAge") hphase (by simp [readField, hheap, hq1]; rfl)
      have take : (∃ s', ExecsL prog s2 [.set "active" (.var "phase")] .normal s' ∧ R (some q) s') :=
        ⟨_, ExecsL.cons_normal (Execs.set hphase) (ExecsL.nil _ _),
          hh, by simp [s2, Env.put, r0], by simp [s2, Env.put, r1], .ref lq, by simp [s2, Env.put],
          lq, fs, rfl, hq1, hid, hname, hage, hmoney⟩
      cases hfa : q.fromAge with
      | none =>
        rw [hfa] at hage
        simp [hfa] at hb
        have hnull : nullish ((fs.lookup "fromAge").getD .undef) = true := by
          rcases hage with h | h <;> simp [h, nullish]
        obtain ⟨s', he, hR'⟩ := take
        refine Or.inl ⟨_, hb.symm, s', ?_, hR'⟩
        exact ExecsL.cons_exit' (Execs.ite_true (Evals.or_true (Evals.isNullish hfield) (by simp [hnull, truthy])) (by simp [hnull, truthy]) he) (ExecsL.nil _ _)
      | some t =>
        rw [hfa] at hage
        have hage' : (fs.lookup "fromAge").getD .undef = .num t.val := hage
        have hcmp := Evals.bin (op := .le) (Evals.field (k := "fromAge") hphase (by simp [readField, hheap, hq1]; rfl))
          (Evals.var (s := s2) (x := "age") (v := vage) (by simp [s2, Env.put, r1])) (r := .bool (decide (t.val ≤ age.val)))
          (by rw [hage', ha]; rfl)
        have hnn : nullish ((fs.lookup "fromAge").getD .undef) = false := by simp [hage', nullish]
        have hor := Evals.or_false (Evals.isNullish hfield) (by simp [hnn, truthy]) hcmp
        simp [hfa] at hb
        by_cases hle : t.val ≤ age.val
        · simp [hle] at hb
          obtain ⟨s', he, hR'⟩ := take
          refine Or.inl ⟨_, hb.symm, s', ?_, hR'⟩
          exact ExecsL.cons_exit' (Execs.ite_true hor (by simp [truthy, hle]) he) (ExecsL.nil _ _)
        · simp [hle] at hb
          refine Or.inr ⟨a, hb.symm, s2, ?_, hh, by simp [s2, Env.put, r0], by simp [s2, Env.put, r1], w, by simp [s2, Env.put, hw], hwe⟩
          exact ExecsL.cons_exit (Execs.ite_false hor (by simp [truthy, hle]) (ExecsL.cons_exit (Execs.brk _ _) (by simp))) (by simp))
  obtain ⟨hh, -, -, w, hw, hwe⟩ := hQ
  refine ⟨w, sf, Runs.of (ExecsL.cons_normal hset (ExecsL.cons_normal (Execs.forOf (Evals.var (by simp [s1, Env.put, e0])) hit)
    (ExecsL.cons_exit (Execs.ret (Evals.var hw)) (by simp)))), hh, hwe⟩
