import Spike.WP
open Core Aeneas Aeneas.Std Result

/-! Scaling the bridge. `core_run` simplifies the whole remaining program at every step,
so its cost grows much faster than the function. Here each statement is a closed step:
the state is an abstract `s` described by facts about live variables, so a step only
sees one statement. -/
namespace Core

/-- Variable `x` holds the number `a`. -/
def VarIs (s : St) (x : String) (a : Js.Num) : Prop := s.env x = some (.num (F64.ofInt a.val))

/-- `e` evaluates to the number `a`, without changing anything. -/
def NumE (p : Prog) (s : St) (e : Expr) (a : Js.Num) : Prop := Evals p s e (.num (F64.ofInt a.val)) s

/-- `e` is truthy exactly when `c` holds, without changing anything. -/
def SimB (p : Prog) (s : St) (e : Expr) (c : Prop) [Decidable c] : Prop :=
  ∃ v, Evals p s e v s ∧ truthy v = decide c

theorem NumE.var {p s x a} (h : VarIs s x a) : NumE p s (.var x) a := Evals.var h
theorem NumE.lit {p s} (a : Js.Num) {n : Int} (h : a.val = n) : NumE p s (.lit (.num (F64.ofInt n))) a := by
  subst h; exact Evals.lit _ _ _
theorem NumE.add {p s x y a b r} (hx : NumE p s x a) (hy : NumE p s y b) (h : Js.add a b = ok r) :
    NumE p s (.bin .add x y) r := by
  have hv := add_val h
  refine Evals.bin hx hy ?_
  have hlo : -9007199254740991 ≤ a.val + b.val := hv ▸ r.lo
  have hhi : a.val + b.val ≤ 9007199254740991 := hv ▸ r.hi
  simp only [binary, F64.add_ofInt hlo hhi, hv]

theorem SimB.gt {p s x y a b} (hx : NumE p s x a) (hy : NumE p s y b) :
    SimB p s (.bin .gt x y) (a.val > b.val) :=
  ⟨_, Evals.bin hx hy rfl, by simp [truthy]⟩
theorem SimB.eq {p s x y a b} (hx : NumE p s x a) (hy : NumE p s y b) :
    SimB p s (.bin .eq x y) (a.val = b.val) :=
  ⟨_, Evals.bin hx hy rfl, by simp [truthy]⟩

theorem SimB.gt_lit {p s x a} {n : Int} (hx : NumE p s x a) :
    SimB p s (.bin .gt x (.lit (.num (F64.ofInt n)))) (a.val > n) :=
  ⟨_, Evals.bin hx (Evals.lit _ _ _) rfl, by simp [truthy]⟩
theorem SimB.eq_lit {p s x a} {n : Int} (hx : NumE p s x a) :
    SimB p s (.bin .eq x (.lit (.num (F64.ofInt n)))) (a.val = n) :=
  ⟨_, Evals.bin hx (Evals.lit _ _ _) rfl, by simp [truthy]⟩

/-- What a step leaves true of the other variables. -/
def Keeps (s s' : St) (x : String) : Prop := s'.heap = s.heap ∧ ∀ y, y ≠ x → s'.env y = s.env y

theorem VarIs.keep {s s' x y a} (hk : Keeps s s' x) (hne : y ≠ x) (h : VarIs s y a) : VarIs s' y a := by
  unfold VarIs at *; rw [hk.2 y hne]; exact h

theorem step_set {p s x e a cs Φ} (he : NumE p s e a)
    (k : ∀ s', VarIs s' x a → Keeps s s' x → Wp p s' cs Φ) : Wp p s (.set x e :: cs) Φ := by
  obtain ⟨r, s₂, ht, hΦ⟩ := k { s with env := s.env.put x (.num (F64.ofInt a.val)) } (by simp [VarIs, Env.put])
    ⟨rfl, fun y hy => by simp [Env.put, hy]⟩
  exact ⟨r, s₂, ExecsL.cons_normal (Execs.set he) ht, hΦ⟩

/-- `if (c) { x = e }`, with the two sides joined into one value, so paths don't multiply. -/
theorem step_join {p s x c e cs Φ} {P : Prop} [Decidable P] {a old : Js.Num}
    (hc : SimB p s c P) (he : P → NumE p s e a) (hold : VarIs s x old)
    (k : ∀ s', VarIs s' x (if P then a else old) → Keeps s s' x → Wp p s' cs Φ) :
    Wp p s (.ite c [.set x e] [] :: cs) Φ := by
  obtain ⟨v, hv, ht⟩ := hc
  by_cases hp : P
  · have hset := Execs.set (x := x) (he hp)
    have hk := k { s with env := s.env.put x (.num (F64.ofInt a.val)) }
      (by simp [VarIs, Env.put, hp]) ⟨rfl, fun y hy => by simp [Env.put, hy]⟩
    obtain ⟨r, s₂, hrest, hΦ⟩ := hk
    exact ⟨r, s₂, ExecsL.cons_normal (Execs.ite_true hv (by simp [ht, hp])
      (ExecsL.cons_normal hset (ExecsL.nil _ _))) hrest, hΦ⟩
  · have hk := k s (by simpa [hp] using hold) ⟨rfl, fun _ _ => rfl⟩
    obtain ⟨r, s₂, hrest, hΦ⟩ := hk
    exact ⟨r, s₂, ExecsL.cons_normal (Execs.ite_false hv (by simp [ht, hp]) (ExecsL.nil _ _)) hrest, hΦ⟩

/-- The same join, stated for the value the typed view computed. -/
theorem step_join' {p s x c e cs Φ} {P : Prop} [Decidable P] {tj old : Js.Num}
    (hc : SimB p s c P) (hp : P → NumE p s e tj) (hn : ¬P → tj = old) (hold : VarIs s x old)
    (k : ∀ s', VarIs s' x tj → Keeps s s' x → Wp p s' cs Φ) :
    Wp p s (.ite c [.set x e] [] :: cs) Φ := by
  refine step_join (a := tj) hc hp hold fun s' hv hk' => k s' ?_ hk'
  by_cases h : P
  · simpa [h] using hv
  · rw [hn h]; simpa [h] using hv

/-- Splits only the outermost `if`, so a long chain costs one step per link. -/
theorem ite_intro {α : Type} {c : Prop} [Decidable c] {a b r : Result α} {G : Prop}
    (t : c → a = r → G) (f : ¬c → b = r → G) : (if c then a else b) = r → G := by
  by_cases h : c
  · simp only [h, ite_true]; exact t h
  · simp only [h, ite_false]; exact f h

theorem step_exit_true {p s c e cs t v Φ} {P : Prop} [Decidable P] (hc : SimB p s c P) (hp : P)
    (he : Evals p s e v s) (ho : Φ (.ret v) s) (ht : t = [.ret e]) : Wp p s (.ite c t [] :: cs) Φ := by
  subst ht
  obtain ⟨w, hw, hb⟩ := hc
  exact ⟨_, _, ExecsL.cons_exit (Execs.ite_true hw (by simp [hb, hp])
    (ExecsL.cons_exit (Execs.ret he) (by simp))) (by simp), ho⟩

theorem step_exit_false {p s c t cs Φ} {P : Prop} [Decidable P] (hc : SimB p s c P) (hp : ¬P)
    (k : Wp p s cs Φ) : Wp p s (.ite c t [] :: cs) Φ := by
  obtain ⟨w, hw, hb⟩ := hc
  obtain ⟨r, s₂, hrest, hΦ⟩ := k
  exact ⟨r, s₂, ExecsL.cons_normal (Execs.ite_false hw (by simp [hb, hp]) (ExecsL.nil _ _)) hrest, hΦ⟩

theorem step_ret {p s e a Φ cs} (he : NumE p s e a) (ho : Φ (.ret (.num (F64.ofInt a.val))) s) :
    Wp p s (.ret e :: cs) Φ :=
  ⟨_, _, ExecsL.cons_exit (Execs.ret he) (by simp), ho⟩

end Core
