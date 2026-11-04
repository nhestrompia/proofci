import Spike.Phase
open Core Aeneas Aeneas.Std Result

/-! The bridge without hand-written steps. Each rule says what must hold after a step,
so nobody names intermediate states, and symbolic execution is one tactic. -/
namespace Core

def WpE (p : Prog) (s : St) (e : Expr) (Ψ : Val → St → Prop) : Prop := ∃ v s', Evals p s e v s' ∧ Ψ v s'
def WpF (p : Prog) (s : St) (e : List (String × Expr)) (Ψ : List (String × Val) → St → Prop) : Prop :=
  ∃ v s', EvalsF p s e v s' ∧ Ψ v s'
def WpA (p : Prog) (s : St) (e : List Expr) (Ψ : List Val → St → Prop) : Prop := ∃ v s', EvalsL p s e v s' ∧ Ψ v s'
def WpS (p : Prog) (s : St) (c : Stmt) (Φ : Cmp → St → Prop) : Prop := ∃ r s', Execs p s c r s' ∧ Φ r s'
def Wp (p : Prog) (s : St) (c : List Stmt) (Φ : Cmp → St → Prop) : Prop := ∃ r s', ExecsL p s c r s' ∧ Φ r s'
def WpIter (p : Prog) (x : String) (v : Val) (i : Nat) (b : List Stmt) (s : St) (Ψ : St → Prop) : Prop :=
  ∃ s', Iterates p x v i b s .normal s' ∧ Ψ s'
def WpRun (p : Prog) (fn : Fn) (a : List Val) (h : Heap) (Ψ : Val → St → Prop) : Prop :=
  ∃ v s', Runs p fn a h v s' ∧ Ψ v s'

theorem wpe_lit {p s v Ψ} (h : Ψ v s) : WpE p s (.lit v) Ψ := ⟨_, _, Evals.lit _ _ _, h⟩
theorem wpe_var {p s x Ψ} (h : match s.env x with | some v => Ψ v s | none => False) : WpE p s (.var x) Ψ := by
  cases hx : s.env x with
  | some v => rw [hx] at h; exact ⟨_, _, Evals.var hx, h⟩
  | none => rw [hx] at h; exact h.elim
theorem wpe_field {p s o k Ψ}
    (h : WpE p s o fun v s' => match readField s'.heap v k with | some r => Ψ r s' | none => False) :
    WpE p s (.field o k) Ψ := by
  obtain ⟨v, s', he, hr⟩ := h
  cases hx : readField s'.heap v k with
  | some r => rw [hx] at hr; exact ⟨_, _, Evals.field he hx, hr⟩
  | none => rw [hx] at hr; exact hr.elim
theorem wpe_bin {p s op a b Ψ}
    (h : WpE p s a fun x s₁ => WpE p s₁ b fun y s₂ => match binary op x y with | some r => Ψ r s₂ | none => False) :
    WpE p s (.bin op a b) Ψ := by
  obtain ⟨x, s₁, ha, y, s₂, hb, hr⟩ := h
  cases hx : binary op x y with
  | some r => rw [hx] at hr; exact ⟨_, _, Evals.bin ha hb hx, hr⟩
  | none => rw [hx] at hr; exact hr.elim
theorem wpe_isNullish {p s a Ψ} (h : WpE p s a fun v s' => Ψ (.bool (nullish v)) s') : WpE p s (.isNullish a) Ψ := by
  obtain ⟨v, s', he, hr⟩ := h; exact ⟨_, _, Evals.isNullish he, hr⟩
theorem wpe_not {p s a Ψ} (h : WpE p s a fun v s' => Ψ (.bool (!truthy v)) s') : WpE p s (.not a) Ψ := by
  obtain ⟨v, s', he, hr⟩ := h; exact ⟨_, _, Evals.not he, hr⟩
theorem wpe_or {p s a b Ψ}
    (h : WpE p s a fun v s' => if truthy v then Ψ v s' else WpE p s' b Ψ) : WpE p s (.or a b) Ψ := by
  obtain ⟨v, s', he, hk⟩ := h
  cases ht : truthy v
  · simp only [ht, Bool.false_eq_true, if_false] at hk
    obtain ⟨w, s₂, hb, hr⟩ := hk
    exact ⟨_, _, Evals.or_false he ht hb, hr⟩
  · simp only [ht, if_true] at hk
    exact ⟨_, _, Evals.or_true he ht, hk⟩
theorem wpe_and {p s a b Ψ}
    (h : WpE p s a fun v s' => if truthy v then WpE p s' b Ψ else Ψ v s') : WpE p s (.and a b) Ψ := by
  obtain ⟨v, s', he, hk⟩ := h
  cases ht : truthy v
  · simp only [ht, Bool.false_eq_true, if_false] at hk
    exact ⟨_, _, Evals.and_false he ht, hk⟩
  · simp only [ht, if_true] at hk
    obtain ⟨w, s₂, hb, hr⟩ := hk
    exact ⟨_, _, Evals.and_true he ht hb, hr⟩
theorem wpe_cond {p s c a b Ψ}
    (h : WpE p s c fun v s' => if truthy v then WpE p s' a Ψ else WpE p s' b Ψ) : WpE p s (.cond c a b) Ψ := by
  obtain ⟨v, s', he, hk⟩ := h
  cases ht : truthy v
  · simp only [ht, Bool.false_eq_true, if_false] at hk
    obtain ⟨w, s₂, hb, hr⟩ := hk
    exact ⟨_, _, Evals.cond_false he ht hb, hr⟩
  · simp only [ht, if_true] at hk
    obtain ⟨w, s₂, hb, hr⟩ := hk
    exact ⟨_, _, Evals.cond_true he ht hb, hr⟩
theorem wpe_index {p s o i Ψ}
    (h : WpE p s o fun v s₁ => WpE p s₁ i fun n s₂ => ∃ l xs m, v = .ref l ∧ n = .num m ∧
      s₂.heap[l]? = some (.array xs) ∧ Ψ (if m < 0 then .undef else xs[m.toNat]?.getD .undef) s₂) :
    WpE p s (.index o i) Ψ := by
  obtain ⟨v, s₁, ho, n, s₂, hi, l, xs, m, rfl, rfl, hl, hr⟩ := h
  exact ⟨_, _, Evals.index ho hi rfl hl, hr⟩
theorem wpe_length {p s o Ψ}
    (h : WpE p s o fun v s' => ∃ l xs, v = .ref l ∧ s'.heap[l]? = some (.array xs) ∧ Ψ (.num xs.length) s') :
    WpE p s (.length o) Ψ := by
  obtain ⟨v, s', he, l, xs, rfl, hl, hr⟩ := h
  exact ⟨_, _, Evals.length he hl, hr⟩
theorem wpf_nil {p s Ψ} (h : Ψ [] s) : WpF p s [] Ψ := ⟨_, _, EvalsF.nil _ _, h⟩
theorem wpf_cons {p s k e es Ψ}
    (h : WpE p s e fun v s₁ => WpF p s₁ es fun vs s₂ => Ψ ((k, v) :: vs) s₂) : WpF p s ((k, e) :: es) Ψ := by
  obtain ⟨v, s₁, he, vs, s₂, ht, hr⟩ := h; exact ⟨_, _, EvalsF.cons he ht, hr⟩
theorem wpa_nil {p s Ψ} (h : Ψ [] s) : WpA p s [] Ψ := ⟨_, _, EvalsL.nil _ _, h⟩
theorem wpa_cons {p s e es Ψ}
    (h : WpE p s e fun v s₁ => WpA p s₁ es fun vs s₂ => Ψ (v :: vs) s₂) : WpA p s (e :: es) Ψ := by
  obtain ⟨v, s₁, he, vs, s₂, ht, hr⟩ := h; exact ⟨_, _, EvalsL.cons he ht, hr⟩
theorem wpe_record {p s es Ψ}
    (h : WpF p s es fun vs s' => Ψ (.ref s'.heap.length) { s' with heap := s'.heap ++ [.record vs] }) :
    WpE p s (.record es) Ψ := by
  obtain ⟨vs, s', he, hr⟩ := h; exact ⟨_, _, Evals.record he, hr⟩
theorem wpe_call {p s g args fn Ψ} (hg : p g = some fn)
    (h : WpA p s args fun vs s₁ => WpRun p fn vs s₁.heap fun v s₂ => Ψ v { s₁ with heap := s₂.heap }) :
    WpE p s (.call g args) Ψ := by
  obtain ⟨vs, s₁, ha, v, s₂, hr, hk⟩ := h; exact ⟨_, _, Evals.call ha hg hr, hk⟩
theorem wpe_call' {p s g args Ψ}
    (h : match p g with
      | some fn => WpA p s args fun vs s₁ => WpRun p fn vs s₁.heap fun v s₂ => Ψ v { s₁ with heap := s₂.heap }
      | none => False) : WpE p s (.call g args) Ψ := by
  cases hg : p g with
  | some fn => rw [hg] at h; exact wpe_call hg h
  | none => rw [hg] at h; exact h.elim
theorem wprun {p fn a h Ψ}
    (hb : Wp p ⟨fn.env0 a, h⟩ fn.body fun c s => ∃ v, c = .ret v ∧ Ψ v s) : WpRun p fn a h Ψ := by
  obtain ⟨c, s', he, v, rfl, hr⟩ := hb; exact ⟨_, _, Runs.of he, hr⟩

/-- A function that ends without `return` gives `undefined`. -/
theorem wprun_void {p fn a h Ψ}
    (hb : Wp p ⟨fn.env0 a, h⟩ fn.body fun c s => c = .normal ∧ Ψ .undef s) : WpRun p fn a h Ψ := by
  obtain ⟨c, s', ⟨F, hF⟩, rfl, hr⟩ := hb
  refine ⟨_, s', ⟨F + 1, fun f hf => ?_⟩, hr⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  simp only [run]
  have := hF g hg
  simp only [Fn.env0] at this
  simp only [this]

theorem wps_set {p s x e Φ} (h : WpE p s e fun v s' => Φ .normal { s' with env := s'.env.put x v }) :
    WpS p s (.set x e) Φ := by
  obtain ⟨v, s', he, hr⟩ := h; exact ⟨_, _, Execs.set he, hr⟩
theorem wps_ret {p s e Φ} (h : WpE p s e fun v s' => Φ (.ret v) s') : WpS p s (.ret e) Φ := by
  obtain ⟨v, s', he, hr⟩ := h; exact ⟨_, _, Execs.ret he, hr⟩
theorem wps_brk {p s Φ} (h : Φ .brk s) : WpS p s .brk Φ := ⟨_, _, Execs.brk _ _, h⟩
theorem wps_ite {p s c t e Φ}
    (h : WpE p s c fun v s' => if truthy v then Wp p s' t Φ else Wp p s' e Φ) : WpS p s (.ite c t e) Φ := by
  obtain ⟨v, s', he, hk⟩ := h
  cases ht : truthy v
  · simp only [ht, Bool.false_eq_true, if_false] at hk
    obtain ⟨r, s₂, hb, hr⟩ := hk
    exact ⟨_, _, Execs.ite_false he ht hb, hr⟩
  · simp only [ht, if_true] at hk
    obtain ⟨r, s₂, hb, hr⟩ := hk
    exact ⟨_, _, Execs.ite_true he ht hb, hr⟩
theorem wps_setField {p s o k e Φ}
    (h : WpE p s o fun ov s₁ => WpE p s₁ e fun v s₂ => ∃ l fs, ov = .ref l ∧ s₂.heap[l]? = some (.record fs) ∧
      Φ .normal { s₂ with heap := s₂.heap.set l (.record ((k, v) :: fs.filter (·.1 != k))) }) :
    WpS p s (.setField o k e) Φ := by
  obtain ⟨ov, s₁, ho, v, s₂, he, l, fs, rfl, hl, hk⟩ := h
  exact ⟨_, _, Execs.setField ho he hl, hk⟩
theorem wps_forOf {p s x e body Φ}
    (h : WpE p s e fun v s₁ => WpIter p x v 0 body s₁ fun s₂ => Φ .normal s₂) : WpS p s (.forOf x e body) Φ := by
  obtain ⟨v, s₁, he, s₂, hi, hk⟩ := h; exact ⟨_, _, Execs.forOf he hi, hk⟩
theorem wp_nil {p s Φ} (h : Φ .normal s) : Wp p s [] Φ := ⟨_, _, ExecsL.nil _ _, h⟩
theorem wp_cons {p s c cs Φ}
    (h : WpS p s c fun r s' => if r = .normal then Wp p s' cs Φ else Φ r s') : Wp p s (c :: cs) Φ := by
  obtain ⟨r, s₁, he, hk⟩ := h
  by_cases hr : r = .normal
  · subst hr
    simp only [if_true] at hk
    obtain ⟨r', s₂, ht, hk'⟩ := hk
    exact ⟨_, _, ExecsL.cons_normal he ht, hk'⟩
  · simp only [hr, if_false] at hk
    exact ⟨_, _, ExecsL.cons_exit he hr, hk⟩

/-- The loop rule. Its inputs are the invariant `R` and one simulated turn of the body. -/
theorem wp_loop {T σ β : Type} [Enc T] {p x l vs body h}
    {B : List T × σ → Result (ControlFlow (List T × σ) β)}
    (R : σ → St → Prop) (Q : β → St → Prop)
    (hheap : ∀ a s, R a s → s.heap = h)
    (harr : h[l]? = some (.array vs))
    (hnil : ∀ a s y, R a s → B ([], a) = ok y → ∃ r, y = .done r ∧ Q r s)
    (hcons : ∀ q rest a s item y, R a s → Enc.enc h q item → B (q :: rest, a) = ok y →
      Wp p { s with env := s.env.put x item } body fun c s' =>
        (c = .normal ∧ ∃ a', y = .cont (rest, a') ∧ R a' s') ∨ (c = .brk ∧ ∃ r, y = .done r ∧ Q r s')) :
    ∀ (rest : List T) i a s r, List.Forall₂ (Enc.enc h) rest (vs.drop i) → R a s → loop B (rest, a) = ok r →
      WpIter p x (.ref l) i body s (Q r) := by
  intro rest i a s r hf hR hl
  obtain ⟨s', hi, hq⟩ := sim_loop (p := p) (x := x) (body := body) B R Q hheap harr hnil (by
    intro q rest a s item y hR hq hb
    obtain ⟨c, s', he, ⟨rfl, a', hy, hR'⟩ | ⟨rfl, r, hy, hQ⟩⟩ := hcons q rest a s item y hR hq hb
    · exact Or.inl ⟨a', hy, s', he, hR'⟩
    · exact Or.inr ⟨r, hy, s', he, hQ⟩) rest i a s r hf hR hl
  exact ⟨s', hi, hq⟩

@[simp] theorem put_same (e : Env) (x v) : (e.put x v) x = some v := by simp [Env.put]

end Core

namespace Core

@[simp] theorem enc_num {h} {a : Js.Num} {v} : Enc.enc h a v ↔ v = .num a.val := Iff.rfl
@[simp] theorem enc_big {h} {a : Int} {v} : Enc.enc h a v ↔ v = .big a := Iff.rfl
@[simp] theorem enc_bool {h} {a : Bool} {v} : Enc.enc h a v ↔ v = .bool a := Iff.rfl
@[simp] theorem enc_some {α} [Enc α] {h} {a : α} {v} : Enc.enc h (some a) v ↔ Enc.enc h a v := Iff.rfl
@[simp] theorem enc_none {α} [Enc α] {h} {v} : Enc.enc h (none : Option α) v ↔ v = .undef ∨ v = .null := Iff.rfl

@[simp] theorem enc_str {h} {a : List Nat} {v} : Enc.enc h a v ↔ v = .str a := Iff.rfl
@[simp] theorem enc_list {α} [Enc α] {h} {a : List α} {v} : Enc.enc h a v ↔ EncArray h a v := Iff.rfl

theorem strLt_eq (a b : List Nat) : strLt a b = Js.strLt a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      by_cases hxy : x = y
      · subst hxy; simp [strLt, Js.strLt, ih]
      · simp [strLt, Js.strLt, hxy]

theorem add_val {x y r : Js.Num} (h : Js.add x y = ok r) : r.val = x.val + y.val := by
  simp only [Js.add, Js.mk] at h; split at h <;> simp_all; subst h; rfl
theorem sub_val {x y r : Js.Num} (h : Js.sub x y = ok r) : r.val = x.val - y.val := by
  simp only [Js.sub, Js.mk] at h; split at h <;> simp_all; subst h; rfl
theorem mul_val {x y r : Js.Num} (h : Js.mul x y = ok r) : r.val = x.val * y.val := by
  simp only [Js.mul, Js.mk] at h; split at h <;> simp_all; subst h; rfl
theorem bdiv_val {x y r : Int} (h : Js.bdiv x y = ok r) : y ≠ 0 ∧ r = x.tdiv y := by
  simp only [Js.bdiv] at h; split at h <;> simp_all
theorem brem_val {x y r : Int} (h : Js.brem x y = ok r) : y ≠ 0 ∧ r = x.tmod y := by
  simp only [Js.brem] at h; split at h <;> simp_all
theorem unwrap_val {α} {x : Option α} {r : α} (h : Js.unwrap x = ok r) : x = some r := by
  cases x <;> simp_all [Js.unwrap]

theorem bind_intro {α β : Type} {G : Prop} {x : Result α} {f : α → Result β} {r : β}
    (k : ∀ a, x = ok a → f a = ok r → G) : Aeneas.Std.bind x f = ok r → G := by
  intro h
  obtain ⟨a, ha, hf⟩ := bind_ok_inv h
  exact k a ha hf

theorem ok_intro {α : Type} {G : Prop} {a b : α} (k : a = b → G) : (ok a : Result α) = ok b → G :=
  fun h => k (Result.ok_injective h)

theorem len_intro {α : Type} {G : Prop} {xs : List α} {r : Js.Num} (k : r.val = xs.length → G) :
    Js.len xs = ok r → G := fun h => k (by
  simp only [Js.len, Js.mk] at h; split at h <;> simp_all; subst h; rfl)
theorem neg_intro {G : Prop} {x r : Js.Num} (k : r.val = -x.val → G) : Js.neg x = ok r → G := fun h => k (by
  simp only [Js.neg, Js.mk] at h; split at h <;> simp_all; subst h; rfl)
theorem add_intro {G : Prop} {x y r : Js.Num} (k : r.val = x.val + y.val → G) : Js.add x y = ok r → G :=
  fun h => k (add_val h)
theorem sub_intro {G : Prop} {x y r : Js.Num} (k : r.val = x.val - y.val → G) : Js.sub x y = ok r → G :=
  fun h => k (sub_val h)
theorem mul_intro {G : Prop} {x y r : Js.Num} (k : r.val = x.val * y.val → G) : Js.mul x y = ok r → G :=
  fun h => k (mul_val h)
theorem bdiv_intro {G : Prop} {x y r : Int} (k : y ≠ 0 → r = x.tdiv y → G) : Js.bdiv x y = ok r → G :=
  fun h => k (bdiv_val h).1 (bdiv_val h).2
theorem brem_intro {G : Prop} {x y r : Int} (k : y ≠ 0 → r = x.tmod y → G) : Js.brem x y = ok r → G :=
  fun h => k (brem_val h).1 (brem_val h).2
theorem unwrap_intro {α : Type} {G : Prop} {x : Option α} {r : α} (k : x = some r → G) : Js.unwrap x = ok r → G :=
  fun h => k (unwrap_val h)

theorem wp_iter_loop {T σ β : Type} [Enc T] {p x l vs body h}
    {B : List T × σ → Result (ControlFlow (List T × σ) β)} {xs a r s} {Ψ : St → Prop}
    (hl : loop B (xs, a) = ok r) (hf : List.Forall₂ (Enc.enc h) xs vs)
    (R : σ → St → Prop) (Q : β → St → Prop) (hR : R a s) (hQ : ∀ s, Q r s → Ψ s)
    (hheap : ∀ a s, R a s → s.heap = h)
    (harr : h[l]? = some (.array vs))
    (hnil : ∀ a s y, R a s → B ([], a) = ok y → ∃ r, y = .done r ∧ Q r s)
    (hcons : ∀ q rest a s item y, R a s → Enc.enc h q item → B (q :: rest, a) = ok y →
      Wp p { s with env := s.env.put x item } body fun c s' =>
        (c = .normal ∧ ∃ a', y = .cont (rest, a') ∧ R a' s') ∨ (c = .brk ∧ ∃ r, y = .done r ∧ Q r s')) :
    WpIter p x (.ref l) 0 body s Ψ := by
  obtain ⟨s', hi, hq⟩ := wp_loop R Q hheap harr hnil hcons xs 0 a s r (by simpa using hf) hR hl
  exact ⟨s', hi, hQ _ hq⟩

end Core

/-- Runs Core forward over a goal. On each path the shallow side has fixed the values, so
`simp` decides most branches; `split` takes the rest, and `omega` closes impossible ones. -/
macro "core_step" : tactic => `(tactic| first
  | apply Core.wp_cons | apply Core.wp_nil | apply Core.wprun
  | apply Core.wps_set | apply Core.wps_setField | apply Core.wps_ret | apply Core.wps_brk | apply Core.wps_ite | apply Core.wps_forOf
  | apply Core.wpe_lit | apply Core.wpe_var | apply Core.wpe_field | apply Core.wpe_bin | apply Core.wpe_isNullish
  | apply Core.wpe_not | apply Core.wpe_length | apply Core.wpe_cond | apply Core.wpe_or | apply Core.wpe_and | apply Core.wpe_index
  | apply Core.wpe_call' | apply Core.wpe_record | apply Core.wpf_cons | apply Core.wpf_nil
  | apply Core.wpa_cons | apply Core.wpa_nil)

macro "core_simp" : tactic => `(tactic| simp [Core.Env.put, Core.Fn.env0, Core.readField, Core.binary, Core.truthy, Core.nullish, List.lookup, Core.strLt_eq, *])

macro "core_run" : tactic => `(tactic| iterate 60 (all_goals try (first | core_step | core_simp | (exfalso; omega) | split | (exfalso; simp_all; done))))

set_option hygiene false in
/-- Follows the shallow side: each `do` step that succeeded becomes a fact. -/
macro "shallow" : tactic => `(tactic| iterate 24 (all_goals try (first
  | (revert hr; with_reducible refine Core.ok_intro ?_; intro hr; subst hr)
  | split at hr
  | (revert hr; with_reducible refine Core.bind_intro ?_; intro _ step hr
     first
       | (revert step; with_reducible refine Core.len_intro ?_; intro this)
       | (revert step; with_reducible refine Core.neg_intro ?_; intro this)
       | (revert step; with_reducible refine Core.add_intro ?_; intro this)
       | (revert step; with_reducible refine Core.sub_intro ?_; intro this)
       | (revert step; with_reducible refine Core.mul_intro ?_; intro this)
       | (revert step; with_reducible refine Core.bdiv_intro ?_; intro nz this; subst this)
       | (revert step; with_reducible refine Core.brem_intro ?_; intro nz this; subst this)
       | (revert step; with_reducible refine Core.unwrap_intro ?_; intro this; subst this)
       | (revert step; with_reducible refine Core.ok_intro ?_; intro this; subst this)
       | skip))))
