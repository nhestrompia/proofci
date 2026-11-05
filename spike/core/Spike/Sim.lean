import Core
import Spike.Rules
import Spike.Safe
open Aeneas Aeneas.Std Result Lean Elab Tactic Meta

/-! The general bridge. `TyRep h a v` says value `v` in heap `h` stands for typed value `a`.
A proof walks Core one statement at a time: `V s x a` says variable `x` holds `a`, and
`SimE` says an expression reads as a typed value in any extension of the state. The typed
function's steps are ordinary hypotheses, so no step looks at the rest of the program. -/
namespace Core.F64

theorem le_isInt {x y : F64} {a b : Int} (hx : Core.F64.IsInt x a) (hy : Core.F64.IsInt y b) : x.le y = decide (a ≤ b) := by
  have h : x.le y = (x.lt y || x.eq y) := rfl
  rw [h, lt_isInt hx hy, eq_isInt hx hy]
  by_cases hab : a ≤ b
  · have : a < b ∨ a = b := by omega
    rcases this with h | h <;> simp [h]; omega
  · have h1 : ¬ a < b := by omega
    have h2 : ¬ a = b := by omega
    simp [h1, h2, hab]

theorem isInt_zero (s : Bool) : Core.F64.IsInt (fin s 0) 0 := by
  cases s
  · exact Or.inl (by simp [ofInt])
  · exact Or.inr ⟨rfl, rfl⟩

theorem neg_isInt {y : F64} {b : Int} (h : Core.F64.IsInt y b) : Core.F64.IsInt y.neg (-b) := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · by_cases hb : b = 0
    · subst hb; simpa [ofInt, neg] using isInt_zero true
    · exact Or.inl (neg_ofInt_nonzero hb)
  · simpa [neg] using isInt_zero false

theorem sub_isInt {x y : F64} {a b : Int} (hx : Core.F64.IsInt x a) (hy : Core.F64.IsInt y b)
    (hlo : -9007199254740991 ≤ a - b) (hhi : a - b ≤ 9007199254740991) : Core.F64.IsInt (x.sub y) (a - b) := by
  have := add_isInt hx (neg_isInt hy) (by omega) (by omega)
  simpa [sub, Int.sub_eq_add_neg] using this

theorem mul_isInt' {x y : F64} {a b : Int} (hx : Core.F64.IsInt x a) (hy : Core.F64.IsInt y b)
    (hlo : -9007199254740991 ≤ a * b) (hhi : a * b ≤ 9007199254740991) : Core.F64.IsInt (x.mul y) (a * b) := by
  rcases hx with rfl | ⟨rfl, rfl⟩ <;> rcases hy with rfl | ⟨rfl, rfl⟩
  · exact mul_isInt hlo hhi
  · simpa [ofInt, mul, round_zero] using isInt_zero _
  · simpa [ofInt, mul, round_zero] using isInt_zero _
  · simpa [mul, round_zero] using isInt_zero _

end Core.F64

namespace Core

theorem bind_ok_inv' {α β : Type} {x : Result α} {f : α → Result β} {r : β} (h : Aeneas.Std.bind x f = ok r) :
    ∃ a, x = ok a ∧ f a = ok r := by
  revert h
  refine Result.cases (motive := fun x => Aeneas.Std.bind x f = ok r → ∃ a, x = ok a ∧ f a = ok r) x ?_ ?_ ?_
  · intro a h; exact ⟨a, rfl, by simpa using h⟩
  · intro i k h; simp at h
  · intro h; simp at h

theorem add_val {x y r : Js.Num} (h : Js.add x y = ok r) : r.val = x.val + y.val := by
  simp only [Js.add, Js.mk] at h; split at h <;> simp_all; subst h; rfl
theorem sub_val {x y r : Js.Num} (h : Js.sub x y = ok r) : r.val = x.val - y.val := by
  simp only [Js.sub, Js.mk] at h; split at h <;> simp_all; subst h; rfl
theorem mul_val {x y r : Js.Num} (h : Js.mul x y = ok r) : r.val = x.val * y.val := by
  simp only [Js.mul, Js.mk] at h; split at h <;> simp_all; subst h; rfl
theorem len_val {α} {xs : List α} {r : Js.Num} (h : Js.len xs = ok r) : r.val = xs.length := by
  simp only [Js.len, Js.mk] at h; split at h <;> simp_all; subst h; rfl
theorem bdiv_val' {x y r : Int} (h : Js.bdiv x y = ok r) : y ≠ 0 ∧ r = x.tdiv y := by
  simp only [Js.bdiv] at h; split at h <;> simp_all
theorem brem_val' {x y r : Int} (h : Js.brem x y = ok r) : y ≠ 0 ∧ r = x.tmod y := by
  simp only [Js.brem] at h; split at h <;> simp_all

class TyRep (α : Type) where
  rep : Heap → α → Val → Prop
  mono {h h' : Heap} {a : α} {v : Val} : h <+: h' → rep h a v → rep h' a v
open TyRep (rep mono)

theorem lookup_mono {h h' : Heap} (hp : h <+: h') {l : Nat} {o : Obj} (hl : h[l]? = some o) : h'[l]? = some o := by
  obtain ⟨t, rfl⟩ := hp
  have : l < h.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hl
    cases hl
  rw [List.getElem?_append_left this]; exact hl

instance : TyRep Js.Num := ⟨fun _ a v => ∃ x, v = .num x ∧ Core.F64.IsInt x a.val, fun _ h => h⟩
instance : TyRep Int := ⟨fun _ a v => v = .big a, fun _ h => h⟩
instance : TyRep Bool := ⟨fun _ a v => v = .bool a, fun _ h => h⟩
/-- Which nullish value a type allows. The translator keeps this, and `===` depends on it. -/
inductive Nothing where
  | undef | null | both
  deriving DecidableEq, Repr
def nothingOk : Nothing → Val → Prop
  | .undef, v => v = .undef
  | .null, v => v = .null
  | .both, v => v = .undef ∨ v = .null
theorem nothing_nullish {k v} (h : nothingOk k v) : nullish v = true := by
  cases k <;> simp only [nothingOk] at h
  · subst h; rfl
  · subst h; rfl
  · rcases h with rfl | rfl <;> rfl
/-- An option whose encoding is fixed by the declared type. -/
def Opt (_k : Nothing) (α : Type) : Type := Option α
def optRep {α} [TyRep α] (k : Nothing) (h : Heap) : Option α → Val → Prop
  | none, v => nothingOk k v
  | some x, v => rep h x v
theorem optRep_mono {α} {_ : TyRep α} {k} {h h' : Heap} (hp : h <+: h') {a : Option α} {v} (r : optRep k h a v) : optRep k h' a v := by
  cases a with
  | none => exact r
  | some x => exact mono hp r
instance {k α} [TyRep α] : TyRep (Opt k α) := ⟨optRep k, fun hp r => optRep_mono hp r⟩
instance {α} [TyRep α] : TyRep (Option α) := inferInstanceAs (TyRep (Opt .both α))
instance {α} [TyRep α] : TyRep (List α) where
  rep h xs v := ∃ l vs, v = .ref l ∧ h[l]? = some (.array vs) ∧ List.Forall₂ (rep h) xs vs
  mono hp := by
    rintro ⟨l, vs, rfl, hl, hf⟩
    exact ⟨l, vs, rfl, lookup_mono hp hl, hf.imp fun _ _ hr => mono hp hr⟩
instance (priority := high) : TyRep (List Nat) := ⟨fun _ a v => v = .str a, fun _ h => h⟩

/-- `s'` has the same variables and at least the same heap. -/
def Ext (s s' : St) : Prop := s'.env = s.env ∧ s.heap <+: s'.heap
theorem Ext.refl (s) : Ext s s := ⟨rfl, List.prefix_refl _⟩
theorem Ext.trans {a b c} (h : Ext a b) (k : Ext b c) : Ext a c := ⟨k.1.trans h.1, h.2.trans k.2⟩

def SimE (p : Prog) (s : St) (e : Expr) {α} [TyRep α] (a : α) : Prop :=
  ∀ s₁, Ext s s₁ → ∃ v s₂, Evals p s₁ e v s₂ ∧ Ext s₁ s₂ ∧ rep s₂.heap a v

/-- `e` is truthy exactly when `P` holds. -/
def SimB (p : Prog) (s : St) (e : Expr) (P : Prop) : Prop :=
  ∀ s₁, Ext s s₁ → ∃ v s₂, Evals p s₁ e v s₂ ∧ Ext s₁ s₂ ∧ (truthy v = true ↔ P)

/-- `e` gives exactly the boolean `decide P`. -/
def SimC (p : Prog) (s : St) (e : Expr) (P : Prop) [Decidable P] : Prop :=
  ∀ s₁, Ext s s₁ → ∃ s₂, Evals p s₁ e (.bool (decide P)) s₂ ∧ Ext s₁ s₂

def V (s : St) (x : String) {α} [TyRep α] (a : α) : Prop := ∃ v, s.env x = some v ∧ rep s.heap a v

def Upd (s s' : St) (x : String) : Prop := s.heap <+: s'.heap ∧ ∀ y, y ≠ x → s'.env y = s.env y

theorem V.upd {s s' x y α} {_ : TyRep α} {a : α} (k : Upd s s' x) (hne : y ≠ x) (h : V s y a) : V s' y a := by
  obtain ⟨v, he, hr⟩ := h
  exact ⟨v, by rw [k.2 y hne]; exact he, mono k.1 hr⟩
theorem V.ext {s s' y α} {_ : TyRep α} {a : α} (k : Ext s s') (h : V s y a) : V s' y a := by
  obtain ⟨v, he, hr⟩ := h
  exact ⟨v, by rw [k.1]; exact he, mono k.2 hr⟩

theorem SimB.of_c {p s e P} {_ : Decidable P} (h : SimC p s e P) : SimB p s e P := by
  intro s₁ hx
  obtain ⟨s₂, he, hk⟩ := h s₁ hx
  exact ⟨_, s₂, he, hk, by simp [truthy]⟩
theorem SimE.of_c {p s e P} {_ : Decidable P} (h : SimC p s e P) : SimE p s e (decide P) := by
  intro s₁ hx
  obtain ⟨s₂, he, hk⟩ := h s₁ hx
  exact ⟨_, s₂, he, hk, rfl⟩

/-! Reading -/

theorem SimE.var {p s x α} {_ : TyRep α} {a : α} (h : V s x a) : SimE p s (.var x) a := by
  intro s₁ hx
  obtain ⟨v, he, hr⟩ := h
  exact ⟨v, s₁, Evals.var (by rw [hx.1]; exact he), Ext.refl _, mono hx.2 hr⟩

theorem SimE.lit_num {p s} (a : Js.Num) {n : Int} (h : a.val = n) : SimE p s (.lit (.num (F64.ofInt n))) a := by
  subst h
  intro s₁ _
  exact ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, _, rfl, Or.inl rfl⟩
theorem SimE.lit_big {p s} (n : Int) : SimE p s (.lit (.big n)) n := fun s₁ _ =>
  ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, rfl⟩
theorem SimE.lit_bool {p s} (b : Bool) : SimE p s (.lit (.bool b)) b := fun s₁ _ =>
  ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, rfl⟩
theorem SimE.lit_str {p s} (c : List Nat) : SimE p s (.lit (.str c)) c := fun s₁ _ =>
  ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, rfl⟩
theorem SimE.lit_undef {p s k α} [TyRep α] (hk : nothingOk k .undef) : SimE (α := Opt k α) p s (.lit .undef) Option.none := fun s₁ _ =>
  ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, hk⟩
theorem SimE.lit_null {p s k α} [TyRep α] (hk : nothingOk k .null) : SimE (α := Opt k α) p s (.lit .null) Option.none := fun s₁ _ =>
  ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, hk⟩
theorem SimE.some {p s e k α} {_ : TyRep α} {a : α} (h : SimE p s e a) : SimE (α := Opt k α) p s e (Option.some a) := h
theorem SimE.conv {p s e α} {_ : TyRep α} {a b : α} (h : SimE p s e a) (hab : a = b) : SimE p s e b := hab ▸ h

def Fn.env0 (fn : Fn) (args : List Val) : Env :=
  let env : Env := (fn.params.zip args).foldl (fun e (x, v) => e.put x v) (fun _ => none)
  fn.params.foldl (fun e x => if (e x).isSome then e else e.put x .undef) env

theorem Runs.of {p fn args h v s'} (hb : ExecsL p ⟨fn.env0 args, h⟩ fn.body (.ret v) s') :
    Runs p fn args h v s' := by
  obtain ⟨F, hF⟩ := hb
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [run]
    have := hF g hg
    simp only [Fn.env0] at this
    simp only [this]⟩

/-- A general binary step on typed operands. -/
theorem sim_bin {p s op x y α β γ} {_ : TyRep α} {_ : TyRep β} {_ : TyRep γ} {a : α} {b : β} {r : γ}
    (hx : SimE p s x a) (hy : SimE p s y b)
    (hf : ∀ h v w, rep h a v → rep h b w → ∃ u, binary op v w = some u ∧ rep h r u) :
    SimE p s (.bin op x y) r := by
  intro s₁ h₁
  obtain ⟨v, s₂, ex, h₂, rv⟩ := hx s₁ h₁
  obtain ⟨w, s₃, ey, h₃, rw⟩ := hy s₂ (h₁.trans h₂)
  obtain ⟨u, hb, ru⟩ := hf _ v w (mono h₃.2 rv) rw
  exact ⟨u, s₃, Evals.bin ex ey hb, h₂.trans h₃, ru⟩

theorem sim_cmp {p s op x y α β} {_ : TyRep α} {_ : TyRep β} {a : α} {b : β} {P : Prop} [Decidable P]
    (hx : SimE p s x a) (hy : SimE p s y b)
    (hf : ∀ h v w, rep h a v → rep h b w → binary op v w = some (.bool (decide P))) :
    SimC p s (.bin op x y) P := by
  intro s₁ h₁
  obtain ⟨v, s₂, ex, h₂, rv⟩ := hx s₁ h₁
  obtain ⟨w, s₃, ey, h₃, rw⟩ := hy s₂ (h₁.trans h₂)
  exact ⟨s₃, Evals.bin ex ey (hf _ v w (mono h₃.2 rv) rw), h₂.trans h₃⟩

theorem SimE.add {p s x y a b r} (hx : SimE p s x a) (hy : SimE p s y b) (h : Js.add a b = ok r) :
    SimE p s (.bin .add x y) r := by
  refine sim_bin hx hy ?_
  rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
  have hv := add_val h
  have := F64.add_isInt hx hy (hv ▸ r.lo) (hv ▸ r.hi)
  exact ⟨_, rfl, _, rfl, hv ▸ this⟩

theorem SimE.sub {p s x y a b r} (hx : SimE p s x a) (hy : SimE p s y b) (h : Js.sub a b = ok r) :
    SimE p s (.bin .sub x y) r := by
  refine sim_bin hx hy ?_
  rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
  have hv := sub_val h
  have := F64.sub_isInt hx hy (hv ▸ r.lo) (hv ▸ r.hi)
  exact ⟨_, rfl, _, rfl, hv ▸ this⟩

theorem SimE.mul {p s x y a b r} (hx : SimE p s x a) (hy : SimE p s y b) (h : Js.mul a b = ok r) :
    SimE p s (.bin .mul x y) r := by
  refine sim_bin hx hy ?_
  rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
  have hv := mul_val h
  have hlo : -9007199254740991 ≤ a.val * b.val := hv ▸ r.lo
  have hhi : a.val * b.val ≤ 9007199254740991 := hv ▸ r.hi
  exact ⟨_, rfl, _, rfl, hv ▸ F64.mul_isInt' hx hy hlo hhi⟩

theorem SimE.neg {p s e} {a r : Js.Num} (hx : SimE p s e a) (h : Js.neg a = ok r) : SimE p s (.neg e) r := by
  have hv : r.val = -a.val := by simp only [Js.neg, Js.mk] at h; split at h <;> simp_all; subst h; rfl
  intro s₁ h₁
  obtain ⟨v, s₂, ev, h₂, x, rfl, hi⟩ := hx s₁ h₁
  exact ⟨_, s₂, Evals.neg ev, h₂, _, rfl, hv ▸ F64.neg_isInt hi⟩

theorem SimE.badd {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.bin .add x y) (a + b) := by
  refine sim_bin hx hy ?_; rintro _ _ _ rfl rfl; exact ⟨_, rfl, rfl⟩
theorem SimE.bsub {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.bin .sub x y) (a - b) := by
  refine sim_bin hx hy ?_; rintro _ _ _ rfl rfl; exact ⟨_, rfl, rfl⟩
theorem SimE.bmul {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.bin .mul x y) (a * b) := by
  refine sim_bin hx hy ?_; rintro _ _ _ rfl rfl; exact ⟨_, rfl, rfl⟩
theorem SimE.bdiv {p s x y} {a b r : Int} (hx : SimE p s x a) (hy : SimE p s y b) (h : Js.bdiv a b = ok r) :
    SimE p s (.bin .div x y) r := by
  refine sim_bin hx hy ?_; rintro _ _ _ rfl rfl
  obtain ⟨hb, rfl⟩ := bdiv_val' h
  exact ⟨_, by simp [binary, hb], rfl⟩
theorem SimE.brem {p s x y} {a b r : Int} (hx : SimE p s x a) (hy : SimE p s y b) (h : Js.brem a b = ok r) :
    SimE p s (.bin .rem x y) r := by
  refine sim_bin hx hy ?_; rintro _ _ _ rfl rfl
  obtain ⟨hb, rfl⟩ := brem_val' h
  exact ⟨_, by simp [binary, hb], rfl⟩
theorem SimE.concat {p s x y} {a b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) :
    SimE p s (.bin .add x y) (a ++ b) := by
  refine sim_bin hx hy ?_; rintro _ _ _ rfl rfl; exact ⟨_, rfl, rfl⟩

/-! Comparing -/

theorem SimC.lt {p s x y} {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .lt x y) (a.val < b.val) :=
  sim_cmp hx hy (by rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩; simp [binary, F64.lt_isInt hx hy])
theorem SimC.gt {p s x y} {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .gt x y) (a.val > b.val) :=
  sim_cmp hx hy (by rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩; simp [binary, F64.lt_isInt hy hx])
theorem SimC.le {p s x y} {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .le x y) (a.val ≤ b.val) :=
  sim_cmp hx hy (by rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩; simp [binary, F64.le_isInt hx hy])
theorem SimC.ge {p s x y} {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .ge x y) (a.val ≥ b.val) :=
  sim_cmp hx hy (by rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩; simp [binary, F64.le_isInt hy hx])
theorem SimC.eq {p s x y} {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .eq x y) (a.val = b.val) :=
  sim_cmp hx hy (by rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩; simp [binary, F64.eq_isInt hx hy])
theorem SimC.ne {p s x y} {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .ne x y) (a.val ≠ b.val) :=
  sim_cmp hx hy (by rintro _ _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩; simp [binary, F64.eq_isInt hx hy])

theorem SimC.eq_str {p s x y} {a b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .eq x y) (a = b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.ne_str {p s x y} {a b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .ne x y) (a ≠ b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.eq_bool {p s x y} {a b : Bool} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .eq x y) (a = b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.ne_bool {p s x y} {a b : Bool} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .ne x y) (a ≠ b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.lt_big {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .lt x y) (a < b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.gt_big {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .gt x y) (a > b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.le_big {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .le x y) (a ≤ b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.ge_big {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .ge x y) (a ≥ b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.eq_big {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .eq x y) (a = b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])
theorem SimC.ne_big {p s x y} {a b : Int} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .ne x y) (a ≠ b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary])

theorem strLt_same (a b : List Nat) : Core.strLt a b = Js.strLt a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [Core.strLt, Js.strLt, ih]
      by_cases hxy : x = y
      · subst hxy; simp
      · have : (x < y ∨ x = y ∧ Js.strLt xs ys = true) ↔ x < y := by simp [hxy]
        simp [hxy, this]
theorem SimB.lt_str {p s x y} {a b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .lt x y) (Js.strLt a b = true) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary, strLt_same])
theorem SimB.gt_str {p s x y} {a b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .gt x y) (Js.strLt b a = true) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary, strLt_same])

/-! Truth -/

theorem SimB.bool {p s e} {a : Bool} (h : SimE p s e a) : SimB p s e (a = true) := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, rfl⟩ := h s₁ hx
  exact ⟨_, s₂, he, hk, by simp [truthy]⟩
theorem SimB.str {p s e} {a : List Nat} (h : SimE p s e a) : SimB p s e (a ≠ []) := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, rfl⟩ := h s₁ hx
  exact ⟨_, s₂, he, hk, by cases a <;> simp [truthy]⟩
theorem SimB.num {p s e} {a : Js.Num} (h : SimE p s e a) : SimB p s e (a.val ≠ 0) := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, x, rfl, hi⟩ := h s₁ hx
  refine ⟨_, s₂, he, hk, ?_⟩
  rcases hi with rfl | ⟨h0, rfl⟩
  · generalize a.val = n
    by_cases hn : n = 0
    · subst hn; simp [truthy, F64.ofInt]
    · have : n.natAbs * F64.unit ≠ 0 := Nat.mul_ne_zero (by omega) (by have := F64.unit_pos; omega)
      simp only [truthy, F64.ofInt, hn, ne_eq, not_false_eq_true, iff_true]
      split <;> simp_all
  · simp [truthy, h0]
theorem SimB.big {p s e} {a : Int} (h : SimE p s e a) : SimB p s e (a ≠ 0) := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, rfl⟩ := h s₁ hx
  exact ⟨_, s₂, he, hk, by simp [truthy]⟩
theorem nullish_not_truthy {v} (h : nullish v = true) : truthy v = false := by
  cases v <;> simp_all [nullish, truthy]
theorem SimB.none {p s e k α} {_ : TyRep α} {a : Opt k α} (h : SimE p s e a) (ha : a = Option.none) : SimB p s e False := by
  intro s₁ hx
  subst ha
  obtain ⟨v, s₂, he, hk, rv⟩ := h s₁ hx
  refine ⟨v, s₂, he, hk, ?_⟩
  simp [nullish_not_truthy (nothing_nullish rv)]

/-- Values that are always objects. -/
class IsObj (α : Type) [TyRep α] : Prop where
  ref {h : Heap} {a : α} {v : Val} : rep h a v → ∃ l, v = .ref l
instance {α} [TyRep α] : IsObj (List α) := ⟨fun ⟨l, _, h, _⟩ => ⟨l, h⟩⟩

theorem SimB.obj {p s e α} {_ : TyRep α} {a : α} (h : SimE p s e a) (hobj : IsObj α) : SimB p s e True := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, rv⟩ := h s₁ hx
  obtain ⟨l, rfl⟩ := IsObj.ref rv
  exact ⟨_, s₂, he, hk, by simp [truthy]⟩
theorem SimE.some_inv {p s e k α} {_ : TyRep α} {a : α} (h : SimE (α := Opt k α) p s e (Option.some a)) : SimE p s e a := h
theorem SimE.unwrap {p s e k α} {_ : TyRep α} {x : Opt k α} {a : α} (h : SimE p s e x) (hx : x = Option.some a) : SimE p s e a := by
  subst hx; exact h
theorem SimE.of_eq_some {p s e k α} {_ : TyRep α} {x : Opt k α} {a : α} (hx : x = Option.some a) (h : SimE p s e a) : SimE p s e x := by
  subst hx; exact h
theorem SimE.of_eq_none {p s e k α} {_ : TyRep α} {x : Opt k α} (h : SimE (α := Opt k α) p s e Option.none) (hx : x = Option.none) : SimE p s e x := by
  subst hx; exact h
/-- A value whose type allows one nullish form also fits a type that allows both. -/
theorem up_rep {k k' α} {_ : TyRep α} (hk : ∀ v, nothingOk k v → nothingOk k' v) {a : Option α} {h v}
    (r : optRep k h a v) : optRep k' h a v := by
  cases a with
  | none => exact hk v r
  | some x => exact r
theorem SimE.up {p s e k k' α} {_ : TyRep α} (hk : ∀ v, nothingOk k v → nothingOk k' v) {a : Option α}
    (h : SimE (α := Opt k α) p s e a) : SimE (α := Opt k' α) p s e a := by
  intro s₁ hx
  obtain ⟨v, s₂, ev, hk', rv⟩ := h s₁ hx
  exact ⟨v, s₂, ev, hk', up_rep hk rv⟩
theorem up_undef (v) (h : nothingOk .undef v) : nothingOk .both v := Or.inl h
theorem up_null (v) (h : nothingOk .null v) : nothingOk .both v := Or.inr h

theorem SimB.not {p s e P} (h : SimB p s e P) : SimB p s (.not e) (¬P) := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, ht⟩ := h s₁ hx
  refine ⟨_, s₂, Evals.not he, hk, ?_⟩
  cases htv : truthy v
  · have : ¬P := fun hp => by simp [ht.mpr hp] at htv
    simp [truthy, this]
  · simp [truthy, ht.mp htv]
theorem SimC.not {p s e P} (h : SimB p s e P) [Decidable P] : SimC p s (.not e) (¬P) := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, ht⟩ := h s₁ hx
  refine ⟨s₂, ?_, hk⟩
  have : (!truthy v) = decide (¬P) := by
    cases htv : truthy v
    · have : ¬P := fun hp => by simp [ht.mpr hp] at htv
      simp [this]
    · simp [ht.mp htv]
  rw [← this]; exact Evals.not he
theorem SimB.isNullish_none {p s e k α} {_ : TyRep α} {a : Opt k α} (h : SimE p s e a) (ha : a = Option.none) : SimC p s (.isNullish e) True := by
  intro s₁ hx
  subst ha
  obtain ⟨v, s₂, he, hk, rv⟩ := h s₁ hx
  refine ⟨s₂, ?_, hk⟩
  have : nullish v = decide True := by simpa using nothing_nullish rv
  rw [← this]; exact Evals.isNullish he

/-- A non-nullish value: everything a typed value can be except an absent option. -/
class NotNull (α : Type) [TyRep α] : Prop where
  ok {h : Heap} {a : α} {v : Val} : rep h a v → nullish v = false
instance : NotNull Js.Num := ⟨by rintro _ _ _ ⟨x, rfl, -⟩; rfl⟩
instance : NotNull Int := ⟨by rintro _ _ _ rfl; rfl⟩
instance : NotNull Bool := ⟨by rintro _ _ _ rfl; rfl⟩
instance : NotNull (List Nat) := ⟨by rintro _ _ _ rfl; rfl⟩
instance {α} [TyRep α] [IsObj α] : NotNull α := ⟨fun h => by obtain ⟨l, rfl⟩ := IsObj.ref h; rfl⟩
theorem SimB.isNullish_some {p s e α} {_ : TyRep α} {a : α} (h : SimE p s e a) (hn : NotNull α) : SimC p s (.isNullish e) False := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, rv⟩ := h s₁ hx
  refine ⟨s₂, ?_, hk⟩
  have : nullish v = decide False := by rw [NotNull.ok rv]; rfl
  rw [← this]; exact Evals.isNullish he

theorem SimC.eq_undef_none {p s e α} {_ : TyRep α} {a : Opt .undef α} (h : SimE p s e a) (ha : a = Option.none) :
    SimC p s (.bin .eq e (.lit .undef)) True := by
  subst ha
  exact sim_cmp h (SimE.lit_undef (k := .undef) (α := α) rfl) (fun _ _ _ h1 h2 => by cases h1; cases h2; rfl)
theorem SimC.eq_null_none {p s e α} {_ : TyRep α} {a : Opt .null α} (h : SimE p s e a) (ha : a = Option.none) :
    SimC p s (.bin .eq e (.lit .null)) True := by
  subst ha
  exact sim_cmp h (SimE.lit_null (k := .null) (α := α) rfl) (fun _ _ _ h1 h2 => by cases h1; cases h2; rfl)
theorem SimC.eq_nothing_some {p s e w α} {_ : TyRep α} {a : α} (hw : nullish w = true) (h : SimE p s e a) (hn : NotNull α) :
    SimC p s (.bin .eq e (.lit w)) False := by
  intro s₁ hx
  obtain ⟨v, s₂, ev, hk, rv⟩ := h s₁ hx
  have hne : v ≠ w := fun he => by subst he; simp [NotNull.ok rv] at hw
  have hb : binary .eq v w = some (.bool (decide False)) := by
    cases v <;> cases w <;> simp_all [binary, nullish]
  exact ⟨s₂, Evals.bin ev (Evals.lit _ _ _) hb, hk⟩
theorem SimC.ne_nothing_some {p s e w α} {_ : TyRep α} {a : α} (hw : nullish w = true) (h : SimE p s e a) (hn : NotNull α) :
    SimC p s (.bin .ne e (.lit w)) True := by
  intro s₁ hx
  obtain ⟨v, s₂, ev, hk, rv⟩ := h s₁ hx
  have hne : v ≠ w := fun he => by subst he; simp [NotNull.ok rv] at hw
  have hb : binary .ne v w = some (.bool (decide True)) := by
    cases v <;> cases w <;> simp_all [binary, nullish]
  exact ⟨s₂, Evals.bin ev (Evals.lit _ _ _) hb, hk⟩
theorem SimC.ne_undef_none {p s e α} {_ : TyRep α} {a : Opt .undef α} (h : SimE p s e a) (ha : a = Option.none) :
    SimC p s (.bin .ne e (.lit .undef)) False := by
  subst ha
  exact sim_cmp h (SimE.lit_undef (k := .undef) (α := α) rfl) (fun _ _ _ h1 h2 => by cases h1; cases h2; rfl)
theorem SimC.ne_null_none {p s e α} {_ : TyRep α} {a : Opt .null α} (h : SimE p s e a) (ha : a = Option.none) :
    SimC p s (.bin .ne e (.lit .null)) False := by
  subst ha
  exact sim_cmp h (SimE.lit_null (k := .null) (α := α) rfl) (fun _ _ _ h1 h2 => by cases h1; cases h2; rfl)

/-- `c` is known, so only one side runs. -/
theorem SimE.cond_t {p s c a b P α} {_ : TyRep α} {x : α} (hc : SimB p s c P) (hp : P) (ha : SimE p s a x) :
    SimE p s (.cond c a b) x := by
  intro s₁ h₁
  obtain ⟨v, s₂, ec, h₂, ht⟩ := hc s₁ h₁
  obtain ⟨w, s₃, ea, h₃, rw⟩ := ha s₂ (h₁.trans h₂)
  exact ⟨w, s₃, Evals.cond_true ec (ht.mpr hp) ea, h₂.trans h₃, rw⟩
theorem SimE.cond_f {p s c a b P α} {_ : TyRep α} {x : α} (hc : SimB p s c P) (hp : ¬P) (hb : SimE p s b x) :
    SimE p s (.cond c a b) x := by
  intro s₁ h₁
  obtain ⟨v, s₂, ec, h₂, ht⟩ := hc s₁ h₁
  obtain ⟨w, s₃, eb, h₃, rw⟩ := hb s₂ (h₁.trans h₂)
  have : truthy v = false := by cases h : truthy v <;> simp_all
  exact ⟨w, s₃, Evals.cond_false ec this eb, h₂.trans h₃, rw⟩
theorem SimE.or_t {p s a b P} {α} {_ : TyRep α} {x : α} (ha : SimE p s a x) (hb : SimB p s a P) (hp : P)
    (hu : ∀ s₁ s₂ s₃ v w, Evals p s₁ a v s₂ → Evals p s₁ a w s₃ → v = w ∧ s₂ = s₃) : SimE p s (.or a b) x := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := ha s₁ h₁
  obtain ⟨w, s₃, e', h₃, ht⟩ := hb s₁ h₁
  obtain ⟨rfl, rfl⟩ := hu _ _ _ _ _ e e'
  exact ⟨v, s₂, Evals.or_true e (ht.mpr hp), h₂, rv⟩
theorem Evals.unique {p s e v w s₂ s₃} (a : Evals p s e v s₂) (b : Evals p s e w s₃) : v = w ∧ s₂ = s₃ := by
  obtain ⟨F, hF⟩ := a
  obtain ⟨G, hG⟩ := b
  have := (hF (F + G) (by omega)).symm.trans (hG (F + G) (by omega))
  cases this
  exact ⟨rfl, rfl⟩
theorem SimB.and_f {p s a b P} (ha : SimB p s a P) (hp : ¬P) : SimB p s (.and a b) False := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, ht⟩ := ha s₁ h₁
  have : truthy v = false := by cases h : truthy v <;> simp_all
  exact ⟨v, s₂, Evals.and_false e this, h₂, by simp [this]⟩
theorem SimB.and_t {p s a b P Q} (ha : SimB p s a P) (hp : P) (hb : SimB p s b Q) : SimB p s (.and a b) Q := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, ht⟩ := ha s₁ h₁
  obtain ⟨w, s₃, e', h₃, ht'⟩ := hb s₂ (h₁.trans h₂)
  exact ⟨w, s₃, Evals.and_true e (ht.mpr hp) e', h₂.trans h₃, ht'⟩
theorem SimB.or_t {p s a b P} (ha : SimB p s a P) (hp : P) : SimB p s (.or a b) True := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, ht⟩ := ha s₁ h₁
  exact ⟨v, s₂, Evals.or_true e (ht.mpr hp), h₂, by simp [ht.mpr hp]⟩
theorem SimB.or_f {p s a b P Q} (ha : SimB p s a P) (hp : ¬P) (hb : SimB p s b Q) : SimB p s (.or a b) Q := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, ht⟩ := ha s₁ h₁
  obtain ⟨w, s₃, e', h₃, ht'⟩ := hb s₂ (h₁.trans h₂)
  have : truthy v = false := by cases h : truthy v <;> simp_all
  exact ⟨w, s₃, Evals.or_false e this e', h₂.trans h₃, ht'⟩
theorem SimB.iff {p s e P Q} (h : SimB p s e P) (hi : P ↔ Q) : SimB p s e Q := by
  intro s₁ hx
  obtain ⟨v, s₂, he, hk, ht⟩ := h s₁ hx
  exact ⟨v, s₂, he, hk, ht.trans hi⟩

theorem SimB.and_both {p s a b P Q} (ha : SimB p s a P) (hb : SimB p s b Q) : SimB p s (.and a b) (P ∧ Q) := by
  by_cases hp : P
  · exact (SimB.and_t ha hp hb).iff (by simp [hp])
  · exact (SimB.and_f ha hp).iff (by simp [hp])
theorem SimB.or_both {p s a b P Q} (ha : SimB p s a P) (hb : SimB p s b Q) : SimB p s (.or a b) (P ∨ Q) := by
  by_cases hp : P
  · exact (SimB.or_t ha hp).iff (by simp [hp])
  · exact (SimB.or_f ha hp hb).iff (by simp [hp])
/-- `a || b` and `a && b` as values, with the left side's truth known. -/
theorem SimE.or_true {p s a b P α} {_ : TyRep α} {x : α} (ha : SimE p s a x) (hb : SimB p s a P) (hp : P) : SimE p s (.or a b) x :=
  SimE.or_t ha hb hp fun _ _ _ _ _ a b => Evals.unique a b
theorem SimE.or_false {p s a b P α} {_ : TyRep α} {x : α} (ha : SimB p s a P) (hp : ¬P) (hb : SimE p s b x) : SimE p s (.or a b) x := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, ht⟩ := ha s₁ h₁
  obtain ⟨w, s₃, e', h₃, rw⟩ := hb s₂ (h₁.trans h₂)
  have : truthy v = false := by cases h : truthy v <;> simp_all
  exact ⟨w, s₃, Evals.or_false e this e', h₂.trans h₃, rw⟩
theorem SimE.and_true {p s a b P α} {_ : TyRep α} {x : α} (ha : SimB p s a P) (hp : P) (hb : SimE p s b x) : SimE p s (.and a b) x := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, ht⟩ := ha s₁ h₁
  obtain ⟨w, s₃, e', h₃, rw⟩ := hb s₂ (h₁.trans h₂)
  exact ⟨w, s₃, Evals.and_true e (ht.mpr hp) e', h₂.trans h₃, rw⟩
theorem SimE.and_false {p s a b P α} {_ : TyRep α} {x : α} (ha : SimE p s a x) (hb : SimB p s a P) (hp : ¬P) : SimE p s (.and a b) x := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := ha s₁ h₁
  obtain ⟨w, s₃, e', h₃, ht⟩ := hb s₁ h₁
  obtain ⟨rfl, rfl⟩ := Evals.unique e e'
  have : truthy v = false := by cases h : truthy v <;> simp_all
  exact ⟨v, s₂, Evals.and_false e this, h₂, rv⟩

theorem SimE.coalesce_some {p s a b α} {_ : TyRep α} {x : α} (ha : SimE p s a x) (hn : NotNull α) : SimE p s (.coalesce a b) x := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := ha s₁ h₁
  obtain ⟨F, hF⟩ := e
  refine ⟨v, s₂, ⟨F + 1, fun f hf => ?_⟩, h₂, rv⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  simp [eval, hF g hg, NotNull.ok rv]
theorem SimE.coalesce_none {p s a b k α β} {_ : TyRep α} {_ : TyRep β} {o : Opt k α} {y : β} (ha : SimE p s a o) (ho : o = Option.none)
    (hb : SimE p s b y) : SimE p s (.coalesce a b) y := by
  subst ho
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := ha s₁ h₁
  obtain ⟨w, s₃, e', h₃, rw⟩ := hb s₂ (h₁.trans h₂)
  obtain ⟨F, hF⟩ := e
  obtain ⟨G, hG⟩ := e'
  refine ⟨w, s₃, ⟨F + G + 1, fun f hf => ?_⟩, h₂.trans h₃, rw⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  have hn : nullish v = true := nothing_nullish rv
  simp [eval, hF g (by omega), hn, hG g (by omega)]

/-! Fields, arrays and built-ins -/

theorem sim_field {p s o k α β} {_ : TyRep α} {_ : TyRep β} {a : α} {b : β} (hx : SimE p s o a)
    (hf : ∀ h v, rep h a v → ∃ r, readField h v k = some r ∧ rep h b r) : SimE p s (.field o k) b := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := hx s₁ h₁
  obtain ⟨r, hr, rb⟩ := hf _ v rv
  exact ⟨r, s₂, Evals.field e hr, h₂, rb⟩
theorem sim_optField {p s o k α β} {_ : TyRep α} {_ : TyRep β} [NotNull α] {a : α} {b : β} (hx : SimE p s o a)
    (hf : ∀ h v, rep h a v → ∃ r, readField h v k = some r ∧ rep h b r) : SimE p s (.optField o k) b := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := hx s₁ h₁
  obtain ⟨r, hr, rb⟩ := hf _ v rv
  obtain ⟨F, hF⟩ := e
  refine ⟨r, s₂, ⟨F + 1, fun f hf => ?_⟩, h₂, rb⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  simp [eval, hF g hg, NotNull.ok rv, hr]
theorem SimE.optField_none {p s o f k k' α β} {_ : TyRep α} {_ : TyRep β} {a : Opt k α} (hx : SimE p s o a) (ha : a = Option.none)
    (hk : nothingOk k' .undef) : SimE (α := Opt k' β) p s (.optField o f) Option.none := by
  subst ha
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := hx s₁ h₁
  obtain ⟨F, hF⟩ := e
  refine ⟨.undef, s₂, ⟨F + 1, fun f hf => ?_⟩, h₂, hk⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  have hn : nullish v = true := nothing_nullish rv
  simp [eval, hF g hg, hn]

theorem SimE.len_str {p s e} {a : List Nat} {r : Js.Num} (hx : SimE p s e a) (h : Js.len a = ok r) :
    SimE p s (.length e) r := by
  intro s₁ h₁
  obtain ⟨v, s₂, ev, h₂, rfl⟩ := hx s₁ h₁
  obtain ⟨F, hF⟩ := ev
  have hl : (a.length : Int) = r.val := (len_val h).symm
  refine ⟨.num (F64.ofInt a.length), s₂, ⟨F + 1, fun f hf => ?_⟩, h₂, _, rfl, Or.inl (by rw [hl])⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  simp [eval, hF g hg]
theorem SimE.len_arr {p s e α} {_ : TyRep α} {a : List α} {r : Js.Num} (hx : SimE p s e a) (h : Js.len a = ok r) :
    SimE p s (.length e) r := by
  intro s₁ h₁
  obtain ⟨v, s₂, ev, h₂, l, vs, rfl, hl, hf⟩ := hx s₁ h₁
  have hlen := hf.length_eq
  refine ⟨_, s₂, Evals.length ev hl, h₂, _, rfl, Or.inl ?_⟩
  rw [len_val h, hlen]

theorem Forall₂_get {α} {R : α → Val → Prop} {xs : List α} {vs : List Val} (hf : List.Forall₂ R xs vs) (i : Nat) (hi : i < xs.length) :
    ∃ a v, xs[i]? = some a ∧ vs[i]? = some v ∧ R a v := by
  induction hf generalizing i with
  | nil => simp at hi
  | cons hab _ ih =>
    cases i with
    | zero => exact ⟨_, _, rfl, rfl, hab⟩
    | succ n => exact ih n (by simpa using hi)

theorem F64.index_isInt {x : F64} {a : Int} (h : Core.F64.IsInt x a) (ha : 0 ≤ a) : x.index = some a.toNat := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact F64.index_ofInt_nonneg ha
  · rfl

theorem F64.index_ofInt_neg {a : Int} (h : a < 0) : (F64.ofInt a).index = Option.none := by
  have hu := F64.unit_pos
  have : a.natAbs * F64.unit ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  simp [F64.ofInt, F64.index, h, this]

theorem SimE.at_ {p s o i α} {_ : TyRep α} {a : List α} {b : Js.Num} (ho : SimE p s o a) (hi : SimE p s i b) :
    SimE (α := Opt .undef α) p s (.index o i) (Js.at_ a b) := by
  intro s₁ h₁
  obtain ⟨v, s₂, eo, h₂, l, vs, rfl, hl, hf⟩ := ho s₁ h₁
  obtain ⟨n, s₃, ei, h₃, x, rfl, hx⟩ := hi s₂ (h₁.trans h₂)
  have hl' := lookup_mono h₃.2 hl
  have hf' := hf.imp fun _ _ hr => mono h₃.2 hr
  refine ⟨_, s₃, Evals.index eo ei rfl hl', h₂.trans h₃, ?_⟩
  by_cases hb : b.val < 0
  · have : x.index = none := by
      rcases hx with rfl | ⟨h0, rfl⟩
      · exact F64.index_ofInt_neg hb
      · omega
    simp only [Js.at_, hb, ite_true, this]
    exact rfl
  · have hn := F64.index_isInt hx (by omega)
    simp only [Js.at_, hb, ite_false, hn, Option.bind_some]
    by_cases hlt : b.val.toNat < a.length
    · obtain ⟨c, w, h1, h2, h3⟩ := Forall₂_get hf' _ hlt
      simp only [h1, h2, Option.getD_some]
      exact h3
    · have h1 : a[b.val.toNat]? = none := by simp; omega
      have h2 : vs[b.val.toNat]? = none := by simp; rw [← hf'.length_eq]; omega
      simp only [h1, h2, Option.getD_none]
      exact rfl

theorem asNum_isInt {x : F64} {a : Js.Num} (h : Core.F64.IsInt x a.val) : asNum (.num x) = some a := by
  have key : ∀ (s : Bool) (n : Nat) (i : Int), F64.signed s n = i → (∀ hl hh, (⟨i, hl, hh⟩ : Js.Num) = a) →
      -9007199254740991 ≤ i → i ≤ 9007199254740991 → asNum (.num (.fin s (n * F64.unit))) = some a := by
    intro s n i hi he hl hh
    have hu := F64.unit_pos
    have h1 : n * F64.unit % F64.unit = 0 := Nat.mul_mod_left _ _
    have h2 : n * F64.unit / F64.unit = n := Nat.mul_div_cancel _ hu
    simp only [asNum, h1, h2, ite_true, hi]
    rw [dif_pos ⟨hl, hh⟩, he]
  have hb := a.lo
  have hc := a.hi
  rcases h with rfl | ⟨h0, rfl⟩
  · refine key _ _ a.val ?_ (fun _ _ => rfl) hb hc
    simp only [F64.signed]
    by_cases hn : a.val < 0
    · rw [if_pos (by simpa using hn)]; omega
    · rw [if_neg (by simpa using hn)]; omega
  · have : F64.fin true 0 = F64.fin true (0 * F64.unit) := by simp
    rw [this]
    refine key true 0 0 (by simp [F64.signed]) (fun _ _ => ?_) (by decide) (by decide)
    cases a; simp_all

/-- A built-in on typed arguments. -/
theorem sim_prim {p s op es} {vs' : Heap → List Val → Prop} {α} {_ : TyRep α} {r : α}
    (ha : ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsL p s₁ es vs s₂ ∧ Ext s₁ s₂ ∧ vs' s₂.heap vs)
    (hf : ∀ h vs, vs' h vs → ∃ v h', primV op h vs = some (v, h') ∧ h <+: h' ∧ rep h' r v) :
    SimE p s (.prim op es) r := by
  intro s₁ h₁
  obtain ⟨vs, s₂, ea, h₂, hv⟩ := ha s₁ h₁
  obtain ⟨v, h', hp, hpre, rv⟩ := hf _ _ hv
  obtain ⟨F, hF⟩ := ea
  refine ⟨v, { s₂ with heap := h' }, ⟨F + 1, fun f hf => ?_⟩, h₂.trans ⟨rfl, hpre⟩, rv⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  simp [eval, hF g hg, hp]

def SimF (p : Prog) (s : St) (es : List (String × Expr)) (Q : Heap → List (String × Val) → Prop) : Prop :=
  ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsF p s₁ es vs s₂ ∧ Ext s₁ s₂ ∧ Q s₂.heap vs
theorem simf_nil {p s} : SimF p s [] (fun _ vs => vs = []) := fun s₁ _ => ⟨[], s₁, EvalsF.nil _ _, Ext.refl _, rfl⟩
theorem simf_cons {p s k e es α} {Q : Heap → List (String × Val) → Prop} {_ : TyRep α} {a : α} (h : SimE p s e a) (t : SimF p s es Q) :
    SimF p s ((k, e) :: es) (fun h vs => ∃ v tail, vs = (k, v) :: tail ∧ rep h a v ∧ Q h tail) := by
  intro s₁ h₁
  obtain ⟨v, s₂, ev, h₂, rv⟩ := h s₁ h₁
  obtain ⟨vs, s₃, ef, h₃, hq⟩ := t s₂ (h₁.trans h₂)
  exact ⟨(k, v) :: vs, s₃, EvalsF.cons ev ef, h₂.trans h₃, v, vs, rfl, mono h₃.2 rv, hq⟩
theorem sim_record {p s es α} {Q : Heap → List (String × Val) → Prop} {_ : TyRep α} {X : α} (hf : SimF p s es Q)
    (hq : ∀ h vs, Q h vs → rep (h ++ [.record vs]) X (.ref h.length)) : SimE p s (.record es) X := by
  intro s₁ h₁
  obtain ⟨vs, s₂, ef, h₂, hv⟩ := hf s₁ h₁
  exact ⟨_, _, Evals.record ef, h₂.trans ⟨rfl, List.prefix_append _ _⟩, hq _ _ hv⟩

def SimL {α} [TyRep α] (p : Prog) (s : St) (es : List Expr) (xs : List α) : Prop :=
  ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsL p s₁ es vs s₂ ∧ Ext s₁ s₂ ∧ List.Forall₂ (rep s₂.heap) xs vs
theorem siml_nil {p s α} {_ : TyRep α} : SimL p s [] ([] : List α) := fun s₁ _ => ⟨[], s₁, EvalsL.nil _ _, Ext.refl _, .nil⟩
theorem siml_cons {p s e es α} {_ : TyRep α} {a : α} {xs : List α} (h : SimE p s e a) (t : SimL p s es xs) : SimL p s (e :: es) (a :: xs) := by
  intro s₁ h₁
  obtain ⟨v, s₂, ev, h₂, rv⟩ := h s₁ h₁
  obtain ⟨vs, s₃, el, h₃, hl⟩ := t s₂ (h₁.trans h₂)
  exact ⟨v :: vs, s₃, EvalsL.cons ev el, h₂.trans h₃, .cons (mono h₃.2 rv) hl⟩
theorem SimE.array {p s es α} {_ : TyRep α} {xs : List α} (h : SimL p s es xs) : SimE p s (.array es) xs := by
  intro s₁ h₁
  obtain ⟨vs, s₂, el, h₂, hl⟩ := h s₁ h₁
  refine ⟨_, _, Evals.array el, h₂.trans ⟨rfl, List.prefix_append _ _⟩, _, vs, rfl, by simp, hl.imp fun _ _ r => mono (List.prefix_append _ _) r⟩

def Args1 {α} [TyRep α] (a : α) (h : Heap) (vs : List Val) : Prop := ∃ v, vs = [v] ∧ rep h a v
def Args2 {α β} [TyRep α] [TyRep β] (a : α) (b : β) (h : Heap) (vs : List Val) : Prop := ∃ v w, vs = [v, w] ∧ rep h a v ∧ rep h b w
def Args3 {α β γ} [TyRep α] [TyRep β] [TyRep γ] (a : α) (b : β) (c : γ) (h : Heap) (vs : List Val) : Prop :=
  ∃ v w u, vs = [v, w, u] ∧ rep h a v ∧ rep h b w ∧ rep h c u

theorem args0 {p s} : ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsL p s₁ [] vs s₂ ∧ Ext s₁ s₂ ∧ (fun (_ : Heap) (vs : List Val) => vs = []) s₂.heap vs :=
  fun s₁ _ => ⟨[], s₁, EvalsL.nil _ _, Ext.refl _, rfl⟩

theorem args1 {p s x α} {_ : TyRep α} {a : α} (hx : SimE p s x a) :
    ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsL p s₁ [x] vs s₂ ∧ Ext s₁ s₂ ∧ Args1 a s₂.heap vs := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := hx s₁ h₁
  exact ⟨[v], s₂, EvalsL.cons e (EvalsL.nil _ _), h₂, v, rfl, rv⟩
theorem args2 {p s x y α β} {_ : TyRep α} {_ : TyRep β} {a : α} {b : β} (hx : SimE p s x a) (hy : SimE p s y b) :
    ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsL p s₁ [x, y] vs s₂ ∧ Ext s₁ s₂ ∧ Args2 a b s₂.heap vs := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := hx s₁ h₁
  obtain ⟨w, s₃, e', h₃, rw⟩ := hy s₂ (h₁.trans h₂)
  exact ⟨[v, w], s₃, EvalsL.cons e (EvalsL.cons e' (EvalsL.nil _ _)), h₂.trans h₃, v, w, rfl, mono h₃.2 rv, rw⟩
theorem args3 {p s x y z α β γ} {_ : TyRep α} {_ : TyRep β} {_ : TyRep γ} {a : α} {b : β} {c : γ} (hx : SimE p s x a) (hy : SimE p s y b) (hz : SimE p s z c) :
    ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsL p s₁ [x, y, z] vs s₂ ∧ Ext s₁ s₂ ∧ Args3 a b c s₂.heap vs := by
  intro s₁ h₁
  obtain ⟨v, s₂, e, h₂, rv⟩ := hx s₁ h₁
  obtain ⟨w, s₃, e', h₃, rw⟩ := hy s₂ (h₁.trans h₂)
  obtain ⟨u, s₄, e'', h₄, ru⟩ := hz s₃ ((h₁.trans h₂).trans h₃)
  exact ⟨[v, w, u], s₄, EvalsL.cons e (EvalsL.cons e' (EvalsL.cons e'' (EvalsL.nil _ _))), (h₂.trans h₃).trans h₄, v, w, u, rfl, mono (h₃.2.trans h₄.2) rv, mono h₄.2 rw, ru⟩

section prims
variable {p : Prog} {s : St} {x y z : Expr} {a b : List Nat}
theorem SimC.startsWith (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.prim .startsWith [x, y]) (Js.startsWith a b) :=
  by refine sim_prim (args2 hx hy) ?_; rintro _ _ ⟨_, _, rfl, rfl, rfl⟩; exact ⟨_, _, rfl, List.prefix_refl _, rfl⟩
theorem SimC.endsWith (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.prim .endsWith [x, y]) (Js.endsWith a b) :=
  by refine sim_prim (args2 hx hy) ?_; rintro _ _ ⟨_, _, rfl, rfl, rfl⟩; exact ⟨_, _, rfl, List.prefix_refl _, rfl⟩
theorem SimC.strIncludes (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.prim .strIncludes [x, y]) (Js.strIncludes a b) :=
  by refine sim_prim (args2 hx hy) ?_; rintro _ _ ⟨_, _, rfl, rfl, rfl⟩; exact ⟨_, _, rfl, List.prefix_refl _, rfl⟩
theorem SimC.includes_str (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.prim .includes [x, y]) (Js.strIncludes a b) :=
  by refine sim_prim (args2 hx hy) ?_; rintro _ _ ⟨_, _, rfl, rfl, rfl⟩; exact ⟨_, _, rfl, List.prefix_refl _, rfl⟩
theorem SimE.trim (hx : SimE p s x a) : SimE p s (.prim .trim [x]) (Js.trim a) :=
  by refine sim_prim (args1 hx) ?_; rintro _ _ ⟨_, rfl, rfl⟩; exact ⟨_, _, rfl, List.prefix_refl _, rfl⟩
theorem SimE.trimStart (hx : SimE p s x a) : SimE p s (.prim .trimStart [x]) (Js.trimStart a) :=
  by refine sim_prim (args1 hx) ?_; rintro _ _ ⟨_, rfl, rfl⟩; exact ⟨_, _, rfl, List.prefix_refl _, rfl⟩
theorem SimE.trimEnd (hx : SimE p s x a) : SimE p s (.prim .trimEnd [x]) (Js.trimEnd a) :=
  by refine sim_prim (args1 hx) ?_; rintro _ _ ⟨_, rfl, rfl⟩; exact ⟨_, _, rfl, List.prefix_refl _, rfl⟩
theorem okStr_ok {r : Result (List Nat)} {c} (h : r = ok c) : okStr r = some (.str c) := by
  subst h; simp [okStr, Result.match.ok]
theorem SimE.toLower {r} (hx : SimE p s x a) (h : Js.toLower a = ok r) : SimE p s (.prim .toLower [x]) r :=
  by refine sim_prim (args1 hx) ?_; rintro _ _ ⟨_, rfl, rfl⟩; exact ⟨_, _, by simp [primV, okStr_ok h], List.prefix_refl _, rfl⟩
theorem SimE.toUpper {r} (hx : SimE p s x a) (h : Js.toUpper a = ok r) : SimE p s (.prim .toUpper [x]) r :=
  by refine sim_prim (args1 hx) ?_; rintro _ _ ⟨_, rfl, rfl⟩; exact ⟨_, _, by simp [primV, okStr_ok h], List.prefix_refl _, rfl⟩
end prims

section moreprims
variable {p : Prog} {s : St} {x y z : Expr}
theorem num_arg {v : Val} {a : Js.Num} {h : Heap} (r : rep h a v) : asNum v = some a := by
  obtain ⟨x, rfl, hi⟩ := r; exact asNum_isInt hi
theorem SimE.slice_str {a : List Nat} {i j : Js.Num} (hx : SimE p s x a) (hy : SimE p s y i) (hz : SimE p s z j) :
    SimE p s (.prim .slice [x, y, z]) (Js.slice a i j) := by
  refine sim_prim (args3 hx hy hz) ?_
  rintro _ _ ⟨_, v, w, rfl, rfl, ri, rj⟩
  exact ⟨_, _, by simp [primV, num_arg ri, num_arg rj], List.prefix_refl _, rfl⟩
theorem SimE.sliceFrom_str {a : List Nat} {i : Js.Num} (hx : SimE p s x a) (hy : SimE p s y i) :
    SimE p s (.prim .sliceFrom [x, y]) (Js.sliceFrom a i) := by
  refine sim_prim (args2 hx hy) ?_
  rintro _ _ ⟨_, v, rfl, rfl, ri⟩
  exact ⟨_, _, by simp [primV, num_arg ri], List.prefix_refl _, rfl⟩
theorem SimE.slice_arr {α} {_ : TyRep α} {a : List α} {i j : Js.Num} (hx : SimE p s x a) (hy : SimE p s y i) (hz : SimE p s z j) :
    SimE p s (.prim .slice [x, y, z]) (Js.slice a i j) := by
  refine sim_prim (args3 hx hy hz) ?_
  rintro h _ ⟨_, v, w, rfl, ⟨l, vs, rfl, hl, hf⟩, ri, rj⟩
  have hlen := hf.length_eq
  refine ⟨.ref h.length, h ++ [.array (Js.slice vs i j)], by simp [primV, hl, num_arg ri, num_arg rj], List.prefix_append _ _, h.length, Js.slice vs i j, rfl, by simp, ?_⟩
  have hd : List.Forall₂ (rep (h ++ [.array (Js.slice vs i j)])) a vs := hf.imp fun _ _ r => mono (List.prefix_append _ _) r
  simp only [Js.slice, hlen]
  exact List.forall₂_drop _ (List.forall₂_take _ hd)
theorem SimE.sliceFrom_arr {α} {_ : TyRep α} {a : List α} {i : Js.Num} (hx : SimE p s x a) (hy : SimE p s y i) :
    SimE p s (.prim .sliceFrom [x, y]) (Js.sliceFrom a i) := by
  refine sim_prim (args2 hx hy) ?_
  rintro h _ ⟨_, v, rfl, ⟨l, vs, rfl, hl, hf⟩, ri⟩
  have hlen := hf.length_eq
  refine ⟨.ref h.length, h ++ [.array (Js.sliceFrom vs i)], by simp [primV, hl, num_arg ri], List.prefix_append _ _, h.length, Js.sliceFrom vs i, rfl, by simp, ?_⟩
  have hd : List.Forall₂ (rep (h ++ [.array (Js.sliceFrom vs i)])) a vs := hf.imp fun _ _ r => mono (List.prefix_append _ _) r
  simp only [Js.sliceFrom, hlen]
  exact List.forall₂_drop _ hd
theorem SimE.strIndexOf {a b : List Nat} {r : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) (h : Js.strIndexOf a b = ok r) :
    SimE p s (.prim .strIndexOf [x, y]) r := by
  refine sim_prim (args2 hx hy) ?_
  rintro _ _ ⟨_, _, rfl, rfl, rfl⟩
  exact ⟨numVal r, _, by simp [primV, h, Result.match.ok], List.prefix_refl _, _, rfl, Or.inl rfl⟩
theorem SimE.charAt {a : List Nat} {i : Js.Num} (hx : SimE p s x a) (hy : SimE p s y i) :
    SimE p s (.prim .charAt [x, y]) (Js.charAt a i) := by
  refine sim_prim (args2 hx hy) ?_
  rintro _ _ ⟨_, v, rfl, rfl, ri⟩
  exact ⟨_, _, by simp [primV, num_arg ri], List.prefix_refl _, rfl⟩
theorem SimE.numStr {a : Js.Num} (hx : SimE p s x a) : SimE p s (.prim .numStr [x]) (Js.numStr a) := by
  refine sim_prim (args1 hx) ?_
  rintro _ _ ⟨v, rfl, ri⟩
  exact ⟨_, _, by simp [primV, num_arg ri], List.prefix_refl _, rfl⟩
theorem SimE.min {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.prim .min [x, y]) (Js.min a b) := by
  refine sim_prim (args2 hx hy) ?_
  rintro _ _ ⟨v, w, rfl, ri, rj⟩
  exact ⟨numVal (Js.min a b), _, by simp [primV, num_arg ri, num_arg rj], List.prefix_refl _, _, rfl, Or.inl rfl⟩
theorem SimE.max {a b : Js.Num} (hx : SimE p s x a) (hy : SimE p s y b) : SimE p s (.prim .max [x, y]) (Js.max a b) := by
  refine sim_prim (args2 hx hy) ?_
  rintro _ _ ⟨v, w, rfl, ri, rj⟩
  exact ⟨numVal (Js.max a b), _, by simp [primV, num_arg ri, num_arg rj], List.prefix_refl _, _, rfl, Or.inl rfl⟩
theorem SimE.abs {a : Js.Num} (hx : SimE p s x a) : SimE p s (.prim .abs [x]) (Js.abs a) := by
  refine sim_prim (args1 hx) ?_
  rintro _ _ ⟨v, rfl, ri⟩
  exact ⟨numVal (Js.abs a), _, by simp [primV, num_arg ri], List.prefix_refl _, _, rfl, Or.inl rfl⟩
theorem strs_of {h : Heap} : ∀ {xs : List (List Nat)} {vs : List Val}, List.Forall₂ (rep h) xs vs → strsOf vs = some xs
  | _, _, .nil => rfl
  | _, _, .cons (a := a) (l₁ := l) hab t => by
    have hv : _ = Val.str a := hab
    subst hv
    simp [strsOf, strs_of t]
theorem SimE.join {a : List (List Nat)} {b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) :
    SimE p s (.prim .join [x, y]) (Js.join a b) := by
  refine sim_prim (args2 hx hy) ?_
  rintro _ _ ⟨_, _, rfl, ⟨l, vs, rfl, hl, hf⟩, rfl⟩
  exact ⟨_, _, by simp [primV, hl, strs_of hf], List.prefix_refl _, rfl⟩
theorem SimE.includes_arr {a : List (List Nat)} {b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) :
    SimE p s (.prim .includes [x, y]) (Js.includes a b) := by
  refine sim_prim (args2 hx hy) ?_
  rintro _ _ ⟨_, _, rfl, ⟨l, vs, rfl, hl, hf⟩, rfl⟩
  exact ⟨_, _, by simp [primV, hl, strs_of hf], List.prefix_refl _, rfl⟩
theorem forall_strs {h : Heap} (xs : List (List Nat)) : List.Forall₂ (rep h) xs (xs.map .str) := by
  induction xs with
  | nil => exact .nil
  | cons a t ih => exact .cons rfl ih
theorem SimE.split {a b : List Nat} (hx : SimE p s x a) (hy : SimE p s y b) :
    SimE p s (.prim .split [x, y]) (Js.split a b) := by
  refine sim_prim (args2 hx hy) ?_
  rintro h _ ⟨_, _, rfl, rfl, rfl⟩
  exact ⟨.ref h.length, h ++ [.array ((Js.split a b).map .str)], by simp [primV], List.prefix_append _ _, h.length, (Js.split a b).map .str, rfl, by simp, forall_strs _⟩
end moreprims

/-! Statements -/

def Wp (p : Prog) (s : St) (c : List Stmt) (Φ : Cmp → St → Prop) : Prop := ∃ r s', ExecsL p s c r s' ∧ Φ r s'
def WpRun (p : Prog) (fn : Fn) (a : List Val) (h : Heap) (Ψ : Val → St → Prop) : Prop :=
  ∃ v s', Runs p fn a h v s' ∧ Ψ v s'

/-- After a branch, run what follows it, unless the branch exited. -/
def Seq (p : Prog) (cs : List Stmt) (Φ : Cmp → St → Prop) (r : Cmp) (s : St) : Prop :=
  if r = .normal then Wp p s cs Φ else Φ r s

def Base (h : Heap) (s : St) : Prop := h <+: s.heap
def Ret {α} [TyRep α] (h : Heap) (a : α) (c : Cmp) (s : St) : Prop :=
  ∃ v, c = .ret v ∧ h <+: s.heap ∧ rep s.heap a v
theorem wprun' {p fn a h α} {_ : TyRep α} {r : α} (hb : Wp p ⟨fn.env0 a, h⟩ fn.body (Ret h r)) :
    WpRun p fn a h fun v s => h <+: s.heap ∧ rep s.heap r v := by
  obtain ⟨c, s', he, v, rfl, hr⟩ := hb; exact ⟨_, _, Runs.of he, hr⟩

/-- `Φ` accepts returning `a`. -/
def Post {α} [TyRep α] (Φ : Cmp → St → Prop) (h : Heap) (a : α) : Prop :=
  ∀ v s, h <+: s.heap → rep s.heap a v → Φ (.ret v) s
theorem post_ret {α} {_ : TyRep α} {h : Heap} {a : α} : Post (Ret h a) h a := fun v _ hb hr => ⟨v, rfl, hb, hr⟩
theorem post_seq {α} {_ : TyRep α} {p cs Φ h} {a : α} (k : Post Φ h a) : Post (Seq p cs Φ) h a := fun v s hb hr => by
  simpa [Seq] using k v s hb hr

theorem step_set {p s x e cs Φ α} {_ : TyRep α} {a : α} (he : SimE p s e a)
    (k : ∀ s', V s' x a → Upd s s' x → Wp p s' cs Φ) : Wp p s (.set x e :: cs) Φ := by
  obtain ⟨v, s₂, ev, h₂, rv⟩ := he s (Ext.refl _)
  obtain ⟨r, s₃, hrest, hΦ⟩ := k { s₂ with env := s₂.env.put x v } ⟨v, by simp [Env.put], rv⟩
    ⟨h₂.2, fun y hy => by simp [Env.put, hy, h₂.1]⟩
  exact ⟨r, s₃, ExecsL.cons_normal (Execs.set ev) hrest, hΦ⟩

theorem step_expr {p s e cs Φ α} {_ : TyRep α} {a : α} (he : SimE p s e a)
    (k : ∀ s', Ext s s' → Wp p s' cs Φ) : Wp p s (.expr e :: cs) Φ := by
  obtain ⟨v, s₂, ev, h₂, rv⟩ := he s (Ext.refl _)
  obtain ⟨r, s₃, hrest, hΦ⟩ := k s₂ h₂
  exact ⟨r, s₃, ExecsL.cons_normal (Execs.expr ev) hrest, hΦ⟩

theorem step_ret {p s e cs Φ h α} {_ : TyRep α} {a : α} (ho : Post Φ h a) (hb : Base h s) (he : SimE p s e a) :
    Wp p s (.ret e :: cs) Φ := by
  obtain ⟨v, s₂, ev, h₂, rv⟩ := he s (Ext.refl _)
  exact ⟨_, s₂, ExecsL.cons_exit (Execs.ret ev) (by simp), ho v s₂ (List.IsPrefix.trans hb h₂.2) rv⟩

theorem step_nil {p s cs Φ} (k : Wp p s cs Φ) : Wp p s [] (Seq p cs Φ) :=
  ⟨.normal, s, ExecsL.nil _ _, by simpa [Seq] using k⟩

theorem step_ite {p s c t e cs Φ P} (hc : SimB p s c P)
    (ht : P → ∀ s', Ext s s' → Wp p s' t (Seq p cs Φ))
    (hf : ¬P → ∀ s', Ext s s' → Wp p s' e (Seq p cs Φ)) : Wp p s (.ite c t e :: cs) Φ := by
  obtain ⟨v, s₂, ev, h₂, hv⟩ := hc s (Ext.refl _)
  cases htv : truthy v
  · have hn : ¬P := fun hp => by simp [hv.mpr hp] at htv
    obtain ⟨r, s₃, ht', hΦ⟩ := hf hn s₂ h₂
    by_cases hr : r = .normal
    · subst hr
      simp only [Seq, ite_true] at hΦ
      obtain ⟨r', s₄, hrest, hΦ'⟩ := hΦ
      exact ⟨r', s₄, ExecsL.cons_normal (Execs.ite_false ev htv ht') hrest, hΦ'⟩
    · simp only [Seq, if_neg hr] at hΦ
      exact ⟨r, s₃, ExecsL.cons_exit (Execs.ite_false ev htv ht') hr, hΦ⟩
  · have hp : P := hv.mp htv
    obtain ⟨r, s₃, ht', hΦ⟩ := ht hp s₂ h₂
    by_cases hr : r = .normal
    · subst hr
      simp only [Seq, ite_true] at hΦ
      obtain ⟨r', s₄, hrest, hΦ'⟩ := hΦ
      exact ⟨r', s₄, ExecsL.cons_normal (Execs.ite_true ev htv ht') hrest, hΦ'⟩
    · simp only [Seq, if_neg hr] at hΦ
      exact ⟨r, s₃, ExecsL.cons_exit (Execs.ite_true ev htv ht') hr, hΦ⟩

theorem wprun {p fn a h Ψ}
    (hb : Wp p ⟨fn.env0 a, h⟩ fn.body fun c s => ∃ v, c = .ret v ∧ Ψ v s) : WpRun p fn a h Ψ := by
  obtain ⟨c, s', he, v, rfl, hr⟩ := hb; exact ⟨_, _, Runs.of he, hr⟩

/-- Calling a function whose bridge is known. -/
theorem sim_call {p s g args} {vs' : Heap → List Val → Prop} {fn α} {_ : TyRep α} {r : α} (hg : p g = some fn)
    (ha : ∀ s₁, Ext s s₁ → ∃ vs s₂, EvalsL p s₁ args vs s₂ ∧ Ext s₁ s₂ ∧ vs' s₂.heap vs)
    (hb : ∀ h vs, vs' h vs → WpRun p fn vs h fun v s => h <+: s.heap ∧ rep s.heap r v) :
    SimE p s (.call g args) r := by
  intro s₁ h₁
  obtain ⟨vs, s₂, ea, h₂, hv⟩ := ha s₁ h₁
  obtain ⟨v, s₃, hrun, hpre, rv⟩ := hb _ _ hv
  exact ⟨v, { s₂ with heap := s₃.heap }, Evals.call ea hg hrun, h₂.trans ⟨rfl, hpre⟩, rv⟩

theorem ite_intro {α : Type} {c : Prop} [Decidable c] {a b : Result α} {r : α} {G : Prop}
    (t : c → a = ok r → G) (f : ¬c → b = ok r → G) : (if c then a else b) = ok r → G := by
  by_cases h : c
  · simp only [h, ite_true]; exact t h
  · simp only [h, ite_false]; exact f h
theorem unwrap_iff {α} {x : Option α} {r : α} : Js.unwrap x = ok r ↔ x = some r := by
  cases x <;> simp [Js.unwrap]
theorem bind_intro {α β : Type} {G : Prop} {x : Result α} {f : α → Result β} {r : β}
    (k : ∀ a, x = ok a → f a = ok r → G) : Aeneas.Std.bind x f = ok r → G := by
  intro h
  obtain ⟨a, ha, hf⟩ := bind_ok_inv' h
  exact k a ha hf
theorem ok_intro {α : Type} {G : Prop} {a b : α} (k : a = b → G) : (ok a : Result α) = ok b → G :=
  fun h => k (by simpa using h)
theorem fail_intro {α : Type} {G : Prop} {e} {r : α} : (Result.fail e : Result α) = ok r → G := by
  intro h; simp at h

end Core

/-- The heap half of a step's fact. -/
def carryHeap (kE : Lean.Expr) : MetaM Lean.Expr := do
  let t ← whnfR (← instantiateMVars (← inferType kE))
  let t' ← whnfCore (← unfoldDefinition t)
  let k' ← mkExpectedTypeHint kE t'
  if t.isAppOf ``Core.Upd then mkAppM ``And.left #[k'] else mkAppM ``And.right #[k']

/-- Moves every fact about variables across a step. -/
elab "carry " k:term : tactic => withMainContext do
  let kE ← Tactic.elabTerm k none
  let kT ← whnfR (← instantiateMVars (← inferType kE))
  let old := kT.getArg! 0
  let new := kT.getArg! 1
  let isUpd := kT.isAppOf ``Core.Upd
  let x := if isUpd then kT.getArg! 2 else mkNatLit 0
  let heap ← carryHeap kE
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Core.V 5 && (ty.getArg! 0) == old then
      let y := ty.getArg! 1
      let g ← getMainGoal
      if isUpd then
        if y == x then
          replaceMainGoal [← g.tryClear d.fvarId]
          continue
        let ne ← mkDecideProof (mkNot (← mkEq y x))
        let pf ← mkAppM ``Core.V.upd #[kE, ne, d.toExpr]
        let (_, g') ← (← g.assert d.userName (← inferType pf) pf).intro1P
        replaceMainGoal [← g'.tryClear d.fvarId]
      else
        let pf ← mkAppM ``Core.V.ext #[kE, d.toExpr]
        let (_, g') ← (← g.assert d.userName (← inferType pf) pf).intro1P
        replaceMainGoal [← g'.tryClear d.fvarId]
    else if ty.isAppOfArity ``Core.Base 2 && (ty.getArg! 1) == old then
      let g ← getMainGoal
      let pre ← mkAppM ``List.IsPrefix.trans #[d.toExpr, heap]
      let t ← mkAppM ``Core.Base #[ty.getArg! 0, new]
      let pf ← mkExpectedTypeHint pre t
      let (_, g') ← (← g.assert d.userName t pf).intro1P
      replaceMainGoal [← g'.tryClear d.fvarId]
