import Dyn
import Spike.Sim

/-! The typed view against the dynamic semantics. `crep h a v` says the dynamic value `v`
represents the typed value `a`. A number is any double equal to it, `-0` included, as in Core. -/

open Core Dyn Aeneas Aeneas.Std Result

class CRep (α : Type) where
  crep : Core.Heap → α → Core.Val → Prop

export CRep (crep)

namespace Dyn

/-- `v` is a number equal to the integer `a`; `-0` stands for `0`. -/
def NumIs (v : Val) (a : Int) : Prop := ∃ x, v = .num x ∧ F64.IsInt x a

theorem numIs_num {a : Int} : NumIs (num a) a := ⟨_, rfl, Or.inl rfl⟩

instance : CRep Js.Num := ⟨fun _ a v => NumIs v a.val⟩
instance : CRep Bool := ⟨fun _ a v => v = .bool a⟩
instance (priority := high) : CRep (List Nat) := ⟨fun _ a v => v = .str a⟩
instance {α} [CRep α] : CRep (List α) :=
  ⟨fun h xs v => ∃ l vs, v = .ref l ∧ h[l]? = some (.array vs) ∧ List.Forall₂ (crep h) xs vs⟩

/-- An optional value whose missing case is `nul`. -/
def crepOpt {α} [CRep α] (nul : Val) (h : Heap) : Option α → Val → Prop
  | none, v => v = nul
  | some a, v => crep h a v

theorem crep_num {h : Heap} {a : Js.Num} {v} : crep h a v ↔ NumIs v a.val := Iff.rfl
theorem crep_bool {h : Heap} {a : Bool} {v} : crep h a v ↔ v = .bool a := Iff.rfl
theorem crep_str {h : Heap} {a : List Nat} {v} : crep h a v ↔ v = .str a := Iff.rfl
theorem crep_list {α} [CRep α] {h : Heap} {xs : List α} {v} :
    crep h xs v ↔ ∃ l vs, v = .ref l ∧ h[l]? = some (.array vs) ∧ List.Forall₂ (crep h) xs vs := Iff.rfl
@[simp] theorem crepOpt_none {α} [CRep α] {nul h v} : crepOpt (α := α) nul h none v ↔ v = nul := Iff.rfl
@[simp] theorem crepOpt_some {α} [CRep α] {nul h v} {a : α} : crepOpt nul h (some a) v ↔ crep h a v := Iff.rfl

end Dyn

namespace Dyn

theorem ok_eq_ok {α : Type} {a b : α} : (ok a : Result α) = ok b ↔ a = b :=
  ⟨fun h => by simpa using h, fun h => h ▸ rfl⟩

theorem bind_ok {α β : Type} {x : Result α} {f : α → Result β} {r : β} (h : (x >>= f) = ok r) :
    ∃ a, x = ok a ∧ f a = ok r := bind_ok_inv' h

theorem add_ok_safe {x y t : Js.Num} (h : Js.add x y = ok t) :
    -9007199254740991 ≤ x.val + y.val ∧ x.val + y.val ≤ 9007199254740991 := by
  have := add_val h; have := t.lo; have := t.hi; omega
theorem sub_ok_safe {x y t : Js.Num} (h : Js.sub x y = ok t) :
    -9007199254740991 ≤ x.val - y.val ∧ x.val - y.val ≤ 9007199254740991 := by
  have := sub_val h; have := t.lo; have := t.hi; omega
theorem mul_ok_safe {x y t : Js.Num} (h : Js.mul x y = ok t) :
    -9007199254740991 ≤ x.val * y.val ∧ x.val * y.val ≤ 9007199254740991 := by
  have := mul_val h; have := t.lo; have := t.hi; omega

/-- An operation is safe on the dynamic side when the typed side computed it. -/
macro_rules | `(tactic| dsafe) => `(tactic| first | exact add_ok_safe ‹_› | exact sub_ok_safe ‹_› | exact mul_ok_safe ‹_›)


/-- The typed result `t`, when there is one, is related by `Q` to what `d` returns from `h`. -/
@[irreducible] def Rel {α : Type} (t : Result α) (d : M Val) (h : Heap) (Q : α → Val → Heap → Prop) : Prop :=
  ∀ r, t = ok r → Spec d h (Q r)

theorem rel_intro {α : Type} {t : Result α} {d h Q} (H : Rel t d h Q) {r} (e : t = ok r) : Spec d h (Q r) := by
  unfold Rel at H; exact H r e

theorem rel_ok {α : Type} {x : α} {d h Q} (H : Spec d h (Q x)) : Rel (ok x) d h Q := by
  unfold Rel; intro r e; rw [ok_eq_ok] at e; subst e; exact H

theorem tbind_ok {α β : Type} {x : α} {g : α → Result β} : Std.bind (ok x) g = g x := by simp

theorem dbind_assoc {α β γ : Type} {m : M α} {f : α → M β} {k : β → M γ} :
    ((m >>= f) >>= k) = (m >>= fun a => f a >>= k) := by
  funext h; show M.bind (M.bind m f) k h = M.bind m (fun a => M.bind (f a) k) h
  unfold M.bind; cases m h <;> rfl

theorem dpure_bind {α β : Type} {a : α} {k : α → M β} : ((pure a : M α) >>= k) = k a := rfl

theorem spec_rok {α : Type} {a : α} {h : Heap} {P : α → Heap → Prop} :
    Spec (R.ok a : M α) h P ↔ P a h := Iff.rfl

/-- One dynamic step the typed side doesn't see. -/
theorem rel_dbind {α β : Type} {t : Result α} {m : M β} {k : β → M Val} {h Q}
    (H : Spec m h fun v h' => Rel t (k v) h' Q) : Rel t (m >>= k) h Q := by
  unfold Rel at *; intro r e; rw [spec_bind]; exact spec_mono H fun _ _ H' => H' r e

open Core.F64 in
theorem rel_add {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, a.val + b.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.add a b) g) (bin .add v w >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hval := add_val et
  have hlo := t.lo; have hhi := t.hi; rw [hval] at hlo hhi
  have hi : IsInt _ t.val := hval ▸ add_isInt hx hy hlo hhi
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

open Core.F64 in
theorem rel_sub {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, a.val - b.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.sub a b) g) (bin .sub v w >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hval := sub_val et
  have hlo := t.lo; have hhi := t.hi; rw [hval] at hlo hhi
  have hi : IsInt _ t.val := hval ▸ sub_isInt hx hy hlo hhi
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

open Core.F64 in
theorem rel_mul {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, a.val * b.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.mul a b) g) (bin .mul v w >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hval := mul_val et
  have hlo := t.lo; have hhi := t.hi; rw [hval] at hlo hhi
  have hi : IsInt _ t.val := hval ▸ mul_isInt' hx hy hlo hhi
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

open Core.F64 in
theorem rel_rem {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, Int.tmod a.val b.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.rem a b) g) (bin .rem v w >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  obtain ⟨hb, hval⟩ := rem_val et
  have hi : IsInt _ t.val := hval ▸ rem_isInt hx hy hb
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

open Core.F64 in
theorem rel_floorDiv {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, Int.fdiv a.val b.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.floorDiv a b) g) (bin .div v w >>= fun q => math F64.floor q >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  obtain ⟨hb, hval⟩ := floorDiv_val et
  have hi : IsInt _ t.val := hval ▸ floorDiv_isInt hx hy hb a.lo a.hi b.lo b.hi
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

open Core.F64 in
theorem rel_ceilDiv {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, -Int.fdiv (-a.val) b.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.ceilDiv a b) g) (bin .div v w >>= fun q => math F64.ceil q >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  obtain ⟨hb, hval⟩ := ceilDiv_val et
  have hi : IsInt _ t.val := hval ▸ ceilDiv_isInt hx hy hb a.lo a.hi b.lo b.hi
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

open Core.F64 in
theorem rel_truncDiv {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, Int.tdiv a.val b.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.truncDiv a b) g) (bin .div v w >>= fun q => math F64.trunc q >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  obtain ⟨hb, hval⟩ := truncDiv_val et
  have hi : IsInt _ t.val := hval ▸ truncDiv_isInt hx hy hb a.lo a.hi b.lo b.hi
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

open Core.F64 in
theorem rel_neg {α : Type} {a : Js.Num} {v : Val} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (hv : NumIs v a.val) (H : ∀ t : Js.Num, -a.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.neg a) g) (neg v >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hval : t.val = -a.val := by simp only [Js.neg, Js.mk] at et; split at et <;> simp_all; subst et; rfl
  have hi : IsInt _ t.val := hval ▸ neg_isInt hx
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

section
open Core.F64
variable {v w : Val} {a b : Int}
theorem bin_lt_is (hv : NumIs v a) (hw : NumIs w b) : bin .lt v w = pure (.bool (decide (a < b))) := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  show (pure (.bool (x.lt y)) : M Val) = _; rw [lt_isInt hx hy]
theorem bin_gt_is (hv : NumIs v a) (hw : NumIs w b) : bin .gt v w = pure (.bool (decide (b < a))) := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  show (pure (.bool (y.lt x)) : M Val) = _; rw [lt_isInt hy hx]
theorem bin_le_is (hv : NumIs v a) (hw : NumIs w b) : bin .le v w = pure (.bool (decide (a ≤ b))) := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  show (pure (.bool (x.le y)) : M Val) = _; rw [le_isInt hx hy]
theorem bin_ge_is (hv : NumIs v a) (hw : NumIs w b) : bin .ge v w = pure (.bool (decide (b ≤ a))) := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  show (pure (.bool (y.le x)) : M Val) = _; rw [le_isInt hy hx]
theorem bin_eq_is (hv : NumIs v a) (hw : NumIs w b) : bin .eq v w = pure (.bool (decide (a = b))) := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  show (pure (.bool (x.eq y)) : M Val) = _; rw [eq_isInt hx hy]
theorem bin_ne_is (hv : NumIs v a) (hw : NumIs w b) : bin .ne v w = pure (.bool (!decide (a = b))) := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  show (pure (.bool (!x.eq y)) : M Val) = _; rw [eq_isInt hx hy]
end

theorem dbind_pure {α : Type} {m : M α} : (m >>= pure) = m := by
  funext h; show M.bind m M.pure h = m h
  unfold M.bind M.pure; cases m h <;> rfl

/-- An operation in tail position: give it a `pure` continuation. -/
theorem rel_tail {α : Type} {t : Result α} {m : M Val} {h Q} (H : Rel t (m >>= pure) h Q) : Rel t m h Q := by
  rwa [dbind_pure] at H

open Core.F64 in
theorem spec_min {a b : Js.Num} {v w : Val} {h P} (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ u, NumIs u (Js.min a b).val → P u h) : Spec (prim .min [v, w]) h P := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  have e : prim .min [.num x, .num y] h = .ok (.num (x.fmin y)) h := by simp [prim, primV] <;> rfl
  rw [spec_eq e]
  refine H _ ⟨_, rfl, ?_⟩
  have := min_isInt hx hy
  unfold Js.min; split <;> simp_all

theorem rel_min_ok {a b : Js.Num} {v w : Val} {h} {Q : Js.Num → Val → Heap → Prop}
    (hv : NumIs v a.val) (hw : NumIs w b.val) (H : ∀ u, NumIs u (Js.min a b).val → Q (Js.min a b) u h) :
    Rel (ok (Js.min a b)) (prim .min [v, w]) h Q := by
  unfold Rel; intro r e; rw [ok_eq_ok] at e; subst e
  exact spec_min (P := Q (Js.min a b)) hv hw H

macro_rules | `(tactic| dsafe) => `(tactic| first | exact numIs_num | assumption)

/-- Closes the side goals of a relational lemma: the operands are numbers, then introduces the result. -/
macro "rnum" : tactic => `(tactic| first | (intro _ _ _ _) | exact numIs_num | assumption)

macro "rmin" : tactic => `(tactic| first | (intro _ _) | exact numIs_num | assumption)

/-- One typed number operation with its dynamic twin. -/
macro "rops" : tactic => `(tactic| first
  | (refine rel_add ?_ ?_ ?_ <;> rnum)
  | (refine rel_sub ?_ ?_ ?_ <;> rnum)
  | (refine rel_mul ?_ ?_ ?_ <;> rnum)
  | (refine rel_rem ?_ ?_ ?_ <;> rnum)
  | (refine rel_floorDiv ?_ ?_ ?_ <;> rnum)
  | (refine rel_ceilDiv ?_ ?_ ?_ <;> rnum)
  | (refine rel_truncDiv ?_ ?_ ?_ <;> rnum)
  | (refine rel_neg ?_ ?_ <;> rnum))

/-- Steps the typed view and the dynamic code together: a typed operation with its dynamic
twin, a typed `ok` bind, a branch on both sides at once, or one dynamic step. -/
macro "rsteps" : tactic => `(tactic| repeat' (first
  | (refine rel_min_ok ?_ ?_ ?_ <;> rmin)
  | (exfalso; (try simp only [truthy_bool, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not, decide_eq_false_iff_not] at *); omega)
  | rops
  | (refine rel_tail ?_; (try simp only [dbind_assoc]); rops)
  | (simp only [Std.bind_ok, Std.bind_assoc, bind_tc_ok, bind_assoc_eq, dbind_assoc, dpure_bind])
  | (apply rel_ok; (try simp only [spec_rok]); first | (refine spec_min ?_ ?_ ?_ <;> first | (intro _ _) | exact numIs_num | assumption) | (try dsteps [bin_lt_is, bin_gt_is, bin_le_is, bin_ge_is, bin_eq_is, bin_ne_is]))
  | (split <;> (rename_i hc
                try simp only [truthy_bool, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not, decide_eq_false_iff_not] at hc
                try dsteps [bin_lt_is, bin_gt_is, bin_le_is, bin_ge_is, bin_eq_is, bin_ne_is]))
  | (apply rel_dbind; dsteps [bin_lt_is, bin_gt_is, bin_le_is, bin_ge_is, bin_eq_is, bin_ne_is])))

end Dyn
