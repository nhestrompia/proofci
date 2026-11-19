import Dyn
import Spike.Sim

/-! The typed view against the dynamic semantics. `crep h a v` says the dynamic value `v`
represents the typed value `a`, canonically: a number is `num a.val`. -/

open Core Dyn Aeneas Aeneas.Std Result

class CRep (α : Type) where
  crep : Core.Heap → α → Core.Val → Prop

export CRep (crep)

namespace Dyn

instance : CRep Js.Num := ⟨fun _ a v => v = num a.val⟩
instance : CRep Bool := ⟨fun _ a v => v = .bool a⟩
instance (priority := high) : CRep (List Nat) := ⟨fun _ a v => v = .str a⟩
instance {α} [CRep α] : CRep (List α) :=
  ⟨fun h xs v => ∃ l vs, v = .ref l ∧ h[l]? = some (.array vs) ∧ List.Forall₂ (crep h) xs vs⟩

/-- An optional value whose missing case is `nul`. -/
def crepOpt {α} [CRep α] (nul : Val) (h : Heap) : Option α → Val → Prop
  | none, v => v = nul
  | some a, v => crep h a v

theorem crep_num {h : Heap} {a : Js.Num} {v} : crep h a v ↔ v = num a.val := Iff.rfl
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

theorem rel_add {α : Type} {a b : Js.Num} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (H : ∀ t : Js.Num, a.val + b.val = t.val → Rel (g t) (k (num t.val)) h Q) :
    Rel (Std.bind (Js.add a b) g) (bin .add (num a.val) (num b.val) >>= k) h Q := by
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hv := add_val et
  rw [spec_bind, bin_add_num (add_ok_safe et), spec_pure, ← hv]
  have H' := H t hv.symm; unfold Rel at H'; exact H' r er

theorem rel_sub {α : Type} {a b : Js.Num} {g : Js.Num → Result α} {k : Val → M Val} {h Q}
    (H : ∀ t : Js.Num, a.val - b.val = t.val → Rel (g t) (k (num t.val)) h Q) :
    Rel (Std.bind (Js.sub a b) g) (bin .sub (num a.val) (num b.val) >>= k) h Q := by
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hv := sub_val et
  rw [spec_bind, bin_sub_num (sub_ok_safe et), spec_pure, ← hv]
  have H' := H t hv.symm; unfold Rel at H'; exact H' r er

/-- Steps the typed view and the dynamic code together: a typed operation with its dynamic
twin, a typed `ok` bind, a branch on both sides at once, or one dynamic step. -/
macro "rsteps" : tactic => `(tactic| repeat' (first
  | (exfalso; (try simp only [truthy_bool, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not, decide_eq_false_iff_not] at *); omega)
  | (apply rel_add; intro _ _)
  | (apply rel_sub; intro _ _)
  | (simp only [Std.bind_ok, Std.bind_assoc, bind_tc_ok, bind_assoc_eq, dbind_assoc, dpure_bind])
  | (apply rel_ok; (try simp only [spec_rok]); try dsteps)
  | (split <;> (rename_i hc
                try simp only [truthy_bool, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not, decide_eq_false_iff_not] at hc
                try dsteps))
  | (apply rel_dbind; dsteps)))

end Dyn
