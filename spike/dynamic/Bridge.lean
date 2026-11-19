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

set_option hygiene false in
/-- Takes the typed result `hr` apart: each bind, branch and final `ok`. -/
macro "tsteps" : tactic => `(tactic| repeat' (first
  | (rw [ok_eq_ok] at hr; subst hr)
  | (obtain ⟨_, he, hr⟩ := bind_ok hr
     try (rw [ok_eq_ok] at he; subst he)
     try (have := add_val he)
     try (have := sub_val he)
     try (have := mul_val he))
  | (split at hr)))

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

end Dyn
