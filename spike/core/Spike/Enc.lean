import Core
import Spike.Rules
import ProofciJs
open Core Aeneas Aeneas.Std Result

/-! TypeScript types as preconditions: `enc h a v` says that JavaScript value `v`, in
heap `h`, represents the typed value `a`. Nothing about a value's type is assumed
beyond this, so a wrong cast would simply leave the bridge theorem unusable. -/
namespace Core

class Enc (α : Type) where
  enc : Heap → α → Val → Prop

instance : Enc Js.Num := ⟨fun _ a v => v = .num (F64.ofInt a.val)⟩
instance : Enc Int := ⟨fun _ a v => v = .big a⟩
instance : Enc Bool := ⟨fun _ a v => v = .bool a⟩
instance : Enc (List Nat) := ⟨fun _ a v => v = .str a⟩

instance {α} [Enc α] : Enc (Option α) := ⟨fun h a v => match a with
  | none => v = .undef ∨ v = .null
  | some x => Enc.enc h x v⟩

def EncArray {α} [Enc α] (h : Heap) (xs : List α) (v : Val) : Prop :=
  ∃ l vs, v = .ref l ∧ h[l]? = some (.array vs) ∧ List.Forall₂ (Enc.enc h) xs vs

instance {α} [Enc α] : Enc (List α) := ⟨EncArray⟩

theorem enc_at {α} [Enc α] {h : Heap} {xs : List α} {vs : List Val} (hl : List.Forall₂ (Enc.enc h) xs vs)
    (i : Nat) : Enc.enc h (xs[i]?) (vs[i]?.getD .undef) := by
  induction hl generalizing i with
  | nil => exact Or.inl (by simp)
  | cons hab _ ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.getD_some]; exact hab
    | succ n => simp only [List.getElem?_cons_succ]; exact ih n

end Core

namespace Core

/-- `e` reads as the typed value `a`, without changing anything. -/
def SimE {α} [Enc α] (p : Prog) (s : St) (e : Expr) (a : α) : Prop :=
  ∃ v, Evals p s e v s ∧ Enc.enc s.heap a v

end Core

namespace Core

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

end Core
