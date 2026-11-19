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
/-- A typed `none` is `null` or `undefined`: the typed view does not tell them apart. -/
instance {α} [CRep α] : CRep (Option α) :=
  ⟨fun h o v => match o with | none => v = .null ∨ v = .undef | some a => crep h a v⟩

/-- An optional value whose missing case is `nul`. -/
def crepOpt {α} [CRep α] (nul : Val) (h : Heap) : Option α → Val → Prop
  | none, v => v = nul
  | some a, v => crep h a v

theorem crep_num {h : Heap} {a : Js.Num} {v} : crep h a v ↔ NumIs v a.val := Iff.rfl
theorem crep_bool {h : Heap} {a : Bool} {v} : crep h a v ↔ v = .bool a := Iff.rfl
theorem crep_str {h : Heap} {a : List Nat} {v} : crep h a v ↔ v = .str a := Iff.rfl
theorem crep_list {α} [CRep α] {h : Heap} {xs : List α} {v} :
    crep h xs v ↔ ∃ l vs, v = .ref l ∧ h[l]? = some (.array vs) ∧ List.Forall₂ (crep h) xs vs := Iff.rfl
theorem crep_none {α} [CRep α] {h : Heap} {v} : crep h (none : Option α) v ↔ v = .null ∨ v = .undef := Iff.rfl
theorem crep_some {α} [CRep α] {h : Heap} {a : α} {v} : crep h (some a) v ↔ crep h a v := Iff.rfl
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
@[irreducible] def Rel {α δ : Type} (t : Result α) (d : M δ) (h : Heap) (Q : α → δ → Heap → Prop) : Prop :=
  ∀ r, t = ok r → Spec d h (Q r)

theorem rel_intro {α : Type} {t : Result α} {δ : Type} {d : M δ} {h Q} (H : Rel t d h Q) {r} (e : t = ok r) : Spec d h (Q r) := by
  unfold Rel at H; exact H r e

theorem rel_ok {α : Type} {x : α} {δ : Type} {d : M δ} {h Q} (H : Spec d h (Q x)) : Rel (ok x) d h Q := by
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
theorem rel_dbind {α β : Type} {t : Result α} {m : M β} {δ : Type} {k : β → M δ} {h Q}
    (H : Spec m h fun v h' => Rel t (k v) h' Q) : Rel t (m >>= k) h Q := by
  unfold Rel at *; intro r e; rw [spec_bind]; exact spec_mono H fun _ _ H' => H' r e

open Core.F64 in
theorem rel_add {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
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
theorem rel_sub {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
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
theorem rel_mul {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
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
theorem rel_div {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ t : Js.Num, a.val = b.val * t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.div a b) g) (bin .div v w >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv
  obtain ⟨y, rfl, hy⟩ := hw
  unfold Rel at *
  intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  obtain ⟨hb, hq⟩ := div_val et
  have hi : IsInt (x.div y) t.val := div_isInt (hq ▸ hx) hy hb t.lo t.hi
  have H' := H t hq _ ⟨_, rfl, hi⟩
  unfold Rel at H'
  exact H' r er

open Core.F64 in
theorem rel_rem {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
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
theorem rel_floorDiv {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
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
theorem rel_ceilDiv {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
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
theorem rel_truncDiv {α : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
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
theorem rel_neg {α : Type} {a : Js.Num} {v : Val} {g : Js.Num → Result α} {δ : Type} {k : Val → M δ} {h Q}
    (hv : NumIs v a.val) (H : ∀ t : Js.Num, -a.val = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.neg a) g) (neg v >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hval : t.val = -a.val := by simp only [Js.neg, Js.mk] at et; split at et <;> simp_all; subst et; rfl
  have hi : IsInt _ t.val := hval ▸ neg_isInt hx
  have H' := H t hval.symm _ ⟨_, rfl, hi⟩
  unfold Rel at H'; exact H' r er

theorem rel_arr {α β δ : Type} [CRep α] {xs : List α} {vs : List Val} {g : List α → Result β}
    {k : Val → M δ} {h Q}
    (hf : List.Forall₂ (crep (h ++ [.array vs])) xs vs)
    (H : (h ++ [.array vs])[h.length]? = some (.array vs) →
      List.Forall₂ (crep (h ++ [.array vs])) xs vs → Rel (g xs) (k (.ref h.length)) (h ++ [.array vs]) Q) :
    Rel (Std.bind (ok xs) g) (arr vs >>= k) h Q := by
  have H' := H (by simp) hf
  unfold Rel at *; intro r e
  rw [Std.bind_ok] at e
  rw [spec_bind, spec_arr]
  exact H' r e

theorem nullish_of_crep_none {α} [CRep α] {h : Heap} {u : Val} (hu : crep h (none : Option α) u) :
    nullish u = true := by rcases hu with rfl | rfl <;> rfl

theorem not_nullish_of_crep_some {h : Heap} {u : Val} {x : Js.Num} (hu : crep h (some x) u) :
    nullish u = false := by obtain ⟨_, rfl, _⟩ := hu; rfl

theorem rel_dtoNum {α δ : Type} {t : Result α} {b : Bool} {v : Val} {k : Val → M δ} {h Q}
    (hv : v = .bool b) (H : ∀ u, NumIs u (Js.boolNum b).val → Rel t (k u) h Q) :
    Rel t (toNum v >>= k) h Q := by
  subst hv
  have H' := H (num (if b then 1 else 0)) (by cases b <;> exact numIs_num)
  unfold Rel at *; intro r e
  show Spec (pure (num (if b then 1 else 0)) >>= k) h (Q r)
  rw [dpure_bind]; exact H' r e

@[simp] theorem isArray_true {α} (xs : List α) : Js.isArray xs = true := rfl

theorem rel_isArray_arr {α δ : Type} {t : Result α} {v : Val} {l : Loc} {vs : List Val}
    {k : Val → M δ} {h Q} (hv : v = .ref l) (hl : h[l]? = some (.array vs))
    (H : Rel t (k (.bool true)) h Q) : Rel t (isArray v >>= k) h Q := by
  subst hv; unfold Rel at *; intro r e
  have ep : isArray (.ref l) h = .ok (.bool true) h := by
    show (match h[l]? with | some (.array _) => _ | some (.record _) => _ | none => _) = _
    rw [hl]
  rw [spec_bind, spec_eq ep]; exact H r e

theorem rel_isArray_nul {α δ : Type} {t : Result α} {v : Val} {k : Val → M δ} {h Q}
    (hv : v = .null ∨ v = .undef) (H : Rel t (k (.bool false)) h Q) : Rel t (isArray v >>= k) h Q := by
  unfold Rel at *; intro r e
  rcases hv with rfl | rfl <;>
  · show Spec (pure (Val.bool false) >>= k) h (Q r)
    rw [dpure_bind]; exact H r e

theorem rel_isArray_opt {α β δ : Type} [CRep α] {t : Result β} {o : Option (List α)} {v nul : Val}
    {k : Val → M δ} {h Q} (hv : crepOpt nul h o v) (hn : nul = .null ∨ nul = .undef)
    (H : Rel t (k (.bool o.isSome)) h Q) : Rel t (isArray v >>= k) h Q := by
  cases o with
  | none =>
    simp only [crepOpt_none] at hv; subst hv
    exact rel_isArray_nul hn H
  | some xs =>
    simp only [crepOpt_some] at hv
    obtain ⟨l, vs, rfl, hl, _⟩ := hv
    exact rel_isArray_arr rfl hl H

@[simp] theorem truthy_str {s : List Nat} : truthy (.str s) = decide (s ≠ []) := by
  cases s <;> rfl

theorem rel_trim {β δ : Type} {s : List Nat} {g : List Nat → Result β} {k : Val → M δ} {h Q}
    (H : Rel (g (Js.trim s)) (k (.str (Js.trim s))) h Q) :
    Rel (Std.bind (ok (Js.trim s)) g) (method .trim (.str s) [] >>= k) h Q := by
  unfold Rel at *; intro r e
  rw [Std.bind_ok] at e
  show Spec (pure (Val.str (Js.trim s)) >>= k) h (Q r)
  rw [dpure_bind]; exact H r e

open Core.F64 in
theorem truthy_numIs {v : Val} {a : Int} (hv : NumIs v a) : truthy v = decide (a ≠ 0) := by
  obtain ⟨x, rfl, hx⟩ := hv
  rcases hx with rfl | ⟨rfl, rfl⟩
  · unfold F64.ofInt
    generalize hn : a.natAbs * unit = n
    have hu := unit_pos
    cases n with
    | zero =>
      have ha : a = 0 := by rcases Nat.mul_eq_zero.mp hn with h | h <;> omega
      subst ha; rfl
    | succ m =>
      have ha : a ≠ 0 := by rintro rfl; simp at hn
      simp [truthy, ha]
  · rfl

open Core.F64 in
theorem rel_dneg {α δ : Type} {t : Result α} {a : Int} {v : Val} {k : Val → M δ} {h Q}
    (hv : NumIs v a) (H : ∀ u, NumIs u (-a) → Rel t (k u) h Q) :
    Rel t (neg v >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv
  have H' := H _ ⟨_, rfl, neg_isInt hx⟩
  unfold Rel at *
  intro r e
  show Spec (pure (Val.num x.neg) >>= k) h (Q r)
  rw [dpure_bind]
  exact H' r e

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
theorem rel_tail {α δ : Type} {t : Result α} {m : M δ} {h Q} (H : Rel t (m >>= pure) h Q) : Rel t m h Q := by
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
    (hv : NumIs v a.val) (hw : NumIs w b.val) (H : ∀ u, NumIs u (min a.val b.val) → Q (Js.min a b) u h) :
    Rel (ok (Js.min a b)) (prim .min [v, w]) h Q := by
  unfold Rel; intro r e; rw [ok_eq_ok] at e; subst e
  have m : (Js.min a b).val = min a.val b.val := by
    unfold Js.min; split <;> rename_i hc <;> simp [Int.min_def, hc]
  exact spec_min (P := Q (Js.min a b)) hv hw fun u hu => H u (m ▸ hu)

@[simp] theorem max_val {a b : Js.Num} : (Js.max a b).val = max a.val b.val := by
  unfold Js.max; split <;> rename_i hc <;> simp [Int.max_def, hc]

open Core.F64 in
theorem rel_max {β : Type} {a b : Js.Num} {v w : Val} {g : Js.Num → Result β} {δ : Type} {k : Val → M δ} {h Q}
    (hv : NumIs v a.val) (hw : NumIs w b.val)
    (H : ∀ u, NumIs u (Js.max a b).val → Rel (g (Js.max a b)) (k u) h Q) :
    Rel (Std.bind (ok (Js.max a b)) g) (prim .max [v, w] >>= k) h Q := by
  obtain ⟨x, rfl, hx⟩ := hv; obtain ⟨y, rfl, hy⟩ := hw
  have e : prim .max [.num x, .num y] h = .ok (.num (x.fmax y)) h := by simp [prim, primV] <;> rfl
  have m : (Js.max a b).val = if a.val ≤ b.val then b.val else a.val := by
    unfold Js.max; split <;> rfl
  have H' := H _ ⟨_, rfl, m ▸ max_isInt hx hy⟩
  unfold Rel at *; intro r e'
  rw [Std.bind_ok] at e'
  rw [spec_bind, spec_eq e]
  exact H' r e'

theorem rel_len {α β : Type} [CRep α] {xs : List α} {vs : List Val} {l : Loc}
    {g : Js.Num → Result β} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (H : ∀ t : Js.Num, (xs.length : Int) = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.len xs) g) (length (.ref l) >>= k) h Q := by
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have H' := H t (len_val et).symm (num vs.length) ⟨_, rfl, Or.inl (by rw [len_val et, hf.length_eq])⟩
  unfold Rel at H'
  rw [spec_bind, spec_eq (length_arr hl)]; exact H' r er

theorem rel_slen {β : Type} {s : List Nat} {g : Js.Num → Result β} {δ : Type} {k : Val → M δ} {h Q}
    (H : ∀ t : Js.Num, (s.length : Int) = t.val → ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.len s) g) (length (.str s) >>= k) h Q := by
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have H' := H t (len_val et).symm (num s.length) ⟨_, rfl, Or.inl (by rw [len_val et])⟩
  unfold Rel at H'; exact H' r er

theorem f2_get {α β : Type} {R : α → β → Prop} : ∀ {xs ys} (_ : List.Forall₂ R xs ys) {i : Nat}
    (hx : i < xs.length) (hy : i < ys.length), R xs[i] ys[i]
  | _, _, .nil, _, hx, _ => absurd hx (by simp)
  | _, _, .cons hr _, 0, _, _ => hr
  | _, _, .cons _ hf, i + 1, hx, hy => f2_get hf (i := i) (by simpa using hx) (by simpa using hy)

theorem f2_append {α β : Type} {R : α → β → Prop} : ∀ {a b c d},
    List.Forall₂ R a b → List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons r h, h' => .cons r (f2_append h h')

theorem map_ok {α β : Type} {f : α → Result β} : ∀ {xs : List α} {ys : List β},
    Js.map f xs = ok ys → List.Forall₂ (fun x y => f x = ok y) xs ys
  | [], ys, e => by simp only [Js.map, ok_eq_ok] at e; subst e; exact .nil
  | x :: rest, ys, e => by
    simp only [Js.map] at e
    obtain ⟨y, ey, e2⟩ := bind_ok e
    obtain ⟨ys', eys, e3⟩ := bind_ok e2
    rw [ok_eq_ok] at e3; subst e3
    exact .cons ey (map_ok eys)

/-- `xs.map(f)` on numbers, with a callback that leaves the heap alone. -/
theorem rel_map {γ : Type} {f : Js.Num → Result Js.Num} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {G : List Js.Num → Result γ} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun y w h' => h' = h ∧ crep h y w))
    (H : ∀ ys ws, crep (h ++ [.array ws]) ys (.ref h.length) → Rel (G ys) (k (.ref h.length)) (h ++ [.array ws]) Q) :
    Rel (Std.bind (Js.map f xs) G) (jsMap (.ref l) g >>= k) h Q := by
  unfold Rel at *; intro r e
  obtain ⟨ys, ey, er⟩ := bind_ok e
  have hm := map_ok ey
  rw [spec_bind]
  refine jsMap_spec (I := fun i out h' => h' = h ∧ List.Forall₂ (crep h) (ys.take i) out)
    ⟨rfl, by rw [List.take_zero]; exact .nil⟩ (fun _ _ _ hI => hI.1 ▸ hl) ?_ ?_
  · rintro i out h' hi ⟨rfl, hI⟩
    have hx : i < xs.length := hf.length_eq ▸ hi
    have hy : i < ys.length := hm.length_eq ▸ hx
    have H' := hg xs[i] vs[i] i (f2_get hf hx hi)
    unfold Rel at H'
    refine spec_mono (H' ys[i] (f2_get hm hx hy)) ?_
    rintro w h'' ⟨rfl, hw⟩
    refine ⟨rfl, ?_⟩
    rw [List.take_succ, List.getElem?_eq_getElem hy, Option.toList_some]
    exact f2_append hI (.cons hw .nil)
  · rintro out h' ⟨he, hI⟩
    rw [he]
    rw [List.take_of_length_le (by rw [← hm.length_eq, hf.length_eq])] at hI
    have H' := H ys out ⟨h.length, out, rfl, by simp, hI⟩
    unfold Rel at H'; exact H' r er

def filtBy {α : Type} : List α → List Bool → List α
  | x :: xs, b :: bs => if b then x :: filtBy xs bs else filtBy xs bs
  | _, _ => []

theorem filtBy_append {α : Type} : ∀ {a : List α} {c : List Bool} {b d},
    a.length = c.length → filtBy (a ++ b) (c ++ d) = filtBy a c ++ filtBy b d
  | [], [], _, _, _ => rfl
  | x :: a, y :: c, b, d, e => by
    simp only [List.cons_append, filtBy]; rw [filtBy_append (by simpa using e)]; split <;> rfl
  | [], _ :: _, _, _, e => by simp at e
  | _ :: _, [], _, _, e => by simp at e

theorem filter_ok {α : Type} {f : α → Result Bool} : ∀ {xs ys : List α},
    Js.filter f xs = ok ys → ∃ bs, List.Forall₂ (fun x b => f x = ok b) xs bs ∧ ys = filtBy xs bs
  | [], ys, e => by simp only [Js.filter, ok_eq_ok] at e; subst e; exact ⟨[], .nil, rfl⟩
  | x :: rest, ys, e => by
    simp only [Js.filter] at e
    obtain ⟨b, eb, e2⟩ := bind_ok e
    obtain ⟨ys', eys, e3⟩ := bind_ok e2
    rw [ok_eq_ok] at e3; subst e3
    obtain ⟨bs, hbs, rfl⟩ := filter_ok eys
    exact ⟨b :: bs, .cons eb hbs, by cases b <;> rfl⟩

/-- `xs.filter(f)` on numbers, with a callback that leaves the heap alone. -/
theorem rel_filter {γ : Type} {f : Js.Num → Result Bool} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {G : List Js.Num → Result γ} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w))
    (H : ∀ ys ws, crep (h ++ [.array ws]) ys (.ref h.length) → Rel (G ys) (k (.ref h.length)) (h ++ [.array ws]) Q) :
    Rel (Std.bind (Js.filter f xs) G) (jsFilter (.ref l) g >>= k) h Q := by
  unfold Rel at *; intro r e
  obtain ⟨ys, ey, er⟩ := bind_ok e
  obtain ⟨bs, hb, rfl⟩ := filter_ok ey
  unfold jsFilter each
  simp only [spec_bind]
  rw [spec_eq (items_arr hl)]
  refine spec_mono (eachLoop_spec
    (fun i out h' => h' = h ∧ List.Forall₂ (crep h) (filtBy (xs.take i) (bs.take i)) out)
    (fun _ _ _ hI => hI.1 ▸ hl) ?_ vs.length 0 [] h (by simp)
    ⟨rfl, by simp only [List.take_zero, filtBy]; exact .nil⟩) ?_
  · rintro i out h' hi ⟨he, hI⟩
    rw [he]
    have hx : i < xs.length := hf.length_eq ▸ hi
    have hbl : i < bs.length := hb.length_eq ▸ hx
    have H' := hg xs[i] vs[i] i (f2_get hf hx hi)
    unfold Rel at H'
    simp only [spec_bind, spec_pure]
    refine spec_mono (H' bs[i] (f2_get hb hx hbl)) ?_
    rintro w h'' ⟨rfl, hw⟩
    refine ⟨_, rfl, rfl, ?_⟩
    have hlen : (xs.take i).length = (bs.take i).length := by
      simp only [List.length_take, hb.length_eq]
    rw [List.take_succ, List.take_succ, List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hbl,
      Option.toList_some, Option.toList_some, filtBy_append hlen]
    simp only [crep_bool] at hw
    subst hw
    cases hc : bs[i]
    · simpa [filtBy, truthy_bool, hc] using hI
    · simpa [filtBy, truthy_bool, hc] using f2_append hI (.cons (f2_get hf hx hi) .nil)
  · rintro out h' ⟨he, hI⟩
    rw [he]
    rw [List.take_of_length_le (by rw [← hf.length_eq]),
      List.take_of_length_le (by rw [← hb.length_eq, ← hf.length_eq])] at hI
    rw [spec_arr]
    have H' := H _ out ⟨h.length, out, rfl, by simp, hI⟩
    unfold Rel at H'; exact H' r er

theorem rel_padStart {β : Type} {s fill f : List Nat} {n : Js.Num} {w : Val}
    {g : List Nat → Result β} {δ : Type} {k : Val → M δ} {h Q}
    (hv : NumIs w n.val) (hf : f = fill) (H : ∀ t, Rel (g t) (k (.str t)) h Q) :
    Rel (Std.bind (Js.padStart s n fill) g) (method .padStart (.str s) [w, .str f] >>= k) h Q := by
  subst hf
  obtain ⟨x, rfl, hx⟩ := hv
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hp : method .padStart (.str s) [.num x, .str f] h = .ok (.str t) h := by
    simp [method, prim, primV, asNum_isInt hx, et, okStr]
  rw [spec_bind, spec_eq hp]
  have H' := H t; unfold Rel at H'; exact H' r er

theorem mk_ok_val {n : Int} {t : Js.Num} (e : Js.mk n = ok t) : t.val = n := by
  simp only [Js.mk] at e
  split at e <;> simp_all
  subst e
  rfl

def fiStep (g : Val → Val → M Val) (i : Nat) (x : Val) (_ : Int) : M (ForInStep Int) := do
  return if truthy (← g x (num i)) then .done (i : Int) else .yield (-1)

theorem jsFindIndex_eq {o : Val} {g : Val → Val → M Val} :
    jsFindIndex o g = (do let r ← each o (-1) (fiStep g); return num r) := rfl

theorem fi_loop {f : Js.Num → Result Bool} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {h : Heap}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w)) :
    ∀ (k i : Nat) (t : Js.Num), i + k = vs.length → Js.findIndexFrom f (xs.drop i) i = ok t →
      eachLoop l (fiStep g) k i (-1) h = .ok t.val h
  | 0, i, t, e, ef => by
    have hd : xs.drop i = [] := List.drop_eq_nil_of_le (by rw [hf.length_eq]; omega)
    rw [hd] at ef
    simp only [Js.findIndexFrom] at ef
    rw [mk_ok_val ef]; rfl
  | k + 1, i, t, e, ef => by
    have hi : i < vs.length := by omega
    have hx : i < xs.length := hf.length_eq ▸ hi
    rw [List.drop_eq_getElem_cons hx] at ef
    simp only [Js.findIndexFrom] at ef
    obtain ⟨b, eb, e2⟩ := bind_ok ef
    have H' := hg xs[i] vs[i] i (f2_get hf hx hi)
    unfold Rel at H'
    have es : fiStep g i vs[i] (-1) h = .ok (if b then ForInStep.done (i : Int) else .yield (-1)) h :=
      ok_of_spec (by
        simp only [fiStep, spec_bind, spec_pure]
        refine spec_mono (H' b eb) ?_
        rintro w h'' ⟨rfl, hw⟩
        simp only [crep_bool] at hw; subst hw
        exact ⟨by cases b <;> rfl, rfl⟩)
    simp only [eachLoop, hl, List.getElem?_eq_getElem hi, es]
    cases b
    · simp only [Bool.false_eq_true, if_false] at e2 ⊢
      exact fi_loop hl hf hg k (i + 1) t (by omega) e2
    · simp only [if_true] at e2 ⊢
      rw [mk_ok_val e2]

/-- `xs.findIndex(f)` on numbers, with a callback that leaves the heap alone. -/
theorem rel_findIndex {γ : Type} {f : Js.Num → Result Bool} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {G : Js.Num → Result γ} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w))
    (H : ∀ t : Js.Num, ∀ u, NumIs u t.val → Rel (G t) (k u) h Q) :
    Rel (Std.bind (Js.findIndex f xs) G) (jsFindIndex (.ref l) g >>= k) h Q := by
  unfold Rel; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hloop := fi_loop hl hf hg vs.length 0 t (by simp) (by rw [List.drop_zero]; exact et)
  rw [jsFindIndex_eq]
  unfold each
  simp only [spec_bind, spec_pure]
  rw [spec_eq (items_arr hl)]
  refine (spec_eq hloop).2 ?_
  have H' := H t (num t.val) numIs_num
  unfold Rel at H'; exact H' r er

def soStep (g : Val → Val → M Val) (i : Nat) (x : Val) (_ : Bool) : M (ForInStep Bool) := do
  return if truthy (← g x (num i)) then .done true else .yield false

def evStep (g : Val → Val → M Val) (i : Nat) (x : Val) (_ : Bool) : M (ForInStep Bool) := do
  return if truthy (← g x (num i)) then .yield true else .done false

theorem jsSome_eq {o : Val} {g : Val → Val → M Val} :
    jsSome o g = (do let r ← each o false (soStep g); return .bool r) := rfl

theorem jsEvery_eq {o : Val} {g : Val → Val → M Val} :
    jsEvery o g = (do let r ← each o true (evStep g); return .bool r) := rfl

theorem bool_step {f : Js.Num → Result Bool} {g : Val → Val → M Val} {h : Heap} {x : Js.Num} {u : Val}
    {i : Nat} {b : Bool} {c : Bool → ForInStep Bool}
    (hg : Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w)) (eb : f x = ok b) :
    (do return c (truthy (← g u (num i))) : M (ForInStep Bool)) h = .ok (c b) h :=
  ok_of_spec (by
    unfold Rel at hg
    simp only [spec_bind, spec_pure]
    refine spec_mono (hg b eb) ?_
    rintro w h'' ⟨rfl, hw⟩
    simp only [crep_bool] at hw; subst hw
    exact ⟨rfl, rfl⟩)

theorem so_loop {f : Js.Num → Result Bool} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {h : Heap}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w)) :
    ∀ (k i : Nat) (t : Bool), i + k = vs.length → Js.some_ f (xs.drop i) = ok t →
      eachLoop l (soStep g) k i false h = .ok t h
  | 0, i, t, e, ef => by
    have hd : xs.drop i = [] := List.drop_eq_nil_of_le (by rw [hf.length_eq]; omega)
    rw [hd] at ef
    simp only [Js.some_, ok_eq_ok] at ef; subst ef; rfl
  | k + 1, i, t, e, ef => by
    have hi : i < vs.length := by omega
    have hx : i < xs.length := hf.length_eq ▸ hi
    rw [List.drop_eq_getElem_cons hx] at ef
    simp only [Js.some_] at ef
    obtain ⟨b, eb, e2⟩ := bind_ok ef
    have es : soStep g i vs[i] false h = .ok (if b then ForInStep.done true else .yield false) h :=
      bool_step (c := fun b => if b then .done true else .yield false) (hg xs[i] vs[i] i (f2_get hf hx hi)) eb
    simp only [eachLoop, hl, List.getElem?_eq_getElem hi, es]
    cases b
    · simp only [Bool.false_eq_true, if_false] at e2 ⊢
      exact so_loop hl hf hg k (i + 1) t (by omega) e2
    · simp only [if_true, ok_eq_ok] at e2 ⊢
      subst e2; rfl

theorem ev_loop {f : Js.Num → Result Bool} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {h : Heap}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w)) :
    ∀ (k i : Nat) (t : Bool), i + k = vs.length → Js.every f (xs.drop i) = ok t →
      eachLoop l (evStep g) k i true h = .ok t h
  | 0, i, t, e, ef => by
    have hd : xs.drop i = [] := List.drop_eq_nil_of_le (by rw [hf.length_eq]; omega)
    rw [hd] at ef
    simp only [Js.every, ok_eq_ok] at ef; subst ef; rfl
  | k + 1, i, t, e, ef => by
    have hi : i < vs.length := by omega
    have hx : i < xs.length := hf.length_eq ▸ hi
    rw [List.drop_eq_getElem_cons hx] at ef
    simp only [Js.every] at ef
    obtain ⟨b, eb, e2⟩ := bind_ok ef
    have es : evStep g i vs[i] true h = .ok (if b then ForInStep.yield true else .done false) h :=
      bool_step (c := fun b => if b then .yield true else .done false) (hg xs[i] vs[i] i (f2_get hf hx hi)) eb
    simp only [eachLoop, hl, List.getElem?_eq_getElem hi, es]
    cases b
    · simp only [Bool.false_eq_true, if_false, ok_eq_ok] at e2 ⊢
      subst e2; rfl
    · simp only [if_true] at e2 ⊢
      exact ev_loop hl hf hg k (i + 1) t (by omega) e2

/-- `xs.some(f)` on numbers, with a callback that leaves the heap alone. -/
theorem rel_some {γ : Type} {f : Js.Num → Result Bool} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {G : Bool → Result γ} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w))
    (H : ∀ b : Bool, Rel (G b) (k (.bool b)) h Q) :
    Rel (Std.bind (Js.some_ f xs) G) (jsSome (.ref l) g >>= k) h Q := by
  unfold Rel; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hloop := so_loop hl hf hg vs.length 0 t (by simp) (by rw [List.drop_zero]; exact et)
  rw [jsSome_eq]
  unfold each
  simp only [spec_bind, spec_pure]
  rw [spec_eq (items_arr hl)]
  refine (spec_eq hloop).2 ?_
  have H' := H t
  unfold Rel at H'; exact H' r er

/-- `xs.every(f)` on numbers, with a callback that leaves the heap alone. -/
theorem rel_every {γ : Type} {f : Js.Num → Result Bool} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → M Val} {G : Bool → Result γ} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ x u (i : Nat), NumIs u x.val → Rel (f x) (g u (num i)) h (fun b w h' => h' = h ∧ crep h b w))
    (H : ∀ b : Bool, Rel (G b) (k (.bool b)) h Q) :
    Rel (Std.bind (Js.every f xs) G) (jsEvery (.ref l) g >>= k) h Q := by
  unfold Rel; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have hloop := ev_loop hl hf hg vs.length 0 t (by simp) (by rw [List.drop_zero]; exact et)
  rw [jsEvery_eq]
  unfold each
  simp only [spec_bind, spec_pure]
  rw [spec_eq (items_arr hl)]
  refine (spec_eq hloop).2 ?_
  have H' := H t
  unfold Rel at H'; exact H' r er

def rdStep (g : Val → Val → Val → M Val) (i : Nat) (x : Val) (acc : Val) : M (ForInStep Val) := do
  return .yield (← g acc x (num i))

theorem jsReduce_eq {o init : Val} {g : Val → Val → Val → M Val} :
    jsReduce o g init = each o init (rdStep g) := rfl

theorem rd_loop {f : Js.Num → Js.Num → Result Js.Num} {xs : List Js.Num} {vs : List Val} {l : Loc}
    {g : Val → Val → Val → M Val} {h : Heap}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs)
    (hg : ∀ (a x : Js.Num) z u (i : Nat), NumIs z a.val → NumIs u x.val →
      Rel (f a x) (g z u (num i)) h (fun b w h' => h' = h ∧ crep h b w)) :
    ∀ (k i : Nat) (a : Js.Num) (z : Val) (t : Js.Num), i + k = vs.length → NumIs z a.val →
      Js.reduce f a (xs.drop i) = ok t → ∃ z', eachLoop l (rdStep g) k i z h = .ok z' h ∧ NumIs z' t.val
  | 0, i, a, z, t, e, hz, ef => by
    have hd : xs.drop i = [] := List.drop_eq_nil_of_le (by rw [hf.length_eq]; omega)
    rw [hd] at ef
    simp only [Js.reduce, ok_eq_ok] at ef; subst ef
    exact ⟨z, rfl, hz⟩
  | k + 1, i, a, z, t, e, hz, ef => by
    have hi : i < vs.length := by omega
    have hx : i < xs.length := hf.length_eq ▸ hi
    rw [List.drop_eq_getElem_cons hx] at ef
    simp only [Js.reduce] at ef
    obtain ⟨b, eb, e2⟩ := bind_ok ef
    have H' := hg a xs[i] z vs[i] i hz (f2_get hf hx hi)
    unfold Rel at H'
    have hs := H' b eb
    obtain ⟨w, hm, hw⟩ : ∃ w, g z vs[i] (num i) h = .ok w h ∧ crep h b w := by
      revert hs; unfold Spec; split
      · rename_i w h'' e; rintro ⟨rfl, hw⟩; exact ⟨w, e, hw⟩
      all_goals intro hs; exact hs.elim
    have es : rdStep g i vs[i] z h = .ok (.yield w) h :=
      ok_of_spec (by simp only [rdStep, spec_bind, spec_pure]; rw [spec_eq hm]; exact ⟨rfl, rfl⟩)
    simp only [eachLoop, hl, List.getElem?_eq_getElem hi, es]
    exact rd_loop hl hf hg k (i + 1) b w t (by omega) hw e2

/-- `xs.reduce(f, init)` on numbers, with a callback that leaves the heap alone. -/
theorem rel_reduce {γ : Type} {f : Js.Num → Js.Num → Result Js.Num} {xs : List Js.Num} {vs : List Val}
    {l : Loc} {g : Val → Val → Val → M Val} {a : Js.Num} {w0 : Val} {G : Js.Num → Result γ}
    {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs) (hw : NumIs w0 a.val)
    (hg : ∀ (a x : Js.Num) z u (i : Nat), NumIs z a.val → NumIs u x.val →
      Rel (f a x) (g z u (num i)) h (fun b w h' => h' = h ∧ crep h b w))
    (H : ∀ t : Js.Num, ∀ u, NumIs u t.val → Rel (G t) (k u) h Q) :
    Rel (Std.bind (Js.reduce f a xs) G) (jsReduce (.ref l) g w0 >>= k) h Q := by
  unfold Rel; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  obtain ⟨z', hz, hzt⟩ := rd_loop hl hf hg vs.length 0 a w0 t (by simp) hw (by rw [List.drop_zero]; exact et)
  rw [jsReduce_eq]
  unfold each
  simp only [spec_bind, spec_pure]
  rw [spec_eq (items_arr hl)]
  refine (spec_eq hz).2 ?_
  have H' := H t z' hzt
  unfold Rel at H'; exact H' r er

theorem strsOf_f2 {h : Heap} : ∀ {xs : List (List Nat)} {vs : List Val},
    List.Forall₂ (crep h) xs vs → strsOf vs = some xs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hx hr => by
    obtain rfl := hx
    simp [strsOf, strsOf_f2 hr]

/-- `xs.lastIndexOf(s)` on an array of strings. -/
theorem rel_lastIndexOf {β : Type} {xs : List (List Nat)} {vs : List Val} {l : Loc} {s : List Nat} {w : Val}
    {g : Js.Num → Result β} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs) (hw : w = .str s)
    (H : ∀ t : Js.Num, ∀ u, NumIs u t.val → Rel (g t) (k u) h Q) :
    Rel (Std.bind (Js.lastIndexOf xs s) g) (method .lastIndexOf (.ref l) [w] >>= k) h Q := by
  subst hw
  unfold Rel at *; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have ep : method .lastIndexOf (.ref l) [.str s] h = .ok (numVal t) h := by
    simp [method, prim, primV, hl, strsOf_f2 hf, et, Result.match.ok]
  rw [spec_bind, spec_eq ep]
  exact H t (numVal t) ⟨_, rfl, Or.inl rfl⟩ r er

/-- `for (const x of xs)` with one mutable variable, whose body leaves the heap alone. -/
theorem rel_forOf {α β γ : Type} [CRep α] [CRep β]
    {B : List α × β → Result (ControlFlow (List α × β) β)} {xs : List α} {vs : List Val} {l : Loc}
    {acc : β} {w : Val} {f : Val → Val → M (ForInStep Val)} {G : β → Result γ} {δ : Type} {k : Val → M δ} {h Q}
    (hl : h[l]? = some (.array vs)) (hf : List.Forall₂ (crep h) xs vs) (hw : crep h acc w)
    (hnil : ∀ a, B ([], a) = ok (.done a))
    (hstep : ∀ x rest a u z, crep h x u → crep h a z → Rel (B (x :: rest, a)) (f u z) h
      (fun c s h' => h' = h ∧ ∃ a' z', c = .cont (rest, a') ∧ s = .yield z' ∧ crep h a' z'))
    (H : ∀ t z, crep h t z → Rel (G t) (k z) h Q) :
    Rel (Std.bind (Aeneas.Std.loop B (xs, acc)) G)
      (iter (.ref l) >>= fun it => forIn it w f >>= k) h Q := by
  unfold Rel; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have key := Core.loop_ind (B := B)
    (fun a t => ∀ i z, a.1 = xs.drop i → crep h a.2 z →
      ∃ z', forLoop l f (vs.length - i) i z h = .ok z' h ∧ crep h t z') ?_ (xs, acc) t et
  · obtain ⟨z', hz, hc⟩ := key 0 w (List.drop_zero).symm hw
    rw [spec_bind, spec_eq (iter_arr hl), spec_bind]
    have hfor : forIn (m := M) (⟨l⟩ : Live) w f h = .ok z' h := by
      show (match h[l]? with | some (.array xs) => forLoop l f xs.length 0 w h | _ => .stuck) = _
      rw [hl]; simpa using hz
    rw [spec_eq hfor]
    have H' := H t z' hc; unfold Rel at H'; exact H' r er
  · rintro ⟨rest0, a0⟩ y ey
    cases rest0 with
    | nil =>
      rw [hnil, ok_eq_ok] at ey; subst ey
      intro i z hd hz
      have hle : vs.length ≤ i := by
        rw [← hf.length_eq]; exact List.drop_eq_nil_iff.mp hd.symm
      refine ⟨z, ?_, hz⟩
      rw [show vs.length - i = 0 by omega]
      simp only [forLoop, hl]; rw [if_neg (by omega)]
    | cons x rest =>
      have pre : ∀ i z, (x :: rest, a0).1 = xs.drop i → crep h a0 z →
          ∃ hi : i < vs.length, ∃ z' a', forLoop l f (vs.length - i) i z h
            = forLoop l f (vs.length - (i + 1)) (i + 1) z' h ∧ y = .cont (xs.drop (i + 1), a') ∧ crep h a' z' := by
        intro i z hd hz
        simp only at hd
        have hx : i < xs.length := by
          rcases Nat.lt_or_ge i xs.length with h1 | h1
          · exact h1
          · rw [List.drop_eq_nil_of_le h1] at hd; cases hd
        have hi : i < vs.length := hf.length_eq ▸ hx
        rw [List.drop_eq_getElem_cons hx] at hd
        injection hd with e1 e2
        subst e1 e2
        have S := hstep xs[i] (xs.drop (i + 1)) a0 vs[i] z (f2_get hf hx hi) hz
        unfold Rel at S
        obtain ⟨s, h', es, he, a', z', ec, rfl, hc⟩ := spec_ok (S _ ey)
        rw [he] at es
        refine ⟨hi, z', a', ?_, ec, hc⟩
        rw [show vs.length - i = (vs.length - (i + 1)) + 1 by omega]
        simp only [forLoop, hl, List.getElem?_eq_getElem hi, es]
      cases y with
      | done r0 =>
        intro i z hd hz
        obtain ⟨_, _, _, _, ec, _⟩ := pre i z hd hz
        cases ec
      | cont a1 =>
        intro r0 hr0 i z hd hz
        obtain ⟨_, z', a', ef, ec, hc⟩ := pre i z hd hz
        cases ec
        obtain ⟨z'', hz'', hc''⟩ := hr0 (i + 1) z' rfl hc
        exact ⟨z'', ef ▸ hz'', hc''⟩

/-- What one round of a typed loop and of `whileLoop` must agree on. -/
def wpost {σ β ε : Type} (S : σ → ε → Heap → Prop) (T : β → ε → Heap → Prop) :
    ControlFlow σ β → ForInStep ε → Heap → Prop
  | .cont s, .yield z, h => S s z h
  | .done r, .done z, h => T r z h
  | _, _, _ => False

@[simp] theorem wpost_cy {σ β ε} {S : σ → ε → Heap → Prop} {T : β → ε → Heap → Prop} {s z h} :
    wpost S T (.cont s) (.yield z) h = S s z h := rfl
@[simp] theorem wpost_dd {σ β ε} {S : σ → ε → Heap → Prop} {T : β → ε → Heap → Prop} {r z h} :
    wpost S T (.done r) (.done z) h = T r z h := rfl
@[simp] theorem wpost_cd {σ β ε} {S : σ → ε → Heap → Prop} {T : β → ε → Heap → Prop} {s z h} :
    wpost S T (.cont s) (.done z) h = False := rfl
@[simp] theorem wpost_dy {σ β ε} {S : σ → ε → Heap → Prop} {T : β → ε → Heap → Prop} {r z h} :
    wpost S T (.done r) (.yield z) h = False := rfl

/-- A typed loop against `while`/`for (;;)`: `S` relates the states before each round, `T` the results. -/
theorem rel_while {σ β γ ε δ : Type} {B : σ → Result (ControlFlow σ β)} {s0 : σ}
    {G : β → Result γ} {f : Unit → ε → M (ForInStep ε)} {z0 : ε} {k : ε → M δ} {h : Heap} {Q}
    (S : σ → ε → Heap → Prop) (T : β → ε → Heap → Prop)
    (h0 : S s0 z0 h)
    (hstep : ∀ s z h, S s z h → Rel (B s) (f () z) h (wpost S T))
    (H : ∀ r z h', T r z h' → Rel (G r) (k z) h' Q) :
    Rel (Std.bind (Aeneas.Std.loop B s0) G) (forIn (m := M) fuel z0 f >>= k) h Q := by
  unfold Rel; intro r e
  obtain ⟨t, et, er⟩ := bind_ok e
  have key := Core.loop_ind (B := B)
    (fun s t => ∀ z h, S s z h → Spec (whileLoop f z) h (fun z' h' => T t z' h')) ?_ s0 t et
  · obtain ⟨z', h', ew, hT⟩ := spec_ok (key z0 h h0)
    rw [spec_bind]
    show Spec (whileLoop f z0) h _
    rw [spec_eq ew]
    have H' := H t z' h' hT; unfold Rel at H'; exact H' r er
  · intro s y ey
    have one : ∀ z h, S s z h → Spec (f () z) h (wpost S T y) := by
      intro z h hS
      have S1 := hstep s z h hS; unfold Rel at S1
      exact S1 _ ey
    cases y with
    | done t0 =>
      intro z h hS
      have sp := one z h hS
      unfold Spec at sp ⊢; rw [whileLoop]
      revert sp; cases f () z h with
      | ok st h' => cases st <;> simp
      | thrown v h' => simp
      | stuck => simp
    | cont s' =>
      intro r0 ih z h hS
      have sp := one z h hS
      unfold Spec at sp ⊢; rw [whileLoop]
      revert sp; cases f () z h with
      | ok st h' =>
        cases st with
        | done z' => simp
        | yield z' => intro sp; have := ih z' h' sp; unfold Spec at this; exact this
      | thrown v h' => simp
      | stuck => simp

macro_rules | `(tactic| dsafe) => `(tactic| first | exact numIs_num | assumption)

/-- Closes the side goals of a relational lemma: the operands are numbers, then introduces the result. -/
macro "rnum" : tactic => `(tactic| first | (intro _ _ _ _) | exact numIs_num | assumption | (simp only [crep_some, crep_num] at *; assumption))

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
  | (refine rel_neg ?_ ?_ <;> rnum)
  | (refine rel_div ?_ ?_ ?_ <;> rnum)
  | (refine rel_max ?_ ?_ ?_ <;> first | (intro u hu; simp only [max_val] at hu; try simp only [truthy_numIs hu]) | exact numIs_num | assumption)
  | (refine rel_dneg numIs_num ?_; intro _ _)
  | (casesm ∃ _, _)
  | (with_reducible refine rel_trim ?_)
  | (with_reducible refine rel_isArray_opt (by assumption) (by first | (left; rfl) | (right; rfl)) ?_)
  | (with_reducible subst_vars; refine rel_isArray_arr rfl (by assumption) ?_)
  | (with_reducible refine rel_isArray_nul (by first | (left; rfl) | (right; rfl) | assumption | (simp only [crep_none] at *; assumption)) ?_)
  | (refine rel_dtoNum (by first | rfl | assumption) ?_; intro _ _)
  | (refine rel_arr (by simp [crep_num, crep_none, crep_some, crep_str, crep_bool, numIs_num]; try assumption) ?_; intro _ _)
  | (refine rel_len (by assumption) (by assumption) ?_; intro _ _ _ _)
  | (refine rel_slen ?_; intro _ _ _ _)
  | (refine rel_map (by assumption) (by assumption) ?_ ?_ <;> intros)
  | (refine rel_filter (by assumption) (by assumption) ?_ ?_ <;> intros)
  | (refine rel_findIndex (by assumption) (by assumption) ?_ ?_ <;> intros)
  | (refine rel_some (by assumption) (by assumption) ?_ ?_ <;> intros)
  | (refine rel_every (by assumption) (by assumption) ?_ ?_ <;> intros)
  | (refine rel_lastIndexOf (by assumption) (by assumption) (by first | rfl | decide) ?_; intro _ _ _)
  | (refine rel_reduce (by assumption) (by assumption) (by first | exact numIs_num | assumption) ?_ ?_ <;> intros)
  | (refine rel_padStart ?_ (by first | rfl | decide) ?_ <;> first | (intro _) | rnum)
  | (refine rel_forOf (by assumption) (by assumption) (by first | exact numIs_num | assumption) (fun _ => rfl) ?_ ?_ <;> intros))

/-- Steps the typed view and the dynamic code together: a typed operation with its dynamic
twin, a typed `ok` bind, a branch on both sides at once, or one dynamic step. -/
macro "rsteps" : tactic => `(tactic| repeat' (first
  | (refine rel_min_ok ?_ ?_ ?_ <;> rmin)
  | (exfalso; simp only [not_true_eq_false, Bool.false_eq_true, truthy_bool, decide_eq_true_eq] at *; done)
  | (exfalso; (try simp only [truthy_bool, decide_eq_true_eq, Bool.not_eq_true, Bool.not_eq_true', not_not, decide_eq_false_iff_not] at *); omega)
  | (exfalso; have := nullish_of_crep_none ‹crep _ (none : Option _) _›; simp_all; done)
  | (exfalso; have := not_nullish_of_crep_some ‹crep _ (some (_ : Js.Num)) _›; simp_all; done)
  | rops
  | (simp only [Std.bind_ok, Std.bind_assoc, bind_tc_ok, bind_assoc_eq, dbind_assoc, dpure_bind])
  | (refine rel_tail ?_; (try simp only [dbind_assoc]); rops)
  | (apply rel_ok; (try simp only [spec_rok]); (try simp only [true_and, false_and, decide_false]); first | (refine spec_min ?_ ?_ ?_ <;> first | (intro _ _) | exact numIs_num | assumption) | (try dsteps [bin_lt_is, bin_gt_is, bin_le_is, bin_ge_is, bin_eq_is, bin_ne_is]))
  | (split <;> (rename_i hc
                try simp only [truthy_bool, decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not, max_val, Js.isArray, Option.isSome, truthy_str] at hc
                try dsteps [bin_lt_is, bin_gt_is, bin_le_is, bin_ge_is, bin_eq_is, bin_ne_is]))
  | (apply rel_dbind; dsteps [bin_lt_is, bin_gt_is, bin_le_is, bin_ge_is, bin_eq_is, bin_ne_is])))

end Dyn
