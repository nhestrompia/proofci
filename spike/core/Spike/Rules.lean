import Core
open Core

/-! Rules for reasoning about Core without counting fuel. Each says "with enough fuel,
this is the result", which composes by taking the larger bound. -/
namespace Core

def Evals (p : Prog) (s : St) (e : Expr) (v : Val) (s' : St) : Prop :=
  ∃ F, ∀ f, F ≤ f → eval f p s e = .ok v s'
def ExecsL (p : Prog) (s : St) (c : List Stmt) (r : Cmp) (s' : St) : Prop :=
  ∃ F, ∀ f, F ≤ f → execList f p s c = .ok r s'
def Execs (p : Prog) (s : St) (c : Stmt) (r : Cmp) (s' : St) : Prop :=
  ∃ F, ∀ f, F ≤ f → exec f p s c = .ok r s'
def Iterates (p : Prog) (x : String) (v : Val) (i : Nat) (b : List Stmt) (s : St) (r : Cmp) (s' : St) : Prop :=
  ∃ F, ∀ f, F ≤ f → iterate f p x v i b s = .ok r s'
def Runs (p : Prog) (fn : Fn) (args : List Val) (h : Heap) (v : Val) (s' : St) : Prop :=
  ∃ F, ∀ f, F ≤ f → run f p fn args h = .ok v s'

theorem succ_of_le {f F : Nat} (h : F + 1 ≤ f) : ∃ g, f = g + 1 ∧ F ≤ g :=
  ⟨f - 1, by omega, by omega⟩

theorem Evals.lit (p s v) : Evals p s (.lit v) v s :=
  ⟨1, fun f h => by obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) h; simp only [eval]⟩

theorem Evals.var {p s x v} (h : s.env x = some v) : Evals p s (.var x) v s :=
  ⟨1, fun f hf => by obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) hf; simp only [eval, h]⟩

theorem Evals.field {p s o k v r s'} (ho : Evals p s o v s') (hr : readField s'.heap v k = some r) :
    Evals p s (.field o k) r s' := by
  obtain ⟨F, hF⟩ := ho
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg, hr]⟩

theorem Evals.isNullish {p s a v s'} (ha : Evals p s a v s') :
    Evals p s (.isNullish a) (.bool (nullish v)) s' := by
  obtain ⟨F, hF⟩ := ha
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg]⟩

theorem Evals.bin {p s op a b x y r s₁ s₂} (ha : Evals p s a x s₁) (hb : Evals p s₁ b y s₂)
    (hr : binary op x y = some r) : Evals p s (.bin op a b) r s₂ := by
  obtain ⟨F, hF⟩ := ha
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [eval, hF g (by omega), hG g (by omega), hr]⟩

theorem Evals.or_true {p s a b v s'} (ha : Evals p s a v s') (ht : truthy v = true) :
    Evals p s (.or a b) v s' := by
  obtain ⟨F, hF⟩ := ha
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg, ht, ite_true]⟩

theorem Evals.or_false {p s a b v w s₁ s₂} (ha : Evals p s a v s₁) (ht : truthy v = false)
    (hb : Evals p s₁ b w s₂) : Evals p s (.or a b) w s₂ := by
  obtain ⟨F, hF⟩ := ha
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp [eval, hF g (by omega), ht, hG g (by omega)]⟩

theorem Evals.index {p s o i v n l xs s₁ s₂} (ho : Evals p s o v s₁) (hi : Evals p s₁ i (.num n) s₂)
    (hv : v = .ref l) (hl : s₂.heap[l]? = some (.array xs)) :
    Evals p s (.index o i) ((n.index.bind (xs[·]?)).getD .undef) s₂ := by
  subst hv
  obtain ⟨F, hF⟩ := ho
  obtain ⟨G, hG⟩ := hi
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [eval, hF g (by omega), hG g (by omega), hl]⟩

theorem ExecsL.nil (p s) : ExecsL p s [] .normal s :=
  ⟨1, fun f h => by obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) h; simp only [execList]⟩

theorem ExecsL.cons_normal {p s c cs s₁ r s₂} (h : Execs p s c .normal s₁) (t : ExecsL p s₁ cs r s₂) :
    ExecsL p s (c :: cs) r s₂ := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨G, hG⟩ := t
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [execList, hF g (by omega), hG g (by omega)]⟩

theorem ExecsL.cons_exit {p s c cs r s₁} (h : Execs p s c r s₁) (hr : r ≠ .normal) :
    ExecsL p s (c :: cs) r s₁ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    cases r <;> simp_all [execList]⟩

/-- A statement that finished normally, then the rest. -/
theorem ExecsL.cons_exit' {p s c cs s₁ r s₂} (h : Execs p s c .normal s₁) (t : ExecsL p s₁ cs r s₂) :
    ExecsL p s (c :: cs) r s₂ := ExecsL.cons_normal h t

theorem Execs.set {p s x e v s'} (h : Evals p s e v s') :
    Execs p s (.set x e) .normal { s' with env := s'.env.put x v } := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [exec, hF g hg]⟩

theorem Execs.ret {p s e v s'} (h : Evals p s e v s') : Execs p s (.ret e) (.ret v) s' := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [exec, hF g hg]⟩

theorem Execs.brk (p s) : Execs p s .brk .brk s :=
  ⟨1, fun f h => by obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) h; simp only [exec]⟩

theorem Execs.ite_true {p s c t e v s₁ r s₂} (hc : Evals p s c v s₁) (ht : truthy v = true)
    (hb : ExecsL p s₁ t r s₂) : Execs p s (.ite c t e) r s₂ := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp [exec, hF g (by omega), ht, hG g (by omega)]⟩

theorem Execs.ite_false {p s c t e v s₁ r s₂} (hc : Evals p s c v s₁) (ht : truthy v = false)
    (hb : ExecsL p s₁ e r s₂) : Execs p s (.ite c t e) r s₂ := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp [exec, hF g (by omega), ht, hG g (by omega)]⟩

theorem Execs.forOf {p s x e body v s₁ r s₂} (he : Evals p s e v s₁)
    (ht : Iterates p x v 0 body s₁ r s₂) : Execs p s (.forOf x e body) r s₂ := by
  obtain ⟨F, hF⟩ := he
  obtain ⟨G, hG⟩ := ht
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [exec, hF g (by omega), hG g (by omega)]⟩

theorem Iterates.done {p x l i b s xs} (hl : s.heap[l]? = some (.array xs)) (hi : xs[i]? = none) :
    Iterates p x (.ref l) i b s .normal s :=
  ⟨1, fun f h => by
    obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) h
    simp only [iterate, hl, hi]⟩

theorem Iterates.next {p x l i b s xs item s₁ r s₂} (hl : s.heap[l]? = some (.array xs))
    (hi : xs[i]? = some item) (hb : ExecsL p { s with env := s.env.put x item } b .normal s₁)
    (ht : Iterates p x (.ref l) (i + 1) b s₁ r s₂) : Iterates p x (.ref l) i b s r s₂ := by
  obtain ⟨F, hF⟩ := hb
  obtain ⟨G, hG⟩ := ht
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [iterate, hl, hi, hF g (by omega), hG g (by omega)]⟩

theorem Iterates.brk {p x l i b s xs item s₁} (hl : s.heap[l]? = some (.array xs))
    (hi : xs[i]? = some item) (hb : ExecsL p { s with env := s.env.put x item } b .brk s₁) :
    Iterates p x (.ref l) i b s .normal s₁ := by
  obtain ⟨F, hF⟩ := hb
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [iterate, hl, hi, hF g hg]⟩

end Core

namespace Core

theorem Evals.neg {p s a x s'} (ha : Evals p s a (.num x) s') : Evals p s (.neg a) (.num x.neg) s' := by
  obtain ⟨F, hF⟩ := ha
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg]⟩

theorem Evals.math {p s g a x s'} (ha : Evals p s a (.num x) s') : Evals p s (.math g a) (.num (g x)) s' := by
  obtain ⟨F, hF⟩ := ha
  exact ⟨F + 1, fun f hf => by obtain ⟨g', rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g' hg]⟩

theorem Evals.not {p s a v s'} (ha : Evals p s a v s') : Evals p s (.not a) (.bool (!truthy v)) s' := by
  obtain ⟨F, hF⟩ := ha
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg]⟩

theorem Evals.and_true {p s a b v w s₁ s₂} (ha : Evals p s a v s₁) (ht : truthy v = true)
    (hb : Evals p s₁ b w s₂) : Evals p s (.and a b) w s₂ := by
  obtain ⟨F, hF⟩ := ha
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp [eval, hF g (by omega), ht, hG g (by omega)]⟩

theorem Evals.and_false {p s a b v s'} (ha : Evals p s a v s') (ht : truthy v = false) :
    Evals p s (.and a b) v s' := by
  obtain ⟨F, hF⟩ := ha
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp [eval, hF g hg, ht]⟩

theorem Evals.cond_true {p s c a b v w s₁ s₂} (hc : Evals p s c v s₁) (ht : truthy v = true)
    (ha : Evals p s₁ a w s₂) : Evals p s (.cond c a b) w s₂ := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨G, hG⟩ := ha
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp [eval, hF g (by omega), ht, hG g (by omega)]⟩

theorem Evals.cond_false {p s c a b v w s₁ s₂} (hc : Evals p s c v s₁) (ht : truthy v = false)
    (hb : Evals p s₁ b w s₂) : Evals p s (.cond c a b) w s₂ := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp [eval, hF g (by omega), ht, hG g (by omega)]⟩

def EvalsF (p : Prog) (s : St) (es : List (String × Expr)) (vs : List (String × Val)) (s' : St) : Prop :=
  ∃ F, ∀ f, F ≤ f → evalFields f p s es = .ok vs s'
def EvalsL (p : Prog) (s : St) (es : List Expr) (vs : List Val) (s' : St) : Prop :=
  ∃ F, ∀ f, F ≤ f → evalList f p s es = .ok vs s'

theorem EvalsF.nil (p s) : EvalsF p s [] [] s :=
  ⟨1, fun f h => by obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) h; simp only [evalFields]⟩
theorem EvalsF.cons {p s k e es v vs s₁ s₂} (he : Evals p s e v s₁) (ht : EvalsF p s₁ es vs s₂) :
    EvalsF p s ((k, e) :: es) ((k, v) :: vs) s₂ := by
  obtain ⟨F, hF⟩ := he
  obtain ⟨G, hG⟩ := ht
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [evalFields, hF g (by omega), hG g (by omega)]⟩
theorem EvalsL.nil (p s) : EvalsL p s [] [] s :=
  ⟨1, fun f h => by obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) h; simp only [evalList]⟩
theorem EvalsL.cons {p s e es v vs s₁ s₂} (he : Evals p s e v s₁) (ht : EvalsL p s₁ es vs s₂) :
    EvalsL p s (e :: es) (v :: vs) s₂ := by
  obtain ⟨F, hF⟩ := he
  obtain ⟨G, hG⟩ := ht
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [evalList, hF g (by omega), hG g (by omega)]⟩

theorem Evals.length {p s o l xs s'} (ho : Evals p s o (.ref l) s') (hl : s'.heap[l]? = some (.array xs)) :
    Evals p s (.length o) (.num (F64.ofInt xs.length)) s' := by
  obtain ⟨F, hF⟩ := ho
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg, hl]⟩

theorem Evals.record {p s es vs s'} (h : EvalsF p s es vs s') :
    Evals p s (.record es) (.ref s'.heap.length) { s' with heap := s'.heap ++ [.record vs] } := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg]⟩

theorem Evals.array {p s es vs s'} (h : EvalsL p s es vs s') :
    Evals p s (.array es) (.ref s'.heap.length) { s' with heap := s'.heap ++ [.array vs] } := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [eval, hF g hg]⟩

theorem Evals.call {p s g args vs s₁ fn v s₂} (ha : EvalsL p s args vs s₁) (hg : p g = some fn)
    (hr : Runs p fn vs s₁.heap v s₂) : Evals p s (.call g args) v { s₁ with heap := s₂.heap } := by
  obtain ⟨F, hF⟩ := ha
  obtain ⟨G, hG⟩ := hr
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g', rfl, hg'⟩ := succ_of_le hf
    simp only [eval, hF g' (by omega), hg, hG g' (by omega)]⟩

theorem Execs.setField {p s o k e l v s₁ s₂ fs} (ho : Evals p s o (.ref l) s₁) (he : Evals p s₁ e v s₂)
    (hl : s₂.heap[l]? = some (.record fs)) :
    Execs p s (.setField o k e) .normal
      { s₂ with heap := s₂.heap.set l (.record ((k, v) :: fs.filter (·.1 != k))) } := by
  obtain ⟨F, hF⟩ := ho
  obtain ⟨G, hG⟩ := he
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [exec, hF g (by omega), hG g (by omega), hl]⟩

end Core
