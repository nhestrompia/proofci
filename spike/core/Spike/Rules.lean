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
    Evals p s (.index o i) (if n < 0 then .undef else xs[n.toNat]?.getD .undef) s₂ := by
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
