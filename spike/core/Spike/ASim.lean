import Spike.Tac
import CoreAsync
import ProofciAsync
open Core Core.Async
open TyRep (rep mono)

namespace Js.Eff
open Aeneas.Std Result
variable {W : Js.World} {α β : Type}

/-! Reading a view's run one step at a time, without unfolding `bind`. -/

theorem bind_call {op : W.Op} {arg : W.Arg op} {f : W.Res op → Js.Eff W β} {o h r h'}
    (hr : (call op arg >>= f) o h = ok (r, h')) :
    (∃ x, o op arg h = .value x ∧ f x o (h ++ [⟨op, arg, .value x⟩]) = ok (r, h')) ∨
    (∃ e, o op arg h = .reject e ∧ r = .rejected e ∧ h' = h ++ [⟨op, arg, .reject e⟩]) := by
  rw [bind_run, call_run] at hr
  cases ho : o op arg h with
  | value x => rw [ho] at hr; exact .inl ⟨x, rfl, by simpa using hr⟩
  | reject e => rw [ho] at hr; simp at hr; exact .inr ⟨e, rfl, hr.1.symm, hr.2.symm⟩

theorem call_tail {op : W.Op} {arg : W.Arg op} {o h r h'} (hr : (call op arg : Js.Eff W (W.Res op)) o h = ok (r, h')) :
    (∃ x, o op arg h = .value x ∧ r = .fulfilled x ∧ h' = h ++ [⟨op, arg, .value x⟩]) ∨
    (∃ e, o op arg h = .reject e ∧ r = .rejected e ∧ h' = h ++ [⟨op, arg, .reject e⟩]) := by
  rw [call_run] at hr
  cases ho : o op arg h with
  | value x => rw [ho] at hr; simp at hr; exact .inl ⟨x, rfl, hr.1.symm, hr.2.symm⟩
  | reject e => rw [ho] at hr; simp at hr; exact .inr ⟨e, rfl, hr.1.symm, hr.2.symm⟩

theorem try_bind_call {op : W.Op} {arg : W.Arg op} {f : W.Res op → Js.Eff W β} {k : Js.Exn → Js.Eff W β} {o h r h'}
    (hr : tryCatch (call op arg >>= f) k o h = ok (r, h')) :
    (∃ x, o op arg h = .value x ∧ tryCatch (f x) k o (h ++ [⟨op, arg, .value x⟩]) = ok (r, h')) ∨
    (∃ e, o op arg h = .reject e ∧ k e o (h ++ [⟨op, arg, .reject e⟩]) = ok (r, h')) := by
  rw [tryCatch_run, bind_run, call_run] at hr
  cases ho : o op arg h with
  | value x => rw [ho] at hr; exact .inl ⟨x, rfl, by rw [tryCatch_run]; simpa using hr⟩
  | reject e => rw [ho] at hr; simp at hr; exact .inr ⟨e, rfl, hr⟩

theorem try_call_tail {op : W.Op} {arg : W.Arg op} {k : Js.Exn → Js.Eff W (W.Res op)} {o h r h'}
    (hr : tryCatch (call op arg) k o h = ok (r, h')) :
    (∃ x, o op arg h = .value x ∧ r = .fulfilled x ∧ h' = h ++ [⟨op, arg, .value x⟩]) ∨
    (∃ e, o op arg h = .reject e ∧ k e o (h ++ [⟨op, arg, .reject e⟩]) = ok (r, h')) := by
  rw [tryCatch_run, call_run] at hr
  cases ho : o op arg h with
  | value x => rw [ho] at hr; simp at hr; exact .inl ⟨x, rfl, hr.1.symm, hr.2.symm⟩
  | reject e => rw [ho] at hr; simp at hr; exact .inr ⟨e, rfl, hr⟩

theorem bind_lift {m : Result α} {f : α → Js.Eff W β} {o h r h'} (hr : ((liftM m : Js.Eff W α) >>= f) o h = ok (r, h')) :
    ∃ a, m = ok a ∧ f a o h = ok (r, h') := by
  rw [bind_run, lift_run] at hr
  obtain ⟨⟨r₁, h₁⟩, h₂, h₃⟩ := Core.bind_eq hr
  obtain ⟨a, hm, h₄⟩ := Core.bind_eq h₂
  simp only [ok.injEq, Prod.mk.injEq] at h₄
  obtain ⟨rfl, rfl⟩ := h₄
  exact ⟨a, hm, h₃⟩

theorem lift_tail {m : Result α} {o h r h'} (hr : (liftM m : Js.Eff W α) o h = ok (r, h')) :
    ∃ a, m = ok a ∧ r = .fulfilled a ∧ h' = h := by
  rw [lift_run] at hr
  obtain ⟨a, hm, h₂⟩ := Core.bind_eq hr
  simp only [ok.injEq, Prod.mk.injEq] at h₂
  exact ⟨a, hm, h₂.1.symm, h₂.2.symm⟩

theorem try_lift_ok (v : α) (k : Js.Exn → Js.Eff W α) : tryCatch (liftM (ok v : Result α)) k = liftM (ok v : Result α) := by
  funext o h; rw [tryCatch_run]; simp

theorem try_throw (e : Js.Exn) (k : Js.Exn → Js.Eff W α) : tryCatch (throw e) k = k e := by
  funext o h; rw [tryCatch_run]; simp

theorem try_ite {c : Prop} [Decidable c] (m n : Js.Eff W α) (k : Js.Exn → Js.Eff W α) :
    tryCatch (if c then m else n) k = if c then tryCatch m k else tryCatch n k := by
  split <;> rfl

theorem ite_bind {c : Prop} [Decidable c] (m n : Js.Eff W α) (f : α → Js.Eff W β) :
    ((if c then m else n) >>= f) = if c then m >>= f else n >>= f := by
  split <;> rfl

theorem lift_ok_run (v : α) (o : W.Oracle) (h : W.Hist) : (liftM (ok v : Result α) : Js.Eff W α) o h = ok (.fulfilled v, h) := by
  rw [lift_run]; simp

end Js.Eff

/-! Rules for reasoning about `CoreAsync` without counting fuel, as `Spike/Rules.lean` does for Core. -/
namespace Core.Async

def AOk (p : Prog) (a : AProg) (o : Oracle) (s : AS) (cs : List AStmt) (out : AOut) : Prop :=
  ∃ F, ∀ f, F ≤ f → aexecList f p a o s cs = out
def AOk1 (p : Prog) (a : AProg) (o : Oracle) (s : AS) (c : AStmt) (out : AOut) : Prop :=
  ∃ F, ∀ f, F ≤ f → aexec f p a o s c = out

variable {p : Prog} {a : AProg} {o : Oracle}

theorem AOk.nil (s : AS) : AOk p a o s [] (.ok .normal s) :=
  ⟨1, fun f hf => by obtain ⟨g, rfl, -⟩ := succ_of_le (F := 0) hf; simp only [aexecList]⟩

theorem AOk.cons_normal {s s₁ c cs out} (h : AOk1 p a o s c (.ok .normal s₁)) (t : AOk p a o s₁ cs out) :
    AOk p a o s (c :: cs) out := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨G, hG⟩ := t
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexecList, hF g (by omega), hG g (by omega)]⟩

/-- An outcome that isn't "carry on" ends the list. -/
def AOut.exits : AOut → Prop
  | .ok .normal _ => False
  | .stuck => False
  | _ => True

theorem AOk.cons_exit {s c cs out} (h : AOk1 p a o s c out) (hx : out.exits) :
    AOk p a o s (c :: cs) out := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexecList, hF g (by omega)]
    rcases out with ⟨c, s⟩ | ⟨v, s⟩ | _
    · cases c <;> simp_all [AOut.exits]
    · rfl
    · simp [AOut.exits] at hx⟩

theorem AOk1.stmt {s c r st} (h : Execs p s.st c r st) : AOk1 p a o s (.stmt c) (.ok r ⟨st, s.hist⟩) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [aexec, hF g hg]⟩

theorem AOk1.ret {s e v st} (h : Evals p s.st e v st) : AOk1 p a o s (.ret e) (.ok (.ret v) ⟨st, s.hist⟩) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [aexec, hF g hg]⟩

theorem AOk1.throw {s e v st} (h : Evals p s.st e v st) : AOk1 p a o s (.throw e) (.thrown v ⟨st, s.hist⟩) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F + 1, fun f hf => by obtain ⟨g, rfl, hg⟩ := succ_of_le hf; simp only [aexec, hF g hg]⟩

theorem AOk1.ite_true {s c t e v st out} (hc : Evals p s.st c v st) (ht : truthy v = true)
    (hb : AOk p a o ⟨st, s.hist⟩ t out) : AOk1 p a o s (.ite c t e) out := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexec, hF g (by omega), ht, ↓reduceIte]; exact hG g (by omega)⟩

theorem AOk1.ite_false {s c t e v st out} (hc : Evals p s.st c v st) (ht : truthy v = false)
    (hb : AOk p a o ⟨st, s.hist⟩ e out) : AOk1 p a o s (.ite c t e) out := by
  obtain ⟨F, hF⟩ := hc
  obtain ⟨G, hG⟩ := hb
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexec, hF g (by omega), ht, Bool.false_eq_true, ↓reduceIte]; exact hG g (by omega)⟩

/-- The state after an awaited call answered with `d`. -/
def afterValue (st : St) (hist : List Event) (x op : String) (ds : List Data) (d : Data) : AS :=
  ⟨{ st with env := if x == "" then st.env else st.env.put x (alloc st.heap d).1, heap := (alloc st.heap d).2 },
    hist ++ [⟨op, ds, .value d⟩]⟩

theorem AOk1.await_value {s x op args vs st d} (he : EvalsL p s.st args vs st)
    (ho : o op (vs.map (readData 50 st.heap)) s.hist = .value d) :
    AOk1 p a o s (.await x op args) (.ok .normal (afterValue st s.hist x op (vs.map (readData 50 st.heap)) d)) := by
  obtain ⟨F, hF⟩ := he
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexec, hF g hg, ho, afterValue]⟩

theorem AOk1.await_reject {s x op args vs st n m} (he : EvalsL p s.st args vs st)
    (ho : o op (vs.map (readData 50 st.heap)) s.hist = .reject n m) :
    AOk1 p a o s (.await x op args) (.thrown (rejection st.heap n m).1
      ⟨{ st with heap := (rejection st.heap n m).2 }, s.hist ++ [⟨op, vs.map (readData 50 st.heap), .reject n m⟩]⟩) := by
  obtain ⟨F, hF⟩ := he
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexec, hF g hg, ho]⟩

theorem AOk1.tryCatch_thrown {s body x h v r out} (hb : AOk p a o s body (.thrown v r))
    (hh : AOk p a o ⟨{ r.st with env := r.st.env.put x v }, r.hist⟩ h out) :
    AOk1 p a o s (.tryCatch body x h) out := by
  obtain ⟨F, hF⟩ := hb
  obtain ⟨G, hG⟩ := hh
  exact ⟨F + G + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexec, hF g (by omega), hG g (by omega)]⟩

theorem AOk1.tryCatch_ok {s body x h c r} (hb : AOk p a o s body (.ok c r)) :
    AOk1 p a o s (.tryCatch body x h) (.ok c r) := by
  obtain ⟨F, hF⟩ := hb
  exact ⟨F + 1, fun f hf => by
    obtain ⟨g, rfl, hg⟩ := succ_of_le hf
    simp only [aexec, hF g hg]⟩

theorem _root_.Js.Eff.ite_run {W : Js.World} {α} {c : Prop} [Decidable c] (m n : Js.Eff W α) (o : W.Oracle) (h : W.Hist) :
    (if c then m else n) o h = if c then m o h else n o h := by
  split <;> rfl


/-! ## The outside world on both sides

The view's oracle answers typed values; Core's answers data that `alloc` builds on the heap. The bridge
holds for every pair of oracles that answer related calls alike. `alloc` is `partial`, so what it builds
is part of the relation rather than computed. -/

/-- An `Error` object as `rejection` builds it. -/
instance : TyRep Js.Exn where
  rep h e v := ∃ l, v = .ref l ∧ h[l]? = some (.record [("name", .str e.name), ("message", .str e.message)])
  mono hp := fun ⟨l, hv, hl⟩ => ⟨l, hv, lookup_mono hp hl⟩

theorem SimE.exnMessage {p s ex} {e : Js.Exn} (h : SimE p s ex e) : SimE p s (.field ex "message") e.message := by
  intro s₁ hs
  obtain ⟨v, s₂, hev, hext, ⟨l, rfl, hl⟩⟩ := h s₁ hs
  exact ⟨.str e.message, s₂, Evals.field hev (by simp [readField, hl, List.lookup]), hext, rfl⟩

theorem SimE.exnName {p s ex} {e : Js.Exn} (h : SimE p s ex e) : SimE p s (.field ex "name") e.name := by
  intro s₁ hs
  obtain ⟨v, s₂, hev, hext, ⟨l, rfl, hl⟩⟩ := h s₁ hs
  exact ⟨.str e.name, s₂, Evals.field hev (by simp [readField, hl, List.lookup]), hext, rfl⟩

theorem SimB.lit_true {p s} : SimB p s (.lit (.bool true)) True :=
  fun s₁ _ => ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, by simp [truthy]⟩

theorem SimE.exnRecord {p s n m} {msg : Js.Str} (hm : SimE p s m msg) :
    SimE p s (.record [("name", .lit (.str n)), ("message", m)]) (⟨n, msg⟩ : Js.Exn) := by
  intro s₁ hs
  obtain ⟨v, s₂, hev, hext, hrep⟩ := hm s₁ hs
  have hv : v = .str msg := hrep
  subst hv
  exact ⟨_, _, Evals.record (EvalsF.cons (Evals.lit _ _ _) (EvalsF.cons hev (EvalsF.nil _ _))),
    ⟨hext.1, hext.2.trans (List.prefix_append _ _)⟩, ⟨_, rfl, by simp⟩⟩

macro_rules | `(tactic| s_rec) => `(tactic| (apply SimE.exnRecord; sim'))

theorem SimB.ofC {p s e P} [Decidable P] (h : SimC p s e P) : SimB p s e P :=
  fun s₁ hs => let ⟨s₂, hev, hext⟩ := h s₁ hs; ⟨_, s₂, hev, hext, by simp [truthy]⟩

macro_rules | `(tactic| s_field) => `(tactic| (apply SimE.exnMessage; sim'))
macro_rules | `(tactic| s_field) => `(tactic| (apply SimE.exnName; sim'))
macro_rules | `(tactic| simb) => `(tactic| exact SimB.lit_true)

def AnsRel {α} [TyRep α] : Js.Answer α → Ans → Prop
  | .value r, .value d => ∀ h, h <+: (alloc h d).2 ∧ rep (alloc h d).2 r (alloc h d).1
  | .reject e, .reject n m => e.name = n ∧ e.message = m ∧
      ∀ h, h <+: (rejection h n m).2 ∧ rep (rejection h n m).2 e (rejection h n m).1
  | _, _ => False

section Rel
variable {W : Js.World} [R : ∀ op, TyRep (W.Res op)] (opName : W.Op → String)
  (ArgOK : (op : W.Op) → W.Arg op → List Data → Prop)

def EvRel (ev : W.Event) (ce : Event) : Prop :=
  ce.op = opName ev.op ∧ ArgOK ev.op ev.arg ce.args ∧ AnsRel ev.ans ce.ans

def HRel (hv : W.Hist) (hc : List Event) : Prop := List.Forall₂ (EvRel opName ArgOK) hv hc

def ORel (ov : W.Oracle) (oc : Oracle) : Prop :=
  ∀ op arg ds hv hc, ArgOK op arg ds → HRel opName ArgOK hv hc → AnsRel (ov op arg hv) (oc (opName op) ds hc)

variable {opName ArgOK}

theorem HRel.snoc {hv hc ev ce} (h : HRel opName ArgOK hv hc) (e : EvRel opName ArgOK ev ce) :
    HRel opName ArgOK (hv ++ [ev]) (hc ++ [ce]) :=
  List.rel_append h (List.Forall₂.cons e .nil)

theorem await_value {p : Prog} {a : AProg} {ov oc} (hO : ORel opName ArgOK ov oc) {s : AS} {hv}
    (hH : HRel opName ArgOK hv s.hist) {x op args vs st} {arg : W.Arg op} {r : W.Res op}
    (he : EvalsL p s.st args vs st) (hA : ArgOK op arg (vs.map (readData 50 st.heap)))
    (hov : ov op arg hv = .value r) :
    ∃ s', AOk1 p a oc s (.await x (opName op) args) (.ok .normal s') ∧ st.heap <+: s'.st.heap ∧
      (∃ v, rep s'.st.heap r v ∧ s'.st.env = if x == "" then st.env else st.env.put x v) ∧
      HRel opName ArgOK (hv ++ [⟨op, arg, .value r⟩]) s'.hist := by
  have hr := hO op arg _ hv s.hist hA hH
  rw [hov] at hr
  cases hd : oc (opName op) (vs.map (readData 50 st.heap)) s.hist with
  | reject n m => rw [hd] at hr; exact hr.elim
  | value d =>
    rw [hd] at hr
    exact ⟨_, AOk1.await_value he hd, (hr st.heap).1, ⟨_, (hr st.heap).2, rfl⟩, HRel.snoc hH ⟨rfl, hA, hr⟩⟩

theorem await_reject {p : Prog} {a : AProg} {ov oc} (hO : ORel opName ArgOK ov oc) {s : AS} {hv}
    (hH : HRel opName ArgOK hv s.hist) {x op args vs st} {arg : W.Arg op} {e : Js.Exn}
    (he : EvalsL p s.st args vs st) (hA : ArgOK op arg (vs.map (readData 50 st.heap)))
    (hov : ov op arg hv = .reject e) :
    ∃ v s', AOk1 p a oc s (.await x (opName op) args) (.thrown v s') ∧ st.heap <+: s'.st.heap ∧
      s'.st.env = st.env ∧ rep s'.st.heap e v ∧ HRel opName ArgOK (hv ++ [⟨op, arg, .reject e⟩]) s'.hist := by
  have hr := hO op arg _ hv s.hist hA hH
  rw [hov] at hr
  cases hd : oc (opName op) (vs.map (readData 50 st.heap)) s.hist with
  | value d => rw [hd] at hr; exact hr.elim
  | reject n m =>
    rw [hd] at hr
    obtain ⟨hn, hm, hk⟩ := hr
    obtain ⟨hp, hrep⟩ := hk st.heap
    refine ⟨_, _, AOk1.await_reject he hd, hp, rfl, hrep, HRel.snoc hH ⟨rfl, hA, ?_⟩⟩
    exact ⟨hn, hm, hk⟩

end Rel

/-! ## Running a stack of blocks

A proof walks the statements in order. `Run s k out` runs the frames `k`: a block of statements, or a
`catch` waiting for a throw from the frames above it. -/

inductive Frame where
  | block (xs : List AStmt)
  | catch (x : String) (h : List AStmt)

variable {p : Prog} {a : AProg} {o : Oracle}

mutual
inductive Run (p : Prog) (a : AProg) (o : Oracle) : AS → List Frame → AOut → Prop
  | done (s) : Run p a o s [] (.ok .normal s)
  | block {s xs k mid out} : AOk p a o s xs mid → Cont p a o mid k out → Run p a o s (.block xs :: k) out
  | pass {s x h k out} : Run p a o s k out → Run p a o s (.catch x h :: k) out

inductive Cont (p : Prog) (a : AProg) (o : Oracle) : AOut → List Frame → AOut → Prop
  | normal {s k out} : Run p a o s k out → Cont p a o (.ok .normal s) k out
  | top {m} : m.exits → Cont p a o m [] m
  | skip {m xs k out} : m.exits → Cont p a o m k out → Cont p a o m (.block xs :: k) out
  | caught {v r x h k out} : Run p a o ⟨{ r.st with env := r.st.env.put x v }, r.hist⟩ (.block h :: k) out →
      Cont p a o (.thrown v r) (.catch x h :: k) out
  | skipCatch {c r x h k out} : (AOut.ok c r).exits → Cont p a o (.ok c r) k out →
      Cont p a o (.ok c r) (.catch x h :: k) out
end

theorem Run.top {s body out} (h : Run p a o s [.block body] out) : AOk p a o s body out := by
  cases h with
  | block hb hc =>
    cases hc with
    | normal hr => cases hr; exact hb
    | top _ => exact hb

/-- The goal of a step: some run of the frames ends in an outcome satisfying `Q`. -/
def AW (p : Prog) (a : AProg) (o : Oracle) (s : AS) (k : List Frame) (Q : AOut → Prop) : Prop :=
  ∃ out, Run p a o s k out ∧ Q out

theorem AW.top {s body Q} (h : AW p a o s [.block body] Q) : ∃ out, AOk p a o s body out ∧ Q out :=
  let ⟨out, hr, hq⟩ := h; ⟨out, hr.top, hq⟩

/-- The variables `arun` starts a function with. -/
def AFn.env0 (fn : AFn) (args : List Val) : Env :=
  let env : Env := (fn.params.zip args).foldl (fun e (x, v) => e.put x v) (fun _ => none)
  fn.params.foldl (fun e x => if (e x).isSome then e else e.put x .undef) env

def ARuns (p : Prog) (a : AProg) (o : Oracle) (fn : AFn) (args : List Val) (s : AS) (out : AOut) : Prop :=
  ∃ F, ∀ f, F ≤ f → arun f p a o fn args s = out

/-- A run of the body that returns or throws is a run of the function. -/
theorem AW.top' {fn args h hc Q} (hq : ∀ s, ¬ Q (.ok .normal s)) (hs : ∀ c s, Q (.ok c s) → ∃ v, c = .ret v)
    (w : AW p a o ⟨⟨fn.env0 args, h⟩, hc⟩ [.block fn.body] Q) (st : St) (hh : st.heap = h) :
    ∃ out, ARuns p a o fn args ⟨st, hc⟩ out ∧ Q out := by
  obtain ⟨out, hr, hq'⟩ := AW.top w
  obtain ⟨F, hF⟩ := hr
  refine ⟨out, ⟨F + 1, fun f hf => ?_⟩, hq'⟩
  obtain ⟨g, rfl, hg⟩ := succ_of_le hf
  have e := hF g hg
  simp only [AFn.env0] at e
  simp only [arun, hh, e]
  rcases out with ⟨c, s'⟩ | ⟨v, s'⟩ | _
  · obtain ⟨v, rfl⟩ := hs c s' hq'; rfl
  · rfl
  · rfl

theorem AW.nil {s k Q} (h : AW p a o s k Q) : AW p a o s (.block [] :: k) Q :=
  let ⟨out, hr, hq⟩ := h; ⟨out, .block (AOk.nil s) (.normal hr), hq⟩

theorem AW.pass {s x h k Q} (hw : AW p a o s k Q) : AW p a o s (.catch x h :: k) Q :=
  let ⟨out, hr, hq⟩ := hw; ⟨out, .pass hr, hq⟩

theorem AW.step {s s₁ c xs k Q} (hc : AOk1 p a o s c (.ok .normal s₁)) (h : AW p a o s₁ (.block xs :: k) Q) :
    AW p a o s (.block (c :: xs) :: k) Q := by
  obtain ⟨out, hr, hq⟩ := h
  cases hr with
  | block hb hk => exact ⟨out, .block (AOk.cons_normal hc hb) hk, hq⟩

/-- Where an outcome that ends a block goes: past blocks, to a `catch` if it is a throw. -/
theorem AW.exit {s m c xs k Q} (hc : AOk1 p a o s c m) (hx : m.exits) (h : ∃ out, Cont p a o m k out ∧ Q out) :
    AW p a o s (.block (c :: xs) :: k) Q :=
  let ⟨out, hk, hq⟩ := h; ⟨out, .block (AOk.cons_exit hc hx) hk, hq⟩

theorem Cont.toTop {m} {Q : AOut → Prop} (hx : m.exits) (hq : Q m) : ∃ out, Cont p a o m [] out ∧ Q out := ⟨m, .top hx, hq⟩
theorem Cont.toSkip {m xs k} {Q : AOut → Prop} (hx : m.exits) (h : ∃ out, Cont p a o m k out ∧ Q out) :
    ∃ out, Cont p a o m (.block xs :: k) out ∧ Q out := let ⟨out, hk, hq⟩ := h; ⟨out, .skip hx hk, hq⟩
theorem Cont.toCatch {v r x h k} {Q : AOut → Prop} (hw : AW p a o ⟨{ r.st with env := r.st.env.put x v }, r.hist⟩ (.block h :: k) Q) :
    ∃ out, Cont p a o (.thrown v r) (.catch x h :: k) out ∧ Q out := let ⟨out, hr, hq⟩ := hw; ⟨out, .caught hr, hq⟩
theorem Cont.toSkipCatch {c r x h k} {Q : AOut → Prop} (hx : (AOut.ok c r).exits) (hw : ∃ out, Cont p a o (.ok c r) k out ∧ Q out) :
    ∃ out, Cont p a o (.ok c r) (.catch x h :: k) out ∧ Q out := let ⟨out, hk, hq⟩ := hw; ⟨out, .skipCatch hx hk, hq⟩

/-- A branch runs as a block of its own, then the rest. -/
theorem AW.ite_true {s c t e xs k Q v st} (hc : Evals p s.st c v st) (ht : truthy v = true)
    (h : AW p a o ⟨st, s.hist⟩ (.block t :: .block xs :: k) Q) : AW p a o s (.block (.ite c t e :: xs) :: k) Q := by
  obtain ⟨out, hr, hq⟩ := h
  cases hr with
  | block hb hk =>
    rename_i mid
    have h1 := AOk1.ite_true (e := e) hc ht hb
    cases hk with
    | normal hr =>
      cases hr with
      | block hb2 hk2 => exact ⟨out, .block (AOk.cons_normal h1 hb2) hk2, hq⟩
    | skip hx hk2 => exact ⟨out, .block (AOk.cons_exit h1 hx) hk2, hq⟩

theorem AW.ite_false {s c t e xs k Q v st} (hc : Evals p s.st c v st) (ht : truthy v = false)
    (h : AW p a o ⟨st, s.hist⟩ (.block e :: .block xs :: k) Q) : AW p a o s (.block (.ite c t e :: xs) :: k) Q := by
  obtain ⟨out, hr, hq⟩ := h
  cases hr with
  | block hb hk =>
    have h1 := AOk1.ite_false (t := t) hc ht hb
    cases hk with
    | normal hr =>
      cases hr with
      | block hb2 hk2 => exact ⟨out, .block (AOk.cons_normal h1 hb2) hk2, hq⟩
    | skip hx hk2 => exact ⟨out, .block (AOk.cons_exit h1 hx) hk2, hq⟩

/-- `try`: the body runs as a block with the handler waiting under it. -/
theorem AW.tryCatch {s body x h xs k Q} (hw : AW p a o s (.block body :: .catch x h :: .block xs :: k) Q) :
    AW p a o s (.block (.tryCatch body x h :: xs) :: k) Q := by
  obtain ⟨out, hr, hq⟩ := hw
  cases hr with
  | block hb hk =>
    rename_i mid
    cases hk with
    | normal hr =>
      cases hr with
      | pass hr =>
        cases hr with
        | block hb2 hk2 => exact ⟨out, .block (AOk.cons_normal (AOk1.tryCatch_ok hb) hb2) hk2, hq⟩
    | caught hr =>
      cases hr with
      | block hb2 hk3 =>
        have h1 := AOk1.tryCatch_thrown hb hb2
        cases hk3 with
        | normal hr3 =>
          cases hr3 with
          | block hb3 hk4 => exact ⟨out, .block (AOk.cons_normal h1 hb3) hk4, hq⟩
        | skip hx3 hk4 => exact ⟨out, .block (AOk.cons_exit h1 hx3) hk4, hq⟩
    | skipCatch hx2 hk3 =>
      cases hk3 with
      | normal _ => simp [AOut.exits] at hx2
      | skip hx3 hk4 => exact ⟨out, .block (AOk.cons_exit (AOk1.tryCatch_ok hb) hx3) hk4, hq⟩

/-! ## Steps with typed values -/

theorem AW.set {s x e xs k Q α} [TyRep α] {va : α} (he : SimE p s.st e va)
    (h : ∀ st', Upd s.st st' x → V st' x va → AW p a o ⟨st', s.hist⟩ (.block xs :: k) Q) :
    AW p a o s (.block (.stmt (.set x e) :: xs) :: k) Q := by
  obtain ⟨v, s2, hev, hext, hrep⟩ := he s.st (Ext.refl _)
  refine AW.step (AOk1.stmt (Execs.set hev)) (h _ ⟨hext.2, fun y hy => ?_⟩ ⟨v, by simp [Env.put], hrep⟩)
  simp [Env.put, hy, hext.1]

theorem AW.ret {s e xs k Q α} [TyRep α] {va : α} (he : SimE p s.st e va)
    (h : ∀ v st', s.st.heap <+: st'.heap → rep st'.heap va v → ∃ out, Cont p a o (.ok (.ret v) ⟨st', s.hist⟩) k out ∧ Q out) :
    AW p a o s (.block (.ret e :: xs) :: k) Q := by
  obtain ⟨v, s2, hev, hext, hrep⟩ := he s.st (Ext.refl _)
  exact AW.exit (AOk1.ret hev) trivial (h v s2 hext.2 hrep)

theorem AW.throw {s e xs k Q} {va : Js.Exn} (he : SimE p s.st e va)
    (h : ∀ v st', s.st.heap <+: st'.heap → st'.env = s.st.env → rep st'.heap va v →
      ∃ out, Cont p a o (.thrown v ⟨st', s.hist⟩) k out ∧ Q out) :
    AW p a o s (.block (.throw e :: xs) :: k) Q := by
  obtain ⟨v, s2, hev, hext, hrep⟩ := he s.st (Ext.refl _)
  exact AW.exit (AOk1.throw hev) trivial (h v s2 hext.2 hext.1 hrep)

section Rel
variable {W : Js.World} [R : ∀ op, TyRep (W.Res op)] {opName : W.Op → String}
  {ArgOK : (op : W.Op) → W.Arg op → List Data → Prop} {ov : W.Oracle}

theorem AW.await_val (hO : ORel opName ArgOK ov o) {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist)
    {x op args vs st xs k Q} {arg : W.Arg op} {r : W.Res op}
    (he : EvalsL p s.st args vs st) (hx : Ext s.st st) (hA : ArgOK op arg (vs.map (readData 50 st.heap)))
    (hov : ov op arg hv = .value r) (hne : x ≠ "")
    (h : ∀ s₁ : AS, Upd s.st s₁.st x → V s₁.st x r → HRel opName ArgOK (hv ++ [⟨op, arg, .value r⟩]) s₁.hist →
      AW p a o s₁ (.block xs :: k) Q) :
    AW p a o s (.block (.await x (opName op) args :: xs) :: k) Q := by
  obtain ⟨s₁, h1, hp, ⟨v, hrep, henv⟩, hH1⟩ := await_value (a := a) (x := x) hO hH he hA hov
  have hb : (x == "") = false := by simpa using hne
  rw [hb] at henv
  refine AW.step h1 (h s₁ ⟨hx.2.trans hp, fun y hy => ?_⟩ ⟨v, by simp [henv, Env.put], hrep⟩ hH1)
  simp [henv, Env.put, hy, hx.1]

theorem AW.await_drop (hO : ORel opName ArgOK ov o) {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist)
    {op args vs st xs k Q} {arg : W.Arg op} {r : W.Res op}
    (he : EvalsL p s.st args vs st) (hx : Ext s.st st) (hA : ArgOK op arg (vs.map (readData 50 st.heap)))
    (hov : ov op arg hv = .value r)
    (h : ∀ s₁ : AS, Ext s.st s₁.st → HRel opName ArgOK (hv ++ [⟨op, arg, .value r⟩]) s₁.hist →
      AW p a o s₁ (.block xs :: k) Q) :
    AW p a o s (.block (.await "" (opName op) args :: xs) :: k) Q := by
  obtain ⟨s₁, h1, hp, ⟨v, hrep, henv⟩, hH1⟩ := await_value (a := a) (x := "") hO hH he hA hov
  simp at henv
  exact AW.step h1 (h s₁ ⟨by rw [henv, hx.1], hx.2.trans hp⟩ hH1)

theorem AW.await_rej (hO : ORel opName ArgOK ov o) {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist)
    {x op args vs st xs k Q} {arg : W.Arg op} {e : Js.Exn}
    (he : EvalsL p s.st args vs st) (hx : Ext s.st st) (hA : ArgOK op arg (vs.map (readData 50 st.heap)))
    (hov : ov op arg hv = .reject e)
    (h : ∀ v (s₁ : AS), Ext s.st s₁.st → rep s₁.st.heap e v → HRel opName ArgOK (hv ++ [⟨op, arg, .reject e⟩]) s₁.hist →
      ∃ out, Cont p a o (.thrown v s₁) k out ∧ Q out) :
    AW p a o s (.block (.await x (opName op) args :: xs) :: k) Q := by
  obtain ⟨v, s₁, h1, hp, henv, hrep, hH1⟩ := await_reject (a := a) (x := x) hO hH he hA hov
  exact AW.exit h1 trivial (h v s₁ ⟨by rw [henv, hx.1], hx.2.trans hp⟩ hrep hH1)

/-- How a run of the view and a run of Core end alike: the same value or the same error, and related histories. -/
def ARes {α} [TyRep α] (r : Js.Settled α) (hv : W.Hist) : AOut → Prop
  | .ok (.ret v) s => (match r with | .fulfilled x => rep s.st.heap x v | .rejected _ => False) ∧ HRel opName ArgOK hv s.hist
  | .thrown v s => (match r with | .rejected e => rep s.st.heap e v | .fulfilled _ => False) ∧ HRel opName ArgOK hv s.hist
  | _ => False

/-- The arguments of an awaited call evaluate to data the view's argument stands for. -/
def ASimArgs (p : Prog) (s : St) (es : List Expr) (ArgOK : (op : W.Op) → W.Arg op → List Data → Prop)
    (op : W.Op) (arg : W.Arg op) : Prop :=
  ∃ vs st, EvalsL p s es vs st ∧ Ext s st ∧ ArgOK op arg (vs.map (readData 50 st.heap))

theorem ASimArgs.zero {s op arg} (hA : ArgOK op arg []) : ASimArgs p s [] ArgOK op arg :=
  ⟨[], s, EvalsL.nil _ _, Ext.refl _, hA⟩

theorem ASimArgs.one {s e op arg α} [TyRep α] {x : α} (he : SimE p s e x)
    (hA : ∀ h v, rep h x v → ArgOK op arg [readData 50 h v]) : ASimArgs p s [e] ArgOK op arg := by
  obtain ⟨v, s₁, hev, hext, hrep⟩ := he s (Ext.refl _)
  exact ⟨[v], s₁, EvalsL.cons hev (EvalsL.nil _ _), hext, hA _ _ hrep⟩

theorem ASimArgs.two {s e₁ e₂ op arg α β} [TyRep α] [TyRep β] {x : α} {y : β} (he₁ : SimE p s e₁ x)
    (he₂ : SimE p s e₂ y) (hA : ∀ h v w, rep h x v → rep h y w → ArgOK op arg [readData 50 h v, readData 50 h w]) :
    ASimArgs p s [e₁, e₂] ArgOK op arg := by
  obtain ⟨v, s₁, hev, hext, hrep⟩ := he₁ s (Ext.refl _)
  obtain ⟨w, s₂, hew, hext₂, hrep₂⟩ := he₂ s₁ hext
  exact ⟨[v, w], s₂, EvalsL.cons hev (EvalsL.cons hew (EvalsL.nil _ _)), hext.trans hext₂,
    hA _ _ _ (mono hext₂.2 hrep) hrep₂⟩

variable (opName ArgOK)

omit R in
/-- A `return` passes every frame. -/
theorem Cont.ret_any {v} {s : AS} {Q : AOut → Prop} (hq : Q (.ok (.ret v) s)) :
    ∀ k, ∃ out, Cont p a o (.ok (.ret v) s) k out ∧ Q out
  | [] => Cont.toTop trivial hq
  | .block _ :: k => Cont.toSkip trivial (Cont.ret_any hq k)
  | .catch _ _ :: k => Cont.toSkipCatch trivial (Cont.ret_any hq k)

/-- Frames with no `catch`. -/
def NoCatch : List Frame → Prop
  | [] => True
  | .block _ :: k => NoCatch k
  | .catch _ _ :: _ => False

omit R in
theorem Cont.thrown_top {v} {s : AS} {Q : AOut → Prop} (hq : Q (.thrown v s)) :
    ∀ k, NoCatch k → ∃ out, Cont p a o (.thrown v s) k out ∧ Q out
  | [], _ => Cont.toTop trivial hq
  | .block _ :: k, hk => Cont.toSkip trivial (Cont.thrown_top hq k hk)

theorem ARes.not_normal {α} [TyRep α] {r : Js.Settled α} {hv} (s : AS) : ¬ ARes (opName := opName) (ArgOK := ArgOK) r hv (.ok .normal s) :=
  fun h => h

theorem ARes.ret {α} [TyRep α] {r : Js.Settled α} {hv} (c : Cmp) (s : AS) (h : ARes (opName := opName) (ArgOK := ArgOK) r hv (.ok c s)) :
    ∃ v, c = .ret v := by
  cases c with
  | ret v => exact ⟨v, rfl⟩
  | _ => exact h.elim

theorem AW.ret_top {s : AS} {H} (hH : HRel opName ArgOK H s.hist) {e xs k α} [TyRep α] {X : α}
    (he : SimE p s.st e X) : AW p a o s (.block (.ret e :: xs) :: k) (ARes (opName := opName) (ArgOK := ArgOK) (.fulfilled X) H) :=
  AW.ret he fun _ _ _ hrep => Cont.ret_any ⟨hrep, hH⟩ k

theorem AW.throw_top {s : AS} {H} (hH : HRel opName ArgOK H s.hist) {e xs k α} [TyRep α] {X : Js.Exn}
    (he : SimE p s.st e X) (hk : NoCatch k) :
    AW p a o s (.block (.throw e :: xs) :: k) (ARes (α := α) (opName := opName) (ArgOK := ArgOK) (.rejected X) H) :=
  AW.throw he fun _ _ _ _ hrep => Cont.thrown_top ⟨hrep, hH⟩ k hk

theorem AW.call_val (hO : ORel opName ArgOK ov o) {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist)
    {x op args xs k Q} {arg : W.Arg op} {r : W.Res op} (hs : ASimArgs p s.st args ArgOK op arg)
    (hov : ov op arg hv = .value r) (hne : x ≠ "")
    (h : ∀ s₁ : AS, Upd s.st s₁.st x → V s₁.st x r → HRel opName ArgOK (hv ++ [⟨op, arg, .value r⟩]) s₁.hist →
      AW p a o s₁ (.block xs :: k) Q) :
    AW p a o s (.block (.await x (opName op) args :: xs) :: k) Q :=
  let ⟨_, _, he, hx, hA⟩ := hs; AW.await_val hO hH he hx hA hov hne h

theorem AW.call_drop (hO : ORel opName ArgOK ov o) {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist)
    {op args xs k Q} {arg : W.Arg op} {r : W.Res op} (hs : ASimArgs p s.st args ArgOK op arg)
    (hov : ov op arg hv = .value r)
    (h : ∀ s₁ : AS, Ext s.st s₁.st → HRel opName ArgOK (hv ++ [⟨op, arg, .value r⟩]) s₁.hist →
      AW p a o s₁ (.block xs :: k) Q) :
    AW p a o s (.block (.await "" (opName op) args :: xs) :: k) Q :=
  let ⟨_, _, he, hx, hA⟩ := hs; AW.await_drop hO hH he hx hA hov h

theorem AW.call_rej (hO : ORel opName ArgOK ov o) {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist)
    {x op args xs k Q} {arg : W.Arg op} {e : Js.Exn} (hs : ASimArgs p s.st args ArgOK op arg)
    (hov : ov op arg hv = .reject e)
    (h : ∀ v (s₁ : AS), Ext s.st s₁.st → rep s₁.st.heap e v → HRel opName ArgOK (hv ++ [⟨op, arg, .reject e⟩]) s₁.hist →
      ∃ out, Cont p a o (.thrown v s₁) k out ∧ Q out) :
    AW p a o s (.block (.await x (opName op) args :: xs) :: k) Q :=
  let ⟨_, _, he, hx, hA⟩ := hs; AW.await_rej hO hH he hx hA hov h

theorem AW.set' {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist) {x e xs k Q α} [TyRep α] {va : α}
    (he : SimE p s.st e va)
    (h : ∀ s₁ : AS, Upd s.st s₁.st x → V s₁.st x va → HRel opName ArgOK hv s₁.hist → AW p a o s₁ (.block xs :: k) Q) :
    AW p a o s (.block (.stmt (.set x e) :: xs) :: k) Q :=
  AW.set he fun st' hu hV => h ⟨st', s.hist⟩ hu hV hH

theorem AW.ite_pos {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist) {c t e xs k Q P}
    (hb : SimB p s.st c P) (hP : P)
    (h : ∀ s₁ : AS, Ext s.st s₁.st → HRel opName ArgOK hv s₁.hist → AW p a o s₁ (.block t :: .block xs :: k) Q) :
    AW p a o s (.block (.ite c t e :: xs) :: k) Q := by
  obtain ⟨v, st, hev, hext, hiff⟩ := hb s.st (Ext.refl _)
  exact AW.ite_true hev (hiff.mpr hP) (h ⟨st, s.hist⟩ hext hH)

theorem AW.ite_neg {s : AS} {hv} (hH : HRel opName ArgOK hv s.hist) {c t e xs k Q P}
    (hb : SimB p s.st c P) (hP : ¬P)
    (h : ∀ s₁ : AS, Ext s.st s₁.st → HRel opName ArgOK hv s₁.hist → AW p a o s₁ (.block e :: .block xs :: k) Q) :
    AW p a o s (.block (.ite c t e :: xs) :: k) Q := by
  obtain ⟨v, st, hev, hext, hiff⟩ := hb s.st (Ext.refl _)
  have hf : truthy v = false := by cases hv : truthy v <;> simp_all
  exact AW.ite_false hev hf (h ⟨st, s.hist⟩ hext hH)

/-- A throw caught: the handler sees the thrown value under its name. -/
theorem Cont.catch' {v} {r : AS} {hv} (hH : HRel opName ArgOK hv r.hist) {x h k Q α} [TyRep α] {va : α}
    (hrep : rep r.st.heap va v)
    (hw : ∀ s₂ : AS, Upd r.st s₂.st x → V s₂.st x va → HRel opName ArgOK hv s₂.hist → AW p a o s₂ (.block h :: k) Q) :
    ∃ out, Cont p a o (.thrown v r) (.catch x h :: k) out ∧ Q out :=
  Cont.toCatch (hw _ ⟨List.prefix_refl _, fun y hy => by simp [Env.put, hy]⟩ ⟨v, by simp [Env.put], hrep⟩ hH)

end Rel

end Core.Async

/-! ## The tactic

`arun` walks Core's statements in order, reading the view's run (`hr`) alongside. It names the
history relation `hH`, the oracle relation `hO`, and expects `opName` and `ArgOK` for the file. -/

namespace Core.Async
open Aeneas.Std Result

syntax "a_args" : tactic
syntax "a_view" : tactic
syntax "a_thrown" : tactic
syntax "a_ret" : tactic
syntax "astep" : tactic
syntax "arun" : tactic

macro_rules | `(tactic| a_args) => `(tactic| exact ASimArgs.zero rfl)
macro_rules | `(tactic| a_args) => `(tactic| exact ASimArgs.one (by sim) (fun h v r => ⟨h, v, rfl, r⟩))
macro_rules | `(tactic| a_args) => `(tactic| exact ASimArgs.two (by sim) (by sim) (fun h v w r₁ r₂ => ⟨h, v, w, rfl, r₁, r₂⟩))

syntax "a_simp" : tactic
syntax "a_lift" : tactic
set_option hygiene false in
macro_rules | `(tactic| a_simp) => `(tactic| simp only [Js.Eff.liftM_ok_bind, Js.Eff.ite_run, Js.Eff.try_lift_ok, Js.Eff.try_ite, Js.Eff.try_throw, Js.Eff.ite_bind, Js.Eff.throw_bind, Js.Eff.pure_bind_eff, ite_true, ite_false] at hr)
set_option hygiene false in
macro_rules | `(tactic| a_lift) => `(tactic| (rcases Js.Eff.bind_lift hr with ⟨_, _, hr⟩; try a_simp))
macro_rules | `(tactic| a_view) => `(tactic| ((try a_simp); repeat a_lift))

set_option hygiene false in
macro_rules | `(tactic| a_thrown) => `(tactic| first
  | exact Cont.thrown_top ⟨hrep, hH⟩ _ trivial
  | (repeat (apply Cont.toSkip trivial)
     apply Cont.catch' opName ArgOK hH hrep
     intro s' hu hV hH; carry hu; clear hu))

set_option hygiene false in
macro_rules | `(tactic| a_ret) => `(tactic| first
  | (simp only [Js.Eff.lift_ok_run, ok.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
     exact AW.ret_top opName ArgOK hH (by sim))
  | (rcases Js.Eff.lift_tail hr with ⟨_, _, rfl, rfl⟩
     exact AW.ret_top opName ArgOK hH (by sim))
  | exact AW.ret_top opName ArgOK hH (by sim))

set_option hygiene false in
macro_rules | `(tactic| astep) => `(tactic| first
  | apply AW.nil
  | apply AW.pass
  | apply AW.tryCatch
  | (show AW _ _ _ _ (.block (.stmt (.set _ _) :: _) :: _) _
     apply AW.set' opName ArgOK hH (by sim)
     intro s' hu hV hH; carry hu; clear hu)
  | (show AW _ _ _ _ (.block (.ret _ :: _) :: _) _
     a_ret)
  | (show AW _ _ _ _ (.block (.throw _ :: _) :: _) _
     simp only [Js.Eff.throw_run, ok.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
     exact AW.throw_top opName ArgOK hH (by sim) trivial)
  | (show AW _ _ _ _ (.block (.ite _ _ _ :: _) :: _) _
     first
     | (show AW _ _ _ _ (.block (.ite (.lit (.bool true)) _ _ :: _) :: _) _
        apply AW.ite_pos opName ArgOK hH SimB.lit_true trivial
        intro s' hu hH; carry hu; clear hu)
     | (split at hr
        rename_i hP
        apply AW.ite_pos opName ArgOK hH (by first | simb | exact SimB.ofC (by simc) | exact SimB.ofC (SimC.eq_str (by sim) (by sim))) hP
        intro s' hu hH; carry hu; clear hu; a_view
        rotate_left
        rename_i hP
        apply AW.ite_neg opName ArgOK hH (by first | simb | exact SimB.ofC (by simc) | exact SimB.ofC (SimC.eq_str (by sim) (by sim))) hP
        intro s' hu hH; carry hu; clear hu; a_view))
  | (show AW _ _ _ _ (.block (.await _ _ _ :: _) :: _) _
     first
     | (rcases Js.Eff.bind_call hr with ⟨x, heq, hr⟩ | ⟨e, heq, rfl, rfl⟩ <;> first
        | (apply AW.call_val opName ArgOK hO hH (by a_args) heq (by decide)
           intro s' hu hV hH; carry hu; clear hu; a_view)
        | (apply AW.call_drop opName ArgOK hO hH (by a_args) heq
           intro s' hu hH; carry hu; clear hu; a_view)
        | (apply AW.call_rej opName ArgOK hO hH (by a_args) heq
           intro v s' hu hrep hH; carry hu; clear hu; a_thrown))
     | (rcases Js.Eff.try_bind_call hr with ⟨x, heq, hr⟩ | ⟨e, heq, hr⟩ <;> first
        | (apply AW.call_val opName ArgOK hO hH (by a_args) heq (by decide)
           intro s' hu hV hH; carry hu; clear hu; a_view)
        | (apply AW.call_drop opName ArgOK hO hH (by a_args) heq
           intro s' hu hH; carry hu; clear hu; a_view)
        | (apply AW.call_rej opName ArgOK hO hH (by a_args) heq
           intro v s' hu hrep hH; carry hu; clear hu; a_view; a_thrown))
     | (rcases Js.Eff.call_tail hr with ⟨x, heq, rfl, rfl⟩ | ⟨e, heq, rfl, rfl⟩ <;> first
        | (apply AW.call_val opName ArgOK hO hH (by a_args) heq (by decide)
           intro s' hu hV hH; carry hu; clear hu)
        | (apply AW.call_drop opName ArgOK hO hH (by a_args) heq
           intro s' hu hH; carry hu; clear hu)
        | (apply AW.call_rej opName ArgOK hO hH (by a_args) heq
           intro v s' hu hrep hH; carry hu; clear hu; a_thrown))
     | (rcases Js.Eff.try_call_tail hr with ⟨x, heq, rfl, rfl⟩ | ⟨e, heq, hr⟩ <;> first
        | (apply AW.call_val opName ArgOK hO hH (by a_args) heq (by decide)
           intro s' hu hV hH; carry hu; clear hu)
        | (apply AW.call_drop opName ArgOK hO hH (by a_args) heq
           intro s' hu hH; carry hu; clear hu)
        | (apply AW.call_rej opName ArgOK hO hH (by a_args) heq
           intro v s' hu hrep hH; carry hu; clear hu; a_view; a_thrown))))

macro_rules | `(tactic| arun) => `(tactic| (a_view; repeat (any_goals astep)))

end Core.Async
