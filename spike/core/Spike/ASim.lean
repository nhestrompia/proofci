import Spike.Tac
import CoreAsync
import ProofciAsync
open Core Core.Async
open TyRep (rep mono)

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

/-! ## The outside world on both sides

The view's oracle answers typed values; Core's answers data that `alloc` builds on the heap. The bridge
holds for every pair of oracles that answer related calls alike. `alloc` is `partial`, so what it builds
is part of the relation rather than computed. -/

/-- An `Error` object as `rejection` builds it. -/
instance : TyRep Js.Exn where
  rep h e v := ∃ l, v = .ref l ∧ h[l]? = some (.record [("name", .str e.name), ("message", .str e.message)])
  mono hp := fun ⟨l, hv, hl⟩ => ⟨l, hv, lookup_mono hp hl⟩

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

end Rel

end Core.Async
