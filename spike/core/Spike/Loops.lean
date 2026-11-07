import Spike.WP
open Core Gen

/-! Control flow proved directly on Core, using one loop rule. -/

attribute [simp] Gen.prog

abbrev numV (x : Int) : Val := .num (F64.ofInt x)

theorem take_succ_get {α} (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] :=
  (List.take_append_getElem hi).symm

/-- `return` inside a loop: stops at the first negative, and misses none before it. -/
theorem firstNegative_spec (xs : List Int) (l : Loc) (h : Heap)
    (harr : h[l]? = some (.array (xs.map numV))) :
    WpRun prog src_features_firstNegative [.ref l] h fun v s => s.heap = h ∧
      ((v = .null ∧ ∀ x ∈ xs, 0 ≤ x) ∨
       ∃ i x, xs[i]? = some x ∧ x < 0 ∧ v = numV x ∧ ∀ y ∈ xs.take i, 0 ≤ y) := by
  apply wprun
  simp only [src_features_firstNegative]
  have hp : src_features_firstNegative.params = ["xs"] := rfl
  let Φ : Cmp → St → Prop := fun c s => ∃ v, c = .ret v ∧ s.heap = h ∧
      ((v = .null ∧ ∀ x ∈ xs, 0 ≤ x) ∨
       ∃ i x, xs[i]? = some x ∧ x < 0 ∧ v = numV x ∧ ∀ y ∈ xs.take i, 0 ≤ y)
  let Inv : Nat → St → Prop := fun i s =>
    s.heap = h ∧ s.env "xs" = some (.ref l) ∧ ∀ y ∈ xs.take i, 0 ≤ y
  apply wp_cons
  refine wps_forOf_inv (l := l) (vs := xs.map numV) Inv (Evals.var ?_) ?_ ?_ ?_ ?_
  · simp [Fn.env0, hp, Env.put]
  · exact ⟨rfl, by simp [Fn.env0, hp, Env.put], by simp⟩
  · rintro i s ⟨hh, -, -⟩; rw [hh]; exact harr
  · rintro s ⟨hh, he, hall⟩
    simp only [List.length_map, List.take_length] at hall
    simp only [Cmp.normal, if_true]
    apply wp_cons; apply wps_ret; apply wpe_lit
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_false]
    exact ⟨_, rfl, hh, Or.inl ⟨rfl, hall⟩⟩
  · rintro i s item hi ⟨hh, he, hall⟩ hitem
    have hi' : i < xs.length := by simpa using hi
    have hx : item = numV xs[i] := by simp [hi'] at hitem; exact hitem.symm
    subst hx
    simp only [src_features_firstNegative_loop0]
    by_cases hneg : xs[i] < 0
    · core_run
      exact ⟨i, xs[i], by simp [hi'], hneg, rfl, hall⟩
    · core_run
      refine ⟨rfl, by simp [Env.put, he], ?_⟩
      rw [take_succ_get xs hi']
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hall y hy
      · simp at hy; subst hy; omega

theorem set_last {α} (h : List α) (a b : α) : (h ++ [a]).set h.length b = h ++ [b] := by simp

theorem filter_take_succ (xs : List Int) {i : Nat} (hi : i < xs.length) :
    (xs.take (i + 1)).filter (0 < ·) = (xs.take i).filter (0 < ·) ++ if 0 < xs[i] then [xs[i]] else [] := by
  rw [take_succ_get xs hi, List.filter_append]
  by_cases h : 0 < xs[i] <;> simp [h]

/-- A loop that builds an array: the heap changes on every turn. -/
theorem positivesLoop_spec (xs : List Int) (l : Loc) (h : Heap)
    (harr : h[l]? = some (.array (xs.map numV))) :
    WpRun prog src_features_positivesLoop [.ref l] h fun v s =>
      ∃ m, v = .ref m ∧ s.heap[m]? = some (.array ((xs.filter (0 < ·)).map numV)) := by
  apply wprun
  simp only [src_features_positivesLoop]
  have hl : l < h.length := by
    by_contra hc
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at harr
  let out := fun i => Obj.array (((xs.take i).filter (0 < ·)).map numV)
  let Inv : Nat → St → Prop := fun i s =>
    s.heap = h ++ [out i] ∧ s.env "xs" = some (.ref l) ∧ s.env "out" = some (.ref h.length)
  apply wp_cons; apply wps_set; apply wpe_array; apply wpa_nil
  simp only [ite_true]
  apply wp_cons
  refine wps_forOf_inv (l := l) (vs := xs.map numV) Inv (Evals.var ?_) ?_ ?_ ?_ ?_
  · simp [Fn.env0, Env.put]
  · exact ⟨by simp [Fn.env0, out], by simp [Fn.env0, Env.put], by simp [Env.put]⟩
  · rintro i s ⟨hh, -, -⟩; rw [hh, List.getElem?_append_left hl]; exact harr
  · rintro s ⟨hh, he, ho⟩
    simp only [ite_true]
    apply wp_cons; apply wps_ret; apply wpe_var
    simp only [ho, reduceCtorEq, not_false_eq_true, ite_false]
    refine ⟨_, rfl, h.length, rfl, ?_⟩
    simp [hh, out]
  · rintro i s item hi ⟨hh, he, ho⟩ hitem
    have hi' : i < xs.length := by simpa using hi
    have hx : item = numV xs[i] := by simp [hi'] at hitem; exact hitem.symm
    subst hx
    simp only [src_features_positivesLoop_loop0]
    by_cases hpos : 0 < xs[i]
    · core_run
      refine ⟨((xs.take i).filter (0 < ·)).map numV, rfl, ?_⟩
      core_run
      refine ⟨?_, by simp [Env.put, he], by simp [Env.put, ho]⟩
      simp [out, filter_take_succ xs hi', hpos]
    · core_run
      refine ⟨?_, by simp [Env.put, he], by simp [Env.put, ho]⟩
      simp [out, filter_take_succ xs hi', hpos]

abbrev Safe (x : Int) : Prop := -9007199254740991 ≤ x ∧ x ≤ 9007199254740991

/-- A loop with a running total, specified once. -/
theorem sumAll_spec (xs : List Int) (l : Loc) (h : Heap) (harr : h[l]? = some (.array (xs.map numV)))
    (hsafe : ∀ i, i ≤ xs.length → Safe (xs.take i).sum) :
    WpRun prog src_features_sumAll [.ref l] h fun v s => s.heap = h ∧ v = numV xs.sum := by
  apply wprun
  simp only [src_features_sumAll]
  let Inv : Nat → St → Prop := fun i s =>
    s.heap = h ∧ s.env "xs" = some (.ref l) ∧ s.env "t" = some (numV (xs.take i).sum)
  apply wp_cons; apply wps_set; apply wpe_lit
  simp only [ite_true]
  apply wp_cons
  refine wps_forOf_inv (l := l) (vs := xs.map numV) Inv (Evals.var ?_) ?_ ?_ ?_ ?_
  · simp [Fn.env0, Env.put]
  · exact ⟨rfl, by simp [Fn.env0, Env.put], by simp [Env.put]⟩
  · rintro i s ⟨hh, -, -⟩; rw [hh]; exact harr
  · rintro s ⟨hh, he, ht⟩
    simp only [ite_true]
    apply wp_cons; apply wps_ret; apply wpe_var
    simp only [List.length_map, List.take_length] at ht
    simp only [ht, reduceCtorEq, not_false_eq_true, ite_false]
    exact ⟨_, rfl, hh, rfl⟩
  · rintro i s item hi ⟨hh, he, ht⟩ hitem
    have hi' : i < xs.length := by simpa using hi
    have hx : item = numV xs[i] := by simp [hi'] at hitem; exact hitem.symm
    subst hx
    simp only [src_features_sumAll_loop0]
    have hb := hsafe (i + 1) (by omega)
    rw [take_succ_get xs hi', List.sum_append] at hb
    simp only [List.sum_cons, List.sum_nil, Int.add_zero] at hb
    obtain ⟨b1, b2⟩ := hb
    core_run
    refine ⟨rfl, by simp [Env.put, he], ?_⟩
    rw [take_succ_get xs hi', List.sum_append]
    simp [Env.put]

/-- A caller uses the callee's theorem, not its code, so the loop stays out of this proof. -/
theorem sumPlusOne_spec (xs : List Int) (l : Loc) (h : Heap) (harr : h[l]? = some (.array (xs.map numV)))
    (hsafe : ∀ i, i ≤ xs.length → Safe (xs.take i).sum) (hb : Safe (xs.sum + 1)) :
    WpRun prog src_features_sumPlusOne [.ref l] h fun v s => s.heap = h ∧ v = numV (xs.sum + 1) := by
  apply wprun
  simp only [src_features_sumPlusOne]
  obtain ⟨b1, b2⟩ := hb
  apply wp_cons; apply wps_ret; apply wpe_bin
  apply wpe_call (fn := src_features_sumAll) (by simp)
  apply wpa_cons; apply wpe_var
  simp only [Fn.env0, List.map, Env.put, ite_true]
  apply wpa_nil
  refine WpRun.mono (sumAll_spec xs l h ?_ hsafe) ?_
  · simpa [Fn.env0, Env.put] using harr
  rintro v s ⟨hh, rfl⟩
  apply wpe_lit
  simp (disch := omega) [binary, hh]

/-- A tree, where both children may be one shared object. -/
inductive T where
  | leaf
  | node (x : Int) (a b : T)

def T.total : T → Int
  | .leaf => 0
  | .node x a b => x + a.total + b.total

def T.safe : T → Prop
  | .leaf => True
  | .node x a b => a.safe ∧ b.safe ∧ Safe (x + a.total) ∧ Safe (x + a.total + b.total)

/-- Nothing here says subtrees are separate, so sharing needs no special case. -/
def EncT (h : Heap) : T → Val → Prop
  | .leaf, v => v = .null
  | .node x a b, v => ∃ l fs va vb, v = .ref l ∧ h[l]? = some (.record fs) ∧
      (fs.lookup "value").getD .undef = numV x ∧ (fs.lookup "left").getD .undef = va ∧
      (fs.lookup "right").getD .undef = vb ∧ EncT h a va ∧ EncT h b vb

/-- Recursion: the proof is an induction on the tree. -/
theorem treeSum_spec (h : Heap) (t : T) : ∀ v, EncT h t v → t.safe →
    WpRun prog src_features_treeSum [v] h fun w s => s.heap = h ∧ w = numV t.total := by
  induction t with
  | leaf =>
    intro v hv _
    subst hv
    apply wprun
    simp only [src_features_treeSum]
    core_run
    simp [T.total]
  | node x a b iha ihb =>
    rintro v ⟨l, fs, va, vb, rfl, hl, hx, hva, hvb, ea, eb⟩ ⟨sa, sb, ⟨b1, b2⟩, ⟨b3, b4⟩⟩
    apply wprun
    simp only [src_features_treeSum]
    obtain ⟨wa, ra, runA, hhA, rfl⟩ := iha va ea sa
    obtain ⟨wb, rb, runB, hhB, rfl⟩ := ihb vb eb sb
    let s : St := ⟨src_features_treeSum.env0 [.ref l], h⟩
    have hparams : src_features_treeSum.params = ["t"] := rfl
    have ht : s.env "t" = some (.ref l) := by simp [s, Fn.env0, hparams, Env.put]
    have rd : ∀ k, readField s.heap (.ref l) k = some ((fs.lookup k).getD .undef) := fun k => by
      show readField h (.ref l) k = _
      simp only [readField, hl]
    have ev := fun k => Evals.field (p := prog) (k := k) (Evals.var ht) (rd k)
    have e2 : Evals prog s (.call "src_features_treeSum" [.field (.var "t") "left"]) (numV a.total) s := by
      have := Evals.call (fn := src_features_treeSum) (g := "src_features_treeSum")
        (EvalsL.cons (ev "left") (EvalsL.nil _ _)) (by simp) (hva ▸ runA)
      have hs : ({ s with heap := ra.heap } : St) = s := by
        show St.mk s.env ra.heap = St.mk s.env h
        rw [hhA]
      rwa [hs] at this
    have e3 : Evals prog s (.call "src_features_treeSum" [.field (.var "t") "right"]) (numV b.total) s := by
      have := Evals.call (fn := src_features_treeSum) (g := "src_features_treeSum")
        (EvalsL.cons (ev "right") (EvalsL.nil _ _)) (by simp) (hvb ▸ runB)
      have hs : ({ s with heap := rb.heap } : St) = s := by
        show St.mk s.env rb.heap = St.mk s.env h
        rw [hhB]
      rwa [hs] at this
    have e4 := Evals.bin (op := .add) (Evals.bin (op := .add) (hx ▸ ev "value") e2 rfl) e3 rfl
    have hc : Evals prog s (.bin .eq (.var "t") (.lit .null)) (.bool false) s :=
      Evals.bin (Evals.var ht) (Evals.lit _ _ _) (by simp [binary])
    refine ⟨_, s, ExecsL.cons_normal (Execs.ite_false hc (by simp [truthy]) (ExecsL.nil _ _))
      (ExecsL.cons_exit (Execs.ret e4) (by simp)), _, rfl, rfl, ?_⟩
    simp (disch := omega) [T.total]

#print axioms firstNegative_spec
#print axioms positivesLoop_spec
#print axioms sumPlusOne_spec
#print axioms treeSum_spec
