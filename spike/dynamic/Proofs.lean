import Gen.Unknown
import Gen.Union
import Gen.Budget
import Gen.Slideshow
import Gen.Fixtures
import Gen.Bank
import Gen.Alias
import Spike.Sim

/-! User-level guarantees about the dynamic translations in `Gen/`. -/

open Core Dyn

/-- Whatever the value, the Group by id is a string: the value itself when it is one. -/
theorem groupByFieldId_string (v : Val) (h : Heap) :
    Spec (Unknown.parseChartGroupByFieldId v) h fun r h' =>
      h' = h ∧ (r = v ∧ typeOf v = str "string" ∨ r = str "" ∧ typeOf v ≠ str "string") := by
  unfold Unknown.parseChartGroupByFieldId
  cases v <;> simp [bin, binary, typeOf, typeName, str, utf16, truthy]

theorem heap_len {h : Heap} {l o} (hl : h[l]? = some o) : l < h.length := by
  by_contra hc
  simp [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hl

/-- `bump` adds to the counter it is called on. -/
theorem bump_adds {h : Heap} {l : Loc} {fs} {k b : Int} (hl : h[l]? = some (.record fs))
    (hn : fs.lookup "n" = some (num k)) (b1 : -9007199254740991 ≤ k + b) (b2 : k + b ≤ 9007199254740991) :
    Spec (Fixtures.Counter.bump (.ref l) (num b)) h fun r h' =>
      r = num (k + b) ∧ h' = h.set l (.record (("n", num (k + b)) :: fs.filter (·.1 != "n"))) := by
  unfold Fixtures.Counter.bump
  simp only [spec_bind]
  rw [spec_eq (field_rec hl)]
  simp only [hn, Option.getD_some]
  rw [bin_add_num ⟨b1, b2⟩, spec_pure, spec_eq (setField_rec hl),
    spec_eq (field_rec (List.getElem?_set_self (heap_len hl)))]
  simp [List.lookup]

/-- One counter passed twice is bumped twice: the heap makes the sharing visible. -/
theorem bumpBoth_shared {h : Heap} {l : Loc} {fs} {k : Int} (hl : h[l]? = some (.record fs))
    (hc : fs.lookup "__class" = some (str "Counter")) (hm : fs.lookup "bump" = none)
    (hn : fs.lookup "n" = some (num k)) (b1 : -9007199254740991 ≤ k) (b2 : k + 2 ≤ 9007199254740991) :
    Spec (Fixtures.bumpBoth (.ref l) (.ref l)) h fun r _ => r = num (k + 2) := by
  have hlen := heap_len hl
  unfold Fixtures.bumpBoth
  simp only [spec_bind]
  rw [spec_eq (isMethodOf_rec hl hc hm), if_pos rfl]
  apply spec_mono (bump_adds hl hn (by omega) (by omega))
  rintro _ h1 ⟨-, rfl⟩
  have hl1 := List.getElem?_set_self (a := Obj.record (("n", num (k + 1)) :: fs.filter (·.1 != "n"))) hlen
  rw [spec_eq (isMethodOf_rec hl1 (by rw [lookup_set_ne (by simp)]; exact hc)
    (by rw [lookup_set_ne (by simp)]; exact hm)), if_pos rfl]
  apply spec_mono (bump_adds hl1 lookup_set_same (by omega) (by omega))
  rintro _ h2 ⟨-, rfl⟩
  rw [spec_eq (field_rec (List.getElem?_set_self (by simpa using hlen)))]
  simp [List.lookup, show k + 1 + 1 = k + 2 by omega]

/-- Two counters are bumped once each. -/
theorem bumpBoth_separate {h : Heap} {l m : Loc} {fs gs} {j k : Int} (hne : l ≠ m)
    (hl : h[l]? = some (.record fs)) (hc : fs.lookup "__class" = some (str "Counter")) (hb : fs.lookup "bump" = none)
    (hn : fs.lookup "n" = some (num j))
    (hm : h[m]? = some (.record gs)) (hc' : gs.lookup "__class" = some (str "Counter")) (hb' : gs.lookup "bump" = none)
    (hn' : gs.lookup "n" = some (num k))
    (b1 : -9007199254740991 ≤ j) (b2 : j + 1 ≤ 9007199254740991)
    (b3 : -9007199254740991 ≤ k) (b4 : k + 1 ≤ 9007199254740991) :
    Spec (Fixtures.bumpBoth (.ref l) (.ref m)) h fun r _ => r = num (j + 1) := by
  have hlen := heap_len hl
  unfold Fixtures.bumpBoth
  simp only [spec_bind]
  rw [spec_eq (isMethodOf_rec hl hc hb), if_pos rfl]
  apply spec_mono (bump_adds hl hn (by omega) (by omega))
  rintro _ h1 ⟨-, rfl⟩
  have hm1 : (h.set l (.record (("n", num (j + 1)) :: fs.filter (·.1 != "n"))))[m]? = some (.record gs) := (getElem?_set_ne' hne).trans hm
  rw [spec_eq (isMethodOf_rec hm1 hc' hb'), if_pos rfl]
  apply spec_mono (bump_adds hm1 hn' (by omega) (by omega))
  rintro _ h2 ⟨-, rfl⟩
  rw [spec_eq (field_rec ((getElem?_set_ne' (Ne.symm hne)).trans (List.getElem?_set_self hlen)))]
  simp [List.lookup]

/-- `transfer` keeps the total and never overdraws, as the typed proof shows for the typed view. -/
theorem transfer_conserves {h : Heap} {l : Loc} {fs} {a b amt : Int} (hl : h[l]? = some (.record fs))
    (hf : fs.lookup "from" = some (num a)) (ht : fs.lookup "to" = some (num b))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (htot : a + b ≤ 9007199254740991) :
    Spec (Bank.transfer (.ref l) (num amt)) h fun r h' =>
      r = .null ∨ ∃ a' b', r = .ref h.length ∧ h' = h ++ [.record [("from", num a'), ("to", num b')]] ∧
        a' + b' = a + b ∧ 0 ≤ a' := by
  unfold Bank.transfer; dsteps
  exact .inr ⟨_, _, trivial, rfl, by omega, by omega⟩

/-- `queue` keeps the caller's object, not a copy: the history ends with the same reference. -/
theorem queue_keeps_reference {h : Heap} {l m : Loc} {fs xs} {i : Int} (asset : Val) (hne : l ≠ m)
    (hl : h[l]? = some (.record fs)) (hh : fs.lookup "history" = some (.ref m)) (hi : fs.lookup "index" = some (num i))
    (hm : h[m]? = some (.array xs)) (bi : -9007199254740991 ≤ i ∧ i + 1 ≤ 9007199254740991)
    (bx : xs.length + 1 ≤ 9007199254740991) :
    Spec (Slideshow.SlideshowHistory.queue (.ref l) asset) h fun r h' =>
      r = .undef ∧ h'[m]? = some (.array (xs ++ [asset])) := by
  have hlen := heap_len hl
  unfold Slideshow.SlideshowHistory.queue
  simp only [spec_bind]
  rw [spec_eq (field_rec hl)]
  simp only [hh, Option.getD_some]
  rw [spec_eq (push_arr hm)]
  have hl1 : (h.set m (.array (xs ++ [asset])))[l]? = some (.record fs) := (getElem?_set_ne' (Ne.symm hne)).trans hl
  have hm1 : (h.set m (.array (xs ++ [asset])))[m]? = some (.array (xs ++ [asset])) :=
    List.getElem?_set_self (heap_len hm)
  rw [spec_eq (field_rec hl1)]
  simp only [hi, Option.getD_some]
  rw [spec_eq (field_rec hl1)]
  simp only [hh, Option.getD_some]
  rw [spec_eq (length_arr hm1)]
  simp only [List.length_append, List.length_singleton]
  rw [bin_sub_num ⟨by omega, by omega⟩, spec_pure, bin_eq_num, spec_pure, truthy_bool]
  split
  · simp only [spec_bind]
    rw [spec_eq (field_rec hl1)]
    simp only [hi, Option.getD_some]
    rw [bin_add_num ⟨bi.1.trans (by omega), bi.2⟩, spec_pure, spec_eq (setField_rec hl1)]
    exact ⟨rfl, (getElem?_set_ne' hne).trans hm1⟩
  · exact ⟨rfl, hm1⟩

/-! Loops and callbacks. `dsteps` runs the body of each iteration; the invariants are the user's. -/


theorem messageIsEmpty_str {h : Heap} {m fs s} (hm : h[m]? = some (.record fs))
    (hc : fs.lookup "content" = some (.str s)) :
    Spec (Alias.messageIsEmpty (.ref m)) h fun r h' => h' = h ∧ r = .bool (decide (Js.trim s = [])) := by
  unfold Alias.messageIsEmpty; dsteps
  all_goals trivial

/-- What the content of a message should end up as. -/
def spaced (s : List Nat) : List Nat := if Js.trim s = [] then [32] else s

theorem spaced_step {s0 s : List Nat} (hs : s = s0 ∨ s = spaced s0) :
    (if Js.trim s = [] then [32] else s) = spaced s0 := by
  have t : Js.trim [32] = [] := by decide
  rcases hs with rfl | rfl
  · rfl
  · unfold spaced; split <;> simp_all

/-- After the first `i` messages: the array is intact, and each message's content is either
untouched or spaced, and spaced once the loop has passed it. -/
def Spaced (h H : Heap) (l : Loc) (xs : List Val) (i : Nat) : Prop :=
  H[l]? = some (.array xs) ∧ ∀ m : Nat, Val.ref m ∈ xs → m ≠ l ∧ ∃ fs s0 fs', h[m]? = some (.record fs) ∧
    fs.lookup "content" = some (.str s0) ∧ H[m]? = some (.record fs') ∧
    ∃ s, fs'.lookup "content" = some (.str s) ∧ (s = s0 ∨ s = spaced s0) ∧ (Val.ref m ∈ xs.take i → s = spaced s0)

theorem same_record {h : Heap} {m : Nat} {fs gs k} {s t : List Nat} (hm : h[m]? = some (.record fs))
    (hg : h[m]? = some (.record gs)) (hs : fs.lookup k = some (.str s)) (ht : gs.lookup k = some (.str t)) : s = t := by
  rw [hm] at hg; cases hg; rw [hs] at ht; cases ht; rfl

/-- Every message whose content trims to nothing gets `" "`, the others keep theirs, and the
array returned lists the same messages. Messages may appear more than once. -/
theorem addSpace_spec {h : Heap} {l xs} (hl : h[l]? = some (.array xs))
    (hr : ∀ x ∈ xs, ∃ m : Nat, x = .ref m)
    (hx : ∀ m : Nat, Val.ref m ∈ xs → m ≠ l ∧ ∃ fs s0, h[m]? = some (.record fs) ∧ fs.lookup "content" = some (.str s0)) :
    Spec (Alias.addSpaceToAnyEmptyMessages (.ref l)) h fun r h' =>
      ∃ n, r = .ref n ∧ h'[n]? = some (.array xs) ∧ h'[l]? = some (.array xs) ∧
        ∀ (m : Nat) fs s0, Val.ref m ∈ xs → h[m]? = some (.record fs) → fs.lookup "content" = some (.str s0) →
          ∃ fs', h'[m]? = some (.record fs') ∧ fs'.lookup "content" = some (.str (spaced s0)) := by
  unfold Alias.addSpaceToAnyEmptyMessages
  simp only [spec_bind, spec_pure]
  refine jsMap_spec (xs := xs) (fun i out H => out = xs.take i ∧ Spaced h H l xs i)
    ⟨rfl, hl, fun m hm => ?_⟩ (fun _ _ _ hI => hI.2.1) ?_ ?_
  · obtain ⟨hne, fs, s0, hf, hc⟩ := hx m hm
    exact ⟨hne, fs, s0, fs, hf, hc, hf, s0, hc, Or.inl rfl, by simp⟩
  · rintro i out H hi ⟨ho, hS⟩
    obtain ⟨m, e⟩ := hr _ (List.getElem_mem hi)
    have hmem : Val.ref m ∈ xs := e ▸ List.getElem_mem hi
    have htake : xs.take (i + 1) = xs.take i ++ [.ref m] := by rw [List.take_succ_eq_append_getElem hi, e]
    obtain ⟨hne, fs, s0, fs', hm, hc, hm', s, hs, hss, -⟩ := hS.2 m hmem
    rw [e]; simp only [spec_bind]
    refine spec_mono (messageIsEmpty_str hm' hs) ?_
    rintro r H2 ⟨rfl, rfl⟩
    have hstep := spaced_step hss
    by_cases ht : Js.trim s = []
    · simp only [ht, decide_true, truthy_bool, ite_true, spec_bind, spec_pure] at hstep ⊢
      rw [spec_setField hm']
      refine ⟨by rw [ho, htake], by rw [List.getElem?_set_ne hne]; exact hS.1, fun m' hm'' => ?_⟩
      obtain ⟨hne', gs, t0, gs', hg, hgc, hg', t, ht', hts, htk⟩ := hS.2 m' hm''
      refine ⟨hne', gs, t0, ?_⟩
      by_cases hmm : m' = m
      · subst hmm
        have := same_record hm hg hc hgc; subst this
        exact ⟨_, hg, hgc, List.getElem?_set_self (heap_lt hm'), [32], lookup_set_same, Or.inr hstep,
          fun _ => hstep⟩
      · refine ⟨gs', hg, hgc, by rw [List.getElem?_set_ne (Ne.symm hmm)]; exact hg', t, ht', hts, fun hk => htk ?_⟩
        rw [htake] at hk; simpa [hmm] using hk
    · simp only [ht, decide_false, truthy_bool, Bool.false_eq_true, ite_false, spec_pure] at hstep ⊢
      refine ⟨by rw [ho, htake], hS.1, fun m' hm'' => ?_⟩
      obtain ⟨hne', gs, t0, gs', hg, hgc, hg', t, ht', hts, htk⟩ := hS.2 m' hm''
      refine ⟨hne', gs, t0, gs', hg, hgc, hg', t, ht', hts, fun hk => ?_⟩
      by_cases hmm : m' = m
      · subst hmm
        have := same_record hm hg hc hgc; subst this
        rw [hm'] at hg'; cases hg'; rw [hs] at ht'; cases ht'; exact hstep
      · rw [htake] at hk; exact htk (by simpa [hmm] using hk)
  · rintro out H ⟨rfl, hS⟩
    refine ⟨H.length, rfl, by simp, by rw [List.getElem?_append_left (heap_lt hS.1)]; exact hS.1, ?_⟩
    intro m fs s0 hmem hm hc
    obtain ⟨-, gs, t0, gs', hg, hgc, hg', t, ht', -, htk⟩ := hS.2 m hmem
    have := same_record hm hg hc hgc; subst this
    exact ⟨gs', by rw [List.getElem?_append_left (heap_lt hg')]; exact hg', by rw [ht', htk (by simpa using hmem)]⟩

theorem spec_toStr_of {h : Heap} {x a} {P : Val → Heap → Prop} (e : asNum (.num x) = some a) :
    Spec (toStr (.num x)) h P ↔ P (.str (Js.numStr a)) h := by
  unfold Spec toStr prim; simp only [primV, textOf, e, Option.map_some]

theorem spec_toStr_num {h : Heap} {k : Int} {P : Val → Heap → Prop} (h1 : -9007199254740991 ≤ k)
    (h2 : k ≤ 9007199254740991) : Spec (toStr (num k)) h P ↔ P (.str (Js.numStr ⟨k, h1, h2⟩)) h :=
  spec_toStr_of (asNum_isInt (Or.inl rfl))

macro "dlen" : tactic => `(tactic| ((try simp only [List.length_append, List.length_set,
  List.length_singleton, List.length_cons, List.length_nil]); omega))

syntax "dcell" : tactic
macro_rules
  | `(tactic| dcell) => `(tactic| first
    | with_reducible assumption
    | (rw [List.getElem?_set_ne] <;> first | omega | dcell)
    | (rw [List.getElem?_set_self] <;> first | dlen | rfl)
    | (rw [List.getElem?_append_left] <;> first | dlen | dcell)
    | rfl)

macro "dclose" : tactic => `(tactic| first
  | trivial
  | dlen
  | dframe
  | (refine ⟨?_, ?_, ?_, ?_⟩; rotate_right; dcell; all_goals omega)
  | (refine ⟨?_, ?_⟩; rotate_right; dcell))

/-- How many of the first `i` items are not empty. -/
def cnt (es : List Bool) (i : Nat) : Nat := ((es.take i).filter (! ·)).length

theorem cnt_succ {es : List Bool} {i} (hi : i < es.length) :
    cnt es (i + 1) = cnt es i + if es.getD i false then 0 else 1 := by
  unfold cnt
  rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.length_append, List.getD_eq_getElem _ _ hi]
  cases es[i] <;> simp

/-- The color item `i` should get: `"none"` when empty, else `c` and its place among the non-empty ones. -/
def expColor (es : List Bool) (i : Nat) : Val :=
  if es.getD i false then str "none" else .str (utf16 "c" ++ (textOf (num (cnt es i))).getD [])

/-- Output item `i` is a record with the expected color, and is the input item itself when
that already had it. -/
def Good (H : Heap) (es : List Bool) (cs : List (List Nat)) (xs : List Val) (j : Nat) (y : Val) : Prop :=
  (Val.str (cs.getD j []) = expColor es j → y = xs.getD j .undef) ∧
  ∃ n : Nat, ∃ fs, y = .ref n ∧ H[n]? = some (.record fs) ∧ fs.lookup "color" = some (expColor es j)

theorem Good.set {H : Heap} {es cs xs j y} {c : Nat} {a o} (hc : H[c]? = some (.array a))
    (g : Good H es cs xs j y) : Good (H.set c o) es cs xs j y := by
  obtain ⟨hid, n, fs, rfl, hn, hcol⟩ := g
  have : c ≠ n := by rintro rfl; rw [hc] at hn; cases hn
  exact ⟨hid, n, fs, rfl, by rw [List.getElem?_set_ne this]; exact hn, hcol⟩

theorem Good.append {H : Heap} {es cs xs j y os} (g : Good H es cs xs j y) : Good (H ++ os) es cs xs j y := by
  obtain ⟨hid, n, fs, rfl, hn, hcol⟩ := g
  exact ⟨hid, n, fs, rfl, get_append hn, hcol⟩

syntax "dgood" : tactic
macro_rules
  | `(tactic| dgood) => `(tactic| first
    | assumption
    | (refine Good.append ?_; dgood)
    | (refine Good.set ?_ ?_ <;> first | dheap | dgood))

theorem textOf_num {k : Int} (h1 : -9007199254740991 ≤ k) (h2 : k ≤ 9007199254740991) :
    textOf (num k) = some (Js.numStr ⟨k, h1, h2⟩) := by
  have e : asNum (num k) = some ⟨k, h1, h2⟩ := asNum_isInt (Or.inl rfl)
  rw [show textOf (num k) = (asNum (num k)).map Js.numStr from rfl, e]
  rfl

/-- `colorIndexes` colors every item as its comment says, keeps the items that already had
the right color, and copies the others. -/
theorem colorIndexes_spec {h : Heap} {l xs} {es : List Bool} {cs : List (List Nat)}
    (hl : h[l]? = some (.array xs)) (hlen : xs.length ≤ 9007199254740990) (hes : es.length = xs.length)
    (hx : ∀ i < xs.length, ∃ m : Nat, ∃ fs, xs.getD i .undef = .ref m ∧ h[m]? = some (.record fs) ∧
      fs.lookup "empty" = some (.bool (es.getD i false)) ∧ fs.lookup "color" = some (.str (cs.getD i []))) :
    Spec (Fixtures.colorIndexes (.ref l)) h fun r h' =>
      ∃ n ys, r = .ref n ∧ h'[n]? = some (.array ys) ∧ ys.length = xs.length ∧
        ∀ j < xs.length, Good h' es cs xs j (ys.getD j .undef) := by
  unfold Fixtures.colorIndexes
  simp only [spec_bind, spec_cell, List.length_append, List.length_singleton]
  refine jsMap_spec (xs := xs) (fun i out H => out.length = i ∧ h.length + 2 ≤ H.length ∧ Frame h H ∧
      H[h.length]? = some (.array [num (cnt es i)]) ∧
      (∃ b, H[h.length + 1]? = some (.array [.bool b]) ∧ (b = false → out = xs.take i)) ∧
      ∀ j < i, Good H es cs xs j (out.getD j .undef)) ?_ ?_ ?_ ?_
  · refine ⟨rfl, by simp, Frame.refl.append (by simp) |>.append (by simp), ?_, ⟨false, ?_, fun _ => rfl⟩,
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    · rw [List.append_assoc, List.getElem?_append_right (le_refl _)]; simp [cnt]
    · rw [List.getElem?_append_right (by simp)]; simp
  · rintro i out H ⟨-, -, hf, -⟩; exact hf.get hl
  · rintro i out H hi ⟨ho, hle, hf, hk, ⟨b, hb, hbt⟩, hg⟩
    obtain ⟨m, fs, hxe, hm, he, hc⟩ := hx i hi
    have hml : m < h.length := heap_lt hm
    have hm' := hf.get hm
    have e : xs[i] = .ref m := by rw [← List.getD_eq_getElem _ .undef hi]; exact hxe
    have hesi : i < es.length := hes ▸ hi
    have hcnt := cnt_succ hesi
    have hcb : (cnt es i : Int) ≤ 9007199254740990 := by
      have : cnt es i ≤ i := by unfold cnt; exact (List.length_filter_le _ _).trans (by simp)
      omega
    have htake : out = xs.take i → out ++ [.ref m] = xs.take (i + 1) := fun h0 => by
      rw [List.take_succ_eq_append_getElem hi, e, h0]
    have hnew : ∀ y, (out ++ [y]).getD i .undef = y := fun y => by simp [List.getD_eq_getElem?_getD, ho]
    have hold : ∀ y j, j < i → (out ++ [y]).getD j .undef = out.getD j .undef := fun y j hj => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (ho ▸ hj)]
    rw [e]
    by_cases hE : es.getD i false
    · by_cases hC : cs.getD i [] = utf16 "none"
      · dsteps [str_eq, hE, hC]
        all_goals refine ⟨by simp [ho], by first | dlen | trivial, by first | dframe | trivial, ?_, ?_, fun j hj => ?_⟩
        · first
            | (simp only [Nat.add_zero]; done)
            | (simp only [Nat.add_zero]; dcell)
            | (simp only [Nat.cast_add, Nat.cast_one]; dcell)
        · first
            | exact ⟨b, rfl, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨b, by dcell, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨true, by dcell, fun h => absurd h (by simp)⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · rw [hold _ _ hj]; have := hg j hj; exact this
          · rw [hj, hnew]
            exact ⟨fun _ => hxe.symm, m, fs, rfl, hm', by rw [hc, hC]; simp only [expColor, hE, ↓reduceIte, str_eq]⟩
      · dsteps [str_eq, hE, hC]
        all_goals refine ⟨by simp [ho], by first | dlen | trivial, by first | dframe | trivial, ?_, ?_, fun j hj => ?_⟩
        · first
            | (simp only [Nat.add_zero]; done)
            | (simp only [Nat.add_zero]; dcell)
            | (simp only [Nat.cast_add, Nat.cast_one]; dcell)
        · first
            | exact ⟨b, rfl, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨b, by dcell, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨true, by dcell, fun h => absurd h (by simp)⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · rw [hold _ _ hj]; have := hg j hj; exact (this.set hb).append
          · rw [hj, hnew]
            refine ⟨fun hid => absurd (by simpa only [expColor, hE, ↓reduceIte, str_eq, Val.str.injEq] using hid) hC, _, _, rfl,
              List.getElem?_concat_length .., by rw [lookup_mergeFields_one]; simp only [expColor, hE, ↓reduceIte, str_eq]⟩
    · by_cases hC : cs.getD i [] = utf16 "c" ++ Js.numStr ⟨cnt es i, by omega, by omega⟩ ++ utf16 ""
      · dsteps [spec_toStr_num, str_eq, hE, hC]
        all_goals refine ⟨by simp [ho], by first | dlen | trivial, by first | dframe | trivial, ?_, ?_, fun j hj => ?_⟩
        · first
            | (simp only [Nat.add_zero]; done)
            | (simp only [Nat.add_zero]; dcell)
            | (simp only [Nat.cast_add, Nat.cast_one]; dcell)
        · first
            | exact ⟨b, rfl, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨b, by dcell, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨true, by dcell, fun h => absurd h (by simp)⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · rw [hold _ _ hj]; have := hg j hj; exact this.set hk
          · rw [hj, hnew]
            exact ⟨fun _ => hxe.symm, m, fs, rfl, get_set_ne (by omega) hm', by
              rw [hc, hC]; simp only [expColor, hE, Bool.false_eq_true, ↓reduceIte, textOf_num (k := ↑(cnt es i)) (by omega) (by omega), Option.getD_some, utf16_empty, List.append_nil]⟩
      · dsteps [spec_toStr_num, str_eq, hE, hC]
        all_goals refine ⟨by simp [ho], by first | dlen | trivial, by first | dframe | trivial, ?_, ?_, fun j hj => ?_⟩
        · first
            | (simp only [Nat.add_zero]; done)
            | (simp only [Nat.add_zero]; dcell)
            | (simp only [Nat.cast_add, Nat.cast_one]; dcell)
        · first
            | exact ⟨b, rfl, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨b, by dcell, fun hb0 => htake (hbt hb0)⟩
            | exact ⟨true, by dcell, fun h => absurd h (by simp)⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
          · rw [hold _ _ hj]; have := hg j hj; exact ((this.set hk).set (get_set_ne (by omega) hb)).append
          · rw [hj, hnew]
            refine ⟨fun hid => absurd (by rw [utf16_empty, List.append_nil]; simpa only [expColor, hE, Bool.false_eq_true, ↓reduceIte, textOf_num (k := ↑(cnt es i)) (by omega) (by omega), Option.getD_some, utf16_empty, List.append_nil, Val.str.injEq] using hid) hC,
              _, _, rfl, List.getElem?_concat_length .., by rw [lookup_mergeFields_one]; simp only [expColor, hE, Bool.false_eq_true, ↓reduceIte, textOf_num (k := ↑(cnt es i)) (by omega) (by omega), Option.getD_some, utf16_empty, List.append_nil]⟩
  · rintro out H ⟨ho, hle, hf, -, ⟨b, hb, hbt⟩, hg⟩
    rw [spec_get (by rw [List.getElem?_append_left (by omega)]; exact hb)]
    cases b <;> simp only [truthy_bool, ite_true, ite_false, Bool.false_eq_true, spec_pure]
    · have hxs := hbt rfl
      rw [List.take_of_length_le (by omega)] at hxs
      subst hxs
      refine ⟨l, out, rfl, by rw [List.getElem?_append_left (heap_lt (hf.get hl))]; exact hf.get hl, rfl, ?_⟩
      intro j hj; exact (hg j hj).append
    · exact ⟨H.length, out, rfl, by simp, ho, fun j hj => (hg j (ho ▸ hj)).append⟩

/-- `sumAmounts` returns the sum, when every partial sum is safe, and leaves the heap alone. -/
theorem sumAmounts_sum {h : Heap} {l} {ns : List Int} (hl : h[l]? = some (.array (ns.map num)))
    (hs : ∀ i ≤ ns.length, -9007199254740991 ≤ (ns.take i).sum ∧ (ns.take i).sum ≤ 9007199254740991) :
    Spec (Bank.sumAmounts (.ref l)) h fun r h' => r = num ns.sum ∧ h' = h := by
  unfold Bank.sumAmounts
  simp only [spec_bind]
  rw [spec_eq (iter_arr hl)]
  refine spec_forIn hl (spec_mono (forLoop_spec (xs := ns.map num)
    (fun i t h' => h' = h ∧ t = num (ns.take i).sum) (fun _ _ _ hI => hI.1 ▸ hl) ?_ _ 0 _ h (by simp) ⟨rfl, by simp⟩) ?_)
  · rintro i t h' hi ⟨rfl, rfl⟩
    simp only [List.length_map] at hi
    simp only [List.getElem_map, spec_bind]
    rw [bin_add_num (by have := hs (i + 1) (by omega); rw [List.take_succ_eq_append_getElem hi, List.sum_append] at this; simpa using this)]
    simp only [spec_pure, spec_bind]
    exact ⟨_, rfl, by trivial, by rw [List.take_succ_eq_append_getElem hi, List.sum_append, List.sum_singleton]⟩
  · rintro t h' ⟨rfl, rfl⟩
    simp

/-- With array content, the message is empty exactly when every part is a text part that trims to nothing. -/
theorem messageIsEmpty_arr {h : Heap} {m fs c xs} {ts ss : List (List Nat)}
    (hm : h[m]? = some (.record fs)) (hc : fs.lookup "content" = some (.ref c))
    (hcl : h[c]? = some (.array xs)) (ht : ts.length = xs.length) (hs : ss.length = xs.length)
    (hx : ∀ (i : Nat) (hi : i < xs.length), ∃ mi : Nat, ∃ gs, xs[i] = .ref mi ∧ h[mi]? = some (.record gs) ∧
      gs.lookup "type" = some (.str (ts.getD i [])) ∧ gs.lookup "text" = some (.str (ss.getD i []))) :
    Spec (Alias.messageIsEmpty (.ref m)) h fun r h' => h' = h ∧
      r = .bool (((List.range xs.length).map fun i =>
        decide (ts.getD i [] = utf16 "text") && decide (Js.trim (ss.getD i []) = [])).all id) := by
  unfold Alias.messageIsEmpty
  dsteps [spec_isArray hcl, typeOf_ref_ne]
  rw [jsEvery_spec (qs := (List.range xs.length).map fun i =>
    decide (ts.getD i [] = utf16 "text") && decide (Js.trim (ss.getD i []) = [])) hcl (by simp) ?_]
  · exact ⟨rfl, rfl⟩
  · intro i hi
    obtain ⟨mi, gs, hxi, hmi, hty, htx⟩ := hx i hi
    rw [hxi]
    try simp only [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    apply ok_of_spec
    dsteps [hmi, hty, htx]
    rw [show str "text" = Val.str (utf16 "text") from rfl]
    dsteps [hmi, hty, htx]
    all_goals first
      | (simp only [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range, and_true]
         simp_all; done)
      | (exfalso; simp_all [nullish]; done)
