import Gen.Unknown
import Gen.Union
import Gen.Budget
import Gen.Slideshow
import Gen.Fixtures
import Gen.Bank

/-! User-level guarantees about the dynamic translations in `Gen/`. -/

open Core Dyn

/-- Whatever the value, the Group by id is a string: the value itself when it is one. -/
theorem groupByFieldId_string (v : Val) (h : Heap) :
    Spec (Unknown.parseChartGroupByFieldId v) h fun r h' =>
      h' = h ∧ (r = v ∧ typeOf v = str "string" ∨ r = str "" ∧ typeOf v ≠ str "string") := by
  unfold Unknown.parseChartGroupByFieldId
  cases v <;> simp [bin, binary, typeOf, typeName, str, truthy]

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
  unfold Bank.transfer
  simp only [spec_bind, bin_le_num, spec_pure, truthy_bool]
  by_cases h1 : amt ≤ 0
  · simp [h1]
  · simp only [h1, decide_false, Bool.false_eq_true, if_false, spec_bind]
    rw [spec_eq (field_rec hl)]
    simp only [hf, Option.getD_some, bin_gt_num, spec_pure, truthy_bool]
    by_cases h2 : a < amt
    · simp [h2]
    · simp only [h2, decide_false, Bool.false_eq_true, if_false, spec_bind]
      rw [spec_eq (field_rec hl)]
      simp only [hf, Option.getD_some]
      rw [bin_sub_num ⟨by omega, by omega⟩, spec_pure, spec_eq (field_rec hl)]
      simp only [ht, Option.getD_some]
      rw [bin_add_num ⟨by omega, by omega⟩, spec_pure]
      simp [mergeFields, record, alloc, Spec]
      exact ⟨a - amt, rfl, b + amt, rfl, by omega, by omega⟩

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
