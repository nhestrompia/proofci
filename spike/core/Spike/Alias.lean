import Spike.WP
open Core Gen

set_option exponentiation.threshold 3000

/-! Shared objects, proved directly on Core. The typed path rejects this code: both
accounts may be one object, so a write through `from` is visible through `to`. -/

attribute [simp] Gen.src_shared_moveMoney Gen.src_shared_moveMoneyStale

/-- The object at `l` is a record whose `balance` is `n`. -/
def balance (h : Heap) (l : Loc) (n : F64) : Prop := readField h (.ref l) "balance" = some (.num n)

theorem balance_record {h l n} (hb : balance h l n) :
    ∃ fs, h[l]? = some (.record fs) ∧ (fs.lookup "balance").getD .undef = .num n := by
  simp only [balance, readField] at hb
  cases hl : h[l]? with
  | none => simp [hl] at hb
  | some o =>
    cases o with
    | record fs => simp [hl] at hb; exact ⟨fs, rfl, hb⟩
    | array xs => simp [hl] at hb

theorem heap_len {h : Heap} {l o} (hl : h[l]? = some o) : l < h.length := by
  by_contra hc
  simp [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hl

@[simp] theorem heap_set_same {h : Heap} {l o} (hlen : l < h.length) : (h.set l o)[l]? = some o := by
  simp [hlen]

/-- Writing `balance` at `l` is seen at `l`. -/
theorem balance_write {h : Heap} {l fs v} (hl : h[l]? = some (.record fs)) :
    balance (h.set l (.record (("balance", .num v) :: fs.filter (·.1 != "balance")))) l v := by
  have : l < h.length := by
    by_contra hc
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hl
  simp [balance, readField, this, List.lookup]

/-- Writing at `l` leaves other objects alone. -/
theorem balance_frame {h : Heap} {l m o n} (hne : l ≠ m) (hb : balance h m n) :
    balance (h.set l o) m n := by
  have : (h.set l o)[m]? = h[m]? := by simp [List.getElem?_set, hne]
  simpa [balance, readField, this] using hb

/-- With one shared account, `moveMoney` changes nothing: money is conserved. -/
theorem moveMoney_shared {h l} {a amt : Int} (ha : balance h l (F64.ofInt a))
    (b1 : -9007199254740991 ≤ a - amt) (b2 : a - amt ≤ 9007199254740991)
    (b3 : -9007199254740991 ≤ a - amt + amt) (b4 : a - amt + amt ≤ 9007199254740991) :
    WpRun prog src_shared_moveMoney [.ref l, .ref l, .num (F64.ofInt amt)] h fun _ s => balance s.heap l (F64.ofInt a) := by
  obtain ⟨fs, hl, hv⟩ := balance_record ha
  have hlen := heap_len hl
  have hl2 : h[l] = .record fs := by simpa [hlen] using hl
  apply wprun_void
  simp only [src_shared_moveMoney]
  core_run
  all_goals simp (disch := omega) [balance, readField, List.lookup, hlen]
  all_goals try (congr 2; omega)

/-- With two accounts, the amount moves from one to the other. -/
theorem moveMoney_separate {h l m} {a b amt : Int} (hne : l ≠ m)
    (ha : balance h l (F64.ofInt a)) (hb : balance h m (F64.ofInt b))
    (b1 : -9007199254740991 ≤ a - amt) (b2 : a - amt ≤ 9007199254740991)
    (b3 : -9007199254740991 ≤ b + amt) (b4 : b + amt ≤ 9007199254740991) :
    WpRun prog src_shared_moveMoney [.ref l, .ref m, .num (F64.ofInt amt)] h fun _ s =>
      balance s.heap l (F64.ofInt (a - amt)) ∧ balance s.heap m (F64.ofInt (b + amt)) := by
  obtain ⟨fs, hl, hv⟩ := balance_record ha
  obtain ⟨gs, hm, hw⟩ := balance_record hb
  have hlen := heap_len hl
  have hlen' := heap_len hm
  have hl2 : h[l] = .record fs := by simpa [hlen] using hl
  have hm2 : h[m] = .record gs := by simpa [hlen'] using hm
  have hne' : ¬ m = l := fun e => hne e.symm
  apply wprun_void
  simp only [src_shared_moveMoney]
  core_run
  all_goals simp [balance, readField, List.lookup, hlen, hlen', hne, hne', List.getElem?_set, List.getElem_set, *]

/-- The version that reads both balances first looks the same, but with one shared
account it creates money. Core sees that; a type-directed model never gets to ask. -/
theorem moveMoneyStale_shared_creates_money {h l} {a amt : Int} (ha : balance h l (F64.ofInt a))
    (b1 : -9007199254740991 ≤ a - amt) (b2 : a - amt ≤ 9007199254740991)
    (b3 : -9007199254740991 ≤ a + amt) (b4 : a + amt ≤ 9007199254740991) :
    WpRun prog src_shared_moveMoneyStale [.ref l, .ref l, .num (F64.ofInt amt)] h fun _ s => balance s.heap l (F64.ofInt (a + amt)) := by
  obtain ⟨fs, hl, hv⟩ := balance_record ha
  have hlen := heap_len hl
  have hl2 : h[l] = .record fs := by simpa [hlen] using hl
  apply wprun_void
  simp only [src_shared_moveMoneyStale]
  core_run
  all_goals simp [balance, readField, List.lookup, hlen]

/-- With fractions, `moveMoney` on one shared account doesn't conserve money: Core
computes the rounding that the safe-integer model refuses to represent. -/
theorem fractions_lose_money :
    ((F64.ofBits 0x3F847AE147AE147B).sub (F64.ofBits 0x3F9EB851EB851EB8)).add (F64.ofBits 0x3F9EB851EB851EB8)
      ≠ F64.ofBits 0x3F847AE147AE147B := by decide +kernel

#print axioms fractions_lose_money
#print axioms moveMoney_shared
#print axioms moveMoney_separate
#print axioms moveMoneyStale_shared_creates_money
