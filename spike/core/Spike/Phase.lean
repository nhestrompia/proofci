import Spike.Enc
import Spike.Gen
import Spike.View
open Core Aeneas Aeneas.Std Result

namespace Core

theorem bind_ok_inv {α β : Type} {x : Result α} {f : α → Result β} {r : β} (h : Aeneas.Std.bind x f = ok r) :
    ∃ a, x = ok a ∧ f a = ok r := by
  revert h
  refine Result.cases (motive := fun x => Aeneas.Std.bind x f = ok r → ∃ a, x = ok a ∧ f a = ok r) x ?_ ?_ ?_
  · intro a h; exact ⟨a, rfl, by simpa using h⟩
  · intro i k h; simp at h
  · intro h; simp at h

/-- The loop rule: an Aeneas `loop` over a list, against `for (const x of xs)`. This one
lemma is shared by every array loop that leaves the heap alone. -/
theorem sim_loop {T σ β : Type} [Enc T] {p x l vs body h}
    (B : List T × σ → Result (ControlFlow (List T × σ) β))
    (R : σ → St → Prop) (Q : β → St → Prop)
    (hheap : ∀ a s, R a s → s.heap = h)
    (harr : h[l]? = some (.array vs))
    (hnil : ∀ a s y, R a s → B ([], a) = ok y → ∃ r, y = .done r ∧ Q r s)
    (hcons : ∀ q rest a s item y, R a s → Enc.enc h q item → B (q :: rest, a) = ok y →
      (∃ a', y = .cont (rest, a') ∧ ∃ s', ExecsL p { s with env := s.env.put x item } body .normal s' ∧ R a' s') ∨
      (∃ r, y = .done r ∧ ∃ s', ExecsL p { s with env := s.env.put x item } body .brk s' ∧ Q r s')) :
    ∀ (rest : List T) i a s r, List.Forall₂ (Enc.enc h) rest (vs.drop i) → R a s → loop B (rest, a) = ok r →
      ∃ s', Iterates p x (.ref l) i body s .normal s' ∧ Q r s' := by
  intro rest
  induction rest with
  | nil =>
    intro i a s r hf hR hr
    have hd : vs.drop i = [] := List.forall₂_nil_left_iff.mp hf
    have hi : vs[i]? = none := by
      have : vs.length ≤ i := List.drop_eq_nil_iff.mp hd
      simp [this]
    have hh := hheap a s hR
    unfold loop at hr
    obtain ⟨y, hb, hrest⟩ := bind_ok_inv hr
    obtain ⟨r', rfl, hq⟩ := hnil a s y hR hb
    have : r' = r := by simpa using hrest
    subst this
    exact ⟨s, Iterates.done (xs := vs) (by rw [hh]; exact harr) hi, hq⟩
  | cons q rest ih =>
    intro i a s r hf hR hr
    obtain ⟨item, tail, hitem, htail, hdrop⟩ := List.forall₂_cons_left_iff.mp hf
    have hi : vs[i]? = some item := by
      have : (vs.drop i)[0]? = some item := by rw [hdrop]; rfl
      simpa using this
    have hd' : vs.drop (i + 1) = tail := by
      have := congrArg List.tail hdrop
      simpa [List.tail_drop] using this
    have hh := hheap a s hR
    unfold loop at hr
    obtain ⟨y, hb, hrest⟩ := bind_ok_inv hr
    rcases hcons q rest a s item y hR hitem hb with ⟨a', rfl, s', he, hR'⟩ | ⟨r', rfl, s', he, hq⟩
    · obtain ⟨s₂, hit, hq⟩ := ih (i + 1) a' s' r (hd' ▸ htail) hR' (by simpa using hrest)
      exact ⟨s₂, Iterates.next (xs := vs) (by rw [hh]; exact harr) hi he hit, hq⟩
    · have : r' = r := by simpa using hrest
      subst this
      exact ⟨s', Iterates.brk (xs := vs) (by rw [hh]; exact harr) hi he, hq⟩

/-- `sim_loop` with the shallow loop first, so that its body is known to later arguments. -/
theorem sim_loop' {T σ β : Type} [Enc T] {p x l vs body h}
    {B : List T × σ → Result (ControlFlow (List T × σ) β)} {xs i a s r}
    (hl : loop B (xs, a) = ok r) (hf : List.Forall₂ (Enc.enc h) xs (vs.drop i))
    (R : σ → St → Prop) (Q : β → St → Prop) (hR : R a s)
    (hheap : ∀ a s, R a s → s.heap = h)
    (harr : h[l]? = some (.array vs))
    (hnil : ∀ a s y, R a s → B ([], a) = ok y → ∃ r, y = .done r ∧ Q r s)
    (hcons : ∀ q rest a s item y, R a s → Enc.enc h q item → B (q :: rest, a) = ok y →
      (∃ a', y = .cont (rest, a') ∧ ∃ s', ExecsL p { s with env := s.env.put x item } body .normal s' ∧ R a' s') ∨
      (∃ r, y = .done r ∧ ∃ s', ExecsL p { s with env := s.env.put x item } body .brk s' ∧ Q r s')) :
    ∃ s', Iterates p x (.ref l) i body s .normal s' ∧ Q r s' :=
  sim_loop B R Q hheap harr hnil hcons xs i a s r hf hR hl

end Core
