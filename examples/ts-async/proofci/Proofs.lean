import TsAsync
open Aeneas Aeneas.Std Result

theorem canViewLink_anonymous (auth : src.lib.types.Auth) (linkId : Js.Str)
    (anonymous : auth.user = none)
    (nolink : auth.shareToken.bind (·.linkId) ≠ some linkId)
    (nosite : auth.shareToken.bind (·.websiteId) ≠ some linkId)
    (nolinks : (auth.shareToken.bind (·.linkIds)).map (fun xs => Js.includes xs linkId) ≠ some true) :
    ∀ (o : Proofci.Effects.world.Oracle) (hist : Proofci.Effects.world.Hist),
      src.permissions.link.canViewLink auth linkId o hist = ok (Js.Settled.fulfilled false, hist) := by
  intro o hist
  unfold src.permissions.link.canViewLink
  cases hl : auth.shareToken.bind (·.linkIds) with
  | none => simp [anonymous, nolink, nosite, Js.truthyBool, hl]
  | some xs =>
    have hx : Js.includes xs linkId = false := by
      cases h : Js.includes xs linkId
      · rfl
      · exact absurd (by simp [hl, h]) nolinks
    simp [anonymous, nolink, nosite, Js.truthyBool, hl, hx]

theorem canViewLink_true_sound (auth : src.lib.types.Auth) (linkId : Js.Str) :
    ∀ (o : Proofci.Effects.world.Oracle) (hist : Proofci.Effects.world.Hist),
      Js.Eff.Spec (src.permissions.link.canViewLink auth linkId) o hist fun r hist' =>
      r = Js.Settled.fulfilled true →
      (∃ u, auth.user = some u ∧ u.isAdmin = true) ∨
      auth.shareToken.bind (·.linkId) = some linkId ∨ auth.shareToken.bind (·.websiteId) = some linkId ∨
      (auth.shareToken.bind (·.linkIds)).map (fun xs => Js.includes xs linkId) = some true ∨
      (∃ u l, auth.user = some u ∧
        (⟨Proofci.Effects.Op.getLink, linkId, Js.Answer.value (some l)⟩ : Proofci.Effects.world.Event) ∈ hist' ∧
        (l.userId = some u.id ∨ ∃ t tu, l.teamId = some t ∧
          (⟨Proofci.Effects.Op.getTeamUser, (t, u.id), Js.Answer.value (some tu)⟩ : Proofci.Effects.world.Event) ∈ hist')) := by
  intro o hist r hist' h hr
  subst hr
  unfold src.permissions.link.canViewLink at h
  -- The two database questions at the end: whatever came back, `true` means the link belongs
  -- to the user or the user is in the link's team, and both answers are in the history.
  have tail : ∀ (uid : Js.Str),
      ((do
        let link ← Proofci.Effects.call Proofci.Effects.Op.getLink linkId
        match link with
        | none => (liftM (ok false) : Proofci.Effects.Eff Bool)
        | some link_1 =>
          if Js.truthyStr link_1.userId = true then do
            let tmp5 ← liftM (Js.unwrap link_1.userId)
            liftM (ok (decide (uid = tmp5)))
          else
            if Js.truthyStr link_1.teamId = true then do
              let tmp6 ← liftM (Js.unwrap link_1.teamId)
              let teamUser ← Proofci.Effects.call Proofci.Effects.Op.getTeamUser (tmp6, uid)
              liftM (ok !decide (teamUser = none))
            else liftM (ok false)) : Proofci.Effects.Eff Bool) o hist = ok (Js.Settled.fulfilled true, hist') →
      ∃ l, (⟨Proofci.Effects.Op.getLink, linkId, Js.Answer.value (some l)⟩ : Proofci.Effects.world.Event) ∈ hist' ∧
        (l.userId = some uid ∨ ∃ t tu, l.teamId = some t ∧
          (⟨Proofci.Effects.Op.getTeamUser, (t, uid), Js.Answer.value (some tu)⟩ : Proofci.Effects.world.Event) ∈ hist') := by
    intro uid ht
    simp only [Proofci.Effects.call, Js.Eff.bind_run, Js.Eff.call_run] at ht
    rcases ha : o Proofci.Effects.Op.getLink linkId hist with v | e <;> simp [ha] at ht
    cases v with
    | none => simp at ht
    | some l =>
      simp only at ht
      by_cases hu : Js.truthyStr l.userId = true
      · simp only [hu, ↓reduceIte] at ht
        obtain ⟨s, hu1⟩ : ∃ s, l.userId = some s := by
          cases hq : l.userId
          · simp [Js.truthyStr, hq] at hu
          · exact ⟨_, rfl⟩
        simp [Js.unwrap, hu1] at ht
        obtain ⟨hid, hh⟩ := ht
        subst hh
        exact ⟨l, by simp, Or.inl (by rw [hu1, hid])⟩
      · simp only [hu] at ht
        by_cases hteam : Js.truthyStr l.teamId = true
        · simp only [hteam, ↓reduceIte] at ht
          obtain ⟨t, ht1⟩ : ∃ t, l.teamId = some t := by
            cases hq : l.teamId
            · simp [Js.truthyStr, hq] at hteam
            · exact ⟨_, rfl⟩
          simp [Js.unwrap, ht1, Js.Eff.bind_run, Js.Eff.call_run] at ht
          rcases hb : o Proofci.Effects.Op.getTeamUser (t, uid)
              (hist ++ [{ op := Proofci.Effects.Op.getLink, arg := linkId, ans := Js.Answer.value (some l) }]) with tv | err <;>
            simp [hb] at ht
          cases tv with
          | none => simp at ht
          | some tu =>
            simp at ht
            subst ht
            exact ⟨l, by simp, Or.inr ⟨t, tu, ht1, by simp⟩⟩
        · simp only [hteam] at ht
          simp at ht
  rcases hu : auth.user with _ | u <;> simp [hu, Js.truthyBool] at h
  · by_cases ht : (auth.shareToken.bind fun item => item.linkId) = some linkId ∨
        (auth.shareToken.bind fun item => item.websiteId) = some linkId
    · rcases ht with h1 | h2
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
    · simp only [ht, ↓reduceIte] at h
      cases hl : auth.shareToken.bind (·.linkIds) with
      | none => simp [hl] at h
      | some xs =>
        by_cases hx : Js.includes xs linkId = true
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [hl, hx]))))
        · simp [hl, hx] at h
  · by_cases ha : u.isAdmin = true
    · exact Or.inl ⟨u, rfl, ha⟩
    · simp only [ha] at h
      by_cases ht : (auth.shareToken.bind fun item => item.linkId) = some linkId ∨
          (auth.shareToken.bind fun item => item.websiteId) = some linkId
      · rcases ht with h1 | h2
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inl h2))
      · simp only [ht, ↓reduceIte] at h
        cases hl : auth.shareToken.bind (·.linkIds) with
        | none =>
          simp [hl] at h
          obtain ⟨l, hm, hr⟩ := tail u.id h
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨u, l, rfl, hm, hr⟩)))
        | some xs =>
          by_cases hx : Js.includes xs linkId = true
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [hl, hx]))))
          · simp [hl, hx] at h
            obtain ⟨l, hm, hr⟩ := tail u.id h
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨u, l, rfl, hm, hr⟩)))
