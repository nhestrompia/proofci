import TsAsync
open Aeneas Aeneas.Std Result

/-! `canViewLink` is `async`: it asks the database (`getLink`, `getTeamUser`), and the database
may answer anything, or reject. The statements below are about every answer it could give.
`o` is the database, an arbitrary function from the question and everything asked so far to
an answer, and `hist` is that record of questions. Nothing is assumed about `o`. -/

/-- A visitor with no account and no matching share token is refused, and the database is
never asked: the history is exactly what it was. -/
theorem canViewLink_anonymous (auth : src.lib.types.Auth) (linkId : Js.Str)
    (anonymous : auth.user = none)
    (nolink : auth.shareToken.bind (·.linkId) ≠ some linkId)
    (nosite : auth.shareToken.bind (·.websiteId) ≠ some linkId)
    (nolinks : (auth.shareToken.bind (·.linkIds)).map (fun xs => Js.includes xs linkId) ≠ some true) :
    ∀ (o : Proofci.Effects.world.Oracle) (hist : Proofci.Effects.world.Hist),
      src.permissions.link.canViewLink auth linkId o hist = ok (Js.Settled.fulfilled false, hist) := by
  sorry

/-- `true` is only ever returned for a reason: the user is an admin, or a share token names the
link, or the database was asked for the link and said it belongs to the user or to a team the
database then said the user is in. The reason is visible in the history. -/
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
  sorry
