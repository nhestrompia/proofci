# `async` code: who may view a link

`src/permissions/link.ts` is `canViewLink` from [umami](https://github.com/umami-software/umami)
at `559e3c6` (MIT, Copyright (c) 2022 Umami Software, Inc.; the licence is in
`LICENSE-umami.md`). The one change is that the return type is written as `Promise<boolean>`,
which ProofCI requires of every function a guarantee reaches. In umami `getLink` and
`getTeamUser` are Prisma queries; here `src/queries/prisma` has stand-in bodies, because the
policy lists both under `effects` and ProofCI never reads them.

## What is proved

- **An anonymous visitor is refused and nothing is looked up.** With no user and no share
  token that names the link, the result is `false` and the history of database calls is
  unchanged. This holds for every database.
- **`true` is only returned for a reason.** The user is an admin, or a share token names the
  link, or the history shows that the database was asked for the link and answered that it
  belongs to the user, or that the user is in its team. Again for every database, including
  one that rejects.

Neither proof assumes anything about the database. The report lists the two effects, and says
that the proof relied on `user` not being changed by the caller while a lookup is pending,
because the function reads `user.id` after the first `await`.
