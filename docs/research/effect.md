# Supporting `effect` (the Effect library) in the TypeScript check

The owner: "yes i think we should support effect since its popular now with agents".

This note sizes an Effect subset ProofCI could accept, measured against a real
consumer, and maps each construct of the subset onto the model `async` code
already uses (`ProofciAsync.lean` / `CoreAsync.lean` / `typescript/translate.mjs`).
It changes no code; it is the design an implementation PR would follow.

Measured tree: `pingdotgg/t3code` @ `700a4644` (Effect **4.1.5**, pinned via the
pnpm catalog). Scope: `apps/server`, all of `packages/*`, `apps/web` — 3,486
non-test `.ts/.tsx` files outside `.repos/` (the vendored Effect copies),
measured by `docs/research/effect-survey.mjs` on the TypeScript compiler AST,
not grep. Everything the survey reports is syntactic; "Effect-returning" below
means a return type mentioning `Effect`, or a body that builds an Effect value.

## 1. What t3code uses

1,619 of 3,486 files import from `effect`/`effect/*`. 14,968 exported
functions/consts were classified:

| | count |
|---|---|
| exported functions returning an Effect | 1,304 |
| exported functions not returning an Effect | 13,664 |
| Effect-returning exports using **only** the core subset below | **510 (39%)** |

(The 1,304 counts free functions and `export const f = Effect.fn(...)(...)`;
methods of exported `Context.Service` classes are not counted, so the true
number of Effect entry points is larger.)

Construct frequency (call sites):

| construct | uses | notes |
|---|---|---|
| `yield*` inside `Effect.gen` | 19,675 | in 2,106 `Effect.gen` bodies; `.pipe(...)` chains add 10,969 |
| `Effect.fn` / `Effect.fnUntraced` | 3,906 / 841 | the dominant way functions are declared |
| `Schema.*` (Struct/Union/optional/Literal/…) | ~35,000 total | `Schema.Struct` alone 7,393; Schema is the data layer |
| `Effect.mapError` / `map` / `flatMap` / `andThen` | 2,126 / 1,634 / 1,466 / 764 | `pipe` composition |
| `Effect.succeed` / `fail` / `sync` | 1,438 / 821 / 653 | |
| `Schema.TaggedError` (class extends) | 1,057 | the typed-error convention |
| `Effect.orElseSucceed` / `orElse*` | ~922 | |
| `Ref.*` (`make`/`get`/`set`/`update`/`modify`) | ~2,146 | in-service state — out |
| `Effect.provideService` / `service` / `provide*` | ~960 | service access (the `R` channel) |
| `Context.Service` | 322 | v4 idiom; `Context.Tag` essentially unused (0), `Effect.Service` 0 |
| `Effect.catch*` (`catch`/`catchTag(s)`/`catchIf`/`catchCause*`) | ~1,202 | `catchCause` alone 252 — needs `Cause` |
| `Effect.all` / `forEach` | 332 / 545 | mostly sequential aggregation |
| `Effect.try` / `tryPromise` / `promise` | 104 / 182 / 111 | |
| `Stream.*` | ~1,085 | out |
| `Scope`/`acquireRelease`/`ensuring`/`scoped`/`addFinalizer` | ~420 | out |
| `Schedule`/`retry`/`repeat` | ~140 | out |
| fibers (`fork*`/`race`/`Fiber.*`/`uninterruptible`/`timeout`) | ~700 | out |
| `Deferred`/`Queue`/`Semaphore`/`PubSub`/`SubscriptionRef` | ~1,450 | out |
| `Layer.*` | ~1,440 | wiring — stays outside the verified function |
| `Option.*` (`isSome`/`none`/`some`/`getOr*`) | ~1,900 | yieldable adapter + pure ops |
| `Result`/`Either`/`Match`/`Data.*` | ~350 / 0 / 2 / 9 | v4 renamed Either→Result; Match and Data.TaggedError are rare |
| `Effect.orDie`/`die`/`dieMessage` | ~80 | defects — trivial to model |
| `Effect.log*`/`annotate*`/`withSpan` | ~1,100 | tracing/logging — can be unmodelled |
| `Schema.decode*`/`encode*` | ~900 | boundary validation |
| `Effect.runPromise`/`runFork`/`runSync`/`exit`/`scoped` | ~120 | at the app edge, not inside translated code |

## 2. The smallest subset that fits the existing model

`Effect.Effect<A, E, R>` is already the shape `Eff W α` has: a sequential
computation that can end in a value `A`, a typed failure `E`, or a defect, and
that asks the outside world (`R`, services) questions. The async model's
**oracle + history** covers `R` exactly: a `Context.Service` method is a
`method:` effect entry, the service tag is the handle's owner type.

### Syntax surface

| Effect | Lean view | guarantee reads as |
|---|---|---|
| `Effect.gen(function*(){…})` body | the body is `do` notation over `Eff W`; `yield* e` is `← e` (`Std.bind`) | `f args o hist = ok (.succeeded a, hist')` or `Js.Eff.Spec` |
| `Effect.fn("n")(function* …)` / `fnUntraced` | a plain function returning `Eff W`; the name/span is erased | same |
| `yield* serviceTag` (`yield* ServerConfig`) | `call .services .serverConfig` — one world op returning the service handle/record | the service asked is an event in `hist'` |
| `x.pipe(f, g)`, `pipe(x, f, g)` | parsed sugar: `g(f(x))`; `.pipe` on a value is the same | no semantic content |
| `Effect.succeed(v)` | `pure v` | |
| `Effect.fail(e)` / `yield* new TaggedError(…)` | a *typed failure* outcome (see below) | `failed` with tag + fields |
| `Effect.sync` / `try{…,catch}` | lift of a `Result`; `try`'s `catch` maps the thrown value | |
| `Effect.tryPromise` / `promise` | an `effects` entry: one oracle call; rejection → `catch` maps to a typed failure | identical to an `await`ed outside call today |
| `map`/`flatMap`/`andThen`/`tap`/`tapError`/`as`/`zip*` | `bind`/`map` compositions | |
| `catch`/`catchTag`/`catchTags`/`catchIf`/`orElse`/`orElseSucceed`/`orElseFail`/`mapError` | `tryCatch` on the typed channel with a `_tag`/predicate match | recovery is in the proof |
| `all` (tuple/array) / `forEach` | sequential `bind` chain / `Eff.loop` | `hist'` has every call in order |
| `suspend` | thunk — forced at `bind` time | |
| `orDie`/`die`/`dieMessage`/`filterOrDie` | defect ⇒ `Result.fail` (leaves the model) | defects stay "not covered" |
| `log*`/`annotate*`/`withSpan` | erased | trusted: tracing never changes the result |
| `service`/`provideService` inside a translated function | a lookup on the environment argument; `provide*` at module edge is refused | |
| `Option`/`Result` yielded or matched | `Option.none`/`Option.some`/`Result.*` values; `yield* Option` fails with `NoSuchElementError` (a typed failure) | |

### The typed error channel

`Js.Settled α` is `fulfilled a | rejected e` where `rejected` is an `Error`-like
exception. Effect splits outcomes differently: `Exit<A,E>` is `succeed | fail e
| die defect`. The honest mapping adds one case rather than reusing `rejected`:

```lean
inductive Settled (α : Type) (ε : Type) where
  | fulfilled (a : α)
  | failed    (e : ε)      -- Effect.fail / a yielded TaggedError
  | rejected  (d : Exn)    -- defect: die, a thrown JS error, interruption
```

`failed` is an outcome a guarantee can name (`r = .failed ⟨"MediaFileStatError", …⟩`);
`rejected`/defect stays rare and mostly unprovable-by-design, matching today's
"leaving the model". `tryCatch` on `failed` becomes the body of
`catch*`/`orElse*`. `Schema.TaggedError` classes become one inductive per error
hierarchy, discriminated on `_tag` (verified: `Schema.TaggedError` in
effect@4.1.5 builds a class whose instances are yieldable and carry `_tag` +
schema fields — `packages/effect` `Schema.d.ts`; t3code uses it 1,057×).

### Services = the `effects:` policy

A `Context.Service` class (`ServerConfig.ServerConfig`, `Digest.Digest`,
`ServerSecretStore.ServerSecretStore` — 322 in the tree) is declared to ProofCI
the way an outside call is today:

```yaml
effects:
  - id: serverConfig
    service: src/config.ts::ServerConfig      # a Context.Service tag
  - id: secretsCreate
    method: ServerSecretStore#create
    signature: "(name: string, value: Uint8Array): Effect<void, SecretStoreError>"
    kind: read
```

`yield* ServerConfig` asks the oracle for the service record;
`service.method(args)` inside `gen` is a `method` op whose `Res` is the
Effect's success type and whose rejection is the declared `E`. `Layer.*`,
`ManagedRuntime`, `run*` stay at the application edge: they are *provided*, not
translated — the world an `Eff` proof quantifies over is exactly "every way the
layers could be built". That is the same story `effects:` already tells, and the
policy stays protected: a PR can't add a service or weaken a signature itself.

### Running it under Node (the comparison)

Today: scripted stand-ins answer the oracle, the model must end as Node did and
the history must be the calls the stand-ins saw. For Effect the harness is one
adapter: run the program with `Effect.runPromiseExit` (or `runSyncExit` when no
`tryPromise` is involved — both exist in 4.1.5), providing each declared service
by `Layer.succeed(Tag, stub)` where the stub records the op and returns the
scripted answer. Node's `Exit.succeed value` ↔ the model's `.fulfilled`;
`Exit.fail err` ↔ `.failed` compared on `_tag` + fields; `Exit.die` is "left the
model". The trace check is unchanged.

### The bridge theorem

`Effect.gen` desugars to a `bind` chain; `CoreAsync.AStmt` already has
`await`/`tryCatch`/`throw`. Adding `failTagged` (a `throw` carrying a data
value) and `catchTag` (a `tryCatch` whose handler runs only on a matching
`_tag`) is a small, additive `AStmt` change, and the `ASim.lean` proof rules
transfer almost verbatim (`bind_call`, `try_bind_call`, `call_hist` already
split on the oracle's answer). Loops inside `gen` bodies inherit the same
limits loops have in `async` today (no bridge yet ⇒ "tested, not proved").

**What becomes trusted** (the honest list a reviewer signs off on):

1. `yield*`/`gen`/`fn` semantics = the `bind` chain Effect's adapter performs
   (verified in `effect@4.1.5` `internal/core`/`tracer` — `gen` is an adapter
   over `flatMap`; `fn` adds a span we erase).
2. Yieldables: an `Effect`, an `Option`/`Result`/`Either`, or a `TaggedError`
   instance may be yielded; the last fails. Anything else is refused.
3. Effect's fiber runtime executes the program's steps sequentially — the same
   standing assumption as `async`, plus: nothing else runs between two `yield*`s
   of one fiber (true of a single fiber's happy path).
4. `catchTag`/`catchIf` dispatch on `_tag`/predicate as declared; `_tag` strings
   are stable identifiers (they're the second argument to `Schema.TaggedError`).
5. Erased `log*`/`annotate*`/`withSpan` don't change the result (they can't —
   they're `tap` on the trace context).
6. Services: the declared `signature`/`narrowed` is what the real layer answers;
   the tag's identity is nominal (the `Context.Tag` key).
7. Interruption: a guarantee holds only for runs that complete uninterrupted —
   `runPromiseExit` can return a `die`/`interrupt` `Exit` our model can't
   produce, which is safe: it just means that run isn't covered.

### Refused, and the hint an agent gets

| refused construct | reason → `How to fix:` hint |
|---|---|
| `Stream.*`, `Effect.acquireRelease`, `ensuring`, `scoped`, `addFinalizer` | "Effect streams and scoped resources aren't supported" → run the stream to a value (`Stream.runCollect`) in an `effects` entry, or keep the resource inside one service call |
| `Ref`/`Deferred`/`Queue`/`Semaphore`/`PubSub`/`SubscriptionRef`/`Atom` | "Effect concurrency/state primitives aren't supported" → keep the state inside a service behind a listed `method` effect, so the oracle owns it |
| `fork`/`race`/`timeout`/`sleep`/`retry`/`repeat`/`Schedule`/`uninterruptible` | "concurrent and timed effects aren't supported" → move the retry/timeout into the service implementation |
| `Cause`, `catchCause`, `catchDefect`, `Effect.exit` | "defect inspection isn't modelled" → recover by tag (`catchTag`) and treat defects as fatal |
| `Layer.*` inside a translated function | "layers are wiring, not program logic" → declare the service in `effects:` and `yield*` the tag |
| `Effect.runPromise`/`runFork`/`runSync`/`runMain` inside one | "running an effect inside a translated function isn't supported" → return the `Effect`; run it at the edge |
| module-mutable state read after a `yield*` (e.g. t3code's `lastPendingSweepByDirectory` in `issueAttachmentUploadUrl`) | the existing hazard rule — same refusal as after `await`, hint: move the bookkeeping into a service |
| `Match.*`, `Data.*`, `Context.Tag`, `Effect.Service` | rare in the corpus; `Context.Tag`/`Effect.Service` can be added as aliases later |

## 3. Real functions the subset covers

All from t3code @ `700a4644`; the guarantees are the draft contract a reviewer
would care about, in the `Js.Eff.Spec`/`ok (.failed …)` vocabulary.

1. **`statMediaFile`** (`apps/server/src/assets/MediaFile.ts`) —
   `Effect.fn` wrapping one `Effect.tryPromise` whose `catch` builds a
   `MediaFileStatError`.

   ```lean
   theorem statMediaFile_fails_tagged :
     ∀ (o : Proofci.Effects.world.Oracle) (hist : Proofci.Effects.world.Hist),
       Js.Eff.Spec (statMediaFile path file o hist) o hist
         (fun r _ => match r with
           | .failed e => e._tag = "MediaFileStatError" ∧ e.path = path
           | _ => True)
   ```

   *"A failure is always the tagged stat error for this path — never a bare
   exception leaking to the caller."*

2. **`checkRequestDpopProof`** (`apps/server/src/auth/dpop.ts`) — `Effect.fn`
   gen: yields `DateTime.now`, `ServerSecretStore`, `Digest` services; every
   early `return yield*` is a `ServerAuthInvalidCredentialError`; on success it
   returns `{thumbprint, consume}` where `consume` is itself an `Effect.gen`.

   ```lean
   theorem checkDpop_never_authenticates_without_proof :
     ∀ (o hist), Js.Eff.Spec (checkRequestDpopProof ⟨req, none, _, _⟩ o hist) o hist
       (fun r _ => match r with
         | .fulfilled v => proofHeaderPresent req
         | .failed e => e._tag = "ServerAuthInvalidCredentialError"
         | _ => True)
   ```

   *"With no DPoP proof the function can never return success; and its only
   failure mode is the credential error."* A second guarantee: on success, the
   `consume` effect's history records a `secretsCreate` for the replay key —
   "the jti is recorded exactly once".

3. **`PayloadSigner.verify`** (`apps/server/src/auth/PayloadSigner.ts`) — a
   `pipe` of `Base64Url.decode` → `flatMap mac.verify` → `orDie`-free: returns
   `Effect<boolean>` and answers `succeed false` when the signature doesn't
   decode.

   ```lean
   theorem verify_malformed_signature_is_false_not_error :
     ∀ (o hist) (hbad : malformed signature),
       Js.Eff.Spec (fromSecret secret o hist) o hist
         (fun r _ => match r with
           | .fulfilled signer => ∀ r₂ h₂, (signer.verify payload signature) o h₂ = ok r₂ →
               r₂.1 = .fulfilled false ∨ r₂.1 = .failed _
           | _ => False)
   ```

   *"An unparseable signature is `false`, never a rejection the caller has to
   catch."* (The record-of-functions return needs handles for the closure —
   phase 2; the point stands: the subset covers `fromSecret` itself.)

4. **`managedPolicyPath` + `decodeDocument`** (`packages/shared/src/managedPolicyFile.ts`)
   — pure path selection + `Schema.decodeUnknownExit` with `onExcessProperty:
   "error"`. The decode is the boundary the proof talks about:

   ```lean
   theorem decodePolicy_rejects_unknown_keys :
     ∀ raw, decodeDocumentJsonExit raw = ok exit →
       (∃ d, exit = .succeed d) ∨ (∃ e, exit = .failed e)
   ```

   *"Unknown keys are never silently dropped — every accepted document
   round-trips through the schema."* (Schema decode enters as a `try`-like
   op or a trusted builtin — see phase plan.)

5. **`issueAttachmentUploadUrl`** (`apps/server/src/assets/AttachmentUpload.ts`)
   — **refused, deliberately**: it reads and writes the module-level
   `lastPendingSweepByDirectory` map after `yield*`s. Same hazard rule as
   `await`; the fix-it hint tells the agent to move the sweep bookkeeping into
   the `ServerConfig`/`AttachmentStore` service so the oracle owns it. Worth
   keeping in the doc because it's exactly the kind of function an agent
   writes: mostly clean Effect code with one shared-state escape hatch.

## 4. Phases

| phase | scope | rough effort |
|---|---|---|
| 1. Syntax surface | `gen`/`yield*`/`fn`/`fnUntraced`/`pipe`, `succeed`/`fail`/`sync`/`try`, `map`/`flatMap`/`andThen`/`tap`/`as`/`zip*`, `TaggedError` declarations, `catch*`/`orElse*`/`mapError`, `all`/`forEach` (sequential), `orDie`/`die`; `R = never` (no services). New `Settled.failed` case in `ProofciAsync.lean`. | ~1.5 wk |
| 2. Services | `Context.Service`/`Context.Tag` policy entries (`service:`/`method:`), `yield* Tag`, `service`/`provideService`; service records as handles. | ~1 wk |
| 3. Async inside Effect | `tryPromise`/`promise`/`try` mapped onto the existing oracle+`narrowed`; Node comparison via `runPromiseExit` + `Layer.succeed` stubs; `asynccheck`-style trace tests + mutants. | ~1 wk |
| 4. Bridge | `AStmt` `failTagged`/`catchTag`, `ASim` rules for the gen-desugared bind chain; loops keep the `async` status quo. | ~1 wk |
| 5. Boundary (optional) | `Schema.decodeUnknown*`/`encode*` as trusted builtins or `effects` entries; `Option`/`Result` yieldables. | ~0.5 wk |

**Out of scope** (and refused with hints): `Stream`, `Scope`/`acquireRelease`/
finalizers, `Ref`/`Deferred`/`Queue`/`Semaphore`/`PubSub`/`SubscriptionRef`/`Atom`,
`Fiber`/`fork`/`race`/`timeout`/`sleep`, `Schedule`/`retry`/`repeat`, `Cause`/
`catchCause`/`Exit` inspection, `Layer` internals, `run*` inside translated
code, interruption semantics.

**Risks**

- **`catchCause`/defect inspection is common (252 `catchCause` + Cause ops):**
  guarantees on code that inspects defects stay out; the `failed`/`rejected`
  split keeps the model honest but means some recovery code is refused.
- **Services are the real work:** the 39% headline assumes services are
  declarable as effect entries; service *methods* that return `Effect`s of
  `Effect`s, or generics, will push some of the 510 out — measure again after
  phase 2 with the checker resolving `R`.
- **`R` inference:** the survey is syntactic; a real implementation needs the
  type checker to know when `R ≠ never` — service usage must be found via
  `yield* Tag`/`Effect.service`, not just the annotation.
- **`Effect.gen` internals differ from `await` desugaring:** the generator
  adapter must be trusted, or the lowering must be checked the way `lower.mjs`
  checks async lowering today.
- **Schema is a second library:** t3code's data layer is Schema; treating all
  of it as opaque effects may weaken guarantees (a decode that "can't fail" is
  only believable via the schema). Phase 5 is optional but likely wanted.
