# Proving TypeScript

For coding agents, and people working with them. It takes a TypeScript function to a
proof that CI re-checks on every pull request. Read [writing proofs](writing-proofs.md)
too: the tactics are the same as for Rust. [`examples/ts-real`](../examples/ts-real)
has everything below working on real code.

## What you hand in

Three files, all committed to the repository:

| File | Holds | Who has to trust it |
|---|---|---|
| `proofci.yaml` | Which functions matter and which theorems cover them | Reviewed by a person |
| `proofci/Contract.lean` | The statement of each guarantee, ending in `sorry` | Reviewed by a person |
| `proofci/Proofs.lean` | The same statements, proved | Nobody: Lean checks it |

CI does the rest. Changes to the manifest or contract need a maintainer's approval, so
a pull request can't make its own proof easier. Your job is to make a statement that
says something real, then prove it.

## The loop

1. **Pick the function.** Pure logic with a claim worth having: money, limits, parsing,
   state changes. A function with a doc comment that promises something is ideal, since
   that promise is your theorem.
2. **Declare it** in `proofci.yaml`, with `function: path/to/file.ts::name`.
3. **Read the translation.** Create `proofci/Contract.lean` with only an import, then:

   ```sh
   OPTS="--security-opt seccomp=unconfined --security-opt apparmor=unconfined --security-opt systempaths=unconfined"
   docker run --rm --network none $OPTS -v "$PWD:/repo:ro" -v proofci-dev:/tmp/proofci-dev \
     $IMAGE dev --repo /repo --show
   ```

   `IMAGE` is a ProofCI toolchain image with TypeScript support, which no release has
   yet. If it prints `unsupported`, the function is outside the subset. Don't write a proof.
   Usually the fix is to move the logic into a smaller function that takes plain values.
   If the project imports packages, install them first and add `--vendor`, as
   [TypeScript support](typescript.md#packages) shows. If `dev` can't write to the
   `proofci-dev` volume, the image is older than the fix: run
   `docker run --rm -v proofci-dev:/w alpine chmod 777 /w` once.

   To find out which functions the translator takes, point `--show` at a manifest that
   lists several candidates; each unsupported one is printed with its source line, and
   a project's small private helpers (`isLeapYear`, `validateTime`) are often the best
   first targets. They don't have to be exported.
4. **State the guarantee** in `Contract.lean`, ending in `:= by sorry`.
5. **Prove it** in `Proofs.lean`. Re-run `dev`, which takes seconds, and read the goals
   it prints. Stop when it says `0 error(s)`.
6. **Run the real check** by adding `--judge`, or run `check` as CI does.
7. **Try to break it.** Change the code by hand and confirm the check blocks: flip a
   comparison, or remove a branch. A proof that survives this says nothing.
8. **Commit** all three files. CI translates the code again, compares it with Node on
   generated inputs, and replays your proof.

## Reading the translation

| TypeScript | Lean |
|---|---|
| `src/config/price.ts::f` | `src.config.price.f`, in a module named after the package: `ts-real` is `import TsReal` |
| `number` | `Js.Num`, a safe integer. Use `x.val` for its integer value |
| `bigint` | `Int` |
| `string` | `Js.Str`, a list of UTF-16 code units. Write literals as `js!"text"` |
| `T[]` | `List T` |
| `T \| null`, `T?` | `Option T` |
| `Map`, `Set` | `Js.Dict K V`, `List K` |
| `throw` | `fail .panic` |
| Object type | A structure, with the same field names |
| `'a' \| 'b'` | An inductive with `.a` and `.b` |

Every function returns `Result T`. A module constant that needs computing is a
`Result T` too, so it needs a lemma before `step*` can pass it.

## Stating something true and useful

- **`f x ⦃ r => P r ⦄` means `f` succeeds and `P` holds.** Prefer it. It also rules out
  leaving the model, so it's the strongest thing you can say.
- **Numbers fail rather than round.** An operation that would leave the safe integers
  stops the model, and no proof can cover what happens next. If a sum can overflow, the
  theorem needs a bound as a hypothesis. Only `number` has this limit; `bigint` doesn't.
- **Fractions are outside the model.** A theorem about `Js.Num` says nothing about `0.5`.
  If the function really handles fractions, say so in the pull request.
- **Hypotheses are assumptions about callers.** `(h : 0 ≤ raw)` proves nothing for
  negative input. Keep them few, and make each one something a reviewer can check.
- **Don't assume the result.** A hypothesis that's false for every input makes any
  statement provable. The check warns about some of these, but the reviewer is the
  real defence.
- **Say what the empty case means.** `xs[0]` on an empty array is `undefined` in
  JavaScript even if the type says otherwise. The model stops there, so state the theorem
  for `p :: ps`. That is a real assumption, so name it in the contract's comment.
- **Keep statements self-contained.** `Proofs.lean` can't import `Contract`, so write
  conditions inline where you can. `p.fromAge.all (fun a => a.val ≤ age.val)` reads
  `fromAge == null || fromAge <= age` without a helper.

## Async functions

[`examples/ts-async`](../examples/ts-async) has everything below working on real code.

An `async` function is translated into the type `Proofci.Effects.Eff T`: a computation that
takes an **oracle** `o` (the outside world, any function from a question and the history so
far to an answer) and a **history** `hist`, and gives back `ok (outcome, hist')`. The outcome
is `Js.Settled.fulfilled v` or `Js.Settled.rejected e`. To prove something about it:

1. **List what it awaits** in the `effects` block of `proofci.yaml` (see
   [TypeScript support](typescript.md#listing-the-outside-world)). `dev --show` prints the
   world, `Proofci.Effects.Op`, with one case per entry.
2. **State a guarantee over every oracle.** Either an equation, for something that always
   happens (`f ... o hist = ok (Js.Settled.fulfilled false, hist)`: false, and nothing was
   asked), or `Js.Eff.Spec (f ...) o hist fun r hist' => ...` for something that holds
   whenever the run completes. Facts about the calls are facts about `hist'`: the pair of
   question and answer is in it as an element, written
   `(⟨Proofci.Effects.Op.getLink, linkId, Js.Answer.value (some l)⟩ : Proofci.Effects.world.Event) ∈ hist'`.
3. **Prove it by unfolding.** `unfold` the function, then `simp` with `Js.Eff.bind_run`,
   `Js.Eff.call_run` and `Proofci.Effects.call`. `Js.Eff.liftM_ok_bind` and the other `Eff`
   lemmas are `simp` lemmas. Each outside call splits into the cases of
   `o .getLink linkId hist`: `Js.Answer.value v` or `Js.Answer.reject e`. The repeated
   pattern is to `rcases` on that answer, `simp [ha] at h`, and read the new history.
   `Js.Eff.call_hist` says a call that settles adds exactly one event.

To say something about a particular answer, state it as a hypothesis on the oracle, for
example `(hmiss : o ⟨.getLink⟩ ... = .value none)`. The hypothesis is part of the contract, so
a pull request can't change it.

What to check in the report: the effects listed under the guarantee are the ones you
meant, and the arguments it names are the ones you accept to be unchanged during the call.

## Patterns

Start every proof with `unfold f` and `step*`, as the Rust guide describes.

**A constant.** Give it a step lemma once:

```lean
@[step] theorem divisor_spec : AUCTION_TICK_DIVISOR ⦃ d => d = 100 ⦄ := by
  simp [AUCTION_TICK_DIVISOR, WP.spec_ok]
```

**A remainder.** `x % 4` is `Js.rem x 4`. For a positive divisor `step*` passes it, with
`r.val = Int.tmod x.val y.val`. `omega` doesn't know `Int.tmod`, but it does know `∣` by a
literal, so relate the two with this small lemma in `Proofs.lean`:

```lean
theorem tmod_zero_iff (x d : Int) : Int.tmod x d = 0 ↔ d ∣ x := Int.dvd_iff_tmod_eq_zero.symm
```

After `unfold f`, `step*` leaves `h : tmp.val = 0` style facts, and `rw [tmp_post]`
with `tmod_zero_iff` turns them into `4 ∣ year.val` for `omega`. The leap-year proof in
[`examples/ts-dates`](../examples/ts-dates/proofci/Proofs.lean) is the whole pattern.

**Two functions with the same name.** Files are separate modules, so
`src/a.ts::isLeapYear` and `src/b.ts::isLeapYear` are `src.a.isLeapYear` and
`src.b.isLeapYear`. When a theorem reaches one through another, `open` only one of the
modules or write the full name, or Lean will say the name is ambiguous. A helper the
target calls needs its own `@[step]` lemma, as `leap_iso_spec` does in the example.

**An `if` at the end of a function.** `step*` stops there, because it's the last thing
the function does. Split it:

```lean
step*
split
· simpa [WP.spec_ok]
· simp [WP.spec_ok]
```

**`bigint` division.** `/` and `%` truncate toward zero in JavaScript, and Lean's default
rounds down, so `Js.bdiv` and `Js.brem` use `Int.tdiv` and `Int.tmod`. For non-negative
values, switch before reaching for `omega`:

```lean
have hd : Int.tdiv raw 100 = raw / 100 := Int.tdiv_eq_ediv_of_nonneg h
have hm : raw.tmod t = raw % t := Int.tmod_eq_emod_of_nonneg h
```

**One exact spec, then the guarantees.** Prove what a function computes as a `@[step]`
lemma, then derive each guarantee from it with `WP.spec_mono`:

```lean
apply WP.spec_mono (pricing_spec raw h)
rintro p ⟨ht, hf⟩
```

**A loop.** Loops become `Aeneas.Std.loop` over a state tuple. Peel off the setup with
`WP.spec_bind`, then give `loop.spec_decr_nat` something that shrinks and something that
stays true. The invariant is the whole proof, so write it down in words first. Here,
"finishing from this state gives the same answer as finishing from the start":

```lean
apply loop.spec_decr_nat (fun s => s.1.length)
  (fun s => ∃ a, s.2 = some a ∧ (s.1.takeWhile st).getLast?.getD a = T)
· rintro ⟨rest, cur⟩ ⟨a, h1, h2⟩
  dsimp only at h1 h2 ⊢
  cases rest with
  | nil => simp_all [WP.spec_ok]
  | cons q r => ...        -- one case per branch of the loop body
· exact ⟨p, rfl, hT⟩       -- it holds at the start
```

`Js.total` is the same idea for sums: see `sum_exact` in
[`examples/ts-bank`](../examples/ts-bank/proofci/Proofs.lean).

**A step that doesn't fire.** Read the goal. A leftover `⊢ ¬x = 0` is a side condition
the lemma needs, so prove it with what you have.

## When you're stuck

| You see | It means |
|---|---|
| `unsupported: ...` | The translator can't handle it. Restructure the code or leave it unproven |
| `ProofCI translated this code but the result does not compile` | A translator bug. Report it |
| `model of this code disagrees with Node` | A translator or runtime bug. Report it, and don't prove around it |
| `the comparison with Node did not run` | The module fails when loaded, usually from code at its top level |
| `unsolved goals` | Normal. This is what the loop is for |
| `Tactic split failed` or `No goals` in a proof that used to work | The code changed, so the translation did. The proof has to follow it, or the change is wrong. This is also what a pull request that breaks a guarantee looks like |
| `... types from them are unknown` | The project's packages weren't installed. See [packages](typescript.md#packages) |

Don't change the contract to get a proof through without saying so in the pull request.
If the statement turns out to be false, you may have found a bug in the code, which is
the point. Report it instead of weakening the theorem.
