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

## Patterns

Start every proof with `unfold f` and `step*`, as the Rust guide describes.

**A constant.** Give it a step lemma once:

```lean
@[step] theorem divisor_spec : AUCTION_TICK_DIVISOR ⦃ d => d = 100 ⦄ := by
  simp [AUCTION_TICK_DIVISOR, WP.spec_ok]
```

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

Don't change the contract to get a proof through without saying so in the pull request.
If the statement turns out to be false, you may have found a bug in the code, which is
the point. Report it instead of weakening the theorem.
