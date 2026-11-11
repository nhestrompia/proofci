# TypeScript support

## Status: experimental

TypeScript support is experimental and isn't in a release yet. Use it to try the idea
on a function you care about, not to rely on it.

**What works.** The pull request flow: a manifest names the functions, a pull request
that breaks a proved one is blocked, and one that weakens the policy waits for a
maintainer. A project's packages are installed from its lockfile so that their types
resolve. A call into a package can be listed in the policy with `assumes`. Functions a
guarantee reaches must write out their types.

**How much it covers.** On eight repositories the rules were never tuned on (tldraw,
Rocket.Chat, plane, AFFiNE, medusa, umami, trigger.dev, cal.com), the translator accepted
227 of 2,785 pure functions (8.2%). That is a lower bound,
because those clones had no packages installed, so imported types were unknown. For
178 of the accepted functions (78.4%) a bridge theorem was proved
within 120 seconds. Most functions that aren't accepted use regular expressions, `Date`,
classes or `any`.

**What "proved" means here.** Two different things are proved, and the numbers above are
only the first. The first is a theorem, generated for each function, that ties the Lean view
you read to a formal model of JavaScript (Core). If Lean accepts it, the view means what the
code means under that model. It is generated and checked in [`spike/core`](../spike/core),
and isn't part of the action's check yet: the action compares the translation with Node on
generated inputs. The second is yours: a guarantee about the function, stated in
`Contract.lean` and proved in `Proofs.lean`. The bridge theorem doesn't give you that.

**What is trusted.** The lowering from TypeScript to Core (`spike/core/lower.mjs`) and the
semantics of Core are trusted. They are tested against Node, not against the official
conformance suite (test262). The package install is the only step with network access, and
nothing restricts it at the network level: it relies on the package manager's settings and
the lockfile's hashes.

**What it can't do yet.** Regular expressions, `Date`, `async`, classes and methods,
recursive types, and `any` or `unknown`. `number` is a safe integer, so fractions are
out. Reading a member only an index signature allows, and a variable that might be read
before it is assigned, are also `unsupported`. The check's proofs about your guarantees can
use `%` (`Js.rem` has a step lemma), but the theorem that ties a function's view to Core has
no rule for `%` yet, so functions that use it are never counted as proved above.

## What works today

The manifest names the language and the package, and functions by file:

```yaml
version: 1
language: typescript
package: .
lean: proofci
targets:
  - id: transfer
    function: src/ledger.ts::transfer
    guarantees:
      - id: conservation
        theorem: transfer_conserves
```

Lean sees `src/ledger.ts::transfer` as `src.ledger.transfer`, in a module named after
the package, so `ts-bank` is `import TsBank`. See [`examples/ts-bank`](../examples/ts-bank).
Proofs work the same way as for Rust, including `step*`. Start with
[proving TypeScript](proving-typescript.md), and see
[`examples/ts-real`](../examples/ts-real) and [`examples/ts-dates`](../examples/ts-dates)
for proofs about functions from real projects.

A function can be exported or not. A function that isn't exported is translated and
proved the same way, but it isn't compared with Node, because nothing can import it,
and the report says so.

| Supported | Details |
|---|---|
| Values | `number`, `bigint`, `boolean`, `string`, `T \| null`, `T \| undefined` |
| Types | Interfaces, string-literal unions, unions tagged by `kind`, arrays (with `null` or `undefined` in them when their elements allow it), `Map`, `Set` |
| Functions | Module-level functions and arrow functions across files, self-recursion, inline callbacks |
| Control flow | `if`, `switch`, `for`, `while`, `for...of`, `break`, `continue`, `throw`, `try`/`catch` |
| Local changes | Reassignment, `+=`, `++`, `let x;` assigned on every path before it is read, and in-place changes to a value only one name can see |
| Arrays | `length`, `[i]`, `push`, `map`, `filter`, `reduce`, `find`, `some`, `every`, `slice`, `includes`, `join` and more |
| Strings | `length`, `[i]`, `slice`, `startsWith`, `includes`, `split`, `trim`, `replace` with a string, templates, ASCII case changes |
| Numbers | `+ - * / %`, comparisons, `Math.floor/ceil/trunc(a / b)`, `Math.abs/min/max` |

`??` and `?.` work on values that may be `null` or `undefined`. `||` and `&&` work on any operand, such as `daysInMonth[month] || 28`. An interface with an
index signature (`[key: string]: T`) keeps its named fields; the members the signature
allows are left out, so reading one by name, indexing the value with a key or spreading
it is `unsupported`.

Everything else is `unsupported`, with the source line. That includes fractions,
regular expressions, classes, `async` and calls into packages that aren't listed under `assumes`.

### In-place changes

A value in Lean only behaves like a JavaScript object if nothing else can see the
object change. So a changed array, map or object must start as a new value in that
function, and can only be read, returned or copied. Changing a parameter, storing a
changed array in another object or passing it to a function is `unsupported`.

### Proving loops

A loop translates to Aeneas's `loop`, so `loop.spec_decr_nat` applies. Give it what
shrinks and what stays true. See `sum_exact` in
[`examples/ts-bank`](../examples/ts-bank/proofci/Proofs.lean). `throw` is `fail .panic`,
so "this input throws" is stated as `f x = fail .panic`.

### What `number` means

`number` is a safe integer. If any step would produce a fraction, `NaN`, `Infinity`
or a value past `Number.MAX_SAFE_INTEGER`, the model fails. So a proof that a function
returns a value also proves it never lost precision. Code that needs fractions stays
unproven, and is never judged wrongly.

Each check also runs the translated functions in Node on generated inputs. See the
[security model](../SECURITY.md#typescript).

## Running it on pull requests

The workflow is the one in [getting started](getting-started.md#6-add-the-workflow-and-make-it-required).
Set `path` to the directory that holds `proofci.yaml` (the repository root, even when
`package` points at a workspace member). The base commit's `proofci.yaml` and
`Contract.lean` are the policy: a pull request that removes or weakens a guarantee, or
edits the contract, is blocked until a maintainer approves that exact commit. Code
that breaks a proved function fails as `unproven`, and a proof file edited to make
that pass is checked against the protected statement, not its own.

## Packages

The type checker reads the declarations of every package a file imports, so a project
that imports packages needs them installed. ProofCI installs them for you, from the
lockfile that is already in the repository, before the check:

| Lockfile | Installed with |
|---|---|
| `package-lock.json`, `npm-shrinkwrap.json` | `npm ci` |
| `pnpm-lock.yaml` | `pnpm install --frozen-lockfile` |
| `yarn.lock` (Yarn 1) | `yarn install --frozen-lockfile` |

The nearest lockfile at or above the `package` directory is used, so a workspace
member works. A project without dependencies or without a lockfile is checked as it
is, and the report says that its packages are unknown when that is why a type isn't
supported. Yarn 2 and later isn't supported, because it runs project code while
installing.

The install is the only step with network access, and it runs nothing from the
project:

- Install scripts are off (`--ignore-scripts`), so no package runs code. The package
  manager itself is the version pinned in the toolchain image, not the project's
  `packageManager` choice.
- The install happens in a copy of the repository without `.npmrc`, `.yarnrc*`,
  `.yarn/`, `.pnpmfile.cjs` and `.pnp.*`, because a pull request controls those files
  and some of them run code.
- Packages may only come from `registry.npmjs.org` (and `registry.yarnpkg.com` for
  `yarn.lock`), and the lockfile's integrity hashes decide what they contain. For
  npm, a package from anywhere else (a git repository, a URL, a private registry) is
  left out of the install and named in the report, so that one such package doesn't
  stop everything else. pnpm and Yarn lockfiles with such a package are refused.
- The check itself stays offline. It reads the installed packages through a read-only
  mount inside a copy of the code.

Running a function in Node for the comparison can load installed packages. That is
the project's code running in the same sandbox as before, without network.

Locally, run the install once and pass the result to `dev` and `check`:

```sh
docker run --rm $OPTS -v "$PWD:/base:ro" -v "$PWD:/head:ro" -v "$PWD/.proofci-vendor:/vendor" \
  $IMAGE fetch --base /base --head /head --out /vendor
docker run --rm --network none $OPTS -v "$PWD:/repo:ro" -v "$PWD/.proofci-vendor:/vendor:ro" \
  -v proofci-dev:/tmp/proofci-dev $IMAGE dev --repo /repo --vendor /vendor
```

The vendor directory has to be writable by the image's user (`chmod 777`). The
action does all of this for you. See [`examples/ts-packages`](../examples/ts-packages).

## Written types

Every function a guarantee reaches must write out its parameter and return types.
Inference can change a function's contract without showing up in a diff. The check
rejects a function that leaves them out and says what to add. Callbacks written in
place are exempt, because they take their types from the call.

## Outside calls

A proof can rely on a call to code it can't see, if the policy lists it:

```yaml
assumes:
  - call: slug-maker::slug
    signature: "(title: string): string"
```

The call must be a named import, and it must have exactly this signature. Generic
functions, rest parameters and functions without arguments can't be listed. If the
package isn't installed, the signature in the manifest declares it. If it is
installed, its published types must match, so an upgrade that changes the type stops
the check.

An assumption makes two claims: the function has this type, and it gives the same
result for the same arguments. So don't list a function that reads the clock, the
network or random numbers. The translated model is opaque, so a proof holds for any
function of that type. To rely on what it does, state that as a hypothesis in the
contract:

```lean
theorem label_tagged (title : Js.Str)
    (slug_nonempty : ∃ s, Proofci.Assumed.slug_maker.slug title = ok s ∧ s ≠ []) :
    label title ⦃ r => r.head? = some 35 ∧ 2 ≤ r.length ⦄ := by sorry
```

The manifest and the contract are both protected, so a pull request can't add or
change an assumption for itself. The report lists every assumption a verified
guarantee rests on. See [`examples/ts-assumes`](../examples/ts-assumes).

Functions that rely on an assumed call aren't compared with Node, because the model
has no body to run.

## Survey

### How it works

[`typescript/survey`](../typescript/survey) reads a repository with the TypeScript
compiler and classifies every exported function that makes at least one decision.
A function counts as covered only if everything it reaches is covered. It never
runs code from the repositories it reads.

The numbers below come from 21 public repositories and 22,652 functions.
"Pure" functions (5,701) compute a result from their inputs, without I/O, async,
object state or third-party calls. Those are the natural proof targets.

| Reached | All functions | Pure functions |
|---|---:|---:|
| Milestone 2: core language | 7% | 27% |
| Milestone 3: ownership, `this`, `async`, callbacks | 11% | 35% |
| Also with library models | 22% | not measured |

What blocks pure functions, as a share of the 5,701:

| Blocker | Reaches it | Only blocker |
|---|---:|---:|
| Library calls with no model yet, such as `toLowerCase` | 24% | 8% |
| `Object.keys`, `JSON` and other reflection | 23% | 7% |
| Unchecked casts and `any` | 23% | 6% |
| Regular expressions | 15% | 5% |
| Keys that aren't known types | 9% | 3% |
| Aliased mutation | 7% | 1% |
| Fractional numbers | 5% | 2% |

### What this changed

- **The plan's stop condition didn't trigger.** Fractions and aliasing are not what
  holds pure functions back, so binary64 numbers and a heap model stay later.
- **Library models move earlier.** They matter more than classes or `async` for pure
  code, so a models milestone goes between milestones 2 and 3.
- **Pure logic is the honest target.** ProofCI covers most of a code base's kernels
  long before it covers the code around them, and that's where proofs pay off.
- **Casts can become listed assumptions.** A downcast can't be checked, but a report
  can say that a result depends on it. That is worth trying before rejecting them.

### What the translator accepts today

The table above is what a finished subset would reach. `survey/try.mjs` runs the real
translator on the pure functions of nine of those repositories instead. Today it
accepts 82 of 1,457, about 6%. Acceptance only means the translator produced Lean: of
36 accepted functions that were also compiled, 35 built. The failures are now a long tail, and most of it is
about mapping TypeScript's types onto Lean's: recursive types, generic types,
untagged unions, `any` and `unknown`.

### Limits of these numbers

- The classifier is heuristic. It under-counts aliasing, because it doesn't follow
  values stored in collections and mutated later.
- Dependencies weren't installed, so some types are unresolved. That inflates casts
  from `any` and third-party calls. The check installs them now; the survey doesn't.
- `Pure` still includes plumbing that nobody would prove.
- The repositories were hand-picked, and each is sampled to 1,500 files.
- Library internals skew low: `immer` and `zod` are metaprogramming by nature.

Reproduce it with:

```sh
cd typescript && npm ci --ignore-scripts
node --max-old-space-size=8192 survey/run.mjs <repository> <output.json>
python3 survey/report.py <directory of outputs>
```

## Getting to full TypeScript

"Full" can't mean every program. `eval`, `Proxy` and reflection on unknown objects
have no useful proofs. The realistic goal is that every function gets a sound verdict,
pure logic can usually be proved, and everything else becomes a listed assumption.

The current design maps each TypeScript type to a Lean type, which is why each new
type shape is a new feature. The plan is to add a second path that doesn't need that:

1. **Finish the cheap wins.** Add recursive and generic types, and make `unsupported`
   say how to fix the code. Packages are already installed for their types.
2. **Try a dynamic path.** Translate to a single Lean type of JavaScript values plus an
   explicit heap, so TypeScript types become preconditions. That one change covers
   unions, `unknown`, aliasing, classes and closures. The typed path stays as the fast
   path. This depends on a spike showing proofs stay practical.
3. **Fill in the runtime.** Library models, promises as an event queue, and binary64
   numbers with safe integers as lemmas on top.
4. **Prove the translation.** Generate a proof, per function, that the typed output
   matches the dynamic semantics, so the translator leaves the trusted base.
