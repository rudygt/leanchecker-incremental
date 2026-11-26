# Why skipping the kernel is safe

`leanchecker-inc` adds a declaration without the kernel when its check key is in the verdict store. This page
explains why that gives the same answer as checking it, what the argument rests on, and what it does not promise.

## The guarantee

Suppose the verdict store and the id cache were written only by `leanchecker-inc` runs of the same binary. Then
`leanchecker-inc` accepts a set of modules only if replaying all of their declarations with Lean's kernel would accept
them. "Replaying" means what `Kernel.Environment.replay` does on Lean master as of 2026-11-24. That version includes
the fixes for lean4#16675 and for malformed inductive entries (lean4#16717). Lean `v4.37.0-rc1` predates both, so
on the shapes those fixes cover, this tool is stricter than the toolchain's own `leanchecker --fresh`
(`test/attacks.py`).

It is not stronger than `leanchecker --fresh` in any other way. Lean's kernel assumes that the prelude's definitions
are the ones in Lean's prelude. Lean's maintainers closed lean4#16734 (a forged quotient entry) and lean4#16730 (a
forged projection) on that basis, and point to `lake comparator` and external checkers for adversarial settings. The
same applies here.

## Why equal keys mean equal verdicts

Every skipped declaration has the same key as a declaration that the same kernel accepted in an earlier run that
completed. Equal keys mean equal verdicts for four reasons.

**1. The kernel's verdict depends on a fixed set of inputs.** While checking a declaration `d`, Lean's kernel reads:

- `d` itself: its kind, universe parameters, type, and value or structure.
- for each constant named in `d`: its type and universe parameters, and, for a definition, its body and reducibility
  hints, because the kernel can unfold definitions.
- for each inductive type it meets: the whole block, with its types, constructors and recursor rules.
- the constants it uses by name without `d` naming them (`docs/kernel-builtins.md`).
- its own code, which is fixed by the Lean commit.

It never reads the body of a theorem or of an opaque constant. `has_value()` is `is_definition()` in
`src/kernel/declaration.h`, so only definitions are unfolded. The replay calls the kernel with no heartbeat or
recursion budget (`addDeclCore 0 0`), so the verdict does not depend on how long the check takes.

**2. The key covers all of those inputs.** Every constant has two SHA-256 ids (`IncCheck/Hash.lean`):

- Its **interface id** covers what a check of another declaration can read through it: its name, kind, universe
  parameters and type, a definition's body, reducibility hints and safety, and the structure of an inductive type,
  constructor or recursor. It also covers the interface ids of every constant those name, so it is a Merkle hash over
  everything reachable through types and definition bodies.
- Its **declaration id** covers what its own check reads: its interface id, plus a theorem's proof or an opaque
  constant's body and the interface ids of every constant those name.

A check key is the SHA-256 of the key scheme, `Lean.githash` of the running binary, the interface ids of the constants
the kernel uses by name, and the declaration id.

Expressions are hashed with each constant referred to by name, and the interface ids of those constants are hashed
alongside. Names matter, because the kernel tells constants apart by name: two axioms `a b : Nat` have the same
content and are still different. An inductive block (its types, constructors and recursors) and a mutual group of
definitions are hashed as one unit, because they refer to each other. Every encoding is tagged and length-prefixed, and
large terms are hashed from the digests of their children, so a proof shared as a DAG costs its size as a DAG.

**3. What the key leaves out, the kernel ignores.**

| Left out of the key | Why the kernel's verdict does not change |
|---|---|
| Binder names and binder info | The kernel uses de Bruijn indices, and binder info only guides elaboration. |
| `mdata` annotations | The kernel strips them before it inspects a term. |
| The `nondep` flag of `let` | The kernel checks a `let` the same way either way. |
| A theorem's proof, in its users' keys | The kernel never unfolds a theorem. |
| An opaque constant's body, in its users' keys | The kernel never unfolds an opaque constant. |

Universe levels are hashed exactly as written, never normalized: the kernel compares some levels syntactically, for
example when it asks whether a type is a `Sort 0`, and it rejects an undeclared parameter even inside `imax w 0`.
Universe parameter names are hashed as written too. Renaming one changes the interface id, so the constant's users are
checked again, which costs time but is never wrong.

### Why names are in the key

Up to commit `b568494` the keys were built on [CA](https://github.com/proofinity-it/CA), which leaves names out of its
ids on purpose, so that a renamed lemma keeps its id in a registry. Key schemes 1 and 2 inherited that, and a review on
2026-11-26 found the consequence: `bad : a = b` got the same key as `good : a = a` with the same proof, for two axioms
`a b : Nat`, and `f : A → B := fun x => x` the same key as `g : A → A := fun x => x`, for two inductive types with the
same structure. Those versions accepted both forged declarations from a store that held the verdicts of `good` and
`g`. Key scheme 3 bound CA's ids to names, and scheme 4 replaced CA with the hasher described here, which refers to
constants by name throughout. `test/attacks.py` keeps both counterexamples as regression tests.

**4. Verdicts are recorded only after a complete run.** The replay compares the stored constructors and recursors with
the ones the kernel generates only after everything else. Keys are added to the store only if that comparison passes
too, so no stored verdict depends on data that the end of the run rejected.

## The order of the replay

Declarations and inductive blocks with a stored verdict are inserted first, with Lean's `Kernel.Environment.add`, and
without walking their references. The rest are replayed in dependency order, as Lean's `replay` does, and sent to the
kernel.

A check must find every constant it can reach in the environment. A changed declaration can refer to an inserted
definition whose body names a constant that has not been replayed yet, such as `Quot.lift`, or a theorem whose proof
changed. So before a declaration is checked, the replay also walks through each constant that is already present.
For each one it makes the constants that its type, its definition body, or its inductive structure names present
too. Theorem proofs and opaque bodies are not walked, because the kernel never unfolds them. A missing constant would
make the kernel fail with "unknown constant", which rejects rather than accepts.

## Inductive blocks

The kernel checks an inductive declaration even on its unchecked path, and generates its constructors and recursors
itself. So an inductive block has its own verdict key: a SHA-256 over the check keys of its types, their constructors,
and the recursors whose `all` field names the block's types. The key is recorded after the kernel accepted the block in
a complete run. That run also compared the constructors and recursors the kernel generated with the stored ones. When
the key is in the store, the stored types, constructors and recursors are inserted directly, as importing a module
does, with Lean's `Kernel.Environment.add` (exported as `lean_environment_add`).

The same content gives the same generated constants, because the kernel is deterministic. If the block were missing a
constant that the kernel would generate, the comparison at the end of the replay would fail with "No such recursor",
so a wrong grouping makes the check fail rather than pass.

## What is always checked

- **Quotients.** `Quot` and its three companions go to the kernel on every run.
- **Declarations with an inexact id.** These are declarations with a reference that has no id. In practice there are
  none.
- **Inductive blocks with a member that has no exact id.**
- **Nothing `unsafe` or `partial`.** Those are skipped entirely, as Lean's `replay` does.

## The trusted inputs

- **The verdict store.** A key planted in the store is trusted. `test/attacks.py` plants the key of a proof of `False`
  and shows that the check then accepts it. Protect the store like build credentials. Run with `--no-store` from time
  to time, as Mathlib runs `leanchecker --fresh` daily.
- **The id cache.** A forged cache entry can make a changed module look unchanged, so it needs the same protection.
  Keys computed with and without the cache are byte-identical on the toy project and on Mathlib
  (`docs/mathlib-results.md`).
- **The Lean toolchain.** As with `leanchecker`.

## Evidence

| Test | What it shows |
|---|---|
| `test/KeyProps.lean` (`lake exe inc-key-props`) | Two axioms with the same type give `a = a` and `a = b` different keys. 11 mutations of real declarations of `Init`. For each one, the keys that change are exactly the ones the reference graph says must change. That is thousands for a definition, a statement, a level or a constructor, every key for a constant the kernel uses by name, only the theorem itself for a proof, and none for binder names or `mdata`. |
| `test/attacks.py` | Forged `.olean` files: a constant stored under another name, an inductive type missing from its own `all` field, and `False` proved by `True.intro` are all rejected. So are `bad : a = b` and `f : A → B`, copies of valid declarations about two same-typed axioms and two same-shaped inductive types, checked against the valid ones' verdicts. A poisoned store is trusted, and `--no-store` rejects again. |
| `test/scenarios.py` | Edits to a small project re-check exactly the affected declarations, with and without the id cache, and a false theorem added with `debug.skipKernelTC` is rejected. |
| `docs/mathlib-results.md` | Five Mathlib commits, all accepted, with the declarations re-checked matching what changed. |

## Limits of this argument

- **Point 1 comes from reading** `src/kernel/type_checker.cpp` and `src/kernel/declaration.h` at `v4.37.0-rc1`. It is
  not a formal proof. A kernel change that reads something new would need a matching change to the key, and it would
  come with a new `Lean.githash`, which already separates the stores.
- **SHA-256 is assumed collision-resistant.**
