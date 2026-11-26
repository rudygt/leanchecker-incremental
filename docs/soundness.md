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

**2. The key covers all of those inputs.** A check key is the SHA-256 of:

- the key scheme and `Lean.githash` of the running binary.
- the `ref` id of every constant the kernel uses by name.
- CA's `decl` id of `d`: its kind, type, value and structural fields, hashed with each referenced constant replaced by
  that constant's `ref` id.
- the names of `d`'s universe parameters.

A `ref` id is the constant's name hashed together with its `decl` id, or with only its statement for a theorem. It is
computed the same way, recursively, so it covers everything the kernel can read through that constant, including
which constant it is. Mutually dependent declarations,
including an inductive type with its constructors and recursors, are hashed as one block. Every encoding is tagged
and length-prefixed.

**3. What the key leaves out, the kernel ignores.**

| Left out of the key | Why the kernel's verdict does not change |
|---|---|
| Binder names | The kernel uses de Bruijn indices. Names are only for printing. |
| `mdata` annotations | The kernel strips them before it inspects a term. |
| Names of universe parameters, inside the ids | They are renamed by position, which is a one-to-one renaming of the declared parameters. Repeated names, which the kernel rejects, would break that, so the raw names are added to the key. An undeclared parameter keeps a position of its own and keeps the key distinct. |
| A theorem's proof, inside its users' ids | The kernel never unfolds a theorem. |
| The declaration's own name | The verdict on a declaration does not depend on its own name. The names of the constants it refers to are in the key. |

Three of CA's rules would have broken points 2 and 3, so this repository changes them (`IncCheck/CA/VENDORED.md`):

- **References are bound to names.** CA leaves names out on purpose, so that a renamed lemma keeps its id in a
  registry. But the kernel tells constants apart by name. Two axioms `a b : Nat` have the same content and are still
  different, and so are two inductive types with the same structure. Without names, `bad : a = b` got the same key as
  `good : a = a` with the same proof, and `f : A → B := fun x => x` the same key as `g : A → A := fun x => x`. Key
  scheme 2 accepted both from a store that held the verdicts of `good` and `g`. A review found this on 2026-11-26.
  Key scheme 3 binds every `ref` id to its name, and `test/attacks.py` keeps both counterexamples as regression tests.

- **Levels are not normalized.** The kernel compares some levels syntactically, for example when it asks whether a
  type is a `Sort 0`. Normalizing would also erase an undeclared parameter, as in `imax w 0`.
- **Reducibility hints are part of a definition's id.** They decide which side the kernel unfolds first, and that can
  change whether a check succeeds.

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
