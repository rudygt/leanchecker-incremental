# Why skipping the kernel is safe

`leanchecker-inc` adds a declaration without the kernel when its check key is in the verdict store. This page
explains why that gives the same answer as checking it, what the argument rests on, and what it does not promise.
Source references are to Lean `v4.37.0-rc1`.

## The guarantee

Suppose the verdict store and the id cache were written only by `leanchecker-inc` runs of the same binary, and the
`.olean` files do not change while a run reads them. Then `leanchecker-inc` accepts a set of modules only if
replaying all of their declarations with Lean's kernel would accept them, with the stack and memory of the runs that
recorded the verdicts it reuses (see "The environment of a run"). "Replaying" means what
`Kernel.Environment.replay` does on Lean master as of 2026-11-24. That version includes the fixes for lean4#16675 and
for malformed inductive entries (lean4#16717). Lean `v4.37.0-rc1` predates both, so on the shapes those fixes cover,
this tool is stricter than the toolchain's own `leanchecker --fresh` (`test/attacks.py`).

It is not stronger than `leanchecker --fresh` in any other way. Lean's kernel assumes that the prelude's definitions
are the ones in Lean's prelude. Lean's maintainers closed lean4#16734 (a forged quotient entry) and lean4#16730 (a
forged projection) on that basis, and point to `lake comparator` and external checkers for adversarial settings. The
same applies here.

## Why equal keys mean equal verdicts

Every skipped declaration has the same key as a declaration that the same kernel accepted in an earlier run that
completed. Equal keys mean equal verdicts for the reasons below. Where a reason rests on reading the kernel, the
replay also checks it as it runs, or a test checks it, and the section says which.

### 1. What the kernel reads

While checking a declaration `d`, Lean's kernel reads:

- `d` itself: its kind, name, universe parameters, type, and value or structure.
- for each constant named in `d`: its name, type and universe parameters, and, for a definition, its body and
  reducibility hints, because the kernel unfolds definitions and the hints steer the order
  (`src/kernel/type_checker.cpp:1000-1006`).
- for each inductive type it meets: the whole block, with its types, constructors and recursor rules.
- the constants it uses by name without `d` naming them (`docs/kernel-builtins.md`).
- the `LEAN_NAT_MAX_SIZE` environment variable, which caps `Nat` literals (`type_checker.cpp:1241-1253`).
- its own code, which is fixed by the Lean commit.

**Theorem proofs.** The kernel can unfold a theorem: `constant_info::has_value()` is true for theorems and
definitions (`src/kernel/declaration.h:447`), and `is_delta` uses it (`type_checker.cpp:547`). An earlier version of
this page cited the `declaration` class instead and said the opposite. Usually a proof cannot change a verdict: proofs
are compared by proof irrelevance before anything is unfolded, recursors never reduce a proof major premise
(`src/kernel/inductive.h:106`), and a projection out of a proof is a proof (`infer_proj`). But `Quot.lift` reduces its
major premise with full `whnf` (`src/kernel/quot.h:59`), and over a quotient in `Prop` that premise can be a theorem.
`test/attacks.py` keeps a case where `liftQ thm = true` holds by `Eq.refl` for one proof of `thm` and fails for another
proof of the same statement.

So keys leave a theorem's proof out of its users' keys, and the replay checks that this is safe instead of assuming
it. It turns on the kernel's diagnostics, which record every constant whose value the kernel reads
(`unfold_definition_core`, `type_checker.cpp:553-570`, the only place the type checker reads another constant's value).
A declaration or inductive block whose check read a theorem gets no stored verdict, and is checked again in every run.

**Opaque constants.** The kernel never unfolds them: no call passes `allow_opaque = true` to `has_value`.

**The budget.** The replay calls the kernel with no heartbeat or recursion budget (`addDeclCore 0 0`), as Lean's
`replay` does, so the verdict does not depend on how long the check takes.

### 2. The key covers all of those inputs

Every constant has two SHA-256 ids (`IncCheck/Hash.lean`):

- Its **interface id** covers what a check of another declaration can read through it: its name, kind, universe
  parameters and type, a definition's body, reducibility hints and safety, and the structure of an inductive type,
  constructor or recursor. It also covers the interface ids of every constant those name, so it is a Merkle hash over
  everything reachable through types and definition bodies.
- Its **declaration id** covers what its own check reads: its interface id, plus a theorem's proof or an opaque
  constant's body and the interface ids of every constant those name.

A check key is the SHA-256 of the key scheme, `Lean.githash` of the running binary, the value of `LEAN_NAT_MAX_SIZE`,
the interface ids of the constants the kernel uses by name, and the declaration id.

Expressions are hashed with each constant referred to by name, and the interface ids of those constants are hashed
alongside. Names matter, because the kernel tells constants apart by name: two axioms `a b : Nat` have the same
content and are still different. An inductive block (its types, constructors and recursors) and a mutual group of
definitions are hashed as one unit, because they refer to each other. Every encoding is tagged and length-prefixed, and
large terms are hashed from the digests of their children, so a proof shared as a DAG costs its size as a DAG.

### 3. What the key leaves out, the kernel ignores

| Left out of the key | Why the kernel's verdict does not change |
|---|---|
| Binder names and binder info | The kernel uses de Bruijn indices and decides nothing by binder info. It compares generated recursors with stored ones by `Expr.eqv`, which ignores both. |
| A theorem's proof, in its users' keys | Checked at run time, as section 1 says. |
| An opaque constant's body, in its users' keys | The kernel never unfolds an opaque constant. |

`mdata` and the `nondep` flag of `let` are in the key. The kernel does not look through an `mdata` node when it
matches a term's shape: `mdata` around a constructor's type makes it reject the inductive type. It also compares
`mdata`, contents included, and `nondep` when it merges nested occurrences of an inductive type
(`src/kernel/inductive.cpp:1070-1079`, `src/kernel/expr_eq_fn.cpp:63`). A `Syntax` value in `mdata` is hashed the way
`Syntax.structEq` compares it, which is how the kernel compares it.

Universe levels are hashed exactly as written, never normalized: the kernel compares some levels syntactically, for
example when it asks whether a type is a `Sort 0`, and it rejects an undeclared parameter even inside `imax w 0`.
Universe parameter names are hashed as written too. Renaming one changes the interface id, so the constant's users are
checked again, which costs time but is never wrong.

### 4. What a single key cannot cover

A key speaks for one declaration. Two facts about the whole run are needed as well, and a key cannot carry them:

- **References are well-founded.** `--fresh` adds a constant only after everything its type and value name, proofs
  included, so it rejects any cycle. Keys leave proofs out of other constants' keys, so two verdicts from separate runs,
  `t1 := t2` with `t2` from an axiom and `t2 := t1` with `t1` from an axiom, would together cover `t1 := t2` and
  `t2 := t1`, a proof of `False`. So the hasher finds every cycle of references, proofs and opaque bodies included,
  with an inductive block as one node, and gives no key to a constant on one (`onCycles` in `IncCheck/Hash.lean`).
  Those go to the kernel, which rejects them as `--fresh` does. A cycle across modules puts the modules in one
  component of the id cache, so the check sees it too.
- **Everything a skipped block inserts was compared.** A block's key covers its stored members, and the run that
  recorded it compared only the safe ones with what the kernel generated. So a block skips only if every member is
  safe, and only the pass before the replay skips: a block it does not insert goes to the kernel.

### 5. Verdicts are recorded only after a complete run

The replay compares the stored constructors and recursors with the ones the kernel generates only after everything
else. Keys are added to the store only if that comparison passes too, so no stored verdict depends on data that the
end of the run rejected.

## The order of the replay and free names

Declarations and inductive blocks with a stored verdict are inserted first, with Lean's `Kernel.Environment.add`, and
without walking their references. That pass is the only place that skips the kernel. The rest are replayed in
dependency order, as Lean's `replay` does, and sent to the kernel.

A check must find every constant it can reach in the environment. A changed declaration can refer to an inserted
definition whose body names a constant that has not been replayed yet, such as `Quot.lift`, or a theorem whose proof
changed. So before a declaration is checked, the replay also walks through each constant that is already present.
For each one it makes the constants that its type, its definition body, or its inductive structure names present
too. A missing constant would make the kernel fail with "unknown constant", which rejects rather than accepts. The walk
leaves out theorem proofs, so a check that reads the proof of a skipped theorem (section 1) can find a constant of that
proof missing. So when the kernel rejects a declaration, the replay first makes present everything the declaration can
reach, proofs included, and sends it to the kernel once more. `--fresh` has all of those constants by then, so the
second answer is the one `--fresh` gives. Lean `v4.36.0` reduces recursors on proofs, and its kernel reads proofs in a
few hundred checks of `Init`, which then run every time. Lean `v4.37.0-rc1` reads none there.

Inserting a constant without the kernel also skips the kernel's check that its name is free, and the order of the
replay differs from Lean's. Neither can make a run accept what `--fresh` rejects, for these reasons:

- Every constant comes from a map keyed by name, and the replay rejects an entry stored under another name, so no
  two constants of a run share a name.
- The kernel generates names of its own only for inductive blocks and quotients. Quotients always go to the kernel. A
  block skips the kernel only if it stores exactly the recursors the kernel generates for it, so every generated name
  is taken by the constant the kernel would have put there (`generatedRecursors` in `IncCheck/Key.lean`).
- While it checks a nested inductive block, the kernel names auxiliary types `_nested.<type>_<i>` and rejects the
  block if a constant already has such a name. A nested block skips the kernel only if no constant of the run is
  named under `_nested`.

## Sharding

`--shard I/N` treats the keys of the modules outside shard `I` as stored, checks the rest, and stores their verdicts.
A shard's acceptance alone proves nothing. The project is checked when one ordinary run accepts with the stores of all
shards concatenated: every key it skips was then recorded by some shard's kernel. Each such verdict is a real kernel
verdict about its own declaration, so the argument above applies unchanged. It needs the cycle check of section 4: a
cycle split across two shards, `t1 := t2` in one and `t2 := t1` in the other, had each shard assume the other half, and
the merged run then skipped both. `test/attacks.py` keeps that case.

## Inductive blocks

The kernel checks an inductive declaration even on its unchecked path, and generates its constructors and recursors
itself. So an inductive block has its own verdict key: a SHA-256 over the check keys of its types, their constructors,
and the recursors whose `all` field names the block's types. The key is recorded after the kernel accepted the block in
a complete run. That run also compared the constructors and recursors the kernel generated with the stored ones. When
the key is in the store, the stored types, constructors and recursors are inserted directly, as importing a module
does, with Lean's `Kernel.Environment.add` (exported as `lean_environment_add`).

A block gets a key only if its stored recursors are exactly `T.rec` for each type `T`, and `rec_1`, `rec_2`, ... after
the first type's name for its nested auxiliary types (`mk_rec_name` and `mk_aux_rec_name_map` in
`src/kernel/inductive.cpp`). `test/KeyProps.lean` checks that this rule names the stored recursors of every block in
`Init`. A block that stores fewer recursors was once skipped with a name the kernel would generate left free for another
constant to take (`test/attacks.py`).

## What is always checked

- **Quotients.** `Quot` and its three companions go to the kernel on every run.
- **Declarations and blocks whose check read a theorem's proof** (section 1).
- **Declarations with an inexact id.** These are declarations with a reference that has no id. In practice there are
  none.
- **Constants on a cycle of references** (section 4).
- **Inductive blocks with a member that has no exact id, that do not store exactly the generated recursors, that have
  an `unsafe` or `partial` member, or that are nested while a constant is named under `_nested`.**
- **Everything, if a constant the kernel uses by name is present without an exact id.** Its content would be in no
  key.
- **Nothing `unsafe` or `partial`.** Those are skipped entirely, as Lean's `replay` does.

## The trusted inputs

- **The verdict store.** A key planted in the store is trusted. `test/attacks.py` plants the key of a proof of `False`
  and shows that the check then accepts it. Protect the store like build credentials. Run with `--no-store` from time
  to time, as Mathlib runs `leanchecker --fresh` daily.
- **The id cache.** A forged cache entry can make a changed module look unchanged, so it needs the same protection.
  A module's cached ids are reused only if its `.olean` files are byte-identical, the ids it refers to in other modules
  are unchanged, its entry names exactly the constants it owns now, and no other module declares one of them too. The
  last rule matters because an import keeps one copy of a theorem that several modules declare, possibly with another
  proof than the copy in the module the name is attributed to. Keys computed with and without the cache are
  byte-identical on the toy project and on Mathlib (`docs/mathlib-results.md`).
- **The `.olean` files, during a run.** `leanchecker` reads each file once. The id cache reads them a second time, to
  digest them after the import. A file swapped between the two reads could make the cache reuse the ids of content
  that was not imported. Do not let anything write the `.olean` files while a run is in progress, and use
  `--no-id-cache` where something might.
- **The Lean toolchain.** As with `leanchecker`.

## The environment of a run

A kernel check can fail for lack of resources: the thread's stack (set by `ulimit -s`, `LEAN_STACK_SIZE_KB` and
`LEAN_MAIN_USE_THREAD`), a memory cap, or `LEAN_NAT_MAX_SIZE`. How much of them a check uses also depends on how terms
share subterms, which the key ignores. Only `LEAN_NAT_MAX_SIZE` is in the key. A verdict recorded with more stack or memory than a later `--fresh` run has could cover a
declaration that the later run fails on for that reason. Such a failure says nothing about the declaration's validity.
`LEAN_NAT_MAX_SIZE` is in the key, because it is a limit the kernel enforces as a rule.

## Evidence

| Test | What it shows |
|---|---|
| `test/KeyProps.lean` (`lake exe inc-key-props`) | Two axioms with the same type give `a = a` and `a = b` different keys. 12 mutations of real declarations of `Init`. For each one, the keys that change are exactly the ones the reference graph says must change. That is thousands for a definition, a statement, a level, a constructor or `mdata`, every key for a constant the kernel uses by name, only the theorem itself for a proof, and none for binder names. The recursor naming rule matches every inductive block of `Init`. |
| `test/attacks.py` | Forged `.olean` files: a constant stored under another name, an inductive type missing from its own `all` field, and `False` proved by `True.intro` are rejected. Runs that check a module against the verdicts of earlier runs, each a shape that an earlier version accepted: `bad : a = b` and `f : A → B` against valid declarations about same-typed axioms and same-shaped inductive types; an axiom named like a recursor that a stored block left out; an axiom named like a nested block's auxiliary type; `CacheX.0 : False` against a cached `CacheX.4294967296`; a duplicated theorem whose proof changed in the later module; a constructor type wrapped in `mdata`; `g = true` through a stored `unsafe` recursor; a theorem that needs a removed, unhashable `Char.ofNat`; `t1 := t2` and `t2 := t1` against two acyclic runs; `2^200 = 2^200` under a smaller `LEAN_NAT_MAX_SIZE`; and `liftQ thm = true` after `thm`'s proof changed. A poisoned store is trusted, and `--no-store` rejects again. |
| `test/scenarios.py` | Edits to a small project re-check exactly the affected declarations, with and without the id cache, and a false theorem added with `debug.skipKernelTC` is rejected. |
| `docs/mathlib-results.md` | Five Mathlib commits, all accepted, with the declarations re-checked matching what changed. |

## Holes found and fixed

| Found | Shape | Fix |
|---|---|---|
| 2026-11-26 | Keys left constant names out, so `bad : a = b` reused the verdict of `good : a = a` | Key scheme 3: names in every id |
| 2026-11-27 | A theorem's proof read through `Quot.lift` over a `Prop` quotient | Kernel diagnostics; no verdict for a check that read a proof |
| 2026-11-27 | A block stored without a generated recursor left its name free for an axiom | Blocks skip only with exactly the generated recursors |
| 2026-11-27 | A skipped nested block missed the kernel's check that its `_nested` auxiliary names are free | Nested blocks skip only while no constant is named under `_nested` |
| 2026-11-27 | `mdata` and `nondep` were left out of the key, though the kernel can see them | Both hashed (key scheme 5) |
| 2026-11-27 | `LEAN_NAT_MAX_SIZE` was not in the key | In the key prefix |
| 2026-11-27 | The id cache truncated numeric name parts to 32 bits | Full-length encoding; entries must name exactly the owned constants |
| 2026-11-27 | The id cache reused a module's ids for a theorem whose imported copy came from another module | Modules that declare a name another module also declares are hashed every run |
| 2026-11-27 | Verdicts of `t1 := t2` and `t2 := t1` from separate runs combined into a cycle proving `False` | No key for a constant on a cycle of references |
| 2026-11-27 | A second skip path inserted a block's stored `unsafe` recursor, which no run had compared | One skip site; blocks skip only with every member safe |
| 2026-11-27 | A constant the kernel uses by name, present but without an exact id, was keyed as absent | No keys at all in that case |

Each row with a test in `test/attacks.py` was run against the code before its fix and failed there.
`docs/audit/decisions.tsv` records the audit that found the 2026-11-27 rows.

## Limits of this argument

- **Section 1 comes from reading** `src/kernel` at `v4.37.0-rc1`, checked by a second, independent reading and by
  probes. It is not a formal proof. The part about proofs does not rest on reading: the replay observes it. A kernel
  change that reads something new would need a matching change to the key, and it would come with a new
  `Lean.githash`, which already separates the stores.
- **The recursor naming rule** follows `mk_aux_rec_name_map` (`src/kernel/inductive.cpp:1179-1204`): one auxiliary
  recursor per auxiliary type, `numNested` of them, named `rec_1`, `rec_2`, ... after the first declared type. A test
  checks it against every block of `Init`, which has only one nested block. A rule that missed a recursor the kernel
  generates would reopen the free-name gap for blocks that leave it out; one that named a recursor the kernel does not
  generate would only stop blocks from skipping.
- **SHA-256 is assumed collision-resistant.**
