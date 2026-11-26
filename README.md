# leanchecker-incremental

`leanchecker-inc` re-checks a Lean module and everything it imports with Lean's kernel, like `leanchecker --fresh`.
It also keeps a store of the kernel's past verdicts, and skips the kernel for every declaration whose check key is
already in it.

Status: experimental. On Mathlib, after a 20.8-minute first run,
a commit that changes no declaration the kernel can see takes 2.1 minutes, and the kernel accepted every run
(`docs/mathlib-results.md`). The constants the kernel uses by name are listed in `docs/kernel-builtins.md`.

## Use it in a project

The checker reads `.olean` files, so it must be built with the same Lean version as the project. Add it as a Lake
dependency, and Lake builds it with the project's toolchain. The `master` branch tracks Lean `v4.37.0-rc1`.

```toml
# lakefile.toml
[[require]]
name = "leanchecker-incremental"
git = "https://github.com/rudygt/leanchecker-incremental"
rev = "master"
```

Then build the project and check it:

```sh
lake update leanchecker-incremental
lake build
lake exe leanchecker-inc                 # checks the project's root module
lake exe leanchecker-inc Mathlib Archive # or the modules you name, together
```

The first run checks every declaration, like `leanchecker --fresh`. Later runs send only changed declarations to the
kernel. The verdict store and the id cache live in `.lake/leanchecker-inc/`.

| Option | Effect |
|---|---|
| `--store FILE` | Use `FILE` as the verdict store instead of `.lake/leanchecker-inc/verdicts.bin`. |
| `--no-store` | Check every declaration, and neither read nor write a store. |
| `--no-record` | Read the store but do not add new verdicts. |
| `--id-cache FILE` | Use `FILE` as the id cache instead of `.lake/leanchecker-inc/ids.bin`. |
| `--no-id-cache` | Hash every declaration again. The keys are the same as with the cache. |
| `-q`, `--quiet` | Print only the result. |
| `--log-checked FILE` | Write the names of the axioms, definitions, theorems and opaques the kernel checked. |
| `--dump-keys FILE` | Write every check key as `name hex` lines. |
| `--hash-only` | Compute the keys and stop before the replay. |
| `--pure-sha` | Hash with the pure-Lean SHA-256 instead of `c/sha256.c`. The keys are identical. |

The exit code is 0 when the kernel accepts everything, 1 when it rejects something, and 2 for usage errors.

## What it guarantees

If the verdict store and the id cache were written only by this tool, `leanchecker-inc` accepts a project only if
replaying every declaration with Lean's kernel would accept it. It is never weaker than `leanchecker --fresh` with the
same kernel. On two shapes of forged `.olean` that Lean fixed after `v4.37.0-rc1` it is stricter, because it carries
those fixes. It is not stronger in any other way. Like `leanchecker`, it trusts that Lean's prelude is Lean's
prelude, so for adversarial settings use `lake comparator` or an external checker.

A declaration skips the kernel when its check key is in the store. The key is a SHA-256 over everything the kernel
reads while checking it: the declaration, the statements of the theorems it uses, the full content of the other
constants it uses (definitions with their bodies and reducibility hints, inductive types with their constructors and
recursors), the constants the kernel uses by name, and the Lean commit. So a changed proof re-checks only its own
theorem, and a changed definition re-checks everything that can see its body. Inductive types and quotients are
checked on every run.

The store and the id cache are trusted inputs. Keep them where only this tool writes, and run with `--no-store` from
time to time. `docs/soundness.md` gives the full argument, what it rests on, and the tests behind it.

## The id cache

Hashing all of Mathlib, proofs included, takes about 5 minutes. The id cache records, for each module, a SHA-256 of
its `.olean` files, the CA ids of its constants, and the `ref` ids of the constants in other modules that it refers
to. A module is reused when its files and those outside ids are unchanged. Modules are visited in the order of the
references between them, not in import order: constants generated on demand, such as equation lemmas and `match`
splitters, can be copied into several modules, and the environment can take a copy from a module that comes after one
that uses it. Modules that refer to each other are hashed together, and each name is hashed once, in the module the
environment took it from.

## Tests

```sh
lake exe inc-key-props               # key mutation tests over the declarations of Init (about 3 minutes)
python3 test/attacks.py              # forged .olean files and a poisoned store (about 5 minutes)
python3 test/scenarios.py            # edits to test/toy (add --id-cache to use the id cache)
```

- **`inc-key-props`** changes one real declaration of `Init` at a time. It checks that exactly the keys the reference
  graph predicts change. That is thousands for a changed definition, statement, level or constructor, every key for a
  constant the kernel uses by name, only the theorem itself for a changed proof, and none for binder names or `mdata`.
- **`attacks.py`** checks that forged `.olean` files are rejected, compares with the toolchain's `leanchecker
  --fresh`, and shows that a poisoned store is trusted while `--no-store` rejects.
- **`scenarios.py`** edits a small project and checks which declarations reach the kernel: none after an unchanged
  build or a proof edit that only renames binders, one after a real proof change, exactly the dependents after a
  definition change. A false theorem added with `debug.skipKernelTC` is rejected.

`test/mathlib_tree.py` and `test/run_commits.sh` rebuild the trees of later Mathlib master commits from Mathlib's
cache on top of an existing Mathlib build, and run the checker on them. Set `INCCHECK_PFR` to a Lake project whose
`.lake/packages/mathlib` holds the build of `c47f9ad9`.

## Sources

- `IncCheck/CA/` is vendored from [proofinity-it/CA](https://github.com/proofinity-it/CA), Apache-2.0. See `IncCheck/CA/VENDORED.md`.
- `IncCheck/Replay.lean` is adapted from `src/Lean/Replay.lean` in Lean 4, Apache-2.0.
