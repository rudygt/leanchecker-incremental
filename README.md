# leanchecker-incremental

[![test](https://github.com/rudygt/leanchecker-incremental/actions/workflows/test.yml/badge.svg)](https://github.com/rudygt/leanchecker-incremental/actions/workflows/test.yml)

`leanchecker-inc` checks a Lean project with Lean's kernel, the way `leanchecker --fresh` does. It also keeps the
kernel's past verdicts, and sends a declaration to the kernel only if something the kernel would read while checking
it has changed since a verdict was recorded.

Status: experimental, and not reviewed by Lean's maintainers. It is tested with Lean `v4.36.0` and `v4.37.0-rc1`.

## Why

Mathlib re-checks everything with Lean's kernel once a day (`lake env leanchecker --fresh Mathlib`). That run takes
20 to 29 minutes on GitHub's runners, and Mathlib merges dozens of commits a day, so the check cannot run on every
commit. Most commits change very few declarations that the kernel can see. These are measured runs over all of
Mathlib, 823,508 declarations, on one machine (`docs/mathlib-results.md`):

| Mathlib commit | Kernel checks of definitions and theorems | Time |
|---|---:|---:|
| `c47f9ad9`, first run, empty store | 792,580 | 23.2 min |
| `381d8b16`, removes a coercion (Lake rebuilt 3,580 modules) | 2 | 16.7 s |
| `81cb93dd`, adds a lemma about `WfDvdMonoid` | 27 | 17.4 s |
| `06d0af0b`, adds a file | 26 | 16.3 s |
| `d16077d8`, makes an instance global (Lake rebuilt 2,081 modules) | 2 | 16.6 s |

Each commit after the first was checked against the verdicts of the commit before it. The kernel accepted every run.

## Use it in a project

The checker reads `.olean` files, so it must be built with the same Lean version as the project. Add it as a Lake
dependency, and Lake builds it with the project's toolchain. CI runs the full test suite on `v4.37.0-rc1` and the
scenarios on `v4.36.0`. Keys include the Lean commit, so verdicts never carry over from one Lean version to another.
Before trusting it on a newer Lean, check that the kernel uses no new constants by name (`docs/kernel-builtins.md`).

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
lake exe leanchecker-inc Mathlib Archive # or the modules you name, in one environment
```

The first run checks every declaration. Later runs send only changed declarations to the kernel. The verdict store
and the id cache live in `.lake/leanchecker-inc/`. The exit code is 0 when the kernel accepts everything, 1 when it
rejects something, and 2 for usage errors.

| Option | Effect |
|---|---|
| `--store FILE` | Use `FILE` as the verdict store instead of `.lake/leanchecker-inc/verdicts.bin`. |
| `--no-store` | Check every declaration, and neither read nor write a store. |
| `--no-record` | Read the store but do not add new verdicts. |
| `--id-cache FILE` | Use `FILE` as the id cache instead of `.lake/leanchecker-inc/ids.bin`. |
| `--no-id-cache` | Hash every declaration again. The keys are the same as with the cache. |
| `-j N`, `--threads N` | Read and hash `.olean` files with `N` threads (default: all hardware threads). |
| `-q`, `--quiet` | Print only the result. |
| `--log-checked FILE` | Write the names of the declarations the kernel checked, and `inductive T` for each inductive block. |
| `--dump-keys FILE` | Write every check key as `name hex` lines. |
| `--hash-only` | Compute the keys and stop before the replay. |

## Use it in CI

The store has to persist between runs. On GitHub Actions, a cache works. Let only runs on the default branch save
it: a pull request can then read the default branch's verdicts, but can never write to them. The following workflow
is an example built from the commands above. It has not been run as written.

```yaml
name: kernel check
on:
  push:
    branches: [main]
  pull_request:
  schedule:
    - cron: "0 3 * * 0"   # weekly, without the store
jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with:
          auto-config: false
      - run: lake build
      - uses: actions/cache/restore@v4
        with:
          path: .lake/leanchecker-inc
          key: leanchecker-inc-${{ hashFiles('lean-toolchain') }}-${{ github.sha }}
          restore-keys: leanchecker-inc-${{ hashFiles('lean-toolchain') }}-
      - run: lake exe leanchecker-inc ${{ github.event_name == 'schedule' && '--no-store' || '' }}
      - if: github.ref == 'refs/heads/main' && github.event_name == 'push'
        uses: actions/cache/save@v4
        with:
          path: .lake/leanchecker-inc
          key: leanchecker-inc-${{ hashFiles('lean-toolchain') }}-${{ github.sha }}
```

## What it guarantees

If the verdict store and the id cache were written only by this tool, `leanchecker-inc` accepts a project only if
replaying every declaration with Lean's kernel would accept it. It is never weaker than `leanchecker --fresh` with the
same kernel. On two shapes of forged `.olean` that Lean fixed after `v4.37.0-rc1` it is stricter, because it carries
those fixes. It is not stronger in any other way. Like `leanchecker`, it trusts that Lean's prelude is Lean's
prelude, so for adversarial settings use `lake comparator` or an external checker.

A declaration skips the kernel when its check key is in the store. The key is a SHA-256 over everything the kernel
reads while checking it: the declaration, the names and statements of the theorems it uses, the names and full
content of the other constants it uses (definitions with their bodies and reducibility hints, inductive types with
their constructors and recursors), the constants the kernel uses by name, and the Lean commit. So a changed proof re-checks only its own
theorem, and a changed definition re-checks everything that can see its body.

The store and the id cache are trusted inputs. Keep them where only this tool writes, and run with `--no-store` from
time to time. `docs/soundness.md` gives the full argument, what it rests on, and the tests behind it.

Versions up to commit `e177201` (key schemes 1 and 2) left the names of referenced constants out of the keys. Those
versions accepted a proof of `a = b` for two axioms `a b : Nat` when the store held the verdict of a proof of `a = a`.
Key scheme 3 fixes it. Stores and id caches written by older versions are ignored, because every key and the cache
header include the key scheme.

## Limitations

- **The first run costs a full check.** On Mathlib that is about 23 minutes and up to 8 GB of memory. The kernel runs
  on one thread.
- **Every run imports everything.** On Mathlib a run with nothing to check still takes about 16 seconds and 7.5 GB,
  mostly to import Mathlib and read and hash its `.olean` files.
- **It must match the project's Lean version exactly.** It reads `.olean` files and calls Lean's kernel.

## How it works

`leanchecker-inc` imports the modules and computes a check key for every declaration. It inserts every declaration
and inductive block whose key is in the store into an empty kernel environment, as an import would. Then it replays
the rest with the replay code of Lean's `leanchecker`, which sends each one to the kernel. The new keys are added to
the store only after the whole replay succeeds.

The keys come from `IncCheck/Hash.lean`. Every constant gets an interface id, which covers what other declarations
can see through it (its type, a definition's body, an inductive type's structure, and the interface ids of everything
those name), and a declaration id, which adds what only its own check reads, such as a theorem's proof. Expressions are
hashed with constants referred to by name, because the kernel tells constants apart by name. An earlier version built
on [CA](https://github.com/proofinity-it/CA), whose ids leave names out on purpose, and could be fooled by that
(`docs/soundness.md`).

Hashing every declaration of Mathlib, proofs included, takes about 5 minutes. The id cache avoids most of it. For each
module it records a SHA-256 of the module's `.olean` files, the ids of its declarations, and the ids of the outside
constants they refer to, and reuses the module's ids when none of those changed. Lean can copy a constant it
generates on demand, such as an equation lemma, into several modules. So modules are hashed in the order of the
references between them, not in import order. On Mathlib the cached keys are byte-identical to uncached ones.

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

## License and credits

Apache License 2.0, see `LICENSE` and `NOTICE`.

- The idea of Merkle ids over Lean declarations comes from [CA](https://github.com/proofinity-it/CA). Versions up to
  `b568494` vendored its hashing modules. No CA code remains.
- `IncCheck/Replay.lean` is adapted from `src/Lean/Replay.lean` in [Lean 4](https://github.com/leanprover/lean4)
  (Apache-2.0).
