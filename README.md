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
Mathlib, 823,508 declarations, on one machine, with the previous key scheme (`docs/mathlib-results.md`):

| Mathlib commit | Kernel checks of definitions and theorems | Time |
|---|---:|---:|
| First run, empty store | 792,580 | 20.8 min |
| `3ee314d9`, a coercion attribute removed (Lake rebuilt 3,799 modules) | 0 | 2.1 min |
| `7dde1da6`, documentation edits (Lake rebuilt 8,368 modules) | 4 | 6.1 min, before the id cache |
| `90e6eec9`, five commits including a refactor of `Preadditive` | 13,573 | 4.9 min |

The kernel accepted every run.

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
| `-q`, `--quiet` | Print only the result. |
| `--log-checked FILE` | Write the names of the axioms, definitions, theorems and opaques the kernel checked. |
| `--dump-keys FILE` | Write every check key as `name hex` lines. |
| `--hash-only` | Compute the keys and stop before the replay. |
| `--pure-sha` | Hash with the pure-Lean SHA-256 instead of `c/sha256.c`. The keys are identical. |

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
reads while checking it: the declaration, the statements of the theorems it uses, the full content of the other
constants it uses (definitions with their bodies and reducibility hints, inductive types with their constructors and
recursors), the constants the kernel uses by name, and the Lean commit. So a changed proof re-checks only its own
theorem, and a changed definition re-checks everything that can see its body.

The store and the id cache are trusted inputs. Keep them where only this tool writes, and run with `--no-store` from
time to time. `docs/soundness.md` gives the full argument, what it rests on, and the tests behind it.

## Limitations

- **The first run costs a full check.** On Mathlib that is about 21 minutes and up to 9 GB of memory, one thread.
- **Every run has a fixed cost.** On Mathlib it is about 2 minutes: importing, reading and hashing about 6 GB of
  `.olean` files, and re-checking the 7,291 inductive types and quotients, which the kernel checks even when asked
  not to.
- **The id cache is large.** For Mathlib it is about 300 MB.
- **It must match the project's Lean version exactly.** It reads `.olean` files and calls Lean's kernel.

## How it works

`leanchecker-inc` imports the modules, computes a check key for every declaration, and replays every declaration into
an empty kernel environment with the replay code of Lean's `leanchecker`. A definition, theorem, axiom or opaque whose
key is in the store is added with `addDeclWithoutChecking`. Everything else goes to the kernel. The new keys are added
to the store only after the whole replay succeeds.

The keys build on [CA](https://github.com/proofinity-it/CA), which gives every Lean declaration a SHA-256 id derived
from its content, with each constant it refers to replaced by that constant's own id. This repository vendors CA's
hashing modules, with two changes that make the ids follow exactly what the kernel reads (`IncCheck/CA/VENDORED.md`).

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

- `IncCheck/CA/` is vendored from [proofinity-it/CA](https://github.com/proofinity-it/CA) (Apache-2.0).
- `IncCheck/Replay.lean` is adapted from `src/Lean/Replay.lean` in [Lean 4](https://github.com/leanprover/lean4)
  (Apache-2.0).
