# leanchecker-incremental

`leanchecker-inc` re-checks a Lean module and everything it imports with Lean's kernel, like `leanchecker --fresh`.
It also keeps a store of the kernel's past verdicts, and skips the kernel for every declaration whose check key is
already in it.

Status: experimental. It passes the toy scenarios in `test/scenarios.py`. On Mathlib, after a 20.8-minute first run,
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

## When the kernel is skipped

A check key hashes the key scheme, `Lean.githash` of the running binary, the ids of the constants the kernel uses by
name (`IncCheck.kernelBuiltins`), and CA's `decl` id of the declaration. The `decl` id covers the declaration's type,
value and structural fields. References inside it are replaced by their `ref` ids: the statement for a theorem, the
whole declaration otherwise. So a key changes when anything the kernel can observe while checking the declaration
changes, and stays the same when only a proof the declaration uses changes.

Only axioms, definitions, theorems and opaques can be skipped. The kernel checks inductive types and quotients on every
run, and the replay compares stored constructors and recursors with the ones the kernel generates. The tool computes
every key from the declarations it loads. It never reads a key from a build file. The store and the id cache are the
only new inputs the check trusts. Keep them where only the checker writes, and run a full check without them from
time to time.

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
python3 test/scenarios.py            # add --id-cache to run them through the id cache
```

The script edits `test/toy`, rebuilds it, and checks which declarations reach the kernel: none after an unchanged
build, none after a proof edit that only renames binders, one after a real proof change, exactly the dependents after
a definition change, and a rejection for a false theorem added with `debug.skipKernelTC`.

`test/mathlib_tree.py` and `test/run_commits.sh` rebuild the trees of later Mathlib master commits from Mathlib's
cache on top of an existing Mathlib build, and run the checker on them. Set `INCCHECK_PFR` to a Lake project whose
`.lake/packages/mathlib` holds the build of `c47f9ad9`.

## Sources

- `IncCheck/CA/` is vendored from [proofinity-it/CA](https://github.com/proofinity-it/CA), Apache-2.0. See `IncCheck/CA/VENDORED.md`.
- `IncCheck/Replay.lean` is adapted from `src/Lean/Replay.lean` in Lean 4, Apache-2.0.
