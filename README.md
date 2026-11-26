# leanchecker-incremental

`leanchecker-inc` re-checks a Lean module and everything it imports with Lean's kernel, like `leanchecker --fresh`.
It also keeps a store of the kernel's past verdicts, and skips the kernel for every declaration whose check key is
already in it. The plan and the measurements behind it are in LeanMR, under `research/incremental-leanchecker/`.

Status: experimental. It passes the toy scenarios in `test/scenarios.py` and has not run on Mathlib yet.

## Build and run

The toolchain is Lean `v4.37.0-rc1`.

```sh
lake build
cd path/to/project
lake env /path/to/leanchecker-incremental/.lake/build/bin/leanchecker-inc --store verdicts.bin MyProject
```

| Flag | Effect |
|---|---|
| `--store FILE` | Skip the kernel for declarations whose key is in `FILE`. After a run that succeeds completely, append the new verdicts. |
| `--no-record` | Read the store but never write it. |
| `--log-checked FILE` | Write the names of the axioms, definitions, theorems and opaques the kernel checked. |
| `--dump-keys FILE` | Write every check key as `name hex` lines. |
| `--pure-sha` | Hash with CA's pure-Lean SHA-256 instead of `c/sha256.c`. The keys are identical. |

The exit code is 0 when the kernel accepts everything, 1 when it rejects something, and 2 for usage errors.

## When the kernel is skipped

A check key hashes the key scheme, `Lean.githash` of the running binary, the ids of the constants the kernel uses by
name (`IncCheck.kernelBuiltins`), and CA's `decl` id of the declaration. The `decl` id covers the declaration's type,
value and structural fields. References inside it are replaced by their `ref` ids: the statement for a theorem, the
whole declaration otherwise. So a key changes when anything the kernel can observe while checking the declaration
changes, and stays the same when only a proof the declaration uses changes.

Only axioms, definitions, theorems and opaques can be skipped. The kernel checks inductive types and quotients on every
run, and the replay compares stored constructors and recursors with the ones the kernel generates. The tool computes
every key from the declarations it loads. It never reads a key from a build file. The store is the only new input
the check trusts.

## Tests

```sh
python3 test/scenarios.py
```

The script edits `test/toy`, rebuilds it, and checks which declarations reach the kernel: none after an unchanged
build, none after a proof edit that only renames binders, one after a real proof change, exactly the dependents after
a definition change, and a rejection for a false theorem added with `debug.skipKernelTC`.

## Sources

- `CA/` is vendored from [proofinity-it/CA](https://github.com/proofinity-it/CA), Apache-2.0. See `CA/VENDORED.md`.
- `IncCheck/Replay.lean` is adapted from `src/Lean/Replay.lean` in Lean 4, Apache-2.0.
