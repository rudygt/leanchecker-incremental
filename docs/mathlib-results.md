# leanchecker-inc on Mathlib

First results of `leanchecker-inc`, measured on 2026-11-26. Lean `v4.37.0-rc1`,
one thread under `nice -n 19`, on the local WSL machine.

## Setup

- The baseline is the Mathlib build at `c47f9ad9` that `lake exe cache get` unpacked for the PFR project. The trees of later master commits were assembled from Mathlib's
  cache by `test/mathlib_tree.py`, which hard-links the baseline and replaces only the modules whose cache key changed.
- Every run replays all 823,508 constants of `import Mathlib`, including `Init`, `Lean` and the other dependencies,
  into an empty kernel environment, as `leanchecker --fresh Mathlib` does.
- Runs share one verdict store (`--store`). The last two also use the id cache (`--id-cache`).

## Runs

| Commit | Change | Theorems and definitions checked | Ids | Replay | Wall | Peak |
|---|---|---:|---:|---:|---:|---:|
| `c47f9ad9` | none, empty store | 792,580 | 274 s | 967 s | 20.8 min | 9.1 GB |
| `a495318f` | adds `Continuous.re` and similar lemmas | 69 | 294 s | 50 s | 5.8 min | 8.5 GB |
| `7dde1da6` | documentation in `Mathlib.Tactic.Translate` | 4 | 277 s | 65 s | 6.1 min | 7.8 GB |
| `3ee314d9` | removes a `coe` attribute | 0 | 38 s | 70 s | 2.1 min | 8.4 GB |
| `90e6eec9` | 5 commits, including the `Preadditive` refactor | 13,573 | 38 s | 248 s | 4.9 min | 8.7 GB |

The kernel also checked the same 7,291 inductive types and quotients in every run. It checks those even when asked not
to. The kernel accepted every run.

- **`a495318f`.** The 69 declarations are the commit's new lemmas and the few declarations that depend on what it
  changed.
- **`7dde1da6`.** Lake rebuilt 8,368 modules for this commit. The kernel checked 4 definitions, the metaprograms
  whose bodies hold the edited text as string literals.
- **`3ee314d9`.** Lake rebuilt 3,799 modules. Nothing the kernel can see changed.
- **`90e6eec9`.** An earlier analysis, which followed changed constants through types and definition bodies in
  the full environment, predicted 13,614 declarations to re-check for this refactor alone.

For comparison, Mathlib's daily `leanchecker --fresh Mathlib` takes 20 to 29 minutes on GitHub's runner.

## The id cache

Without the cache, computing the ids of all 823,508 constants, proofs included, takes 254 to 297 s. The cache keeps
each module's ids together with a digest of its `.olean` files and the ids of the outside constants it refers to.

- **Cold.** At `c47f9ad9` the cache produced the same 823,508 keys as the uncached computation, byte for byte.
- **Warm.** At `a495318f` it reused 11,184 modules and re-hashed 6, the 6 modules whose outputs changed. Its keys
  were again byte-identical to an uncached run at the same commit. Ids took 33 s instead of 297 s.
- **Size.** The file is 319 MB, because every constant's name is stored in full.

## What costs time now

- **Inductive types.** Re-checking the 7,291 inductive types and quotients takes 50 to 70 s per run.
  `addDeclWithoutChecking` checks inductive types anyway. Skipping them needs a kernel entry point that adds the
  generated constants directly, which only the fork can add.
- **Digests and the cache.** The 38 s of id work is mostly reading and hashing about 6 GB of `.olean` files and
  loading the 319 MB cache. Hashing in parallel and storing names once would cut both.
- **Import.** It takes 2 to 23 s, depending on whether the files are in the page cache.
