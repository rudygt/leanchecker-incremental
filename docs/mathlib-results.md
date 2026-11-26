# leanchecker-inc on Mathlib

Measured on 2026-11-26 with Lean `v4.37.0-rc1` on a local WSL machine with 15 GB of memory, under `nice -n 19`.

## Setup

- The baseline is the Mathlib build at `c47f9ad9` that `lake exe cache get` unpacked for the PFR project. The trees of
  later master commits were assembled from Mathlib's cache by `test/mathlib_tree.py`. It hard-links the baseline and
  replaces only the modules whose cache key changed.
- Every run replays all 823,508 constants of `import Mathlib`, including `Init`, `Lean` and the other dependencies,
  into an empty kernel environment, as `leanchecker --fresh Mathlib` does.
- All runs share one verdict store and one id cache, in the order listed.

## Current version

Key scheme 4: the purpose-built hasher (`IncCheck/Hash.lean`), stored verdicts inserted before the replay, inductive
blocks skipped, and `.olean` files hashed in parallel (`-j`, all hardware threads). Measured on 2026-11-26 and 27 while
another Lean build ran on the same machine, with a load average of 3 to 4 on 16 hardware threads.

| Commit | What the store had seen | Theorems and definitions checked | Inductive blocks checked | Keys | Wall | Peak |
|---|---|---:|---:|---:|---:|---:|
| `c47f9ad9` | nothing | 792,580 | 7,287 | 343 s | 35.1 min | 7.9 GB |
| `90e6eec9` | `c47f9ad9` | 13,690 | 58 | 26 s | 4.5 min | 8.3 GB |
| `381d8b16` | up to the previous commit | 3 | 0 | 12.9 s | 26.2 s | 7.5 GB |
| `81cb93dd` | up to the previous commit | 43 | 0 | 10.9 s | 21.4 s | 7.6 GB |
| `06d0af0b` | up to the previous commit | 28 | 0 | | 20.8 s | 7.4 GB |
| `d16077d8` | up to the previous commit | 2 | 0 | 12.8 s | 28.0 s | 7.5 GB |

The four quotient declarations go to the kernel in every run. The kernel accepted every run.

- **The load explains most of the slowdown against the previous version below.** The first run's kernel replay, whose
  code the new hasher does not touch, took about 1,750 s instead of 1,100 s. Hashing the toy project back to back
  under the same load took 18.9 to 20.4 s with the new hasher and 22.7 to 23.3 s with the previous one.
- **A few more declarations are checked than with key scheme 2.** Names are now part of the keys, and renaming a
  universe parameter re-checks its users.
- The id cache for Mathlib is 91 MB and the verdict store 26 MB.

## Key scheme 2, without other load

Key scheme 2, built on CA's ids. Inductive blocks with a stored verdict are skipped, stored declarations are inserted before the replay,
and `.olean` files are hashed in parallel (`-j`, all hardware threads).

| Commit | What the store had seen | Theorems and definitions checked | Inductive blocks checked | Keys | Wall | Peak |
|---|---|---:|---:|---:|---:|---:|
| `c47f9ad9` | nothing | 792,580 | 7,287 | 282 s | 23.2 min | 7.3 GB |
| `3ee314d9` | `c47f9ad9` | 75 | 0 | 39 s | 1.9 min | 7.8 GB |
| `90e6eec9` | up to `3ee314d9` | 13,579 | 58 | 52 s | 5.2 min | 7.5 GB |
| `381d8b16` | up to the previous commit | 2 | 0 | 8.7 s | 16.7 s | 7.5 GB |
| `81cb93dd` | up to the previous commit | 27 | 0 | 9.0 s | 17.4 s | 7.5 GB |
| `06d0af0b` | up to the previous commit | 26 | 0 | 8.5 s | 16.3 s | 7.5 GB |
| `d16077d8` | up to the previous commit | 2 | 0 | 8.9 s | 16.6 s | 7.5 GB |

The four quotient declarations go to the kernel in every run. The kernel accepted every run.

- **`3ee314d9` and `90e6eec9`.** Those rows ran before the last two speed changes and jump over several commits.
  `3ee314d9`'s 75 declarations are the changes of the three commits before it. `90e6eec9`'s 13,579 are mostly its
  refactor of `Preadditive`. An earlier analysis predicted 13,614 for that refactor alone. It followed changed
  constants through types and definition bodies in the full environment.
- **The consecutive commits are the case of checking every commit.** Each takes about 16 seconds, against 21 to 23
  minutes for a full check. About 9 s of that is reading and hashing the `.olean` files and loading the caches. Most
  of the rest is the import and the replay.
- **`06d0af0b`** adds a file, whose 26 declarations are new.

For comparison, Mathlib's daily `leanchecker --fresh Mathlib` takes 20 to 29 minutes on GitHub's runner.

The id cache for Mathlib is 82 MB and the verdict store 23 MB. Computing the ids without the cache takes about 4 to
5 minutes. Keys computed with the cache are byte-identical to those computed without it, cold at `c47f9ad9` and warm at
`a495318f`. In that warm run 11,184 modules were reused and the 6 whose outputs changed were hashed again.

## Earlier runs (key scheme 1)

The first runs used key scheme 1, before inductive blocks could be skipped and before the id cache and the replay
were sped up. The kernel checked all 7,291 inductive types and quotients in every run.

| Commit | Change | Theorems and definitions checked | Ids | Replay | Wall | Peak |
|---|---|---:|---:|---:|---:|---:|
| `c47f9ad9` | none, empty store | 792,580 | 274 s | 967 s | 20.8 min | 9.1 GB |
| `a495318f` | adds `Continuous.re` and similar lemmas | 69 | 294 s | 50 s | 5.8 min | 8.5 GB |
| `7dde1da6` | documentation in `Mathlib.Tactic.Translate` | 4 | 277 s | 65 s | 6.1 min | 7.8 GB |
| `3ee314d9` | removes a `coe` attribute | 0 | 38 s | 70 s | 2.1 min | 8.4 GB |
| `90e6eec9` | 5 commits, including the `Preadditive` refactor | 13,573 | 38 s | 248 s | 4.9 min | 8.7 GB |

- **`a495318f`.** The 69 declarations are the commit's new lemmas and the few declarations that depend on what it
  changed.
- **`7dde1da6`.** Lake rebuilt 8,368 modules for this commit. The kernel checked 4 definitions, the metaprograms
  whose bodies hold the edited text as string literals.
- **`3ee314d9`.** Lake rebuilt 3,799 modules. Nothing the kernel can see changed.
