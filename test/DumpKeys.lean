import Cache.Hashing
open Lean Cache.IO Cache.Hashing

/-- Print `module cacheFile` for every module the Mathlib cache covers, using the sources in `LEAN_SRC_PATH`. -/
def main : IO Unit := CacheM.run do
  let src ← Lean.findLean (← read).srcSearchPath `Mathlib
  let memo ← getHashMemo ((∅ : Std.HashMap Name System.FilePath).insert `Mathlib src)
  for (m, h) in memo.hashMap do
    IO.println s!"{m} {h.asLTar}"
