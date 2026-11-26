import Std.Data.HashSet

/-!
# Verdict store

A flat file of 32-byte check keys, one per declaration a kernel accepted. The file is only ever appended to, and only
after a run that the kernel accepted completely.
-/

namespace IncCheck

def keySize : Nat := 32

def loadStore (path : System.FilePath) : IO (Std.HashSet ByteArray) := do
  unless ← path.pathExists do return {}
  let bytes ← IO.FS.readBinFile path
  unless bytes.size % keySize == 0 do
    throw <| .userError s!"{path}: size {bytes.size} is not a multiple of {keySize}"
  let mut keys : Std.HashSet ByteArray := {}
  for i in [0:bytes.size / keySize] do
    keys := keys.insert (bytes.extract (i * keySize) ((i + 1) * keySize))
  return keys

def appendStore (path : System.FilePath) (keys : Array ByteArray) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.withFile path .append fun h => do
    for k in keys do
      unless k.size == keySize do throw <| .userError s!"refusing to store a key of {k.size} bytes"
      h.write k

end IncCheck
