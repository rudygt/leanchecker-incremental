import IncCheck.CA.SHA256

namespace IncCheck

/-- SHA-256 in C (`c/sha256.c`). Same digests as `CA.SHA256.sha256Pure`. -/
@[extern "inc_sha256"]
opaque sha256Native (data : @& ByteArray) : ByteArray

def nativeHasher : CA.SHA256.Hasher := fun data => pure (sha256Native data)

end IncCheck
