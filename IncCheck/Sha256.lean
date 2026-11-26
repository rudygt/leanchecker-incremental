namespace IncCheck

/-- SHA-256 in C (`c/sha256.c`). `inc-key-props` checks it against the standard test vectors. -/
@[extern "inc_sha256"]
opaque sha256Native (data : @& ByteArray) : ByteArray

end IncCheck
