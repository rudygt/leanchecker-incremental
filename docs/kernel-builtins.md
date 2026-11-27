# Constants the kernel uses by name

The kernel looks up these constants by name, without the declaration under check referring to them. A check key
must cover them, or a change to one could go unnoticed. Read from `lean4-snap` at `v4.37.0-rc1`.

| Constants | Used for | Source |
|---|---|---|
| `Nat`, `String` | The types of literals | `lean_lit_type`, called from `src/kernel/expr.cpp:70` |
| `Nat.zero`, `Nat.succ` | Converting a `Nat` literal to constructors | `src/kernel/type_checker.cpp:1260`, `src/kernel/inductive.cpp:1380` |
| `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight` | Computing on `Nat` literals with GMP instead of unfolding | `src/kernel/type_checker.cpp:1262-1275` |
| `Bool.true`, `Bool.false` | The results of `Nat.beq` and `Nat.ble` on literals; `Bool.true` also starts a fast path for `decide` | `src/kernel/type_checker.cpp:657`, `:1149-1150`, `:1256`, `src/library/constants.cpp:12-14` |
| `String.ofList`, `Char`, `Char.ofNat`, `List.cons`, `List.nil` | Converting a `String` literal to constructors | `src/kernel/type_checker.cpp:1276`, `src/kernel/inductive.cpp:1384-1391` |
| `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` | Quotient reduction | `src/kernel/quot.cpp:107-113` |
| `eagerReduce` | An annotation that makes the kernel reduce eagerly | `src/kernel/type_checker.cpp:1258` |

Other names the kernel compares do not need to be in the key:

- `Eq` is read by the quotient declaration (`src/kernel/quot.cpp:19-45`), which always goes to the kernel.
- `outParam`, `semiOutParam`, `optParam` and `autoParam` are stripped from the types in an inductive declaration by
  name only (`src/kernel/inductive.cpp:209-216`, `consumeTypeAnnotations`). The declaration must mention them, so its
  own references cover them.
- Names under `_nested` are the kernel's names for the auxiliary types of a nested inductive block. A nested block
  skips the kernel only if no constant is named under `_nested` (`docs/soundness.md`).

A second, independent reading of `src/kernel` on 2026-11-27 found the same list.

`Lean.Kernel.Environment.replay` already replays `String.ofList` and `Char.ofNat` first for the same reason
(`src/Lean/Replay.lean`).

The check key mixes in the interface id of the constant bound to each name, or a marker if the name is absent. If one
of them is present without an exact id, no declaration of the run gets a key, because that constant's content would be
in none. In a normal project all of them come from `Init`, so this adds no invalidation. A forged `.olean` or a
`prelude` module earlier on `LEAN_PATH` can replace them, and the key follows whatever the run imported. A toolchain
change that alters one of them changes every key, which is the intended behavior.
