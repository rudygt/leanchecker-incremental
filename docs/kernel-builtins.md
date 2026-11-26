# Constants the kernel uses by name

The kernel looks up these constants by name, without the declaration under check referring to them. A check key
must cover them, or a change to one could go unnoticed. Read from `lean4-snap` at `v4.37.0-rc1`.

| Constants | Used for | Source |
|---|---|---|
| `Nat`, `String` | The types of literals | `lean_lit_type`, called from `src/kernel/expr.cpp:70` |
| `Nat.zero`, `Nat.succ` | Converting a `Nat` literal to constructors | `src/kernel/type_checker.cpp:1260`, `src/kernel/inductive.cpp:1380` |
| `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight` | Computing on `Nat` literals with GMP instead of unfolding | `src/kernel/type_checker.cpp:1262-1275` |
| `Bool.true` | The result of `Nat.beq` and `Nat.ble` on literals | `src/kernel/type_checker.cpp:1256` |
| `String.ofList`, `Char`, `Char.ofNat`, `List.cons`, `List.nil` | Converting a `String` literal to constructors | `src/kernel/type_checker.cpp:1276`, `src/kernel/inductive.cpp:1384-1391` |
| `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` | Quotient reduction | `src/kernel/quot.cpp:107-113` |
| `eagerReduce` | An annotation that makes the kernel reduce eagerly | `src/kernel/type_checker.cpp:1258` |

`Lean.Kernel.Environment.replay` already replays `String.ofList` and `Char.ofNat` first for the same reason
(`src/Lean/Replay.lean`).

The check key mixes in the interface id of the constant bound to each name, or a marker if the name is absent. All of these
live in `Init`, which no project can redefine, so this adds no invalidation in practice. A toolchain change that alters
one of them changes every key, which is the intended behavior.
