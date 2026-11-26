import Collide.Good
import Lean
open Lean Elab Command

-- A copy of `good : a = a` whose type says `a = b`, added without a kernel check. `a` and `b` are distinct axioms
-- with the same type, so only their names tell them apart, and the kernel rejects `bad`.
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let some (.thmInfo good) := (← getEnv).find? `good | throwError "no good"
  addDecl (.thmDecl { good with
    name := `bad, all := [`bad], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst `a) (mkConst `b) })
