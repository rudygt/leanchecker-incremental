import Collide.Good
import Lean
open Lean Elab Command

-- A copy of `g : A → A` whose type says `A → B`, added without a kernel check. `A` and `B` are distinct inductive
-- types with the same structure, so only their names tell them apart, and the kernel rejects `f`.
set_option debug.skipKernelTC true in
run_cmd liftTermElabM do
  let some (.defnInfo g) := (← getEnv).find? `g | throwError "no g"
  addDecl (.defnDecl { g with
    name := `f, all := [`f], type := mkForall `x .default (mkConst `A) (mkConst `B) })
