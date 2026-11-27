import QuotProof.Lib
import Lean
open Lean Elab Command

-- `liftQ thm = true` by `Eq.refl true`, checked only by the kernel. It holds only while `thm` is proved by `Quot.mk`.
run_cmd liftTermElabM do
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp (mkConst ``liftQ) (mkConst ``thm)) (mkConst ``Bool.true)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  addDecl (.thmDecl { name := `quotUse, levelParams := [], type := ty, value := val })
