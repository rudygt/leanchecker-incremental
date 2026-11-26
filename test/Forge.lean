import Lean

/-!
Writes forged `.olean` files for `test/attacks.py`. Usage: `inc-forge DIR`.

* `ForgedNameMismatch`: a theorem stored under a name other than its own (the shape of lean4#16675).
* `ForgedInductive`: an inductive type that is not listed in its own `all` field (the shape fixed in lean4#16717).
* `ForgedFalse`: the theorem `False`, proved by `True.intro`, which only the kernel can reject.
-/

open Lean

def module (constants : Array ConstantInfo) (names : Array Name := constants.map (·.name)) : ModuleData :=
  { isModule := false, imports := #[{ module := `Init }], constNames := names, constants,
    extraConstNames := #[], entries := #[] }

def thm (name : Name) (type value : Expr) : ConstantInfo :=
  .thmInfo { name, levelParams := [], type, value, all := [name] }

def main (args : List String) : IO Unit := do
  let [dir] := args | throw <| .userError "usage: inc-forge DIR"
  IO.FS.createDirAll dir
  let write (mod : Name) (data : ModuleData) : IO Unit :=
    saveModuleDataParts mod #[((dir : System.FilePath) / s!"{mod}.olean", data)]
  write `ForgedNameMismatch <|
    module #[thm `forgedActual (mkConst ``True) (mkConst ``True.intro)] (names := #[`forgedListed])
  write `ForgedInductive <| module #[.inductInfo {
    name := `ForgedInd, levelParams := [], type := mkSort levelOne, numParams := 0, numIndices := 0,
    all := [], ctors := [], numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }]
  write `ForgedFalse <| module #[thm `forgedFalse (mkConst ``False) (mkConst ``True.intro)]
