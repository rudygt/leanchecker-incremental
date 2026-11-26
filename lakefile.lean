import Lake
open System Lake DSL

package «leanchecker-incremental»

input_file sha256.c where
  path := "c" / "sha256.c"
  text := true

target sha256.o pkg : FilePath := do
  let srcJob ← sha256.c.fetch
  let oFile := pkg.buildDir / "c" / "sha256.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O3"] (← getLeanc) getLeanTrace

target libincsha pkg : FilePath := do
  let o ← sha256.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "incsha") #[o]

/-- The checker, including the content-addressing modules vendored from CA under `IncCheck.CA`
(see `IncCheck/CA/VENDORED.md`). -/
lean_lib IncCheck where
  globs := #[.submodules `IncCheck]
  moreLinkObjs := #[libincsha]

@[default_target]
lean_exe «leanchecker-inc» where
  root := `IncCheck.Main

/-- Mutation tests for check keys (`test/KeyProps.lean`). -/
lean_exe «inc-key-props» where
  root := `KeyProps
  srcDir := "test"

/-- Writes forged `.olean` files for `test/attacks.py`. -/
lean_exe «inc-forge» where
  root := `Forge
  srcDir := "test"
