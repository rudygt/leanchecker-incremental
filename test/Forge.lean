import Lean

/-!
Writes forged `.olean` files for `test/attacks.py`. Usage: `inc-forge DIR`.

* `ForgedNameMismatch`: a theorem stored under a name other than its own (the shape of lean4#16675).
* `ForgedInductive`: an inductive type that is not listed in its own `all` field (the shape fixed in lean4#16717).
* `ForgedFalse`: the theorem `False`, proved by `True.intro`, which only the kernel can reject.
* `ForgedBlockNoRec`: an inductive type stored without the recursor the kernel generates for it.
* `ForgedBlockRecAxiom`: the same type, with an axiom that takes the name of that recursor.

Two versions of a module set go to `DIR/v1` and `DIR/v2`, for attacks on the id cache. A module that is meant to stay
unchanged is written with the same data to both, so its files are byte-identical:

* `CacheBase` and `CacheTop` (which imports it): `CacheTop` proves `CacheX.4294967296 : True`. Version 2 adds
  `CacheX.0 : False`, proved by `True.intro`, to `CacheBase`.
* `DupA` and `DupB`: both declare `dupThm : True`, which an import allows because only the proofs may differ. Version 2
  changes `DupB`'s proof to `Nat.zero`, which only the kernel rejects. `DupA` stays the same.
* `MdBlock`: the inductive type `MdT` with one constructor, its constants as the kernel generates them. Version 2 wraps
  the constructor's type in `mdata`, which the kernel rejects.
* `URec`: an inductive type stored with an `unsafe` recursor whose rule returns `true`, and `g : Bool`, which reduces to
  `false` with the recursor the kernel generates. Version 2 adds `bad : g = true`.
* `P`: a prelude without `Init`, with `Char.ofNat` made unhashable by a missing name in its `all` field, and a theorem
  whose check reduces a string literal through `Char.ofNat`. Version 2 drops `Char.ofNat`.

Other sets, one module each:

* `N1` holds the nested inductive type `NT`, and `N2` adds an axiom with the name of an auxiliary type the kernel makes
  while it checks `NT`.
* `BigLit` proves `2^200 = 2^200` with literals, which the kernel accepts only while `LEAN_NAT_MAX_SIZE` allows them.
* `ShardA` proves `t1 : False` by `t2`, and `ShardB` proves `t2 : False` by `t1`, so that `--shard` can split the cycle
  across two shards.
* `c1`, `c2` and `c3` each hold a module `Circ`: `t1 : False` from an axiom and `t2` from `t1`, the same the other way
  round, and then `t1 := t2` and `t2 := t1` with no axiom.
-/

open Lean

def module (constants : Array ConstantInfo) (names : Array Name := constants.map (·.name))
    (imports : Array Name := #[`Init]) : ModuleData :=
  { isModule := false, imports := imports.map ({ module := · }), constNames := names, constants,
    extraConstNames := #[], entries := #[] }

def thm (name : Name) (type value : Expr) : ConstantInfo :=
  .thmInfo { name, levelParams := [], type, value, all := [name] }

def main (args : List String) : IO Unit := do
  let [dir] := args | throw <| .userError "usage: inc-forge DIR"
  initSearchPath (← findSysroot)
  IO.FS.createDirAll dir
  let write (mod : Name) (data : ModuleData) : IO Unit :=
    saveModuleDataParts mod #[((dir : System.FilePath) / s!"{mod}.olean", data)]
  write `ForgedNameMismatch <|
    module #[thm `forgedActual (mkConst ``True) (mkConst ``True.intro)] (names := #[`forgedListed])
  write `ForgedInductive <| module #[.inductInfo {
    name := `ForgedInd, levelParams := [], type := mkSort Level.one, numParams := 0, numIndices := 0,
    all := [], ctors := [], numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }]
  write `ForgedFalse <| module #[thm `forgedFalse (mkConst ``False) (mkConst ``True.intro)]
  let blockT : ConstantInfo := .inductInfo {
    name := `BlockT, levelParams := [], type := mkSort Level.one, numParams := 0, numIndices := 0,
    all := [`BlockT], ctors := [`BlockT.mk], numNested := 0, isRec := false, isUnsafe := false,
    isReflexive := false }
  let blockMk : ConstantInfo := .ctorInfo {
    name := `BlockT.mk, levelParams := [], type := mkConst `BlockT, induct := `BlockT, cidx := 0,
    numParams := 0, numFields := 0, isUnsafe := false }
  write `ForgedBlockNoRec <| module #[blockT, blockMk]
  write `ForgedBlockRecAxiom <| module #[blockT, blockMk,
    .axiomInfo { name := `BlockT.rec, levelParams := [], type := mkConst ``False, isUnsafe := false }]
  let writeTo (sub : String) (mod : Name) (data : ModuleData) : IO Unit := do
    IO.FS.createDirAll ((dir : System.FilePath) / sub)
    saveModuleDataParts mod #[((dir : System.FilePath) / sub / s!"{mod}.olean", data)]
  let both (mod : Name) (data : ModuleData) : IO Unit := do
    writeTo "v1" mod data
    writeTo "v2" mod data
  let helper := thm `cacheHelper (mkConst ``True) (mkConst ``True.intro)
  writeTo "v1" `CacheBase <| module #[helper]
  writeTo "v2" `CacheBase <| module #[helper, thm (.num `CacheX 0) (mkConst ``False) (mkConst ``True.intro)]
  both `CacheTop <| module #[thm (.num `CacheX 4294967296) (mkConst ``True) (mkConst `cacheHelper)]
    (imports := #[`Init, `CacheBase])
  both `DupA <| module #[thm `dupThm (mkConst ``True) (mkConst ``True.intro)]
  writeTo "v1" `DupB <| module #[thm `dupThm (mkConst ``True) (mkConst ``True.intro)]
  writeTo "v2" `DupB <| module #[thm `dupThm (mkConst ``True) (mkConst ``Nat.zero)]
  let env ← importModules #[{ module := `Init }] {}
  let mdDecl := Declaration.inductDecl [] 0
    [{ name := `MdT, type := mkSort Level.one, ctors := [{ name := `MdT.mk, type := mkConst `MdT }] }] false
  let kenv ← match env.toKernelEnv.addDeclCore 0 0 mdDecl none with
    | .ok k => pure k
    | .error _ => throw <| .userError "the kernel rejected MdT"
  let get (n : Name) : IO ConstantInfo := match kenv.find? n with
    | some c => pure c
    | none => throw <| .userError s!"the kernel did not generate {n}"
  let mdT ← get `MdT
  let mdRec ← get `MdT.rec
  let mdMk ← get `MdT.mk
  writeTo "v1" `MdBlock <| module #[mdT, mdMk, mdRec]
  let wrapped := match mdMk with
    | .ctorInfo v => ConstantInfo.ctorInfo { v with type := .mdata (KVMap.empty.insert `note (.ofBool true)) v.type }
    | c => c
  writeTo "v2" `MdBlock <| module #[mdT, wrapped, mdRec]
  let kernelAdd (k : Kernel.Environment) (d : Declaration) : IO Kernel.Environment :=
    match k.addDeclCore 0 0 d none with
    | .ok k => pure k
    | .error e => do throw <| .userError s!"the kernel rejected a forged prerequisite: {← (e.toMessageData {}).toString}"
  let find (k : Kernel.Environment) (n : Name) : IO ConstantInfo := match k.find? n with
    | some c => pure c
    | none => throw <| .userError s!"the kernel did not generate {n}"
  -- URec
  let uk ← kernelAdd env.toKernelEnv <| .inductDecl [] 0
    [{ name := `UT, type := mkSort Level.one, ctors := [{ name := `UT.mk, type := mkConst `UT }] }] false
  let .recInfo rv ← find uk `UT.rec | throw <| .userError "UT.rec is not a recursor"
  let forgedRec : ConstantInfo := .recInfo { rv with isUnsafe := true, rules := rv.rules.map fun r => match r.rhs with
    | .lam n1 t1 (.lam n2 t2 _ b2) b1 => { r with rhs := .lam n1 t1 (.lam n2 t2 (mkConst ``Bool.true) b2) b1 }
    | _ => r }
  let bool := mkConst ``Bool
  let g : ConstantInfo := .defnInfo {
    name := `g, levelParams := [], type := bool,
    value := mkAppN (mkConst `UT.rec [Level.one])
      #[.lam `x (mkConst `UT) bool .default, mkConst ``Bool.false, mkConst `UT.mk]
    hints := .regular 1, safety := .safe, all := [`g] }
  let badG := thm `bad (mkAppN (mkConst ``Eq [Level.one]) #[bool, mkConst `g, mkConst ``Bool.true])
    (mkAppN (mkConst ``Eq.refl [Level.one]) #[bool, mkConst ``Bool.true])
  writeTo "v1" `URec <| module #[← find uk `UT, ← find uk `UT.mk, forgedRec, g]
  writeTo "v2" `URec <| module #[← find uk `UT, ← find uk `UT.mk, forgedRec, g, badG]
  -- P
  let c (n : Name) (ls : List Level := []) : Expr := mkConst n ls
  let pi (n : Name) (t b : Expr) (bi := BinderInfo.default) : Expr := .forallE n t b bi
  let lam (n : Name) (t b : Expr) : Expr := .lam n t b .default
  let ind (n : Name) (t : Expr) (cs : List (Name × Expr)) : InductiveType :=
    { name := n, type := t, ctors := cs.map fun (n, t) => { name := n, type := t } }
  let u := Level.param `u
  let one := Level.one
  let listOf (a : Expr) (l := u) := mkApp (c `List [l]) a
  let mut k ← kernelAdd (← mkEmptyEnvironment).toKernelEnv <| .inductDecl [] 0
    [ind `Nat (mkSort one) [(`Nat.zero, c `Nat), (`Nat.succ, pi `n (c `Nat) (c `Nat))]] false
  k ← kernelAdd k <| .inductDecl [`u] 1 [ind `List (pi `α (mkSort (.succ u)) (mkSort (.succ u)))
    [(`List.nil, pi `α (mkSort (.succ u)) (listOf (.bvar 0)) .implicit),
     (`List.cons, pi `α (mkSort (.succ u)) (pi `head (.bvar 0) (pi `tail (listOf (.bvar 1)) (listOf (.bvar 2)))) .implicit)]]
    false
  k ← kernelAdd k <| .inductDecl [] 0 [ind `Char (mkSort one) [(`Char.a, c `Char), (`Char.b, c `Char)]] false
  k ← kernelAdd k <| .inductDecl [] 0
    [ind `String (mkSort one) [(`String.ofList, pi `data (listOf (c `Char) .zero) (c `String))]] false
  k ← kernelAdd k <| .inductDecl [`u] 2 [ind `Eq (pi `α (mkSort u) (pi `a (.bvar 0) (pi `b (.bvar 1) (mkSort .zero))) .implicit)
    [(`Eq.refl, pi `α (mkSort u) (pi `a (.bvar 0) (mkApp3 (c `Eq [u]) (.bvar 1) (.bvar 0) (.bvar 0))) .implicit)]] false
  k ← kernelAdd k <| .defnDecl {
    name := `Char.ofNat, levelParams := [], type := pi `n (c `Nat) (c `Char), value := lam `n (c `Nat) (c `Char.a)
    hints := .regular 1, safety := .safe, all := [`Char.ofNat, `Ghost] }
  let listChar := listOf (c `Char) .zero
  let headOr := mkAppN (c `List.rec [one, .zero]) #[c `Char, lam `_ listChar (c `Char), c `Char.b,
    lam `h (c `Char) (lam `t listChar (lam `ih (c `Char) (.bvar 2))), .bvar 0]
  let firstChar := mkApp3 (c `String.rec [one]) (lam `_ (c `String) (c `Char)) (lam `l listChar headOr) (.lit (.strVal "a"))
  k ← kernelAdd k <| .thmDecl {
    name := `x, levelParams := [], all := [`x], type := mkApp3 (c `Eq [one]) (c `Char) firstChar (c `Char.a)
    value := mkApp2 (c `Eq.refl [one]) (c `Char) (c `Char.a) }
  let pNames := [`Nat, `Nat.zero, `Nat.succ, `Nat.rec, `List, `List.nil, `List.cons, `List.rec, `Char, `Char.a, `Char.b,
    `Char.rec, `String, `String.ofList, `String.rec, `Eq, `Eq.refl, `Eq.rec, `Char.ofNat, `x]
  let pConsts ← pNames.toArray.mapM (find k)
  writeTo "v1" `P <| module pConsts (imports := #[])
  writeTo "v2" `P <| module (pConsts.filter (·.name != `Char.ofNat)) (imports := #[])
  -- N1, N2
  let nt := mkConst `NT
  let ntMk : Constructor := { name := `NT.mk, type := .forallE `xs (mkApp (mkConst ``List [.zero]) nt) nt .default }
  let nk ← kernelAdd env.toKernelEnv <| .inductDecl [] 0 [{ name := `NT, type := mkSort Level.one, ctors := [ntMk] }] false
  write `N1 <| module (← #[`NT, `NT.mk, `NT.rec, `NT.rec_1].mapM (find nk))
  let auxName : ConstantInfo := .axiomInfo {
    name := `_nested.List_1.nil, levelParams := [], type := mkConst ``True, isUnsafe := false }
  write `N2 <| module #[auxName] (imports := #[`Init, `N1])
  -- BigLit
  let big := Expr.lit (.natVal (2 ^ 200))
  write `BigLit <| module #[thm `bigLit (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) big big)
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) big)]
  -- Circ
  let fals := mkConst ``False
  let ax : ConstantInfo := .axiomInfo { name := `ax, levelParams := [], type := fals, isUnsafe := false }
  writeTo "c1" `Circ <| module #[ax, thm `t1 fals (mkConst `ax), thm `t2 fals (mkConst `t1)]
  writeTo "c2" `Circ <| module #[ax, thm `t2 fals (mkConst `ax), thm `t1 fals (mkConst `t2)]
  writeTo "c3" `Circ <| module #[thm `t1 fals (mkConst `t2), thm `t2 fals (mkConst `t1)]
  write `ShardA <| module #[thm `t1 fals (mkConst `t2)]
  write `ShardB <| module #[thm `t2 fals (mkConst `t1)]
