/-
Adapted from `src/Lean/Replay.lean` in Lean 4 (Copyright (c) 2023 Kim Morrison, Apache 2.0), as of commit e6e25218c
on master (2026-11-24), which includes the fixes for lean4#16675 (#16677) and malformed inductive entries (#16717).
-/
import Lean

/-!
# Incremental replay

The same replay as `Lean.Kernel.Environment.replay`, with one change in `addDecl`. An axiom, definition, theorem or
opaque whose check key is in the verdict store is added with `addDeclWithoutChecking`. Every other declaration goes
to the kernel as before. Inductive types and quotients always do: the kernel checks and generates them even on the
unchecked path. Constructors and recursors are still compared with the ones the kernel generates.
-/

open Lean Kernel

namespace IncCheck

/-- Lean's `Kernel.Environment.add`, which inserts a constant without the kernel, as importing a module does. It is
private in Lean and exported as `lean_environment_add`. -/
@[extern "lean_environment_add"]
opaque kernelAdd (env : Kernel.Environment) (c : ConstantInfo) : Kernel.Environment

/-- An inductive block's verdict key and the recursors that belong to it. -/
structure InductiveBlock where
  key : ByteArray
  recursors : Array Name

namespace Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  /-- The check key of each constant whose ids are exact. -/
  keys : Std.HashMap Name ByteArray
  /-- Keys of declarations that a complete earlier run of the same kernel accepted. -/
  store : Std.HashSet ByteArray
  /-- The block of each inductive type whose members all have exact keys. -/
  blocks : Std.HashMap Name InductiveBlock := {}

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  /-- Declarations the kernel checked in this run. -/
  checked : Nat := 0
  /-- Declarations added without a check because their key was in the store. -/
  skipped : Nat := 0
  /-- Inductive blocks added without the kernel because their key was in the store. -/
  skippedBlocks : Nat := 0
  /-- Inductive blocks the kernel checked in this run, by the type that started each. -/
  checkedBlocks : Array Name := #[]
  /-- Keys of declarations the kernel accepted in this run. -/
  accepted : Array ByteArray := #[]
  /-- Axioms, definitions, theorems and opaques the kernel checked in this run. -/
  checkedNames : Array Name := #[]

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Add the declaration of `name`, skipping the kernel when the store holds its key. -/
def addDecl (name : Name) (d : Declaration) : M Unit := do
  let skippable := match d with
    | .axiomDecl _ | .defnDecl _ | .thmDecl _ | .opaqueDecl _ => true
    | _ => false
  let ctx ← read
  let key? := if skippable then ctx.keys[name]? else none
  if key?.any ctx.store.contains then
    match (← get).env.addDeclWithoutChecking d with
    | .ok env => modify fun s => { s with env, skipped := s.skipped + 1 }
    | .error ex => throwKernelException ex
  else
    match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
    | .ok env =>
      modify fun s => { s with
        env, checked := s.checked + 1
        checkedNames := if skippable then s.checkedNames.push name else s.checkedNames
        accepted := match key? with
          | some k => s.accepted.push k
          | none => s.accepted }
    | .error ex => throwKernelException ex

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo   info =>
          addDecl name (Declaration.defnDecl   info)
        | .thmInfo    info =>
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              return
          addDecl name (Declaration.thmDecl    info)
        | .axiomInfo  info =>
          addDecl name (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          addDecl name (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          -- Only the members of `info.all` are sent to the kernel, so `name` must be among them.
          unless info.all.contains name do
            throw <| .userError s!"inductive type '{name}' is not listed in its own `all` field"
          let all ← info.all.mapM fun n => do
            let some (ConstantInfo.inductInfo val) := (← read).newConstants[n]?
              | throw <| .userError s!"'{n}', listed in the `all` field of '{name}', is not a stored inductive type"
            pure val
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun val => do
            pure (val, ← val.ctors.mapM fun n => do
              let some ci@(ConstantInfo.ctorInfo _) := (← read).newConstants[n]?
                | throw <| .userError s!"'{n}', listed as a constructor of '{val.name}', is not a stored constructor"
              pure ci)
          for (val, ctors) in ctorInfo do
            replayConstants (ConstantInfo.inductInfo val).getUsedConstantsAsSet
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨val, ctors⟩ =>
            { name := val.name
              type := val.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          match (← read).blocks[name]? with
          | some block =>
            if (← read).store.contains block.key then
              -- A complete earlier run of this kernel accepted a block with this exact content, and compared the
              -- constructors and recursors it generated with these stored ones. Add them as an import would.
              let mut added : Array ConstantInfo := all.toArray.map .inductInfo
              for (_, ctors) in ctorInfo do added := added ++ ctors.toArray
              for r in block.recursors do
                if let some ci := (← read).newConstants[r]? then added := added.push ci
              modify fun s => { s with
                env := added.foldl kernelAdd s.env, skippedBlocks := s.skippedBlocks + 1 }
            else
              addDecl name (Declaration.inductDecl lparams nparams types false)
              modify fun s => { s with accepted := s.accepted.push block.key, checkedBlocks := s.checkedBlocks.push name }
          | none =>
            addDecl name (Declaration.inductDecl lparams nparams types false)
            modify fun s => { s with checkedBlocks := s.checkedBlocks.push name }
          -- The kernel computes the remaining fields (`numIndices`, `isRec`, ...) itself;
          -- the stored values must agree with them.
          for val in all do
            unless (← get).env.find? val.name == some (.inductInfo val) do
              throw <| .userError s!"Invalid inductive type {val.name}"
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayConstant `Eq
          addDecl name (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end Replay

open Replay in
/-- Replay `newConstants` into `env`. Returns the final state, whose `accepted` keys are valid verdicts only because
the whole replay, including the constructor and recursor comparison, succeeded. -/
def replay (newConstants : Std.HashMap Name ConstantInfo) (keys : Std.HashMap Name ByteArray)
    (store : Std.HashSet ByteArray) (env : Kernel.Environment) (blocks : Std.HashMap Name InductiveBlock := {}) :
    IO State := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    -- Constructors and recursors are checked by their own name after replay, so an entry
    -- under a different key would otherwise never be checked.
    unless n == ci.name do
      throw <| .userError s!"declaration '{ci.name}' is stored under the name '{n}'"
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants, keys, store, blocks }) do
      replayConstant ``String.ofList
      replayConstant ``Char.ofNat
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  return s

end IncCheck
