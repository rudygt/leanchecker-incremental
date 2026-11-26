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
  /-- Constants already in the environment whose reachable constants have been made present too. -/
  visited : NameSet := {}
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

/-- The constants a kernel check can reach through `ci` once `ci` is in the environment: its type, the body of a
definition, and the structure of an inductive type, constructor or recursor. Not the proof of a theorem or the body of
an opaque, which the kernel never unfolds. -/
def reachableThrough (ci : ConstantInfo) : NameSet :=
  let s := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo v => v.value.getUsedConstantsAsSet.foldl (·.insert ·) s
  | .inductInfo v => (v.all ++ v.ctors).foldl (·.insert ·) s
  | .ctorInfo v => s.insert v.induct
  | .recInfo v => v.rules.foldl (fun s r => r.rhs.getUsedConstantsAsSet.foldl (·.insert ·) (s.insert r.ctor))
      (v.all.foldl (·.insert ·) s)
  | _ => s

mutual
partial def replayConstant (name : Name) : M Unit := do
  if !(← isTodo name) then
    -- Already in the environment: inserted with a stored verdict, or replayed earlier. A check that reaches it can
    -- reach what its type and body name, so make sure those are present too.
    unless (← get).visited.contains name do
      modify fun s => { s with visited := s.visited.insert name }
      if let some ci := (← read).newConstants[name]? then
        replayConstants (reachableThrough ci)
  else
    modify fun s => { s with visited := s.visited.insert name }
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
  -- First insert everything with a stored verdict, without walking its references: a stored verdict was recorded with
  -- the content of everything it refers to, so the order does not matter, and walking every proof term to find its
  -- references would cost as much as the rest of the run. The usual replay then handles what is left.
  let mut env := env
  let mut skipped := 0
  let mut skippedBlocks := 0
  for (n, ci) in newConstants do
    unless remaining.contains n do continue
    match ci with
    | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      if keys[n]?.any store.contains then
        env := kernelAdd env ci
        remaining := remaining.erase n
        skipped := skipped + 1
    | .inductInfo v =>
      let some block := blocks[n]? | continue
      unless v.all.head? == some n && store.contains block.key do continue
      let types := v.all.filterMap fun t => newConstants[t]?
      let ctors := types.foldl (init := []) fun acc c => match c with
        | .inductInfo tv => acc ++ tv.ctors.filterMap fun c => newConstants[c]?
        | _ => acc
      let recursors := block.recursors.toList.filterMap fun r => newConstants[r]?
      let members := types ++ ctors ++ recursors
      unless types.length == v.all.length && members.all (remaining.contains ·.name) do continue
      env := members.foldl kernelAdd env
      remaining := members.foldl (fun r c => r.erase c.name) remaining
      skippedBlocks := skippedBlocks + 1
    | _ => pure ()
  let (_, s) ← StateRefT'.run (s := { env, remaining, skipped, skippedBlocks }) do
    ReaderT.run (r := { newConstants, keys, store, blocks }) do
      replayConstant ``String.ofList
      replayConstant ``Char.ofNat
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  return s

end IncCheck
