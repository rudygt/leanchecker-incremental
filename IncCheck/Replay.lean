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

Check keys leave a theorem's proof out of the keys of its users. The kernel can still read a proof while checking a
user: `Quot.lift` reduces its major premise with full `whnf`, and over a quotient in `Prop` that premise can be a theorem
(`src/kernel/quot.h`). So the replay turns on the kernel's diagnostics, which record every constant whose value the
kernel reads (`unfold_definition_core` in `src/kernel/type_checker.cpp`), and stores no verdict for a declaration or an
inductive block whose check read a theorem. Those are checked again in every run.
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
  /-- Declarations and inductive blocks whose check read a theorem's proof, so their verdicts are not stored. -/
  readProofs : Array Name := #[]
  /-- Constants whose references, proofs included, a retry after a rejection has made present. -/
  deepVisited : NameSet := {}

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

/-- Whether the kernel read the value of a theorem since the diagnostics were last reset. The diagnostics name every
constant the kernel unfolded, and some recursors and quotient constants it reduced; only theorems matter here. -/
def readAProof (env : Kernel.Environment) : M Bool := do
  let ctx ← read
  return env.getDiagnostics.unfoldCounter.toList.any fun (n, _) =>
    (ctx.newConstants[n]? <|> env.find? n) matches some (.thmInfo _)

/-- Send the declaration of `name` to the kernel. Everything with a stored verdict was inserted before the replay, the
only place that skips the kernel. Returns whether the kernel read a theorem's proof while checking it, in which case no
verdict for it may be stored. -/
def addDecl (name : Name) (d : Declaration) : M Bool := do
  let single := d matches .axiomDecl _ | .defnDecl _ | .thmDecl _ | .opaqueDecl _
  let ctx ← read
  let key? := if single then ctx.keys[name]? else none
  match (← get).env.resetDiag.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env =>
    let sawProof ← readAProof env
    modify fun s => { s with
      env, checked := s.checked + 1
      checkedNames := if single then s.checkedNames.push name else s.checkedNames
      readProofs := if sawProof then s.readProofs.push name else s.readProofs
      accepted := match key? with
        | some k => if sawProof then s.accepted else s.accepted.push k
        | none => s.accepted }
    return sawProof
  | .error ex => throwKernelException ex
    return false

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

/-- Every constant `ci` names, a theorem's proof and an opaque body included. -/
def allRefs (ci : ConstantInfo) : NameSet :=
  match ci.value? (allowOpaque := true) with
  | some v => v.getUsedConstantsAsSet.foldl (·.insert ·) (reachableThrough ci)
  | none => reachableThrough ci

mutual
/-- Send `d` to the kernel. If it rejects, make present everything `name` can reach, proofs included, and try once
more. The replay does not walk the proofs of constants already present, so a check that reads the proof of a theorem
with a stored verdict (`readAProof`) can miss a constant that proof names. `--fresh` has all of them by then. -/
partial def addChecked (name : Name) (d : Declaration) : M Bool := do
  try addDecl name d
  catch _ =>
    replayDeep name
    addDecl name d

partial def replayDeep (name : Name) : M Unit := do
  let mut stack := [name]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail
    if (← get).deepVisited.contains n then continue
    modify fun s => { s with deepVisited := s.deepVisited.insert n }
    if (← get).remaining.contains n then replayConstant n
    if let some ci := (← read).newConstants[n]? then
      stack := (allRefs ci).foldl (fun st r => r :: st) stack

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
          discard <| addChecked name (Declaration.defnDecl   info)
        | .thmInfo    info =>
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              return
          discard <| addChecked name (Declaration.thmDecl    info)
        | .axiomInfo  info =>
          discard <| addChecked name (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          discard <| addChecked name (Declaration.opaqueDecl info)
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
          let sawProof ← addChecked name (Declaration.inductDecl lparams nparams types false)
          let block? := (← read).blocks[name]?
          modify fun s => { s with
            accepted := match block? with
              | some block => if sawProof then s.accepted else s.accepted.push block.key
              | none => s.accepted
            checkedBlocks := s.checkedBlocks.push name }
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
          discard <| addDecl name (Declaration.quotDecl)
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
  let (_, s) ← StateRefT'.run (s := { env := env.enableDiag true, remaining, skipped, skippedBlocks }) do
    ReaderT.run (r := { newConstants, keys, store, blocks }) do
      replayConstant ``String.ofList
      replayConstant ``Char.ofNat
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  return s

end IncCheck
