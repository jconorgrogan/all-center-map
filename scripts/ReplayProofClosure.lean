import Lean.Replay
import Lean.Util.ForEachExpr

/- A selection wrapper around Lean's own trust-zero kernel replay.
No imported environment is passed to replay. Missing dependencies fail closed. -/
open Lean

def expressionDependencies (e : Expr) : IO NameSet := do
  let names ← IO.mkRef ({} : NameSet)
  e.forEach fun node => do
    match node with
    | .const n _ | .proj n _ _ => names.modify (·.insert n)
    | _ => pure ()
  return ← names.get

def dependencies (ci : ConstantInfo) : IO NameSet := do
  let mut names ← expressionDependencies ci.type
  if let some value := ci.value? (allowOpaque := true) then
    names := names ++ (← expressionDependencies value)
  match ci with
  | .inductInfo v => names := names ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v => names := names.insert v.induct
  | .recInfo v =>
    names := names ++ .ofList v.all
    for rule in v.rules do
      names := (names.insert rule.ctor) ++ (← expressionDependencies rule.rhs)
  | .quotInfo _ => names := names.insert `Eq
  | _ => pure ()
  return names

def closure (env : Environment) (target : Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut result : Std.HashMap Name ConstantInfo := {}
  let mut pending := [target]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if result.contains name then continue
    let some ci := env.find? name | throw <| IO.userError s!"Missing dependency: {name}"
    if ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"Unsafe/partial dependency: {name}"
    if let .axiomInfo _ := ci then
      unless name == `propext || name == `Classical.choice || name == `Quot.sound do
        throw <| IO.userError s!"Unapproved axiom: {name}"
    result := result.insert name ci
    for dep in (← dependencies ci) do pending := dep :: pending
  return result

unsafe def main (args : List String) : IO UInt32 := do
  let [moduleName, targetName, manifest] := args |
    throw <| IO.userError "usage: MODULE TARGET MANIFEST"
  initSearchPath (← findSysroot)
  withImportModules #[{module := moduleName.toName}] {} fun env => do
    let target := targetName.toName
    let some (.thmInfo original) := env.find? target |
      throw <| IO.userError "Target is not a theorem"
    let selected ← closure env target
    let names := selected.toList.map (fun p => p.1.toString (escape := true)) |>.mergeSort
    IO.FS.writeFile manifest (String.intercalate "\n" names ++ "\n")
    IO.println s!"Selected {selected.size} declarations for {target}"
    (← IO.getStdout).flush
    let checked ← (← mkEmptyEnvironment).replay selected
    let some (.thmInfo actual) := checked.toKernelEnv.find? target |
      throw <| IO.userError "Target absent after replay"
    unless actual.name == original.name && actual.type == original.type && actual.value == original.value &&
        actual.levelParams == original.levelParams do
      throw <| IO.userError "Target changed during replay"
    IO.println s!"PASS: exact target proof replayed from empty environment: {target}"
  return 0
