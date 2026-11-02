import Lean

open Lean Meta

namespace VeroCertificateAudit

-- Traverse both the declaration type and its body, including opaque bodies.
-- The independent reference audit also traverses the unreduced canonical
-- bundle. Individual evidence follows only its actual theorem type and body.
partial def dependenciesCore (env : Kernel.Environment) (pending : List Name)
    (seen : NameSet) (rejectUnsafe : Bool) : Except String NameSet := do
  match pending with
  | [] => return seen
  | name :: rest =>
    if seen.contains name then return ← dependenciesCore env rest seen rejectUnsafe
    let some info := env.find? name
      | throw s!"missing kernel declaration: {name}"
    if rejectUnsafe && info.isUnsafe then throw s!"unsafe dependency: {name}"
    let mut next := info.type.getUsedConstants.toList
    if let some value := info.value? (allowOpaque := true) then
      next := value.getUsedConstants.toList ++ next
    if let .inductInfo value := info then
      next := value.ctors ++ next
    dependenciesCore env (next ++ rest) (seen.insert name) rejectUnsafe

def dependencies (pending : List Name) (seen : NameSet := {})
    (rejectUnsafe := true) : MetaM NameSet := do
  match dependenciesCore (← getEnv).checked.get pending seen rejectUnsafe with
  | .ok used => return used
  | .error error => throwError "{error}"

-- A manifest may use a short specification name. Resolve it only among
-- declarations originating in the frozen manifest module, never in a
-- certificate's namespace or an identically named helper declaration.
def resolveInModule (names : List (Name × Name)) (short moduleName : Name) : MetaM Name := do
  let candidates := names.filterMap fun (name, origin) => do
    if origin != moduleName then none
    else if name == short || (short.isAtomic && name.getString! == short.toString) then
      some name
    else none
  match candidates with
  | [name] => return name
  | _ => throwError "expected one declaration {short} in {moduleName}; found {candidates}"

structure Request where
  declaration : Name
  spec : Name
  specModule : Name
  harnessModule : Name
  refuted : Bool

def audit (names : List (Name × Name)) (covered : NameSet) (request : Request) : MetaM Json := do
  let { declaration, spec, specModule, harnessModule, refuted } := request
  let info ← getConstInfo declaration
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "certificate is not a theorem: {declaration}"
  let spec ← resolveInModule names spec specModule
  let canonical ← resolveInModule names `canonical harnessModule
  let target ← mkAppM spec #[mkConst canonical]
  let target ← if refuted then mkAppM ``Not #[target] else pure target
  unless ← isDefEq info.type target do
    throwError "wrong certificate type for {declaration}; expected {target}, got {info.type}"
  -- Unsafe checking is shared across all certificate theorem roots. The
  -- standard collector still gives this individual theorem's exact axiom set.
  unless covered.contains declaration do
    let _ ← dependencies [declaration]
    pure ()
  let axioms ← collectAxioms declaration
  for name in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains name do
      throwError "unapproved axiom: {name}"
  return Json.mkObj [("declaration", toJson declaration.toString),
    ("checked", toJson true), ("axioms", toJson (axioms.map Name.toString))]

def referenceAudit (names : List (Name × Name)) (requests : Array Request)
    (benchmarkModules : NameSet) : MetaM Json := do
  let mut roots : List Name := []
  for request in requests do
    roots := (← resolveInModule names request.spec request.specModule) :: roots
    roots := (← resolveInModule names `canonical request.harnessModule) :: roots
  let rawUsed ← dependencies roots {} false
  -- Unused imported benchmark axioms still affect the reference environment.
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if benchmarkModules.contains env.header.modules[idx.toNat]!.module then
        roots := name :: roots
  -- Includes unused helper theorem/definition bodies (for example sorryAx),
  -- not just explicit axiom declarations. Existing metaprogram internals in
  -- Lean/Std are reported as unsafe only when used by the raw logical target.
  let used ← dependencies roots rawUsed false
  let mut blockers : Array Json := #[]
  for name in used.toArray do
    let info ← getConstInfo name
    let localUnsafe := (env.getModuleIdxFor? name).any fun idx =>
      benchmarkModules.contains env.header.modules[idx.toNat]!.module
    if info.isUnsafe && (rawUsed.contains name || localUnsafe) then
      blockers := blockers.push <| Json.mkObj [("kind", toJson "unsafe"), ("declaration", toJson name.toString)]
    if info.isAxiom && ![``propext, ``Classical.choice, ``Quot.sound].contains name then
      blockers := blockers.push <| Json.mkObj [("kind", toJson "axiom"), ("declaration", toJson name.toString)]
  return toJson blockers

def auditMany (requests : Array Request) (reference : Bool)
    (benchmarkModules certificateModules : NameSet) : MetaM Json := do
  let env ← getEnv
  let needed := requests.foldl (fun names request =>
    (names.insert request.specModule).insert request.harnessModule) ({} : NameSet)
  let names := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let origin := env.header.modules[idx.toNat]!.module
    if needed.contains origin then some (name, origin) else none
  if reference then
    referenceAudit names requests benchmarkModules
  else
    -- The user forbids new unsafe declarations and axioms, including unused
    -- helpers. Standard Lean and explicitly trusted dependency modules are not
    -- certificate modules and do not enter this check.
    let mut certificateRoots : List Name := []
    let mut theoremRoots : List Name := []
    for (name, info) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        if certificateModules.contains env.header.modules[idx.toNat]!.module then
          if info.isUnsafe || info.isAxiom then
            throwError "forbidden certificate declaration: {name}"
          certificateRoots := name :: certificateRoots
          if let .thmInfo _ := info then theoremRoots := name :: theoremRoots
    let certificateUsed ← dependencies certificateRoots {} false
    for name in certificateUsed.toArray do
      if (← getConstInfo name).isAxiom && ![``propext, ``Classical.choice, ``Quot.sound].contains name then
        throwError "unapproved certificate axiom: {name}"
    let covered ← dependencies theoremRoots
    let mut results := #[]
    for request in requests do
      try
        results := results.push (← audit names covered request)
      catch error =>
        let error ← error.toMessageData.toString
        results := results.push <| Json.mkObj [("declaration", toJson request.declaration.toString),
          ("checked", toJson false), ("error", toJson error)]
    return toJson results

structure InputRequest where
  declaration : String := ""
  spec : String
  specModule : String
  harnessModule : String
  refuted : Bool := false
  deriving FromJson

structure Configuration where
  imports : Array String
  requests : Array InputRequest
  searchPaths : Array String
  benchmarkModules : Array String
  certificateModules : Array String
  reference : Bool
  deriving FromJson

def run (config : Configuration) : IO Json := do
  initSearchPath (← findSysroot)
  searchPathRef.modify fun paths => config.searchPaths.toList.map System.FilePath.mk ++ paths
  -- No certificate initializer, macro, elaborator, or persistent extension is
  -- loaded. The trusted driver was elaborated before this runtime import.
  let env ← importModules (config.imports.map fun name => { module := name.toName }) {}
    (loadExts := false)
  let requests := config.requests.map fun r =>
    { declaration := r.declaration.toName, spec := r.spec.toName,
      specModule := r.specModule.toName, harnessModule := r.harnessModule.toName,
      refuted := r.refuted : Request }
  let toSet := fun (names : Array String) => names.foldl (fun s n => s.insert n.toName) ({} : NameSet)
  let options := ({} : Options).set `maxRecDepth (100000 : Nat) |>.set `maxHeartbeats (0 : Nat)
  let (result, _, _) ← (auditMany requests config.reference (toSet config.benchmarkModules)
    (toSet config.certificateModules)).toIO
    { fileName := "<certificate-audit>", fileMap := FileMap.ofString "", options }
    { env }
  return result

end VeroCertificateAudit

def main (args : List String) : IO UInt32 := do
  try
    let [path] := args | throw <| IO.userError "expected one JSON request path"
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
    let config ← IO.ofExcept <| fromJson? (α := VeroCertificateAudit.Configuration) json
    IO.println (← VeroCertificateAudit.run config).compress
    return (0 : UInt32)
  catch error =>
    IO.eprintln error
    return (1 : UInt32)
