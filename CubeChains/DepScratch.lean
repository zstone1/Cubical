/- scratch: constant-dependency graph over the CubeChains modules.  Not part of the library. -/
import CubeChains

open Lean

namespace DepScratch

/-- where the reports are written. -/
def outDir : String :=
  "/tmp/claude-1000/-home-zstone-Cubical/9f88bbcc-523d-46d1-badc-fe3a2be1cd8e/scratchpad"

/-- Module indices whose names start with `CubeChains`. -/
def cubeModules (env : Environment) : Array (Nat × Name) := Id.run do
  let mut out := #[]
  for h : i in *...env.header.moduleNames.size do
    let n := env.header.moduleNames[i]
    if n == `CubeChains || Name.isPrefixOf `CubeChains n then
      out := out.push (i, n)
  return out

/-- Every constant declared in a `CubeChains` module, tagged with that module. -/
def cubeConsts (env : Environment) : Array (Name × Name) := Id.run do
  let mut out := #[]
  for (i, mn) in cubeModules env do
    let md := env.header.moduleData[i]!
    for nm in md.constNames do
      out := out.push (nm, mn)
  return out

/-- deps of a constant: constants used in its type and (opaque-allowed) value. -/
def constDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let a := ci.type.getUsedConstants
    match ci.value? (allowOpaque := true) with
    | none => a
    | some v => a ++ v.getUsedConstants

/-- forward closure (what the seeds use), restricted to `dom`. -/
def closure (env : Environment) (dom : Std.HashSet Name) (seeds : Array Name) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  for s in seeds do
    if !seen.contains s then
      seen := seen.insert s
      stack := stack.push s
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    for d in constDeps env n do
      if !seen.contains d && dom.contains d then
        seen := seen.insert d
        stack := stack.push d
  return seen

/-- every constant of `CubeChains` reachable in this environment. -/
def liveDom (cs : Array (Name × Name)) : Std.HashSet Name :=
  cs.foldl (fun s (n, _) => s.insert n) {}

/-- `s` is a digit-suffixed generated component, e.g. `eq_3` after `pfx = "eq_"`. -/
def numbered (pfx s : String) : Bool :=
  s.startsWith pfx && !(s.drop pfx.length).isEmpty && (s.drop pfx.length).all Char.isDigit

/-- A *generated* name component.  Matching must be on whole components: an earlier version
tested `_eq_` as a substring of the full name and so silently dropped hand-written lemmas such
as `Rconj_eq_of` from every count. -/
def isGenComp (s : String) : Bool :=
  ["eq_def", "eq_unfold", "injEq", "noConfusion", "noConfusionType", "ctorIdx", "toCtorIdx",
    "sizeOf_spec", "sizeOf_eq", "ofNat", "ind", "inj", "splitter", "eq_mp", "eq_mpr"].contains s
  || numbered "eq_" s || numbered "_eq_" s || numbered "match_" s || numbered "proof_" s
  || s.endsWith "_sunfold" || s.endsWith "_unsafe_rec" || s.endsWith "_cstage1"
  || s.endsWith "_cstage2"

/-- does any component of the name read as generated? -/
def anyGenComp : Name → Bool
  | .str p s => isGenComp s || anyGenComp p
  | .num p _ => anyGenComp p
  | .anonymous => false

/-- a declaration nobody wrote: internal, an auto-recursor, or a generated component. -/
def isGen (env : Environment) (n : Name) : Bool :=
  n.isInternal || isAuxRecursor env n || isRecCore env n || anyGenComp n

def modPath (m : Name) : String :=
  (m.toString.replace "." "/") ++ ".lean"

/-- the set of source lines a name set covers in its module. -/
def lineSet (ns : Array (Nat × Nat)) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  for (a, b) in ns do
    for i in [a:b+1] do s := s.insert i
  return s

/-- decls (hand-written only) and source lines covered by a cone. -/
def coneSize (seeds : Array Name) : CoreM (Nat × Nat) := do
  let env ← getEnv
  let cs := cubeConsts env
  let cl := closure env (liveDom cs) seeds
  let mut decls := 0
  let mut byMod : Std.HashMap Name (Array (Nat × Nat)) := {}
  for (n, m) in cs do
    if cl.contains n then
      if !isGen env n then decls := decls + 1
      if let some r ← Lean.findDeclarationRanges? n then
        byMod := byMod.insert m ((byMod.getD m #[]).push (r.range.pos.line, r.range.endPos.line))
  let mut lines := 0
  for (_, iv) in byMod.toList do lines := lines + (lineSet iv).size
  return (decls, lines)

/-- forward closure that stops at `leaves`: they are reached, but nothing they use is. -/
def closureCut (env : Environment) (dom : Std.HashSet Name) (leaves : Std.HashSet Name)
    (seeds : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  for s in seeds do
    if !seen.contains s then
      seen := seen.insert s
      stack := stack.push s
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if !leaves.contains n then
      for d in constDeps env n do
        if !seen.contains d && dom.contains d then
          seen := seen.insert d
          stack := stack.push d
  return seen

/-- decls and lines of a name set. -/
def setSize (env : Environment) (cs : Array (Name × Name)) (cl : Std.HashSet Name) :
    CoreM (Nat × Nat) := do
  let mut decls := 0
  let mut byMod : Std.HashMap Name (Array (Nat × Nat)) := {}
  for (n, m) in cs do
    if cl.contains n then
      if !isGen env n then decls := decls + 1
      if let some r ← Lean.findDeclarationRanges? n then
        byMod := byMod.insert m ((byMod.getD m #[]).push (r.range.pos.line, r.range.endPos.line))
  let mut lines := 0
  for (_, iv) in byMod.toList do lines := lines + (lineSet iv).size
  return (decls, lines)

/-- a shortest dependency path `seed ⇝ target`, or `none`. -/
def depPath (env : Environment) (dom : Std.HashSet Name) (seed target : Name) :
    Option (Array Name) := Id.run do
  if seed == target then return some #[seed]
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {seed}
  let mut frontier : Array Name := #[seed]
  while frontier.size > 0 do
    let mut next : Array Name := #[]
    for n in frontier do
      for d in constDeps env n do
        if !seen.contains d && dom.contains d then
          seen := seen.insert d
          parent := parent.insert d n
          if d == target then
            let mut out := #[target]
            let mut cur := target
            while cur != seed do
              cur := parent[cur]!
              out := out.push cur
            return some out.reverse
          next := next.push d
    frontier := next
  return none

/-- every direct dependency of `seed` that reaches `target`. -/
def gateways (env : Environment) (dom : Std.HashSet Name) (seed target : Name) : Array Name :=
  Id.run do
    let mut out := #[]
    let mut seenDep : Std.HashSet Name := {}
    for d in constDeps env seed do
      if dom.contains d && !seenDep.contains d then
        seenDep := seenDep.insert d
        if (closure env dom #[d]).contains target then out := out.push d
    return out

def paperPoly : Name := ``ChainCat.Paper.poly
def paperPres : Name := ``ChainCat.Paper.paperPresents
def probes : Array Name :=
  #[``ChainCat.zCutPresentation, ``ChainCat.chCutPoly, ``ChainCat.chCollapse,
    ``ChainCat.Paper.bottomRun, ``ChainCat.Paper.bottomHom, ``ChainCat.Paper.cutWord,
    ``ChainCat.eltRep, ``ChainCat.runMerge]

end DepScratch

open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let testing := (cubeModules env).filter (fun (_, m) => Name.isPrefixOf `CubeChains.Testing m)
  IO.println s!"modules: {(cubeModules env).size}, of which Testing/: {testing.size}"
  let (dp, lp) ← coneSize #[paperPoly]
  let (dq, lq) ← coneSize #[paperPres]
  IO.println s!"cone(Paper.poly)     : {lp} lines / {dp} decls"
  IO.println s!"cone(paperPresents)  : {lq} lines / {dq} decls"
  IO.println s!"difference           : {lq - lp} lines / {dq - dp} decls"
  let clP := closure env dom #[paperPoly]
  for p in probes do
    IO.println s!"  in cone(Paper.poly)? {clP.contains p}   {p}"
  IO.println "-- gateways: direct deps of Paper.poly that reach zCutPresentation --"
  for g in gateways env dom paperPoly ``ChainCat.zCutPresentation do
    IO.println s!"   {g}"
  IO.println "-- a shortest path Paper.poly ⇝ zCutPresentation --"
  match depPath env dom paperPoly ``ChainCat.zCutPresentation with
  | none => IO.println "   (none)"
  | some p => for n in p do IO.println s!"   {n}"
  IO.println "-- gateways below Paper.poly --"
  for s in #[``ChainCat.Paper.cellWords, ``ChainCat.Paper.factorWords,
             ``ChainCat.Paper.cutWord, ``ChainCat.Paper.Cell,
             ``ChainCat.Paper.bottomRun, ``ChainCat.Paper.bottomHom,
             ``ChainCat.Paper.topOf] do
    IO.println s!"  {s} ↦ {gateways env dom s ``ChainCat.zCutPresentation}"
  -- what a CELL is: the data of `poly`, without its boundary words.
  let cellData : Array Name :=
    #[``ChainCat.Paper.Cell, ``ChainCat.Paper.Cell.mk, ``ChainCat.Paper.Cell.obj,
      ``ChainCat.Paper.Cell.degree_obj, ``ChainCat.Paper.Cell.below, ``ChainCat.Paper.Cell.top,
      ``ChainCat.Paper.Cell.hom, ``CubeChains.Run]
  let (dc, lc) ← coneSize cellData
  let clC := closure env dom cellData
  IO.println s!"cone(cell data)      : {lc} lines / {dc} decls"
  for p in probes do
    IO.println s!"  in cone(cell data)? {clC.contains p}   {p}"
  -- the prize: what `cutWord` alone costs the cone of `poly`.
  let leaf : Std.HashSet Name := {``ChainCat.Paper.cutWord}
  let (dl, ll) ← setSize env cs (closureCut env dom leaf #[paperPoly])
  IO.println s!"cone(Paper.poly), cutWord as a leaf : {ll} lines / {dl} decls"
