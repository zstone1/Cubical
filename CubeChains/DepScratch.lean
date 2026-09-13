/- scratch: constant-dependency graph over the CubeChains modules.  Not part of the library. -/
import CubeChains

open Lean

namespace DepScratch

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

/-- the reverse graph, restricted to `dom`. -/
def revGraph (env : Environment) (dom : Std.HashSet Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for n in dom do
    for d in constDeps env n do
      if dom.contains d && d != n then
        m := m.insert d ((m.getD d #[]).push n)
  return m

/-- the direct users of `n`, restricted to `dom`. -/
def usersOf (env : Environment) (dom : Std.HashSet Name) (n : Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in dom do
    if m != n && (constDeps env m).contains n then out := out.push m
  return out

/-- every constant of `CubeChains`, except those declared in `Testing/`. -/
def liveDom (cs : Array (Name × Name)) : Std.HashSet Name :=
  cs.foldl (fun s (n, _) => s.insert n) {}

/-- namespaces the root module's `example`s read names in. -/
def scanNamespaces : Array Name :=
  #[.anonymous, `CubeChains, `ChainCat, `ChainCat.Paper, `CategoryTheory,
    `CategoryTheory.Polygraph, `CategoryTheory.Presents, `BPSet, `Cut, `COM, `GeoTensor,
    `Relation, `PrecubicalSet, `CubeChain, `RunWedge, `ChStar, `Models, `Polygraph]

def identChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\'' || c.val > 127

/-- every constant named anywhere in the text of `CubeChains.lean` — `example`s leave no constant
behind, so the claims are read off the source. -/
def rootSeeds (env : Environment) : IO (Array Name) := do
  let txt ← IO.FS.readFile "CubeChains.lean"
  let toks := (String.ofList (txt.toList.map fun c => if identChar c then c else ' ')).splitOn " "
  let mut out : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  for t in toks do
    if t.length ≥ 3 then
      let base := t.toName
      for ns in scanNamespaces do
        let n := ns ++ base
        if !seen.contains n && env.contains n then
          seen := seen.insert n
          out := out.push n
  return out

def generated : Array String :=
  #["_eq_", "eq_def", "match_", "mk.", "noConfusion", "ctorIdx", "sizeOf_spec",
    "injEq", "proof_", "below", "brecOn", "_sunfold", "_unsafe_rec", "eq_1", "eq_2", "eq_3",
    "eq_4", "eq_5", "eq_6", "eq_7", "eq_8", "eq_9"]

def isGen (n : Name) : Bool :=
  let s := n.toString
  generated.any (fun g => ((s.splitOn g).length > 1 : Bool)) ||
    [".rec", ".recOn", ".casesOn", ".inj", ".ofNat", ".ind"].any (fun g => s.endsWith g)

/-- claims of `CubeChains.lean` the text scan cannot see: instances found by `inferInstance`, and
dot notation on a local hypothesis. -/
def dotAnchors : Array Name :=
  #[``ChainCat.Paper.isLocalization_Theta, ``ChainCat.instIsDiscreteFibrationObjZbpToChZ,
    ``CategoryTheory.Polygraph.Presents.Map.trans, ``ChainCat.BraidPresentation.braids]

/-- report the dead (non-generated) constants of every module matching one of `pfx`. -/
def report (extraSeeds : Array Name) (pfx : Array Name) : CoreM Unit := do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let seeds := (← rootSeeds env) ++ dotAnchors ++ extraSeeds
  let cl := closure env dom seeds
  IO.println s!"seeds {seeds.size}  live {cl.size} / {dom.size}"
  let mods := (cubeModules env).map (·.2)
  let mut grand := 0
  for pm in mods do
    if pfx.any (fun p => Name.isPrefixOf p pm) then
      let mut ds : Array Name := #[]
      let mut tot := 0
      for (n, m) in cs do
        if m == pm && !n.isInternal && !isGen n then
          tot := tot + 1
          if !cl.contains n then ds := ds.push n
      if ds.size > 0 then
        grand := grand + ds.size
        IO.println s!"---- {pm}   dead {ds.size} / {tot}"
        for d in ds do IO.println s!"   {d}"
      else if tot > 0 then
        IO.println s!"---- {pm}   dead 0 / {tot}"
  IO.println s!"TOTAL DEAD in probed modules: {grand}"

end DepScratch

open CategoryTheory CubeChains ChainCat DepScratch in
/-- results kept although the root module's `example`s do not cite them. -/
def keepExtra : Array Name :=
  #[``ChainCat.chCellPresentation, ``ChainCat.chRunPresentation]

open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  -- sanity: the frozen API and a handful of root claims must all be live.
  let probes : Array Name :=
    #[`ChainCat.Paper.paperPresents, `ChainCat.Paper.polyFunctor,
      `ChainCat.Paper.paperPresentationIso, `ChainCat.Paper.paperPresentationIso_id,
      `ChainCat.Paper.paperArtinIso, `CubeChains.hLocEquiv, `ChainCat.fullBaseEquiv,
      `ChainCat.chCutLocPresentation, `ChainCat.runBraidEquiv,
      `CategoryTheory.Polygraph.isoOfBijective]
  let cs := cubeConsts env
  let dom := liveDom cs
  let cl := closure env dom ((← rootSeeds env) ++ dotAnchors ++ keepExtra)
  for p in probes do
    if !cl.contains p then IO.println s!"!! ANCHOR MISS {p}"
  IO.println "anchor check done"

open DepScratch in
#eval report keepExtra
  #[`CubeChains.Machinery.Presentation, `CubeChains.Concurrency.Presentation]

-- what only `chCellPresentation` / `chRunPresentation` keep alive.
open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let root := (← rootSeeds env) ++ dotAnchors
  let withK := closure env dom (root ++ keepExtra)
  let without := closure env dom root
  let modOf : Std.HashMap Name Name := cs.foldl (fun s (n, m) => s.insert n m) {}
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for n in withK do
    if !without.contains n && !n.isInternal && !isGen n then
      let m := modOf.getD n `unknown
      byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let mut tot := 0
  for (m, ns) in byMod.toList do
    tot := tot + ns.size
    IO.println s!"~~~~ {m}  ({ns.size})"
    for n in ns do IO.println s!"   {n}"
  IO.println s!"ONLY-FOR-chCellPresentation/chRunPresentation: {tot}"

-- the source lines those constants cover, per module.
open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let root := (← rootSeeds env) ++ dotAnchors
  let withK := closure env dom (root ++ keepExtra)
  let without := closure env dom root
  let modOf : Std.HashMap Name Name := cs.foldl (fun s (n, m) => s.insert n m) {}
  let mut byMod : Std.HashMap Name (Array (Nat × Nat)) := {}
  for n in withK do
    if !without.contains n then
      if let some r ← Lean.findDeclarationRanges? n then
        let m := modOf.getD n `unknown
        byMod := byMod.insert m ((byMod.getD m #[]).push (r.range.pos.line, r.range.endPos.line))
  let mut tot := 0
  for (m, ivs) in byMod.toList do
    -- union of the line intervals
    let sorted := ivs.qsort (fun a b => a.1 < b.1)
    let mut lines := 0
    let mut cur : Option (Nat × Nat) := none
    for (a, b) in sorted do
      match cur with
      | none => cur := some (a, b)
      | some (a₀, b₀) =>
          if a ≤ b₀ + 1 then cur := some (a₀, max b₀ b)
          else
            lines := lines + (b₀ + 1 - a₀)
            cur := some (a, b)
    match cur with
    | none => pure ()
    | some (a₀, b₀) => lines := lines + (b₀ + 1 - a₀)
    tot := tot + lines
    IO.println s!"LINES {lines}  {m}"
  IO.println s!"TOTAL LINES held by chCellPresentation/chRunPresentation: {tot}"
