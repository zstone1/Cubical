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

def generated : Array String :=
  #["_eq_", "eq_def", "match_", "mk.", "noConfusion", "ctorIdx", "sizeOf_spec",
    "injEq", "proof_", "below", "brecOn", "_sunfold", "_unsafe_rec", "eq_1", "eq_2", "eq_3",
    "eq_4", "eq_5", "eq_6", "eq_7", "eq_8", "eq_9"]

def isGen (n : Name) : Bool :=
  let s := n.toString
  generated.any (fun g => ((s.splitOn g).length > 1 : Bool)) ||
    [".rec", ".recOn", ".casesOn", ".inj", ".ofNat", ".ind"].any (fun g => s.endsWith g)

/-- THE FOUR RESULTS the user cares about. -/
def theFour : Array Name :=
  #[``ChainCat.Paper.paperPresents, ``ChainCat.Paper.polyFunctor,
    ``ChainCat.Paper.paperPresentationIso, ``ChainCat.Paper.paperPresentationIso_id,
    ``ChainCat.Paper.paperArtinIso]

def modPath (m : Name) : String :=
  (m.toString.replace "." "/") ++ ".lean"

def fileLines (m : Name) : IO Nat := do
  try
    let s ← IO.FS.readFile (modPath m)
    return s.splitOn "\n" |>.length
  catch _ => return 0

/-- the set of source lines a name set covers in its module. -/
def lineSet (ns : Array (Nat × Nat)) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  for (a, b) in ns do
    for i in [a:b+1] do s := s.insert i
  return s

structure ModStat where
  m : Name
  tot : Nat
  inCone : Nat
  dead : Nat
  deadLines : Nat
  coneLines : Nat
  fileLines : Nat
  deadNames : Array Name

end DepScratch

open DepScratch in
/-- the per-module statistics for the cone of `seeds`. -/
def modStats (seeds : Array Name) : CoreM (Array ModStat) := do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let cl := closure env dom seeds
  let mods := (cubeModules env).map (·.2)
  let mut out : Array ModStat := #[]
  for pm in mods do
    let mut tot := 0
    let mut inCone := 0
    let mut ds : Array Name := #[]
    let mut deadIv : Array (Nat × Nat) := #[]
    let mut liveIv : Array (Nat × Nat) := #[]
    for (n, m) in cs do
      if m == pm then
        let rng ← Lean.findDeclarationRanges? n
        let keep := !n.isInternal && !isGen n
        if keep then
          tot := tot + 1
          if cl.contains n then inCone := inCone + 1 else ds := ds.push n
        -- lines: every constant with a range contributes, generated ones included,
        -- so a generated lemma of a live decl does not make its lines look dead.
        match rng with
        | none => pure ()
        | some r =>
          let iv := (r.range.pos.line, r.range.endPos.line)
          if cl.contains n then liveIv := liveIv.push iv else deadIv := deadIv.push iv
    let liveL := lineSet liveIv
    let deadL := lineSet deadIv
    let mut dl := 0
    for i in deadL do
      if !liveL.contains i then dl := dl + 1
    let fl ← fileLines pm
    out := out.push ⟨pm, tot, inCone, ds.size, dl, liveL.size, fl, ds⟩
  return out

open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  -- (0) Testing/ presence check
  let mods := (cubeModules env).map (·.2)
  let testing := mods.filter (fun m => Name.isPrefixOf `CubeChains.Testing m)
  IO.println s!"== modules visible: {mods.size};  of which Testing/: {testing.size}"
  let cs := cubeConsts env
  let dom := liveDom cs
  for f in theFour do
    if !env.contains f then IO.println s!"!! MISSING SEED {f}"
  let cone := closure env dom theFour
  IO.println s!"== FOUR-CONE: {cone.size} / {dom.size} constants of CubeChains"
  -- with generated/internal filtered
  let mut totF := 0
  let mut coneF := 0
  for (n, _) in cs do
    if !n.isInternal && !isGen n then
      totF := totF + 1
      if cone.contains n then coneF := coneF + 1
  IO.println s!"== FOUR-CONE (named decls only): {coneF} / {totF}"
  -- other stated results: in the four-cone, or beside it?
  for p in #[``ChainCat.chCutLocPresentation, ``ChainCat.fullBaseEquiv,
             ``CubeChains.hLocEquiv, ``ChainCat.runBraidEquiv,
             ``ChainCat.BraidPresentation.braids, ``ChainCat.zCutPresentation,
             ``ChainCat.chPresentation, ``ChainCat.chCutPresentation] do
    IO.println s!"   IN CONE? {cone.contains p}   {p}"

open DepScratch in
#eval show CoreM Unit from do
  let stats ← modStats theFour
  let mut h := ""
  let mut totDead := 0
  let mut totDeadLines := 0
  let mut totFile := 0
  let mut totConeLines := 0
  for s in stats do
    totDead := totDead + s.dead
    totDeadLines := totDeadLines + s.deadLines
    totFile := totFile + s.fileLines
    totConeLines := totConeLines + s.coneLines
    h := h ++ s!"{s.m}\t{s.tot}\t{s.inCone}\t{s.dead}\t"
    h := h ++ s!"{s.coneLines}\t{s.deadLines}\t{s.fileLines}\n"
  IO.FS.writeFile (outDir ++ "/modstats.tsv")
    ("module\ttot\tcone\tdead\tconeLines\tdeadLines\tfileLines\n" ++ h)
  IO.println s!"== OUTSIDE THE FOUR-CONE: {totDead} named decls, {totDeadLines} source lines"
  IO.println s!"== cone covers {totConeLines} source lines; files total {totFile} lines"
  -- full dead listing
  let mut d := ""
  for s in stats do
    if s.dead > 0 then
      d := d ++ s!"---- {s.m}  dead {s.dead}/{s.tot}  deadLines {s.deadLines}/{s.fileLines}\n"
      for n in s.deadNames do d := d ++ s!"   {n}\n"
  IO.FS.writeFile (outDir ++ "/dead.txt") d
  IO.println "wrote modstats.tsv, dead.txt"

-- dead roots: nothing else dead uses them.
open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let cone := closure env dom theFour
  let modOf : Std.HashMap Name Name := cs.foldl (fun s (n, m) => s.insert n m) {}
  let mut deadSet : Std.HashSet Name := {}
  for (n, _) in cs do
    if !cone.contains n && !n.isInternal && !isGen n then deadSet := deadSet.insert n
  -- used-by-another-dead
  let mut used : Std.HashSet Name := {}
  for (n, _) in cs do
    if !cone.contains n then
      for d in constDeps env n do
        if deadSet.contains d && d != n then used := used.insert d
  let mut byMod : Std.HashMap Name (Array Name) := {}
  let mut cnt := 0
  for n in deadSet do
    if !used.contains n then
      cnt := cnt + 1
      let m := modOf.getD n `unknown
      byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let mut s := ""
  for (m, ns) in byMod.toList do
    s := s ++ s!"---- {m}  ({ns.size})\n"
    for n in ns do s := s ++ s!"   {n}\n"
  IO.FS.writeFile (outDir ++ "/deadroots.txt") s
  IO.println s!"== DEAD ROOTS (nothing dead uses them): {cnt}; wrote deadroots.txt"

-- per-directory rollup.
open DepScratch in
#eval show CoreM Unit from do
  let stats ← modStats theFour
  let dirOf (m : Name) : String :=
    let parts := m.toString.splitOn "."
    match parts with
    | _ :: a :: b :: _ :: _ => a ++ "/" ++ b
    | _ :: a :: _ => a
    | _ => "?"
  let mut agg : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  for s in stats do
    let d := dirOf s.m
    let (t, c, dd, dl) := agg.getD d (0,0,0,0)
    agg := agg.insert d (t + s.tot, c + s.inCone, dd + s.dead, dl + s.deadLines)
  let mut out := "dir\ttot\tcone\tdead\tdeadLines\n"
  for (d, (t, c, dd, dl)) in agg.toList do
    out := out ++ s!"{d}\t{t}\t{c}\t{dd}\t{dl}\n"
  IO.FS.writeFile (outDir ++ "/dirstats.tsv") out
  IO.println out

-- exclusive cone of a candidate result, beyond the four (and beyond earlier candidates).
open DepScratch in
def exclusive (base : Array Name) (cand : Name) : CoreM (Nat × Nat) := do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let b := closure env dom base
  let w := closure env dom (base.push cand)
  let mut n := 0
  let mut byMod : Std.HashMap Name (Array (Nat × Nat)) := {}
  for (c, m) in cs do
    if w.contains c && !b.contains c then
      if !c.isInternal && !isGen c then n := n + 1
      if let some r ← Lean.findDeclarationRanges? c then
        byMod := byMod.insert m ((byMod.getD m #[]).push (r.range.pos.line, r.range.endPos.line))
  let mut lines := 0
  for (_, iv) in byMod.toList do lines := lines + (lineSet iv).size
  return (n, lines)

open DepScratch in
#eval show CoreM Unit from do
  let cands : Array Name :=
    #[``ChainCat.chCutLocPresentation, ``ChainCat.chPresentation, ``ChainCat.chCutPresentation,
      ``ChainCat.fullBaseEquiv, ``ChainCat.runBraidEquiv, ``ChainCat.runArtinEquiv,
      ``CubeChains.hLocEquiv, ``CubeChains.hLocPresentation, ``CubeChains.hLocActionPresentation,
      ``ChainCat.BraidPresentation.braids, ``ChainCat.germBP,
      ``ChainCat.isLocalization_chDescent, ``ChainCat.chEquivElements]
  IO.println "-- marginal cost of each candidate, added one at a time on top of the four:"
  let mut base := theFour
  for c in cands do
    let (n, l) := ← exclusive base c
    IO.println s!"   +{n} decls  +{l} lines   {c}"
    base := base.push c
  IO.println "-- and each one ALONE on top of the four:"
  for c in cands do
    let (n, l) := ← exclusive theFour c
    IO.println s!"   {n} decls  {l} lines   {c}"

-- full per-declaration dump of what is outside the four-cone.
open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let cone := closure env dom theFour
  let mut s := ""
  for (n, m) in cs do
    if !cone.contains n && !n.isInternal && !isGen n then
      let r ← Lean.findDeclarationRanges? n
      match r with
      | none => s := s ++ s!"{m}\t0\t0\t{n}\n"
      | some r => s := s ++ s!"{m}\t{r.range.pos.line}\t{r.range.endPos.line}\t{n}\n"
  IO.FS.writeFile (outDir ++ "/deadfull.tsv") s
  IO.println "wrote deadfull.tsv"

-- blocks: marginal cone of each area, in order, on top of the four.
open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let blocks : Array (String × Array Name) := #[
    ("B2 second presentation (invPoly / LiftLocalize)",
      #[``ChainCat.chCutLocPresentation, ``CubeChains.chLocPresentation,
        ``ChainCat.chPresentation, ``ChainCat.chCutPresentation]),
    ("B3 base presentation + retraction",
      #[``ChainCat.fullBaseEquiv, ``ChainCat.BraidPresentation.braids, ``ChainCat.germBP,
        ``ChainCat.runBase, ``ChainCat.runBraidEquiv, ``ChainCat.runArtinEquiv]),
    ("B4 H special case (HAction)",
      #[``CubeChains.hLocEquiv, ``CubeChains.hLocPresentation,
        ``CubeChains.hLocActionPresentation, ``CubeChains.hLocArtinEquiv,
        ``CubeChains.chLocEquivElements, ``ChainCat.isLocalization_chDescent]),
    ("B5 critical-pair presentation (PaperAtoms)",
      #[``ChainCat.Paper.critPresents]),
    ("B6 Complexification / H geometry",
      #[``CubeChains.isSegal_H_cube, ``CubeChains.not_desym_natural,
        ``CubeChains.reorientCh_comp_hbpBraidSalEquiv, ``CubeChains.hbpBraidSalEquiv,
        ``CubeChains.wallCrossLoc, ``CubeChains.symFreeCube]),
    ("B7 Salvetti / arrangement / executions",
      #[``CubeChains.Models.salEquiv, ``CubeChains.chFaceCatEquiv,
        ``CubeChains.ConcPos, ``CubeChains.execEquiv]),
    ("B8 Polygraph Day / monoidal / presheaf",
      #[``CategoryTheory.Polygraph.dayIso]),
    ("B9 rewriting", #[``Relation.Convergent]),
    ("B10 nerve", #[``PrecubicalSet.nerveRealizeIso]),
    ("B11 geometric tensor", #[``instMonoidalCategoryGeoBP]),
    ("B12 fibration localization", #[``CategoryTheory.Localization.isLocalization_elementsDescent])]
  let mut base := theFour
  let mut baseCl := closure env dom base
  let mut running := 0
  for (nm, sds) in blocks do
    let w := closure env dom (base ++ sds)
    let mut n := 0
    let mut byMod : Std.HashMap Name (Array (Nat × Nat)) := {}
    for (c, m) in cs do
      if w.contains c && !baseCl.contains c then
        if !c.isInternal && !isGen c then n := n + 1
        if let some r ← Lean.findDeclarationRanges? c then
          byMod := byMod.insert m ((byMod.getD m #[]).push (r.range.pos.line, r.range.endPos.line))
    let mut lines := 0
    for (_, iv) in byMod.toList do lines := lines + (lineSet iv).size
    running := running + lines
    IO.println s!"{nm}\t{n}\t{lines}"
    base := base ++ sds
    baseCl := w
  IO.println s!"-- attributed by blocks: {running} lines"
  -- residue
  let mut rn := 0
  let mut byMod : Std.HashMap Name (Array Name) := {}
  let mut ivMod : Std.HashMap Name (Array (Nat × Nat)) := {}
  for (c, m) in cs do
    if !baseCl.contains c then
      if !c.isInternal && !isGen c then
        rn := rn + 1
        byMod := byMod.insert m ((byMod.getD m #[]).push c)
      if let some r ← Lean.findDeclarationRanges? c then
        ivMod := ivMod.insert m ((ivMod.getD m #[]).push (r.range.pos.line, r.range.endPos.line))
  let mut rl := 0
  let mut s := ""
  for (m, iv) in ivMod.toList do
    let ls := (lineSet iv).size
    rl := rl + ls
    let ns := byMod.getD m #[]
    s := s ++ s!"---- {m}  ({ns.size} decls, {ls} lines)\n"
    for n in ns do s := s ++ s!"   {n}\n"
  IO.FS.writeFile (outDir ++ "/residue.txt") s
  IO.println s!"-- RESIDUE (in no block): {rn} decls, {rl} lines; wrote residue.txt"

-- which decls of the Salvetti / arrangement / H modules ARE in the four-cone.
open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom := liveDom cs
  let cone := closure env dom theFour
  let pfx : Array Name := #[`CubeChains.Concurrency.Salvetti, `CubeChains.Machinery.Arrangement,
    `CubeChains.Concurrency.Complexification, `CubeChains.Concurrency.Executions,
    `CubeChains.Machinery.Braid, `CubeChains.Foundations.Polygraph]
  let mut s := ""
  for (n, m) in cs do
    if cone.contains n && !n.isInternal && !isGen n && pfx.any (fun p => Name.isPrefixOf p m) then
      s := s ++ s!"{m}\t{n}\n"
  IO.FS.writeFile (outDir ++ "/incone_areas.tsv") s
  IO.println "wrote incone_areas.tsv"
