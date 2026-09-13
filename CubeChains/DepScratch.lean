/- scratch: constant-dependency graph over the CubeChains modules.  Not part of the library. -/
import CubeChains.Concurrency.Salvetti.SalBraid
import CubeChains.Concurrency.Executions.ChStarProduct
import CubeChains.Concurrency.Complexification.ChStarSym
import CubeChains.Concurrency.Salvetti.SalCompare
import CubeChains.Machinery.Arrangement.SalSymmetry
import CubeChains.Concurrency.Complexification.SymReorient
import CubeChains.Concurrency.Salvetti.WallCrossing
import CubeChains.Concurrency.Salvetti.CrossCompare
import CubeChains.Concurrency.Complexification.HPresentation
import CubeChains.Machinery.Braid.Artin
import CubeChains.Machinery.Braid.PosGerm
import CubeChains.Machinery.Braid.Matsumoto
import CubeChains.Machinery.Braid.MatsumotoCat
import CubeChains.Machinery.Graded
import CubeChains.Machinery.Braid.Sum
import CubeChains.Precubical.Basic.Nerve
import CubeChains.Precubical.Wedge.GeoTensor.BP
import CubeChains.Machinery.Arrangement.COMSum
import CubeChains.Machinery.Cube.SymBox
import CubeChains.Machinery.Cube.SymPresheaf
import CubeChains.Machinery.Cube.SymRepresentable
import CubeChains.Machinery.Cube.HMonad
import CubeChains.Concurrency.Complexification.SymRun
import CubeChains.Concurrency.Complexification.SymOverRun
import CubeChains.Concurrency.Merge.MergeClass
import CubeChains.Concurrency.Grading.WedgeBraid
import CubeChains.Concurrency.Grading.ChainHom
import CubeChains.Concurrency.Merge.MergeBraid
import CubeChains.Concurrency.Merge.MergeGenerate
import CubeChains.Concurrency.Merge.Factorisation
import CubeChains.Concurrency.Merge.Atom
import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Machinery.Localization.FibrationLocalize
import CubeChains.Machinery.Slice
import CubeChains.Concurrency.Merge.SegalCondition
import CubeChains.Concurrency.Presentation.ElementsFibration
import CubeChains.Concurrency.Complexification.RunClassifier
import CubeChains.Concurrency.Complexification.HSegal
import CubeChains.Machinery.Braid.PosAction
import CubeChains.Concurrency.Merge.CubeCrossing
import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Concurrency.Merge.CubeFaces
import CubeChains.Machinery.Localization.ElementsAction
import CubeChains.Concurrency.Complexification.HPosAction
import CubeChains.Machinery.Presentation.Elements
import CubeChains.Machinery.Presentation.Comparison
import CubeChains.Machinery.Presentation.Localize
import CubeChains.Machinery.Presentation.Contract
import CubeChains.Machinery.Presentation.ContractMap
import CubeChains.Machinery.Presentation.Reduce
import CubeChains.Machinery.Presentation.SpansMap
import CubeChains.Machinery.Presentation.Monoid
import CubeChains.Machinery.Presentation.Coproduct
import CubeChains.Foundations.Polygraph.Presheaf
import CubeChains.Foundations.Polygraph.Day
import CubeChains.Foundations.Polygraph.DayCoend
import CubeChains.Foundations.Polygraph.Tensor
import CubeChains.Foundations.Polygraph.Monoidal
import CubeChains.Machinery.Presentation.ColimitCells
import CubeChains.Concurrency.Presentation.SliceRunSet
import CubeChains.Concurrency.Presentation.CutPresentation
import CubeChains.Concurrency.Presentation.LiftPresentation
import CubeChains.Machinery.Presentation.ElementsLocalize
import CubeChains.Concurrency.Presentation.LocFunctor
import CubeChains.Concurrency.Presentation.LiftLocalize
import CubeChains.Concurrency.Presentation.LocPresentation
import CubeChains.Concurrency.Presentation.RunContract
import CubeChains.Concurrency.Presentation.Retraction
import CubeChains.Concurrency.Presentation.BaseComponent
import CubeChains.Concurrency.Presentation.BasePresentation
import CubeChains.Concurrency.Presentation.ArtinDegreeZero
import CubeChains.Concurrency.Presentation.RunReduce
import CubeChains.Concurrency.Presentation.RunArrows
import CubeChains.Concurrency.Presentation.BeadOrder
import CubeChains.Concurrency.Presentation.TopRefinement
import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.RunCellFunctor
import CubeChains.Concurrency.Presentation.CellNatural
import CubeChains.Concurrency.Presentation.PaperPoly
import CubeChains.Concurrency.Presentation.PaperPresents
import CubeChains.Concurrency.Presentation.PaperFunctor
import CubeChains.Concurrency.Presentation.PaperArtin
import CubeChains.Concurrency.Presentation.PaperAtoms
import CubeChains.Concurrency.Presentation.HAction
import CubeChains.Machinery.Rewriting.Newman
import CubeChains.Machinery.Rewriting.Presentation
import CubeChains.Testing.Enumerate.FastEquiv

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

/-- closure in the reverse graph: everything that (transitively) uses a seed. -/
def revClosure (rg : Std.HashMap Name (Array Name)) (seeds : Array Name) :
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
    for u in rg.getD n #[] do
      if !seen.contains u then
        seen := seen.insert u
        stack := stack.push u
  return seen

/-- module prefixes kept wholesale, whatever the anchors say. -/
def keptPrefixes : Array Name :=
  #[`CubeChains.Precubical, `CubeChains.Machinery.Cube, `CubeChains.Concurrency.Salvetti,
    `CubeChains.Concurrency.Complexification, `CubeChains.Testing,
    `CubeChains.Concurrency.Presentation.HAction]

def inKept (m : Name) : Bool := keptPrefixes.any fun p => Name.isPrefixOf p m

end DepScratch

open CategoryTheory CubeChains ChainCat DepScratch in
/-- the anchors of `CubeChains.lean` that survive the retirement. -/
def keepAnchors : Array Name :=
  #[``runBraidEquiv, ``runArtinEquiv, ``chLocEquivElements, ``hLocEquiv, ``hLocArtinEquiv,
    ``ChainCat.chCutLocPresentation, ``ChainCat.chCellPresentation, ``ChainCat.chCellPresentationIso,
    ``ChainCat.Paper.runEquiv, ``ChainCat.Paper.factorWords, ``ChainCat.Paper.objWords,
    ``ChainCat.Paper.poly, ``ChainCat.Paper.paperPresents, ``ChainCat.Paper.polyFunctor,
    ``ChainCat.Paper.paperPresentationIso, ``ChainCat.Paper.paperPresentationIso_id,
    ``ChainCat.Paper.cell_adj_iff, ``ChainCat.Paper.paperArtinIso,
    ``fullBaseEquiv, ``BraidPresentation.braids, ``BraidPresentation.braids_at',
    ``BraidPresentation.braids_arrow, ``BraidPresentation.pt_injective,
    ``BraidPresentation.exists_pt, ``BraidPresentation.ofMonoids, ``germBP, ``artinBP,
    ``germBP_bySimples, ``artinBP_bySimples, ``artinBraids_arrow,
    ``Polygraph.dayIsCoend, ``Polygraph.dayIso, ``Polygraph.cell_ofDayCells_square,
    ``Polygraph.tensorObj_eq,
    ``chLocMap, ``chLocMap_id, ``chLocMap_comp, ``chLocOpFunctor, ``chLocOpFunctor_map,
    ``Polygraph.Presents.Map.refl, ``Polygraph.Presents.Map.trans,
    ``exists_not_isRun_over, ``zCutPresentation, ``Presents.presentsLocalization,
    ``zCutLocPresentation, ``chPresentation, ``chCutPresentation,
    ``hLocPresentation, ``hLocArtinPresentation, ``hLocActionPresentation,
    ``germPresentation, ``artinComponent, ``Presents.ofThin,
    ``Presents.elements, ``CategoryOfElements.endEquivStabilizer,
    ``presentedMonoidPresentation, ``Polygraph.exists_colimit_ι_obj,
    ``separatesMerges_cube, ``exists_join, ``wedge2Map_isPushout, ``W_iff_crossPerm_eq_one,
    ``W_iff_monotone_coordMap, ``nonempty_wedgeHom_iff_coarser,
    ``oneCutEquivCuts, ``oneCutEquivBool, ``OneCut.codim_snd,
    ``dims_pairChain_of_adj, ``dims_pairChain_of_apart, ``nonempty_hom_atomComp_iff,
    ``exists_atomPair_of_codim_two, ``artin_of_codim_two, ``atomLoop_comm, ``atomLoop_braid,
    ``exists_atomWord_conj, ``Cut.exists_atomComp, ``eq_atomOnes, ``onesTopEquiv,
    ``not_W_wallLeg, ``wallCrossLoc, ``hom_ext_of_crossPerm, ``index_crossPerm,
    ``chEquivElements, ``isLocalization_chDescent, ``isSegal_iff_existsUnique, ``isSegal_H_cube,
    ``separatesMerges_of_invertsMerges, ``HOverRun, ``HbpOverRun, ``isEmpty_cubeProdHom,
    ``run_HbpZbp_eq, ``Models, ``Models.salEquiv, ``Models.hbpEquiv, ``braidModels,
    ``RunWedge.permOf_noDoubleCross, ``ConcPos, ``chFaceCatEquiv, ``execEquiv,
    ``ChStar.stepPerm_eq, ``hbpBraidSalEquiv, ``crossPerm_eq_topeCross,
    ``reorientCh_comp_hbpBraidSalEquiv, ``chToAction, ``chToAction_obj_surjective,
    ``garside_equiv_artin, ``posBraid_equiv_artinPos,
    ``not_surjective_posToBraid, ``end_not_generated_by_simples, ``not_desym_natural,
    ``not_invertsMerges_runBp, ``not_invertsMerges_Hbp_Zbp, ``isEmpty_cubeHom,
    ``not_exists_hom_to_all_cube, ``not_reorientCh_of_over_base,
    ``not_surjective_faceComparison_cube_two, ``not_injective_faceComparison_H_Z,
    ``not_isSegal_cube_two, ``not_invertsMerges_of_splitting,
    ``GeoTensor.geoMonoidal, ``COM.salSumEquiv, ``PrecubicalSet.nerveRealizeIso,
    ``GeoTensor.cubeTensorIsoBP, ``CubeChain.equivWedgeCat,
    ``Relation.Confluent.existsUnique_normal, ``Relation.LocallyConfluent.confluent,
    ``Relation.Confluent.union, ``Polygraph.Orientation.complete,
    ``Polygraph.Orientation.ofShortening, ``Polygraph.Orientation.quot_eq_iff_normal_eq]

open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom : Std.HashSet Name := cs.foldl (fun s (n, _) => s.insert n) {}
  let modOf : Std.HashMap Name Name := cs.foldl (fun s (n, m) => s.insert n m) {}
  let keptConsts := cs.filterMap (fun (n, m) => if inKept m then some n else none)
  let seeds := keepAnchors ++ keptConsts
  let cl := closure env dom seeds
  IO.println s!"seeds: {seeds.size}  closure: {cl.size} / {dom.size}"
  -- per-module: total, in-closure
  let mods := (cubeModules env).map (·.2)
  let mut tot : Std.HashMap Name Nat := {}
  let mut live : Std.HashMap Name Nat := {}
  for (n, m) in cs do
    tot := tot.insert m (tot.getD m 0 + 1)
    if cl.contains n then live := live.insert m (live.getD m 0 + 1)
  let mut deadMods : Array Name := #[]
  for m in mods do
    let t := tot.getD m 0
    let l := live.getD m 0
    if t > 0 && l == 0 then deadMods := deadMods.push m
    else if t > 0 then IO.println s!"LIVE {l}/{t}  {m}"
  IO.println "---- modules with no constant in the closure ----"
  for m in deadMods do IO.println s!"DEAD {tot.getD m 0}  {m}"
  let _ := modOf

/-- modules to explain: which of their constants are live, and which anchor wants them. -/
def probeModules : Array Name :=
  #[`CubeChains.Concurrency.Merge.CubeThin, `CubeChains.Concurrency.Merge.CubeFaces,
    `CubeChains.Concurrency.Merge.CubeCrossing, `CubeChains.Concurrency.Presentation.SliceRuns,
    `CubeChains.Concurrency.Presentation.SliceRunSet,
    `CubeChains.Concurrency.Presentation.BeadRuns,
    `CubeChains.Concurrency.Presentation.BeadOrder,
    `CubeChains.Machinery.Localization.SliceLocalize,
    `CubeChains.Machinery.Localization.HomInduction,
    `CubeChains.Machinery.Localization.FibrationLocalize,
    `CubeChains.Machinery.Braid.PosAction,
    `CubeChains.Machinery.Presentation.ColimitCells,
    `CubeChains.Concurrency.Merge.Factorisation]

open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom : Std.HashSet Name := cs.foldl (fun s (n, _) => s.insert n) {}
  let keptConsts := cs.filterMap (fun (n, m) => if inKept m then some n else none)
  let seeds := keepAnchors ++ keptConsts
  let cl := closure env dom seeds
  let rg := revGraph env dom
  let modOf : Std.HashMap Name Name := cs.foldl (fun s (n, m) => s.insert n m) {}
  let anchorSet : Std.HashSet Name := keepAnchors.foldl (fun s n => s.insert n) {}
  for pm in probeModules do
    IO.println s!"==== {pm}"
    for (n, m) in cs do
      if m == pm && cl.contains n && !n.isInternal then
        let rc := revClosure rg #[n]
        -- which surviving anchors use it
        let mut hits : Array Name := #[]
        for a in keepAnchors do
          if rc.contains a then hits := hits.push a
        -- which kept-directory modules use it
        let mut kmods : Std.HashSet Name := {}
        for u in rc do
          match modOf[u]? with
          | some mu => if inKept mu then kmods := kmods.insert mu
          | none => pure ()
        IO.println s!"  {n}"
        IO.println s!"     anchors: {hits.toList.take 6}"
        IO.println s!"     keptmods: {kmods.toList.take 6}"
    let _ := anchorSet

def trimModules : Array Name :=
  #[`CubeChains.Concurrency.Merge.CubeFaces, `CubeChains.Concurrency.Merge.CubeCrossing,
    `CubeChains.Concurrency.Presentation.BeadOrder,
    `CubeChains.Concurrency.Presentation.SliceRuns,
    `CubeChains.Concurrency.Presentation.SliceRunSet,
    `CubeChains.Concurrency.Presentation.BeadRuns,
    `CubeChains.Machinery.Localization.FibrationLocalize,
    `CubeChains.Machinery.Localization.SliceLocalize,
    `CubeChains.Machinery.Braid.PosAction,
    `CubeChains.Concurrency.Merge.Factorisation,
    `CubeChains.Concurrency.Merge.TotalMerge,
    `CubeChains.Concurrency.Grading.TopBead,
    `CubeChains.Machinery.Braid.WeakOrder,
    `CubeChains.Machinery.Presentation.Comparison,
    `CubeChains.Machinery.Rewriting.Presentation]

open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom : Std.HashSet Name := cs.foldl (fun s (n, _) => s.insert n) {}
  let keptConsts := cs.filterMap (fun (n, m) => if inKept m then some n else none)
  let cl := closure env dom (keepAnchors ++ keptConsts)
  for pm in trimModules do
    let mut ds : Array Name := #[]
    for (n, m) in cs do
      if m == pm && !cl.contains n && !n.isInternal then ds := ds.push n
    IO.println s!"==== {pm}  dead: {ds.size}"
    for d in ds do IO.println s!"   {d}"

def generated : Array String :=
  #["_eq_", "eq_def", "match_", "mk.", "noConfusion", "ctorIdx", "sizeOf_spec",
    "injEq", "proof_", "below", "brecOn", "_sunfold", "_unsafe_rec", "eq_1", "eq_2", "eq_3",
    "eq_4", "eq_5", "eq_6", "eq_7", "eq_8", "eq_9"]

def isGen (n : Name) : Bool :=
  let s := n.toString
  generated.any (fun g => ((s.splitOn g).length > 1 : Bool)) ||
    [".rec", ".recOn", ".casesOn", ".inj", ".ofNat", ".ind"].any (fun g => s.endsWith g)

open DepScratch in
#eval show CoreM Unit from do
  let env ← getEnv
  let cs := cubeConsts env
  let dom : Std.HashSet Name := cs.foldl (fun s (n, _) => s.insert n) {}
  let keptConsts := cs.filterMap (fun (n, m) => if inKept m then some n else none)
  let cl := closure env dom (keepAnchors ++ keptConsts)
  let mods := (cubeModules env).map (·.2)
  IO.println "======== FULL DEAD LIST (non-generated) ========"
  for pm in mods do
    let mut ds : Array Name := #[]
    for (n, m) in cs do
      if m == pm && !cl.contains n && !n.isInternal && !isGen n then ds := ds.push n
    if ds.size > 0 then
      IO.println s!"---- {pm}  ({ds.size})"
      for d in ds do IO.println s!"   {d}"
