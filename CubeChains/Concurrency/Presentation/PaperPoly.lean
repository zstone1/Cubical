import CubeChains.Concurrency.Presentation.TopRefinement
import CubeChains.Concurrency.Presentation.RunCells
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Concurrency/Presentation/PaperPoly — the polygraph, defined directly

0-cells the runs; cells the **objects**, graded by degree — degree one a 1-cell, degree two a
2-cell.  An object needs no refinement beside it, both of its ends being functions of it:

    X.chain ──bottomHom──▸ obj ◂──topOf── Y.chain            a cell  X ⟶ Y

At degree one the greatest refinement is the *only* crossing one, so a degree-one object carries
exactly one 1-cell; at degree two `oneCutEquivBool` names its two factorisations and `cutWord`
spells each — one letter or two, which is the braid/commutation asymmetry.
-/

open CategoryTheory CategoryTheory.Polygraph BPSet CubeChains Equiv

namespace ChainCat.Paper

variable {K : BPSet}

/-! ## The cells -/

/-- A **cell** `X ⟶ Y` of dimension `n`: an **object of degree `n`**, read between the two runs it
spans — `X` the run below it (its merge), `Y` the run its greatest refinement comes out of (the
complement of that merge).  Both ends are functions of the object, so the object is the only datum.

Dimension one is a generator and dimension two a relation: the same data one degree up.  At
dimension one `topOf` is the *only* crossing refinement (`topOf_fst_eq_of_not_W`), which is why a
degree-one object needs no cut beside it. -/
structure Cell (n : ℕ) (X Y : Run K) where
  /-- the object -/
  obj : Ch K
  /-- …of degree `n` -/
  degree_obj : degree obj = n
  /-- the run below it -/
  below : bottomRun obj = X
  /-- the run its greatest refinement comes out of -/
  top : (topOf obj).1 = Y

/-- **A cell is its object** — the three remaining fields are proofs. -/
theorem Cell.ext {n : ℕ} {X Y : Run K} : ∀ {α β : Cell n X Y}, α.obj = β.obj → α = β
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, h => by subst h; rfl

/-- A **1-cell**: a degree-one object. -/
abbrev Gen (X Y : Run K) : Type := Cell 1 X Y

/-- **The refinement a cell carries**, out of the run at its far end. -/
noncomputable abbrev Cell.hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) : Y.chain ⟶ α.obj :=
  eqToHom (congrArg Run.chain α.top.symm) ≫ (topOf α.obj).2

/-- **A cell's refinement has codimension `n`.** -/
theorem Cell.codim_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) : codim α.hom = n :=
  ((codim_eqToHom_comp _ _).trans (codim_topOf α.obj)).trans α.degree_obj

/-- **…and it crosses**, at every positive degree (`not_W_topOf`). -/
theorem Cell.not_W_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) (hn : n ≠ 0) : ¬ W K α.hom := by
  intro h
  exact not_W_topOf α.obj (α.degree_obj.trans_ne hn)
    (W_of_comp_right (eqToHom (congrArg Run.chain α.top.symm)) _ h)

/-- **A 1-cell's refinement is any crossing refinement out of its far end** — at degree one there is
only one (`hom_eq_of_not_W_deg_one`). -/
theorem Cell.hom_eq {X Y : Run K} (α : Gen X Y) {f : Y.chain ⟶ α.obj} (hf : ¬ W K f) :
    α.hom = f :=
  hom_eq_of_not_W_deg_one α.degree_obj (α.not_W_hom one_ne_zero) hf

/-- **A crossing codimension-one refinement out of a run is a 1-cell** — the object it lands on,
read between the run below it and the run it comes out of. -/
def genOfHom {X : Run K} {e : Ch K} (he : degree e = 1) {f : X.chain ⟶ e} (hf : ¬ W K f) :
    Gen (bottomRun e) X := ⟨e, he, rfl, topOf_fst_eq_of_not_W he hf⟩

@[simp] theorem genOfHom_obj {X : Run K} {e : Ch K} (he : degree e = 1) {f : X.chain ⟶ e}
    (hf : ¬ W K f) : (genOfHom he hf).obj = e := rfl

/-- **A cell's refinement crosses what the greatest one does** — it *is* the greatest one, read at
the other name for its source. -/
theorem runCross_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    runCross α.hom = runCross (topOf α.obj).2 := runCross_W_comp (W_eqToHom _) _

/-- …so it attains the capacity. -/
theorem permLen_runCross_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    permLen (runCross α.hom) = crossCap α.obj.dims :=
  (congrArg permLen (runCross_hom α)).trans (permLen_runCross_topOf α.obj)

/-- **…which makes it the object's greatest refinement** — it *is* `topOf`'s, read at the other name
its cell gives the run. -/
theorem isTop_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) : IsTop α.hom :=
  isTop_eqToHom_comp α.top

/-- A 0-cell, as a vertex of the generating quiver — `Polygraph.pt` before `poly` exists. -/
abbrev runPt (X : Run K) : GenObj (Gen (K := K)) := ⟨X⟩

/-- A word read at other names for its two ends — the only transport a word here carries. -/
def readAt {X X' Y Y' : Run K} (hx : X = X') (hy : Y = Y')
    (w : Quiver.Path (runPt X) (runPt Y)) : Quiver.Path (runPt X') (runPt Y') :=
  cellCongr Quiver.Path (congrArg runPt hx) (congrArg runPt hy) w

/-! ## A kept cut of the contraction, as a 1-cell

`RunCut` says the cut starts at a run, and the merge onto the chain it lands on is the contraction's
own (`runMergeK`) — so a kept 1-cell carries exactly a `Gen`'s data. -/

theorem codim_chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b) :
    codim (chCutHom e) = 1 := e.1.2

theorem not_W_chCutHom {a b : (chCutPoly K).V} (e : (chCutPoly K).Gen a b)
    (he : ¬ chCutPicked K e) : ¬ W K (chCutHom e) := fun hW =>
  he ((merge_iff (Cut.genHom e.1)).mpr ⟨(W_baseHom_iff _).mpr hW, Cut.codim_genHom e.1⟩)

/-- **A kept 1-cell of the collapse is a 1-cell here** — the same degree-one object.  Its cut is
the object's greatest refinement, because at degree one there is no other crossing one. -/
noncomputable def genOfRunCut {U V : (chCollapse K).V} (g : (chCollapse K).Gen U V)
    (hg : RunCut g) : Gen (runOfV U) (runOfV V) :=
  cellCongr (Cell 1) (congrArg runOfV (Subtype.ext g.rep_dom))
    (congrArg runOfV (Subtype.ext (hg.symm.trans g.rep_cod)))
    (show Cell 1 (runOfV ⟨eltRep g.dom, eltRep_idem _⟩) (runOfV ⟨g.cod, hg⟩) from
      have hdeg : degree (vChain g.dom) = 1 := by
        have h1 := degree_eq_add_codim (chCutHom g.gen)
        rw [(isRun_iff_degree_eq_zero _).mp (isRun_vChain ⟨g.cod, hg⟩),
          codim_chCutHom g.gen] at h1
        simpa using h1
      { obj := vChain g.dom
        degree_obj := hdeg
        below := eq_bottomRun_of_W (runMergeK g.dom) (W_runMergeK g.dom)
        top := topOf_fst_eq_of_not_W (X := runOfV ⟨g.cod, hg⟩) hdeg
          (not_W_chCutHom g.gen g.not_mem) })

/-- **The comparison of generating quivers**: the kept cuts of the collapse, read on the runs. -/
noncomputable def runPre : GenObj (chRunCutSpans K).poly.Gen ⥤q GenObj (Gen (K := K)) where
  obj U := runPt (runOfV U.as)
  map e := genOfRunCut e.1 e.2

/-! ## The word a codimension-one refinement reads as -/

/-- The 1-cell of the collapse a crossing codimension-one refinement is. -/
noncomputable def chGenOf {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) (hW : ¬ W K u) :
    (chCollapse K).Gen ⟨eltRep (chV d), eltRep_idem _⟩ ⟨eltRep (chV c), eltRep_idem _⟩ :=
  (chCollapse K).genCell
    (Polygraph.cell (cutGen (c := chV d) (c' := chV c) (baseMap u) hu u.w))
    (fun hm => hW ((W_baseHom_iff (a := chV c) (b := chV d) u).mp
      ((merge_iff (baseMap u)).mp hm).1))

/-- **The word a codimension-one refinement reads as**, between the runs of its two ends: a merge
reads as the empty word, and any other cut as the word its conjugate spells — one letter when it
starts at a run, two when it does not. -/
noncomputable def cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    Quiver.Path (runPt (bottomRun d)) (runPt (bottomRun c)) :=
  @dite _ (W K u) (Classical.propDecidable _)
    (fun hW => readAt rfl (bottomRun_eq_of_W u hW) Quiver.Path.nil)
    (fun hW => runPre.mapPath (keptWord (P := (chCollapse K).poly) RunCut
      (runCellWord (chGenOf u hu hW)) (all_runCellWord _)))

/-! ## The two words a codimension-two refinement out of a run reads as -/

/-- **The word a factorisation of a codimension-two refinement out of a run reads as.**  The first
leg is a cut out of the run, hence one letter; the second starts off a run, hence one or two — which
is the whole of the braid/commutation asymmetry. -/
noncomputable def factorWords {X : Run K} {b : Ch K} (f : X.chain ⟶ b) (hf : codim f = 2)
    (ε : Bool) : Quiver.Path (runPt (bottomRun b)) (runPt X) :=
  let F := (oneCutEquivBool f hf).symm ε
  readAt rfl (bottomRun_self X)
    ((cutWord F.1.snd (F.codim_snd hf)).comp (cutWord F.1.fst F.2))

/-- **The two words a degree-two object reads as** — `oneCutEquivBool` names the two factorisations
of its greatest refinement, and `cutWord` spells each.  No data beyond the object. -/
noncomputable def objWords (e : Ch K) (he : degree e = 2) (ε : Bool) :
    Quiver.Path (runPt (bottomRun e)) (runPt (topOf e).1) :=
  factorWords (topOf e).2 ((codim_topOf e).trans he) ε

/-- …read between the two runs a 2-cell spans, which is where its boundary lives. -/
noncomputable def cellWords {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    Quiver.Path (runPt X) (runPt Y) :=
  readAt α.below rfl (factorWords α.hom α.codim_hom ε)

/-- **The polygraph**: the runs, the codimension-one cuts out of them, and one relation per
codimension-two refinement out of a run, equating the words its two factorisations read as. -/
noncomputable def poly (K : BPSet) : Polygraph where
  V := Run K
  Gen := Gen
  Rel x y := Cell 2 x.as y.as
  src α := cellWords α false
  tgt α := cellWords α true

/-- **A 2-cell's two words spell one arrow** — `quot_src_tgt`, with the boundary named by
`cellWords` rather than by the structure projection. -/
theorem quot_cellWords {X Y : Run K} (α : Cell 2 X Y) :
    (poly K).quot.map (cellWords α false) = (poly K).quot.map (cellWords α true) :=
  (poly K).quot_src_tgt (x := runPt X) (y := runPt Y) α

end ChainCat.Paper
