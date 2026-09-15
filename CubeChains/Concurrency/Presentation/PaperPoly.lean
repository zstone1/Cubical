import CubeChains.Concurrency.Presentation.TopRefinement
import CubeChains.Concurrency.Presentation.RunAtoms
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

/-- **A cell's refinement crosses what the greatest one does** — it *is* the greatest one, read at
the other name for its source. -/
theorem runCross_hom {n : ℕ} {X Y : Run K} (α : Cell n X Y) :
    runCross α.hom = runCross (topOf α.obj).2 := runCross_W_comp (W_eqToHom _) _

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

/-! ## The runs over a chain, and the atoms between them

A run-arrow into a chain's *shape* is a run over the chain: the chain on the arrow's own events,
carrying the composite.  The shape is all these see, so the climb below is the same term over every
`K` — which is why the words are natural on the nose.  An ascent is the atom it crosses, read as a
degree-one object between the two runs it joins, so a climb spells a word of 1-cells. -/

/-- The wedge map a refinement of shapes carries. -/
abbrev zPhi {p q : List ℕ+} (r : zObj p ⟶ zObj q) : ⋁p ⟶ ⋁q := Hom.φ r

/-- The runs over a chain, as the crossing permutations its shape realises. -/
abbrev ChPerm (e : Ch K) : Type := ShapePerm (dimSum e.dims) (zObj e.dims)

/-- An ascent between two of them. -/
abbrev ChAsc (e : Ch K) (a b : ChPerm e) : Type :=
  Ascent (shapeLower (dimSum e.dims) (zObj e.dims)).perm a b

/-- The run over a chain a run-arrow of its shape names. -/
noncomputable def shapeRun (e : Ch K) (σ : ChPerm e) : Run K :=
  ⟨⟨𝟙^(dimSum e.dims), zPhi σ.arr ≫ e.map⟩, fun _ hd => List.eq_of_mem_replicate hd⟩

/-- …with the refinement it makes. -/
noncomputable def shapeHom (e : Ch K) (σ : ChPerm e) : (shapeRun e σ).chain ⟶ e :=
  ⟨zPhi σ.arr, rfl⟩

/-- **The merge run's refinement is a merge** — `W` sees only the wedge map. -/
theorem W_shapeHom_shapeBot (e : Ch K) : W K (shapeHom e (shapeBot (zObj e.dims) rfl)) :=
  (W_iff_of_φ (f := shapeHom e (shapeBot (zObj e.dims) rfl))
    (f' := (shapeBot (zObj e.dims) rfl).arr) rfl).mpr (W_shapeBot_arr rfl)

/-- **…so the run below a chain is the one its shape's merge names.** -/
theorem bottomRun_eq_shapeRun (e : Ch K) :
    bottomRun e = shapeRun e (shapeBot (zObj e.dims) rfl) :=
  eq_bottomRun_of_W (shapeHom e _) (W_shapeHom_shapeBot e)

/-- The degree-one object an ascent of a chain's runs names: the atom it crosses, over the
chain. -/
noncomputable def ascObj (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) : Ch K :=
  ⟨atomComp (dimSum e.dims) ε.idx, zPhi (ascLeg ε) ≫ e.map⟩

/-- **The atom an ascent crosses has degree one** — `degree` reads the shape alone. -/
theorem degree_ascObj (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) : degree (ascObj e ε) = 1 :=
  degree_atomComp (dimSum e.dims) ε.idx

/-- A leg out of an ascent's atom commutes over `K`, the leg below it being the ascent's own. -/
private theorem asc_w (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b)
    {m : zObj (𝟙^(dimSum e.dims)) ⟶ zObj (atomComp (dimSum e.dims) ε.idx)} {σ : ChPerm e}
    (h : m ≫ ascLeg ε = σ.arr) :
    zPhi m ≫ zPhi (ascLeg ε) ≫ e.map = zPhi σ.arr ≫ e.map := by
  rw [← Category.assoc, show zPhi m ≫ zPhi (ascLeg ε) = zPhi (m ≫ ascLeg ε) from rfl, h]

/-- The merge onto it out of the run below. -/
noncomputable def ascBot (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) :
    (shapeRun e a).chain ⟶ ascObj e ε :=
  ⟨zPhi (mergeOnes (dimSum e.dims) ε.idx), asc_w e ε (mergeOnes_ascLeg ε)⟩

/-- …and the atom's own cut, out of the run above. -/
noncomputable def ascTop (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) :
    (shapeRun e b).chain ⟶ ascObj e ε :=
  ⟨zPhi (atomOnes (dimSum e.dims) ε.idx), asc_w e ε (atomOnes_ascLeg ε)⟩

theorem W_ascBot (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) : W K (ascBot e ε) :=
  (W_iff_of_φ (f := ascBot e ε) (f' := mergeOnes (dimSum e.dims) ε.idx) rfl).mpr
    (W_mergeOnes _ ε.idx)

theorem not_W_ascTop (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) : ¬ W K (ascTop e ε) :=
  fun h => not_W_atomOnes (dimSum e.dims) ε.idx
    ((W_iff_of_φ (f := ascTop e ε) (f' := atomOnes (dimSum e.dims) ε.idx) rfl).mp h)

/-- **An ascent of a chain's runs is a 1-cell** — its atom is a degree-one object, entered by the
merge below and cut by the atom above. -/
noncomputable def ascGen (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) :
    Gen (shapeRun e a) (shapeRun e b) where
  obj := ascObj e ε
  degree_obj := degree_ascObj e ε
  below := eq_bottomRun_of_W (ascBot e ε) (W_ascBot e ε)
  top := topOf_fst_eq_of_not_W (X := shapeRun e b) (degree_ascObj e ε) (f := ascTop e ε)
    (not_W_ascTop e ε)

@[simp] theorem obj_ascGen (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) :
    (ascGen e ε).obj = ascObj e ε := rfl

/-- The leg an ascent's atom makes onto the chain. -/
noncomputable def ascLegHom (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) : ascObj e ε ⟶ e :=
  ⟨zPhi (ascLeg ε), rfl⟩

/-- **The merge below an ascent's atom is the run below it, read on the chain.** -/
theorem ascBot_comp (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) :
    ascBot e ε ≫ ascLegHom e ε = shapeHom e a :=
  hom_ext' (show zPhi (mergeOnes (dimSum e.dims) ε.idx) ≫ zPhi (ascLeg ε) = zPhi a.arr from
    congrArg zPhi (mergeOnes_ascLeg ε))

/-- **…and its cut is the run above it.** -/
theorem ascTop_comp (e : Ch K) {a b : ChPerm e} (ε : ChAsc e a b) :
    ascTop e ε ≫ ascLegHom e ε = shapeHom e b :=
  hom_ext' (show zPhi (atomOnes (dimSum e.dims) ε.idx) ≫ zPhi (ascLeg ε) = zPhi b.arr from
    congrArg zPhi (atomOnes_ascLeg ε))

/-- **The 1-cells out of the runs over a chain, as a prefunctor on the ascent quiver** — a climb's
word of 1-cells is its `mapPath`. -/
noncomputable def ascPre (e : Ch K) :
    Ascents (shapeLower (dimSum e.dims) (zObj e.dims)).perm ⥤q GenObj (Gen (K := K)) where
  obj a := runPt (shapeRun e a)
  map ε := ascGen e ε

/-- The merge onto a refinement's source out of the run, counted at the target's events. -/
noncomputable def cutMerge {c d : Ch K} (u : c ⟶ d) : zObj (𝟙^(dimSum d.dims)) ⟶ zObj c.dims :=
  runMerge (zObj c.dims) (dimSum_eq_of_hom u)

/-- The run over a refinement's target that its source names. -/
noncomputable def cutTop {c d : Ch K} (u : c ⟶ d) : ChPerm d := runOf (cutMerge u ≫ baseMap u)

private theorem cutTop_w {c d : Ch K} (u : c ⟶ d) :
    zPhi (cutMerge u) ≫ c.map = zPhi ((cutTop u).arr) ≫ d.map := by
  rw [show (cutTop u).arr = cutMerge u ≫ baseMap u from arr_runOf _,
    show zPhi (cutMerge u ≫ baseMap u) = zPhi (cutMerge u) ≫ zPhi (baseMap u) from rfl,
    Category.assoc, show zPhi (baseMap u) ≫ d.map = c.map from u.w]

/-- The merge out of it onto the source. -/
noncomputable def cutTopHom {c d : Ch K} (u : c ⟶ d) : (shapeRun d (cutTop u)).chain ⟶ c :=
  ⟨zPhi (cutMerge u), cutTop_w u⟩

/-- The climb from a chain's merge run up to the run a refinement's source names.

Name `N` here: left implicit, `rfl` solves it as `dimSum (zObj d.dims).dims`, and reconciling that
with `dimSum d.dims` sends `isDefEq` into `crossPerm`, which does not come back. -/
noncomputable def cutClimb {c d : Ch K} (u : c ⟶ d) :
    Climb (shapeLower (dimSum d.dims) (zObj d.dims)).perm
      (shapeBot (zObj d.dims) rfl) (cutTop u) :=
  shapeClimb (N := dimSum d.dims) (zObj d.dims) rfl (cutTop u)

/-- The word of 1-cells that climb spells. -/
noncomputable def cutClimbWord {c d : Ch K} (u : c ⟶ d) :
    Quiver.Path (runPt (shapeRun d (shapeBot (zObj d.dims) rfl)))
      (runPt (shapeRun d (cutTop u))) :=
  (ascPre d).mapPath (cutClimb u)

theorem W_cutTopHom {c d : Ch K} (u : c ⟶ d) : W K (cutTopHom u) :=
  (W_iff_of_φ (f := cutTopHom u) (f' := cutMerge u) rfl).mpr (W_runMerge _ _)

/-- **The run a refinement's source names over its target is the run below the source.** -/
theorem shapeRun_cutTop {c d : Ch K} (u : c ⟶ d) : shapeRun d (cutTop u) = bottomRun c :=
  (eq_bottomRun_of_W (cutTopHom u) (W_cutTopHom u)).symm

/-- **…and its refinement is that merge, followed by the cut.** -/
theorem cutTopHom_comp {c d : Ch K} (u : c ⟶ d) : cutTopHom u ≫ u = shapeHom d (cutTop u) :=
  hom_ext' (show zPhi (cutMerge u) ≫ Hom.φ u = zPhi ((cutTop u).arr) from
    (congrArg zPhi (arr_runOf (cutMerge u ≫ baseMap u))).symm)

/-- **A cut out of a run lands on a degree-one object** — the source has no bead to keep. -/
theorem degree_eq_one_of_isRun {c d : Ch K} {u : c ⟶ d} (hc : IsRun K c) (hu : codim u = 1) :
    degree d = 1 := by
  rw [codim, (isRun_iff_degree_eq_zero c).mp hc, Nat.sub_zero] at hu
  exact hu

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
noncomputable def runPre : GenObj (RunAtom K) ⥤q GenObj (Gen (K := K)) where
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
reads as the empty word, a cut out of a run as its own letter, and any other cut as the climb of
atoms its conjugate spells.  Every letter is a degree-one object. -/
noncomputable def cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) :
    Quiver.Path (runPt (bottomRun d)) (runPt (bottomRun c)) :=
  @dite _ (W K u) (Classical.propDecidable _)
    (fun hW => readAt rfl (bottomRun_eq_of_W u hW) Quiver.Path.nil)
    (fun hW => @dite _ (IsRun K c) (Classical.propDecidable _)
      (fun hc => readAt rfl (bottomRun_self ⟨c, hc⟩).symm
        (Quiver.Hom.toPath (V := GenObj (Gen (K := K)))
          (genOfHom (degree_eq_one_of_isRun hc hu) (X := ⟨c, hc⟩) hW)))
      (fun _ => readAt (bottomRun_eq_shapeRun d).symm (shapeRun_cutTop u) (cutClimbWord u)))

/-! ## The two words a codimension-two refinement out of a run reads as -/

/-- **The word a factorisation of a codimension-two refinement out of a run reads as.**  The first
leg is a cut out of the run, hence one letter; the second starts off a run, hence one or two — which
is the whole of the braid/commutation asymmetry. -/
noncomputable def factorWords {X : Run K} {b : Ch K} (f : X.chain ⟶ b) (hf : codim f = 2)
    (ε : Bool) : Quiver.Path (runPt (bottomRun b)) (runPt X) :=
  let F := (oneCutEquivBool f hf).symm ε
  readAt rfl (bottomRun_self X)
    ((cutWord F.1.π (F.codim_π hf)).comp (cutWord F.1.ι F.2))

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
