import CubeChains.Concurrency.Presentation.GlueVsFibration
import CubeChains.Concurrency.Presentation.GlueRun

/-!
# Concurrency/Presentation/GlueArtin — the Artin generators, spelled by glue 1-cells

`Ch(Hbp □ⁿ)[W⁻¹]` is presented twice: by the colimit of the Artin-inherited slices
(`presentsChainsArtinColimit`) and by the base's Artin generators acting on the fibre over the run
(`hLocArtinPresentation`).  The comparison sends **generator to generator**: the `k`-th Artin
generator at the run `z` is the single 1-cell in the copy at `atomComp n k` carrying the chart `z`
is merged from, whose two 0-cells are the atom leg and the merge leg.

It is a bijection in both dimensions (`bijective_genQuiver`), so the two polygraphs share their
generating data, and on both sides the 2-cells are the base's Artin relations read at a run.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Localization

namespace ChainCat

/-! ## The Artin-inherited slices

A 0-cell of a copy is a run over the copy's chain and a 1-cell is an Artin letter acting on one;
`SliceInherit` supplies both dictionaries, and separation makes the 0-cell one. -/

/-- The Artin-inherited slice family, glued below. -/
noncomputable abbrev artinFam : Ch Zbp ⥤ Polygraph.{0, 0, 0} := artinBP.fam

/-- **The 0-cell of an Artin copy a run names.** -/
noncomputable abbrev artinRunPt {d : Ch Zbp} {N : ℕ} (u : RunAt d N) :
    (slicePolyRaw artinBP.base d).V :=
  artinBP.runPt u

theorem sliceCellOver_artinRunPt {d : Ch Zbp} {N : ℕ} (u : RunAt d N) :
    sliceCellOver (artinRunPt u) = u.1.1 :=
  artinBP.sliceCellOver_runPt u

theorem famV_artinRunPt {d' d : Ch Zbp} (f : d' ⟶ d) {N : ℕ} (u : RunAt d' N) :
    Presents.famV artinBP.base _ (partialFam_push f) (artinRunPt u)
      = artinRunPt (RunAt.push f u) :=
  artinBP.famV_runPt f u

/-- **The 1-cell the `k`-th Artin letter acting on a run names.** -/
noncomputable abbrev artinRunGen {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (k : Fin (N - 1))
    (h : (sliceActionAt d N (posPerm (adjT k))).unop.val (some u) = some v) :
    (⟨artinRunPt u⟩ : GenObj (slicePolyRaw artinBP.base d).Gen) ⟶ ⟨artinRunPt v⟩ :=
  artinBP.runGen k h

/-- **1-cells of a copy are pinned by their letter**, across an identification of their 0-cells. -/
theorem artinRunGen_ext {d : Ch Zbp} {a b a' b' : (slicePolyRaw artinBP.base d).V}
    (ha : a = a') (hb : b = b')
    (g₀ : (⟨a⟩ : GenObj (artinFam.obj d).Gen) ⟶ ⟨b⟩)
    (g : (⟨a'⟩ : GenObj (artinFam.obj d).Gen) ⟶ ⟨b'⟩) (h : HEq g₀.1 g.1) :
    Quiver.homOfEq g₀ (congrArg GenObj.mk ha) (congrArg GenObj.mk hb) = g := by
  subst ha; subst hb; exact Subtype.ext (eq_of_heq h)

/-! ## The atom's cell, as a copy

A copy is indexed by an element of `wedgeHoms K` — a chain of the base with a map into `K`, which
is what `toElements` names — and above a run the `k`-th atom's cell is the chain `atomComp n k`,
with the run as its merge leg.  Its chart is forced: the merges act bijectively on the fibre
(`IsSegal`), so the run determines what it was merged from. -/

section Cube

variable {n : ℕ} (k : Fin (n - 1)) (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n))

/-- **The chart the `k`-th atom's cell carries above a run** — the run, un-merged across the cut.
Nothing is chosen: the merge is inverted in the localized base. -/
noncomputable def atomWitness : ⋁(atomComp n k) ⟶ Hbp.obj (□n) :=
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  (hFibre n).map (inv (((W Zbp).op).Q.map (mergeOnes n k).op)) z

/-- **The merge leg of the cell restricts to the run.** -/
theorem mergeOnes_atomWitness : (mergeOnes n k).φ ≫ atomWitness k z = z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  have h1 : (hFibre n).map (((W Zbp).op).Q.map (mergeOnes n k).op) (atomWitness k z) = z := by
    rw [atomWitness, ← (hFibre n).map_comp_apply, IsIso.inv_hom_id, (hFibre n).map_id_apply]
  rwa [hFibre_map_Q] at h1

/-- **…and the crossing leg restricts to the run the atom acts to.** -/
theorem atomOnes_atomWitness :
    (atomOnes n k).φ ≫ atomWitness k z = (hFibre n).map (atomLoop n k) z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  have hconj : atomLoop n k
      = inv (((W Zbp).op).Q.map (mergeOnes n k).op)
          ≫ ((W Zbp).op).Q.map (atomOnes n k).op := by
    rw [atomLoop, conj,
      show runMerge (zObj (𝟙^n)) (dimSum_replicate n) = 𝟙 _ from endo_eq_id _,
      op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [hconj, (hFibre n).map_comp_apply, hFibre_map_Q]
  rfl

/-- The crossing leg of the atom's cell, as a run over that cell. -/
def atomRunAt : RunAt (zObj (atomComp n k)) n := RunAt.push (atomOnes n k) (runAtSelf n)

/-- …and the merge leg. -/
noncomputable def mergeRunAt : RunAt (zObj (atomComp n k)) n :=
  RunAt.push (mergeOnes n k) (runAtSelf n)

@[simp] theorem perm_atomRunAt : (atomRunAt k).perm = adjT k := by
  rw [atomRunAt, RunAt.push_perm _ (dimSum_replicate n), perm_runAtSelf, mul_one,
    crossPerm_atomOnes]

@[simp] theorem perm_mergeRunAt : (mergeRunAt k).perm = 1 := by
  rw [mergeRunAt, RunAt.push_perm _ (dimSum_replicate n), perm_runAtSelf, mul_one,
    crossPerm_eq_one_of_W _ (W_mergeOnes n k)]

/-- **The two legs of the atom's cell are one crossing apart** — the cell itself is the witness,
with nothing below it. -/
theorem action_atomRunAt :
    (sliceActionAt (zObj (atomComp n k)) n (posPerm (adjT k))).unop.val
      (some (mergeRunAt k)) = some (atomRunAt k) :=
  (sliceActionAt_adjT_iff k _ _).mpr
    ⟨by rw [perm_atomRunAt, perm_mergeRunAt, one_mul],
      by rw [perm_atomRunAt, perm_mergeRunAt, permLen_one, permLen_adjT]⟩

/-- The copy the `k`-th atom's cell is. -/
noncomputable def atomElt : ((wedgeHoms (Hbp.obj (□n))).Elements)ᵒᵖ :=
  (toElements (Hbp.obj (□n))).obj ⟨atomComp n k, atomWitness k z⟩

/-- **The one 1-cell of the atom's copy**: its crossing leg, one crossing above its merge leg.
The slice polygraph is the base's reversed, so the letter runs merge-to-atom and the cell runs
atom-to-merge. -/
noncomputable def atomCell :
    glueV (Hbp.obj (□n)) artinFam (atomElt k z) (artinRunPt (atomRunAt k))
      ⟶ glueV (Hbp.obj (□n)) artinFam (atomElt k z) (artinRunPt (mergeRunAt k)) :=
  glueE (Hbp.obj (□n)) artinFam (atomElt k z) (artinRunGen k (action_atomRunAt k))

/-- **The crossing leg's 0-cell is the run its own leg restricts the chart to.** -/
theorem glueV_atomLeg (K : BPSet) (w : ⋁(atomComp n k) ⟶ K) :
    glueV K artinFam (op ⟨op (zObj (atomComp n k)), w⟩) (artinRunPt (atomRunAt k))
      = artinBP.glueRunV K ((atomOnes n k).φ ≫ w) :=
  (congrArg (glueV K artinFam (op ⟨op (zObj (atomComp n k)), w⟩))
      (famV_artinRunPt (atomOnes n k) (runAtSelf n)).symm).trans
    (glueV_leg K artinFam (eltLeg K (atomOnes n k) w) (artinRunPt (runAtSelf n)))

/-- …and the merge leg's likewise. -/
theorem glueV_mergeLeg (K : BPSet) (w : ⋁(atomComp n k) ⟶ K) :
    glueV K artinFam (op ⟨op (zObj (atomComp n k)), w⟩) (artinRunPt (mergeRunAt k))
      = artinBP.glueRunV K ((mergeOnes n k).φ ≫ w) :=
  (congrArg (glueV K artinFam (op ⟨op (zObj (atomComp n k)), w⟩))
      (famV_artinRunPt (mergeOnes n k) (runAtSelf n)).symm).trans
    (glueV_leg K artinFam (eltLeg K (mergeOnes n k) w) (artinRunPt (runAtSelf n)))

/-- **The crossing leg's 0-cell is the run the atom acts to.** -/
theorem glueV_atomRun :
    glueV (Hbp.obj (□n)) artinFam (atomElt k z) (artinRunPt (atomRunAt k))
      = artinBP.glueRunV (Hbp.obj (□n)) ((hFibre n).map (atomLoop n k) z) :=
  (glueV_atomLeg k (Hbp.obj (□n)) (atomWitness k z)).trans
    (congrArg (artinBP.glueRunV (Hbp.obj (□n))) (atomOnes_atomWitness k z))

/-- **…and the merge leg's is the run itself.** -/
theorem glueV_mergeRun :
    glueV (Hbp.obj (□n)) artinFam (atomElt k z) (artinRunPt (mergeRunAt k))
      = artinBP.glueRunV (Hbp.obj (□n)) z :=
  (glueV_mergeLeg k (Hbp.obj (□n)) (atomWitness k z)).trans
    (congrArg (artinBP.glueRunV (Hbp.obj (□n))) (mergeOnes_atomWitness k z))

/-- **The chart above a run is forced** — the merge acts bijectively on the fibre. -/
theorem eq_atomWitness {w : ⋁(atomComp n k) ⟶ Hbp.obj (□n)}
    (hw : (mergeOnes n k).φ ≫ w = z) : w = atomWitness k z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  have h1 : (hFibre n).map (((W Zbp).op).Q.map (mergeOnes n k).op) w = z := by
    rw [hFibre_map_Q]; exact hw
  have h2 : (hFibre n).map (((W Zbp).op).Q.map (mergeOnes n k).op) (atomWitness k z) = z := by
    rw [hFibre_map_Q]; exact mergeOnes_atomWitness k z
  have h3 := congrArg ((hFibre n).map (inv (((W Zbp).op).Q.map (mergeOnes n k).op)))
    (h1.trans h2.symm)
  rwa [← (hFibre n).map_comp_apply, ← (hFibre n).map_comp_apply, IsIso.hom_inv_id,
    (hFibre n).map_id_apply, (hFibre n).map_id_apply] at h3

theorem arrow_atomCell :
    (presentsChainsArtinColimit (Hbp.obj (□n))).arrow (atomCell k z)
      = eqToHom (at_glueV (Hbp.obj (□n)) artinFam (slicePresentationOf artinBP.base)
            (fun {_ _} f => slicePoly_hP artinBP.base f)
            (atomElt k z) (artinRunPt (atomRunAt k))) ≫
          (locEquivElements (Hbp.obj (□n))).inverse.map
            ((glueSliceEval (wedgeHoms (Hbp.obj (□n))) (W Zbp) (zObj (atomComp n k))
              (atomWitness k z)).map
                ((slicePresentationOf artinBP.base (zObj (atomComp n k))).arrow
                  (artinRunGen k (action_atomRunAt k))))
        ≫ eqToHom (at_glueV (Hbp.obj (□n)) artinFam (slicePresentationOf artinBP.base)
            (fun {_ _} f => slicePoly_hP artinBP.base f)
            (atomElt k z) (artinRunPt (mergeRunAt k))).symm :=
  arrow_glueE _ _ _ _ _ _

theorem over_atomRunAt : ((atomRunAt k).1.1 : Over (zObj (atomComp n k)))
    = Over.mk (atomOnes n k) :=
  congrArg Over.mk (Category.id_comp (atomOnes n k))

theorem over_mergeRunAt : ((mergeRunAt k).1.1 : Over (zObj (atomComp n k)))
    = Over.mk (mergeOnes n k) :=
  congrArg Over.mk (Category.id_comp (mergeOnes n k))

/-- **The braid the atom's 1-cell performs is the `k`-th atom.** -/
theorem chBraid_atomCell :
    chBraid ((locEquivElements (Hbp.obj (□n))).inverse.map
        ((glueSliceEval (wedgeHoms (Hbp.obj (□n))) (W Zbp) (zObj (atomComp n k))
          (atomWitness k z)).map
            ((slicePresentationOf artinBP.base (zObj (atomComp n k))).arrow
              (artinRunGen k (action_atomRunAt k)))))
      (hbpStrands _) (hbpStrands _) = posPerm (adjT k) := by
  have h := chBraid_glueSliceEval_of_eq (Hbp.obj (□n)) (zObj (atomComp n k)) (atomWitness k z)
    (a := Over.mk (atomOnes n k)) (b := Over.mk (mergeOnes n k))
    ((slicePresentationOf_at artinBP.base (zObj (atomComp n k))
        (artinRunPt (atomRunAt k))).trans
      (congrArg ((W Zbp).over (X := zObj (atomComp n k))).Q.obj
        ((sliceCellOver_artinRunPt (atomRunAt k)).trans (over_atomRunAt k))))
    ((slicePresentationOf_at artinBP.base (zObj (atomComp n k))
        (artinRunPt (mergeRunAt k))).trans
      (congrArg ((W Zbp).over (X := zObj (atomComp n k))).Q.obj
        ((sliceCellOver_artinRunPt (mergeRunAt k)).trans (over_mergeRunAt k))))
    ((slicePresentationOf artinBP.base (zObj (atomComp n k))).arrow
      (artinRunGen k (action_atomRunAt k)))
    (t := atomOnes n k) (m := mergeOnes n k) (z := 𝟙 _) (W_mergeOnes n k)
    (Category.comp_id _) (Category.comp_id _)
    (dimSum_replicate n) (dimSum_replicate n) (dimSum_atomComp n k)
    (hbpStrands _) (hbpStrands _)
  exact h.trans (congrArg posPerm (crossPerm_atomOnes n k))

end Cube

/-! ## The dictionary

A 0-cell of the fibration route is a run; a 1-cell is an Artin generator acting on one.  Both go
to the copy at the atom's cell, where the run is the merge leg. -/

/-- The run a 0-cell of the fibration route carries. -/
def artinRun {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) : ⋁(𝟙^n) ⟶ Hbp.obj (□n) := x.as.2

/-- …and the 0-cell a run is. -/
def artinPt {n : ℕ} (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) : GenObj (hLocArtinPoly n).Gen :=
  ⟨⟨SingleObj.star (PresentedMonoid (ArtinRel n)), z⟩⟩

@[simp] theorem artinRun_artinPt {n : ℕ} (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    artinRun (artinPt z) = z := rfl

@[simp] theorem artinPt_artinRun {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    artinPt (artinRun x) = x := rfl

/-- **A generator acts by its atom.** -/
theorem artinRun_step {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    (hFibre n).map (atomLoop n e.1) (artinRun x) = artinRun y := by
  rw [← runLoop_adjT]; exact e.2

/-- **The fibration route names the localized run chain.** -/
noncomputable def artinRunIso {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    ((hLocArtinPresentation n).at' x).unop ≅ (W (Hbp.obj (□n))).Q.obj (runCh (artinRun x)) :=
  haveI : (chDescent (Hbp.obj (□n)) (isSegal_H_of_symFree_repr (symFreeCube n))).IsLocalization
      (W (Hbp.obj (□n))) := isLocalization_chDescent _ _
  haveI : (CategoryOfElements.pre
      (wedgeHomsDescend (Hbp.obj (□n)) (isSegal_H_of_symFree_repr (symFreeCube n)))
      (runBase n)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _
      (cover_of_strands _ n (isSegal_H_of_symFree_repr (symFreeCube n))
        (fun {_} α => hbpCubeStrands α))
  (Localization.compEquivalenceFromModelInverseIso
    (chDescent (Hbp.obj (□n)) (isSegal_H_of_symFree_repr (symFreeCube n)))
    (W (Hbp.obj (□n)))).app (runCh (artinRun x))

/-- **The 0-cell dictionary**: a run, read in its own copy. -/
noncomputable def obCell {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    GenObj ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinFam)).op).Gen :=
  ⟨(artinBP.glueRunV (Hbp.obj (□n)) (artinRun x)).as⟩

/-- **The crossing leg is the 0-cell the generator acts to.** -/
theorem genSrc {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    glueV (Hbp.obj (□n)) artinFam (atomElt e.1 (artinRun x)) (artinRunPt (atomRunAt e.1))
      = artinBP.glueRunV (Hbp.obj (□n)) (artinRun y) :=
  (glueV_atomRun e.1 (artinRun x)).trans
    (congrArg (artinBP.glueRunV (Hbp.obj (□n))) (artinRun_step e))

/-- **…and the merge leg is the 0-cell it acts from.** -/
theorem genTgt {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    glueV (Hbp.obj (□n)) artinFam (atomElt e.1 (artinRun x)) (artinRunPt (mergeRunAt e.1))
      = artinBP.glueRunV (Hbp.obj (□n)) (artinRun x) :=
  glueV_mergeRun e.1 (artinRun x)

/-- **The 1-cell dictionary**: the `k`-th Artin generator at the run `z` is the single crossing in
the copy at `atomComp n k` carrying the chart `z` is merged from.  The polygraphs run in opposite
directions, so the crossing leg is the generator's *target*. -/
noncomputable def genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    obCell x ⟶ obCell y :=
  (Quiver.homOfEq (atomCell e.1 (artinRun x)) (genSrc e) (genTgt e) :
    artinBP.glueRunV (Hbp.obj (□n)) (artinRun y) ⟶ artinBP.glueRunV (Hbp.obj (□n)) (artinRun x))

/-- **The 0-cells name the same object.** -/
noncomputable def thetaCell {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    ((presentsChainsArtinColimit (Hbp.obj (□n))).op).at' (obCell x)
      ≅ (hLocArtinPresentation n).at' x :=
  (artinRunIso x ≪≫ (artinBP.glueRunIso (Hbp.obj (□n)) (artinRun x)).symm).op

/-! ## The comparison

Both sides perform the same atom, and `eq_of_chBraid_eq` is decisive: the localized chains project
faithfully to the localized base. -/

/-- **The glue spelling of a generator performs that generator's atom.** -/
theorem chBraid_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    chBraid ((((presentsChainsArtinColimit (Hbp.obj (□n))).op).arrow (genCell e)).unop)
        (hbpStrands _) (hbpStrands _) = posPerm (adjT e.1) := by
  have h0 : (((presentsChainsArtinColimit (Hbp.obj (□n))).op).arrow (genCell e)).unop
      = (presentsChainsArtinColimit (Hbp.obj (□n))).arrow
          (Quiver.homOfEq (atomCell e.1 (artinRun x)) (genSrc e) (genTgt e)) :=
    congrArg Quiver.Hom.unop
      (Presents.op_arrow (presentsChainsArtinColimit (Hbp.obj (□n))) (genCell e))
  rw [h0, Presents.arrow_homOfEq, arrow_atomCell]
  refine (chBraid_eqToHom_sandwich _ _ _
    (hbpStrands _) (hbpStrands _) (hbpStrands _) (hbpStrands _)).trans ?_
  exact (chBraid_eqToHom_sandwich _ _ _
    (hbpStrands _) (hbpStrands _) (hbpStrands _) (hbpStrands _)).trans
      (chBraid_atomCell e.1 (artinRun x))

/-- **…and so does the fibration route's own generator**, conjugated by the 0-cell dictionary. -/
theorem chBraid_thetaCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    chBraid (((thetaCell x).hom ≫ (hLocArtinPresentation n).arrow e ≫ (thetaCell y).inv).unop)
        (hbpStrands _) (hbpStrands _) = posPerm (adjT e.1) := by
  have hR : ((thetaCell x).hom ≫ (hLocArtinPresentation n).arrow e ≫ (thetaCell y).inv).unop
      = (thetaCell y).inv.unop ≫ ((hLocArtinPresentation n).arrow e).unop
          ≫ (thetaCell x).hom.unop := by
    rw [unop_comp, unop_comp, Category.assoc]
  have h1 : IsIso ((thetaCell y).inv.unop) := inferInstanceAs (IsIso ((thetaCell y).unop).inv)
  have h2 : IsIso ((thetaCell x).hom.unop) := inferInstanceAs (IsIso ((thetaCell x).unop).hom)
  rw [hR]
  exact (chBraid_sandwich _ h1 _ _ h2 (hbpStrands _) (hbpStrands _) (hbpStrands _)
    (hbpStrands _)).trans (chBraid_hLocArtinPresentation_arrow n e)

/-- **The dictionary names the same arrow.**  Both sides perform the `k`-th atom, and the
projection to the localized base is faithful. -/
theorem hgenCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    ((presentsChainsArtinColimit (Hbp.obj (□n))).op).arrow (genCell e)
      = (thetaCell x).hom ≫ (hLocArtinPresentation n).arrow e ≫ (thetaCell y).inv :=
  Quiver.Hom.unop_inj (eq_of_chBraid_eq (isSegal_H_of_symFree_repr (symFreeCube n))
    (N := n) (hbpStrands _) (hbpStrands _)
    ((chBraid_genCell e).trans (chBraid_thetaCell e).symm))

/-- **The colimit presentation of `Ch(Hbp □ⁿ)[W⁻¹]` and the fibration one agree, generator by
generator**: a 0-cell of the fibration route is a run, read in its own copy, and its `k`-th Artin
generator is the *one* crossing of the copy at `atomComp n k`.  No word is ever chosen. -/
noncomputable def glueArtinMap (n : ℕ) :
    Presents.Map (hLocArtinPresentation n)
      ((presentsChainsArtinColimit (Hbp.obj (□n))).op) :=
  Presents.Map.ofGenerators obCell genCell thetaCell fun {_ _} e => hgenCell e

/-- **The spelling is one letter long** — a generator goes to a generator, not to a word. -/
theorem glueArtinMap_cells {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    (glueArtinMap n).hom.cells.map e = (genCell e).toPath := rfl

/-- **…so the two polygraphs present `Ch(Hbp □ⁿ)[W⁻¹]` compatibly**: the equivalence is the one
the generator dictionary spells. -/
noncomputable def glueArtinEquiv (n : ℕ) :
    (hLocArtinPoly n).presented ≌
      ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinFam)).op).presented :=
  (glueArtinMap n).equiv

/-! ## The 0-cells biject

Surjectivity is the colimit's legs (`exists_colimit_ι_obj`) followed by the leg down to a run's own
copy; injectivity is that `PosBraid n` has no non-trivial units, so distinct runs are
non-isomorphic. -/

theorem surjective_obCell (n : ℕ) : Function.Surjective (obCell (n := n)) := by
  intro A
  obtain ⟨c, w, hw⟩ := Polygraph.exists_colimit_ι_obj
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinFam) ⟨A.as⟩
  obtain ⟨z, hz⟩ := artinBP.exists_glueRunV (Hbp.obj (□n)) c (hbpCubeStrands c.unop.2) w.as
  exact ⟨artinPt z, congrArg (fun v : GenObj (colimit
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinFam)).Gen => (⟨v.as⟩ : GenObj _))
    (hz.symm.trans hw)⟩

/-- The fibre over the run, as a category of elements. -/
noncomputable abbrev hFibElt (n : ℕ) :=
  (runBase n ⋙ wedgeHomsDescend (Hbp.obj (□n))
    (isSegal_H_of_symFree_repr (symFreeCube n))).Elements

/-- The element of the fibre a 0-cell of the fibration route is. -/
noncomputable def artinElt {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) : hFibElt n :=
  ⟨(artinComponent n).at' (Polygraph.pt _ x.as.1), artinRun x⟩

/-- **Distinct runs are non-isomorphic in the fibre** — `PosBraid n` has no non-trivial units. -/
theorem artinRun_eq_of_iso {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen}
    (α : artinElt x ≅ artinElt y) : artinRun x = artinRun y := by
  haveI : IsIso (α.hom.val) := inferInstanceAs (IsIso ((CategoryOfElements.π _).map α.hom))
  have h := congrArg Quiver.Hom.unop (IsIso.hom_inv_id (f := α.hom.val))
  rw [unop_comp, unop_id, SingleObj.comp_as_mul, SingleObj.id_as_one] at h
  have hid : α.hom.val = 𝟙 _ :=
    Quiver.Hom.unop_inj ((eq_one_of_mul_eq_one h).trans (SingleObj.id_as_one (PosBraid n) _).symm)
  have hp := α.hom.property
  rw [hid] at hp
  exact (((runBase n ⋙ wedgeHomsDescend (Hbp.obj (□n))
    (isSegal_H_of_symFree_repr (symFreeCube n))).map_id_apply _ (artinRun x)).symm.trans hp)

theorem injective_obCell (n : ℕ) : Function.Injective (obCell (n := n)) := by
  intro x y hxy
  have hι : (hLocArtinPresentation n).at' x ≅ (hLocArtinPresentation n).at' y :=
    (thetaCell x).symm ≪≫
      eqToIso (congrArg ((presentsChainsArtinColimit (Hbp.obj (□n))).op).at' hxy) ≪≫ thetaCell y
  set E := chLocEquivElements (Hbp.obj (□n)) n (isSegal_H_of_symFree_repr (symFreeCube n))
    (fun {_} α => hbpCubeStrands α)
  have hα : op (artinElt y) ≅ op (artinElt x) :=
    (E.counitIso.app (op (artinElt y))).symm ≪≫ E.functor.mapIso hι.unop ≪≫
      E.counitIso.app (op (artinElt x))
  have hz := artinRun_eq_of_iso hα.unop
  exact (artinPt_artinRun x).symm.trans ((congrArg artinPt hz).trans (artinPt_artinRun y))

/-- **The 0-cells of the two polygraphs biject**, generator dictionary and all. -/
theorem bijective_obCell (n : ℕ) : Function.Bijective (obCell (n := n)) :=
  ⟨injective_obCell n, surjective_obCell n⟩

/-- **A 0-cell of the colimit names its run** — the shape the 1-cell dictionary reads a copy's
chart off. -/
theorem injective_glueRunV (n : ℕ) :
    Function.Injective (artinBP.glueRunV (Hbp.obj (□n)) (n := n)) := fun z z' h =>
  congrArg artinRun (injective_obCell n (a₁ := artinPt z) (a₂ := artinPt z')
    (congrArg (fun v : GenObj (colimit
      (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinFam)).Gen => (⟨v.as⟩ : GenObj _)) h))

/-! ## The 1-cells biject

Surjectivity is `exists_colimit_ι_map` followed by `exists_atomComp_leg`: a letter acting anywhere
is the atom's own cell pushed down, and the copy it comes from is the atom's.  Injectivity is the
braid: a generator is pinned by the atom it performs. -/

/-- **A letter acting on a run is the atom's cell, pushed down**: one crossing above the run is one
atom above it, and the cell it comes from is `atomComp n k`. -/
theorem exists_atomComp_leg {n : ℕ} {d : Ch Zbp} (hd : dimSum d.dims = n) {k : Fin (n - 1)}
    {u v : RunAt d n}
    (h : (sliceActionAt d n (posPerm (adjT k))).unop.val (some u) = some v) :
    ∃ w : zObj (atomComp n k) ⟶ d,
      RunAt.push w (atomRunAt k) = v ∧ RunAt.push w (mergeRunAt k) = u := by
  obtain ⟨hperm, hlen⟩ := (sliceActionAt_adjT_iff k u v).mp h
  obtain ⟨⟨⟨la, ⟨⟩, ga⟩, hra⟩, hNa⟩ := u
  obtain rfl : la = zObj (𝟙^n) := RunOver.left_eq hd ⟨Over.mk ga, hra⟩
  obtain ⟨⟨⟨lb, ⟨⟩, gb⟩, hrb⟩, hNb⟩ := v
  obtain rfl : lb = zObj (𝟙^n) := RunOver.left_eq hd ⟨Over.mk gb, hrb⟩
  replace hperm : crossPerm (dimSum_replicate n) gb
      = crossPerm (dimSum_replicate n) ga * adjT k := hperm
  replace hlen : permLen (crossPerm (dimSum_replicate n) ga) + 1
      = permLen (crossPerm (dimSum_replicate n) gb) := hlen
  have hasc : crossPerm (dimSum_replicate n) ga (adjLo k)
      < crossPerm (dimSum_replicate n) ga (adjHi k) := by
    rcases lt_trichotomy (crossPerm (dimSum_replicate n) ga (adjLo k))
      (crossPerm (dimSum_replicate n) ga (adjHi k)) with hlt | heq | hgt
    · exact hlt
    · exact absurd (congrArg Fin.val ((Equiv.injective _) heq))
        (by rw [adjLo_val, adjHi_val]; omega)
    · have hdrop := permLen_mul_adjT_of_descent (i := k) hgt
      rw [← hperm] at hdrop
      omega
  have hdesc : crossPerm (dimSum_replicate n) gb (adjHi k)
      < crossPerm (dimSum_replicate n) gb (adjLo k) := by
    rw [hperm, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_hi, adjT_lo]
    exact hasc
  obtain ⟨w, hmerge, hatom⟩ := exists_atom_step hd k
    (nonempty_atomComp_of_descent hd gb hdesc)
    (rfl : crossPerm (dimSum_replicate n) ga = _) hasc
  have hgb : atomOnes n k ≫ w = gb :=
    hom_ext_of_crossPerm (h := dimSum_replicate n) (hatom.trans hperm.symm)
  exact ⟨w, Subtype.ext (Subtype.ext (congrArg Over.mk (by simpa using hgb))),
    Subtype.ext (Subtype.ext (congrArg Over.mk (by simpa using hmerge)))⟩

theorem surjective_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen}
    (e : obCell x ⟶ obCell y) : ∃ e' : x ⟶ y, genCell e' = e := by
  obtain ⟨c, w₁, w₂, g, hx, hy, he⟩ := Polygraph.exists_colimit_ι_map
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinFam)
    (e : artinBP.glueRunV (Hbp.obj (□n)) (artinRun y)
      ⟶ artinBP.glueRunV (Hbp.obj (□n)) (artinRun x))
  obtain ⟨w₁⟩ := w₁
  obtain ⟨w₂⟩ := w₂
  have hd : dimSum (eltBase (wedgeHoms (Hbp.obj (□n))) c).dims = n := hbpCubeStrands c.unop.2
  obtain ⟨k, u, v, h2, h1, hact, hval⟩ := artinBP.gen_action_of_strands hd
    (g : (⟨w₂⟩ : GenObj (slicePolyRaw artinBP.base
      (eltBase (wedgeHoms (Hbp.obj (□n))) c)).Gen) ⟶ ⟨w₁⟩)
  subst h2
  subst h1
  obtain ⟨t, hatom, hmerge⟩ := exists_atomComp_leg hd hact
  subst hatom
  subst hmerge
  have hleg : ∀ a : RunAt (zObj (atomComp n k)) n,
      glueV (Hbp.obj (□n)) artinFam c (artinRunPt (RunAt.push t a))
        = glueV (Hbp.obj (□n)) artinFam (op ⟨op (zObj (atomComp n k)),
            (wedgeHoms (Hbp.obj (□n))).map t.op c.unop.2⟩) (artinRunPt a) :=
    fun a => (congrArg (glueV (Hbp.obj (□n)) artinFam c) (famV_artinRunPt t a).symm).trans
      (glueV_leg (Hbp.obj (□n)) artinFam (eltLeg (Hbp.obj (□n)) t c.unop.2) (artinRunPt a))
  have hay : (atomOnes n k).φ ≫ (wedgeHoms (Hbp.obj (□n))).map t.op c.unop.2 = artinRun y :=
    injective_glueRunV n
      ((glueV_atomLeg k (Hbp.obj (□n)) _).symm.trans ((hleg (atomRunAt k)).symm.trans hx))
  have hax : (mergeOnes n k).φ ≫ (wedgeHoms (Hbp.obj (□n))).map t.op c.unop.2 = artinRun x :=
    injective_glueRunV n
      ((glueV_mergeLeg k (Hbp.obj (□n)) _).symm.trans ((hleg (mergeRunAt k)).symm.trans hy))
  have hw2 : (wedgeHoms (Hbp.obj (□n))).map t.op c.unop.2 = atomWitness k (artinRun x) :=
    eq_atomWitness k (artinRun x) hax
  have hgen : (hFibre n).map (runLoop n (adjT k)) (artinRun x) = artinRun y := by
    rw [runLoop_adjT]
    exact (atomOnes_atomWitness k (artinRun x)).symm.trans (by rw [← hw2]; exact hay)
  obtain ⟨ι, hι⟩ : ∃ ι : atomElt k (artinRun x) ⟶ c,
      (CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι = t :=
    ⟨(CategoryOfElements.homMk c.unop
      (⟨op (zObj (atomComp n k)), atomWitness k (artinRun x)⟩ :
        (wedgeHoms (Hbp.obj (□n))).Elements) t.op hw2).op, rfl⟩
  subst hι
  refine ⟨⟨k, hgen⟩, Eq.trans ?_ he⟩
  have hg : Quiver.homOfEq ((artinFam.map ((CategoryOfElements.π
        (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)).pre.map (artinRunGen k (action_atomRunAt k)))
      (congrArg GenObj.mk (famV_artinRunPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (atomRunAt k)))
      (congrArg GenObj.mk (famV_artinRunPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (mergeRunAt k))) = g :=
    artinRunGen_ext
      (famV_artinRunPt ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)
        (atomRunAt k))
      (famV_artinRunPt ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)
        (mergeRunAt k)) _ g hval.symm
  change genCell ⟨k, hgen⟩ = Quiver.homOfEq (glueE (Hbp.obj (□n)) artinFam c g) hx hy
  refine eq_of_heq (((Quiver.homOfEq_heq _ _ (atomCell k (artinRun x))).trans ?_).trans
    (Quiver.homOfEq_heq hx hy (glueE (Hbp.obj (□n)) artinFam c g)).symm)
  refine HEq.trans ?_ (heq_of_eq (congrArg (glueE (Hbp.obj (□n)) artinFam c) hg))
  refine HEq.trans ?_ (heq_of_eq (glueE_homOfEq (Hbp.obj (□n)) artinFam c
      ((artinFam.map ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)).pre.map
        (artinRunGen k (action_atomRunAt k)))
      (congrArg GenObj.mk (famV_artinRunPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (atomRunAt k)))
      (congrArg GenObj.mk (famV_artinRunPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (mergeRunAt k)))).symm)
  refine HEq.trans ?_ (Quiver.homOfEq_heq _ _ (glueE (Hbp.obj (□n)) artinFam c
    ((artinFam.map ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)).pre.map
      (artinRunGen k (action_atomRunAt k))))).symm
  refine HEq.trans ?_ (heq_of_eq (glueE_leg (Hbp.obj (□n)) artinFam ι
    (artinRunGen k (action_atomRunAt k))).symm)
  exact (Quiver.homOfEq_heq _ _ (atomCell k (artinRun x))).symm

theorem injective_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} :
    Function.Injective (genCell : (x ⟶ y) → (obCell x ⟶ obCell y)) := by
  intro e e' h
  have hb : posPerm (adjT e.1) = posPerm (adjT e'.1) :=
    (chBraid_genCell e).symm.trans
      ((congrArg (fun t : obCell x ⟶ obCell y =>
        chBraid ((((presentsChainsArtinColimit (Hbp.obj (□n))).op).arrow t).unop)
          (hbpStrands _) (hbpStrands _)) h).trans (chBraid_genCell e'))
  have hp : adjT e.1 = adjT e'.1 := by
    have hh := congrArg (posPermHom n) hb
    rwa [posPermHom_posPerm, posPermHom_posPerm] at hh
  exact Subtype.ext (Fin.ext (adjT_inj hp))

theorem bijective_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} :
    Function.Bijective (genCell : (x ⟶ y) → (obCell x ⟶ obCell y)) :=
  ⟨injective_genCell, fun e => surjective_genCell e⟩

/-- **The generator dictionary, as a map of generating quivers.** -/
noncomputable def genQuiver (n : ℕ) :
    GenObj (hLocArtinPoly n).Gen ⥤q
      GenObj ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinFam)).op).Gen where
  obj := obCell
  map := genCell

/-- **…and it is an isomorphism of generating quivers**: the `n!` runs biject with the colimit's
0-cells, and each hom-set of Artin generators with the colimit's 1-cells there.  With
`glueArtinMap` — the same data, naming the same arrows — the two presentations of
`Ch(Hbp □ⁿ)[W⁻¹]` agree in both generating dimensions. -/
theorem bijective_genQuiver (n : ℕ) :
    Function.Bijective (genQuiver n).obj ∧
      ∀ x y : GenObj (hLocArtinPoly n).Gen,
        Function.Bijective ((genQuiver n).map : (x ⟶ y) → _) :=
  ⟨bijective_obCell n, fun _ _ => bijective_genCell⟩

end ChainCat
