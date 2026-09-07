import CubeChains.Concurrency.Presentation.RouteComparison
import CubeChains.Concurrency.Presentation.RunCells

/-!
# Concurrency/Presentation/ArtinCells — the Artin generators, spelled by colimit 1-cells

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

/-- **1-cells of a copy are pinned by their letter**, across an identification of their 0-cells. -/
theorem artinRunGen_ext {d : Ch Zbp} {a b a' b' : (slicePolyRaw artinBP.base d).V}
    (ha : a = a') (hb : b = b')
    (g₀ : (⟨a⟩ : GenObj (artinBP.fam.obj d).Gen) ⟶ ⟨b⟩)
    (g : (⟨a'⟩ : GenObj (artinBP.fam.obj d).Gen) ⟶ ⟨b'⟩) (h : HEq g₀.1 g.1) :
    Quiver.homOfEq g₀ (congrArg GenObj.mk ha) (congrArg GenObj.mk hb) = g := by
  subst ha; subst hb; exact Subtype.ext (eq_of_heq h)

/-! ## The chart above a run

Restriction along a `W`-arrow is bijective on the charts of the decorated cube, so a run below one
has exactly one chart above it.  This is the whole of what the Segal condition is spent on. -/

section Witness

variable {n : ℕ} {a b : Ch Zbp} {f : a ⟶ b} (hf : W Zbp f)

/-- **Restriction along a `W`-arrow, as a bijection of charts.** -/
noncomputable def wChartEquiv : (⋁(b.dims) ⟶ Hbp.obj (□n)) ≃ (⋁(a.dims) ⟶ Hbp.obj (□n)) :=
  Equiv.ofBijective ((wedgeHoms (Hbp.obj (□n))).map f.op)
    ((isIso_iff_bijective _).mp (invertsMerges_Hbp_cube n f.op hf))

/-- **The chart a run is merged from.**  Nothing is chosen: the merge is inverted. -/
noncomputable def wWitness (z : ⋁(a.dims) ⟶ Hbp.obj (□n)) : ⋁(b.dims) ⟶ Hbp.obj (□n) :=
  (wChartEquiv hf).symm z

/-- **…restricting back to the run below.** -/
theorem φ_wWitness (z : ⋁(a.dims) ⟶ Hbp.obj (□n)) : f.φ ≫ wWitness hf z = z :=
  (wChartEquiv hf).apply_symm_apply z

/-- **…and it is the only chart that does.** -/
theorem eq_wWitness {w : ⋁(b.dims) ⟶ Hbp.obj (□n)} {z : ⋁(a.dims) ⟶ Hbp.obj (□n)}
    (hw : f.φ ≫ w = z) : w = wWitness hf z :=
  ((wChartEquiv hf).eq_symm_apply).mpr hw

/-- **…and the localized arrow acts on charts by it** — the bridge to the fibre over the run. -/
theorem hFibre_map_inv_Q [IsIso (((W Zbp).op).Q.map f.op)] (z : ⋁(a.dims) ⟶ Hbp.obj (□n)) :
    (hFibre n).map (inv (((W Zbp).op).Q.map f.op)) z = wWitness hf z := by
  refine eq_wWitness hf ?_
  have h1 : (hFibre n).map (((W Zbp).op).Q.map f.op)
      ((hFibre n).map (inv (((W Zbp).op).Q.map f.op)) z) = z := by
    rw [← (hFibre n).map_comp_apply, IsIso.inv_hom_id, (hFibre n).map_id_apply]
  rwa [hFibre_map_Q] at h1

end Witness

/-! ## The atom's cell, as a copy

A copy is indexed by an element of `wedgeHoms K` — a chain of the base with a map into `K`, which
is what `toElements` names — and above a run the `k`-th atom's cell is the chain `atomComp n k`,
with the run as its merge leg. -/

section Cube

variable {n : ℕ} (k : Fin (n - 1)) (z : ⋁(𝟙^n) ⟶ Hbp.obj (□n))

/-- **The chart the `k`-th atom's cell carries above a run** — the run, un-merged across the cut. -/
noncomputable def atomWitness : ⋁(atomComp n k) ⟶ Hbp.obj (□n) := wWitness (W_mergeOnes n k) z

/-- **The merge leg of the cell restricts to the run.** -/
theorem mergeOnes_atomWitness : (mergeOnes n k).φ ≫ atomWitness k z = z :=
  φ_wWitness (W_mergeOnes n k) z

/-- **…and the crossing leg restricts to the run the atom acts to.** -/
theorem atomOnes_atomWitness :
    (atomOnes n k).φ ≫ atomWitness k z = (hFibre n).map (atomLoop n k) z := by
  haveI := isIso_Q_op_of_W (W_mergeOnes n k)
  rw [atomLoop_eq_legs, (hFibre n).map_comp_apply, hFibre_map_Q,
    hFibre_map_inv_Q (W_mergeOnes n k)]
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
    ιV (Hbp.obj (□n)) artinBP.fam (atomElt k z) (artinBP.runPt (atomRunAt k))
      ⟶ ιV (Hbp.obj (□n)) artinBP.fam (atomElt k z) (artinBP.runPt (mergeRunAt k)) :=
  ιE (Hbp.obj (□n)) artinBP.fam (atomElt k z) (artinBP.runGen k (action_atomRunAt k))

/-- **The crossing leg's 0-cell is the run its own leg restricts the chart to.** -/
theorem ιV_atomLeg (K : BPSet) (w : ⋁(atomComp n k) ⟶ K) :
    ιV K artinBP.fam (op ⟨op (zObj (atomComp n k)), w⟩) (artinBP.runPt (atomRunAt k))
      = artinBP.ιRun K ((atomOnes n k).φ ≫ w) :=
  (congrArg (ιV K artinBP.fam (op ⟨op (zObj (atomComp n k)), w⟩))
      (artinBP.famV_runPt (atomOnes n k) (runAtSelf n)).symm).trans
    (ιV_leg K artinBP.fam (eltLeg K (atomOnes n k) w) (artinBP.runPt (runAtSelf n)))

/-- …and the merge leg's likewise. -/
theorem ιV_mergeLeg (K : BPSet) (w : ⋁(atomComp n k) ⟶ K) :
    ιV K artinBP.fam (op ⟨op (zObj (atomComp n k)), w⟩) (artinBP.runPt (mergeRunAt k))
      = artinBP.ιRun K ((mergeOnes n k).φ ≫ w) :=
  (congrArg (ιV K artinBP.fam (op ⟨op (zObj (atomComp n k)), w⟩))
      (artinBP.famV_runPt (mergeOnes n k) (runAtSelf n)).symm).trans
    (ιV_leg K artinBP.fam (eltLeg K (mergeOnes n k) w) (artinBP.runPt (runAtSelf n)))

/-- **The crossing leg's 0-cell is the run the atom acts to.** -/
theorem ιV_atomRun :
    ιV (Hbp.obj (□n)) artinBP.fam (atomElt k z) (artinBP.runPt (atomRunAt k))
      = artinBP.ιRun (Hbp.obj (□n)) ((hFibre n).map (atomLoop n k) z) :=
  (ιV_atomLeg k (Hbp.obj (□n)) (atomWitness k z)).trans
    (congrArg (artinBP.ιRun (Hbp.obj (□n))) (atomOnes_atomWitness k z))

/-- **…and the merge leg's is the run itself.** -/
theorem ιV_mergeRun :
    ιV (Hbp.obj (□n)) artinBP.fam (atomElt k z) (artinBP.runPt (mergeRunAt k))
      = artinBP.ιRun (Hbp.obj (□n)) z :=
  (ιV_mergeLeg k (Hbp.obj (□n)) (atomWitness k z)).trans
    (congrArg (artinBP.ιRun (Hbp.obj (□n))) (mergeOnes_atomWitness k z))

/-- **The chart above a run is forced** — the merge acts bijectively on the fibre. -/
theorem eq_atomWitness {w : ⋁(atomComp n k) ⟶ Hbp.obj (□n)}
    (hw : (mergeOnes n k).φ ≫ w = z) : w = atomWitness k z :=
  eq_wWitness (W_mergeOnes n k) hw

/-- **The braid the atom's 1-cell performs is the `k`-th atom** — its merge leg is uncrossed, so
`chBraid_runGen` reads the letter off. -/
theorem chBraid_atomCell :
    chBraid ((presentsChainsArtinColimit (Hbp.obj (□n))).arrow (atomCell k z))
      (hbpStrands _) (hbpStrands _) = posPerm (adjT k) :=
  (artinBP.chBraid_runGen (Hbp.obj (□n)) (atomElt k z) k (action_atomRunAt k)
      (perm_mergeRunAt k) (hbpStrands _) (hbpStrands _)).trans
    (congrArg posPerm (artinBP_perm k))

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
    GenObj ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)).op).Gen :=
  ⟨(artinBP.ιRun (Hbp.obj (□n)) (artinRun x)).as⟩

/-- **The crossing leg is the 0-cell the generator acts to.** -/
theorem genSrc {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    ιV (Hbp.obj (□n)) artinBP.fam (atomElt e.1 (artinRun x)) (artinBP.runPt (atomRunAt e.1))
      = artinBP.ιRun (Hbp.obj (□n)) (artinRun y) :=
  (ιV_atomRun e.1 (artinRun x)).trans
    (congrArg (artinBP.ιRun (Hbp.obj (□n))) (artinRun_step e))

/-- **…and the merge leg is the 0-cell it acts from.** -/
theorem genTgt {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    ιV (Hbp.obj (□n)) artinBP.fam (atomElt e.1 (artinRun x)) (artinBP.runPt (mergeRunAt e.1))
      = artinBP.ιRun (Hbp.obj (□n)) (artinRun x) :=
  ιV_mergeRun e.1 (artinRun x)

/-- **The 1-cell dictionary**: the `k`-th Artin generator at the run `z` is the single crossing in
the copy at `atomComp n k` carrying the chart `z` is merged from.  The polygraphs run in opposite
directions, so the crossing leg is the generator's *target*. -/
noncomputable def genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    obCell x ⟶ obCell y :=
  (Quiver.homOfEq (atomCell e.1 (artinRun x)) (genSrc e) (genTgt e) :
    artinBP.ιRun (Hbp.obj (□n)) (artinRun y) ⟶ artinBP.ιRun (Hbp.obj (□n)) (artinRun x))

/-- **The 0-cells name the same object.** -/
noncomputable def thetaCell {n : ℕ} (x : GenObj (hLocArtinPoly n).Gen) :
    ((presentsChainsArtinColimit (Hbp.obj (□n))).op).at' (obCell x)
      ≅ (hLocArtinPresentation n).at' x :=
  (artinRunIso x ≪≫ (artinBP.ιRunIso (Hbp.obj (□n)) (artinRun x)).symm).op

/-! ## The comparison

Both sides perform the same atom, and `eq_of_chBraid_eq` is decisive: the localized chains project
faithfully to the localized base. -/

/-- **The colimit spelling of a generator performs that generator's atom.** -/
theorem chBraid_genCell {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    chBraid ((((presentsChainsArtinColimit (Hbp.obj (□n))).op).arrow (genCell e)).unop)
        (hbpStrands _) (hbpStrands _) = posPerm (adjT e.1) := by
  have h0 : (((presentsChainsArtinColimit (Hbp.obj (□n))).op).arrow (genCell e)).unop
      = (presentsChainsArtinColimit (Hbp.obj (□n))).arrow
          (Quiver.homOfEq (atomCell e.1 (artinRun x)) (genSrc e) (genTgt e)) :=
    congrArg Quiver.Hom.unop
      (Presents.op_arrow (presentsChainsArtinColimit (Hbp.obj (□n))) (genCell e))
  rw [h0, Presents.arrow_homOfEq]
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
noncomputable def artinColimMap (n : ℕ) :
    Presents.Map (hLocArtinPresentation n)
      ((presentsChainsArtinColimit (Hbp.obj (□n))).op) :=
  Presents.Map.ofGenerators obCell genCell thetaCell fun {_ _} e => hgenCell e

/-- **The spelling is one letter long** — a generator goes to a generator, not to a word. -/
theorem artinColimMap_cells {n : ℕ} {x y : GenObj (hLocArtinPoly n).Gen} (e : x ⟶ y) :
    (artinColimMap n).hom.cells.map e = (genCell e).toPath := rfl

/-- **…so the two polygraphs present `Ch(Hbp □ⁿ)[W⁻¹]` compatibly**: the equivalence is the one
the generator dictionary spells. -/
noncomputable def artinColimEquiv (n : ℕ) :
    (hLocArtinPoly n).presented ≌
      ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)).op).presented :=
  (artinColimMap n).equiv

/-! ## The 0-cells biject

Surjectivity is the colimit's legs (`exists_colimit_ι_obj`) followed by the leg down to a run's own
copy; injectivity is that `PosBraid n` has no non-trivial units, so distinct runs are
non-isomorphic. -/

theorem surjective_obCell (n : ℕ) : Function.Surjective (obCell (n := n)) := by
  intro A
  obtain ⟨c, w, hw⟩ := Polygraph.exists_colimit_ι_obj
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam) ⟨A.as⟩
  obtain ⟨z, hz⟩ := artinBP.exists_ιRun (Hbp.obj (□n)) c (hbpCubeStrands c.unop.2) w.as
  exact ⟨artinPt z, congrArg (fun v : GenObj (colimit
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)).Gen => (⟨v.as⟩ : GenObj _))
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
theorem injective_ιRun (n : ℕ) :
    Function.Injective (artinBP.ιRun (Hbp.obj (□n)) (n := n)) := fun z z' h =>
  congrArg artinRun (injective_obCell n (a₁ := artinPt z) (a₂ := artinPt z')
    (congrArg (fun v : GenObj (colimit
      (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)).Gen => (⟨v.as⟩ : GenObj _)) h))

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
    (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)
    (e : artinBP.ιRun (Hbp.obj (□n)) (artinRun y)
      ⟶ artinBP.ιRun (Hbp.obj (□n)) (artinRun x))
  obtain ⟨w₁⟩ := w₁
  obtain ⟨w₂⟩ := w₂
  have hd : dimSum (eltBase (wedgeHoms (Hbp.obj (□n))) c).dims = n := hbpCubeStrands c.unop.2
  obtain ⟨v, rfl⟩ := artinBP.exists_runPt_of_strands hd w₁
  obtain ⟨u, rfl⟩ := artinBP.exists_runPt_of_strands hd w₂
  obtain ⟨k, hact, rfl⟩ := artinBP.gen_action
    (g : (⟨artinBP.runPt u⟩ : GenObj (slicePolyRaw artinBP.base
      (eltBase (wedgeHoms (Hbp.obj (□n))) c)).Gen) ⟶ ⟨artinBP.runPt v⟩)
  obtain ⟨t, hatom, hmerge⟩ := exists_atomComp_leg hd hact
  subst hatom
  subst hmerge
  have hleg : ∀ a : RunAt (zObj (atomComp n k)) n,
      ιV (Hbp.obj (□n)) artinBP.fam c (artinBP.runPt (RunAt.push t a))
        = ιV (Hbp.obj (□n)) artinBP.fam (op ⟨op (zObj (atomComp n k)),
            (wedgeHoms (Hbp.obj (□n))).map t.op c.unop.2⟩) (artinBP.runPt a) :=
    fun a => (congrArg (ιV (Hbp.obj (□n)) artinBP.fam c) (artinBP.famV_runPt t a).symm).trans
      (ιV_leg (Hbp.obj (□n)) artinBP.fam (eltLeg (Hbp.obj (□n)) t c.unop.2) (artinBP.runPt a))
  have hay : (atomOnes n k).φ ≫ (wedgeHoms (Hbp.obj (□n))).map t.op c.unop.2 = artinRun y :=
    injective_ιRun n
      ((ιV_atomLeg k (Hbp.obj (□n)) _).symm.trans ((hleg (atomRunAt k)).symm.trans hx))
  have hax : (mergeOnes n k).φ ≫ (wedgeHoms (Hbp.obj (□n))).map t.op c.unop.2 = artinRun x :=
    injective_ιRun n
      ((ιV_mergeLeg k (Hbp.obj (□n)) _).symm.trans ((hleg (mergeRunAt k)).symm.trans hy))
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
  have hg : Quiver.homOfEq ((artinBP.fam.map ((CategoryOfElements.π
        (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)).pre.map (artinBP.runGen k (action_atomRunAt k)))
      (congrArg GenObj.mk (artinBP.famV_runPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (atomRunAt k)))
      (congrArg GenObj.mk (artinBP.famV_runPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (mergeRunAt k)))
      = artinBP.runGen k hact :=
    artinRunGen_ext
      (artinBP.famV_runPt ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)
        (atomRunAt k))
      (artinBP.famV_runPt ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)
        (mergeRunAt k)) _ (artinBP.runGen k hact) HEq.rfl
  change genCell ⟨k, hgen⟩
    = Quiver.homOfEq (ιE (Hbp.obj (□n)) artinBP.fam c (artinBP.runGen k hact)) hx hy
  refine eq_of_heq (((Quiver.homOfEq_heq _ _ (atomCell k (artinRun x))).trans ?_).trans
    (Quiver.homOfEq_heq hx hy
      (ιE (Hbp.obj (□n)) artinBP.fam c (artinBP.runGen k hact))).symm)
  refine HEq.trans ?_ (heq_of_eq (congrArg (ιE (Hbp.obj (□n)) artinBP.fam c) hg))
  refine HEq.trans ?_ (heq_of_eq (ιE_homOfEq (Hbp.obj (□n)) artinBP.fam c
      ((artinBP.fam.map ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)).pre.map
        (artinBP.runGen k (action_atomRunAt k)))
      (congrArg GenObj.mk (artinBP.famV_runPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (atomRunAt k)))
      (congrArg GenObj.mk (artinBP.famV_runPt
        ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι) (mergeRunAt k)))).symm)
  refine HEq.trans ?_ (Quiver.homOfEq_heq _ _ (ιE (Hbp.obj (□n)) artinBP.fam c
    ((artinBP.fam.map ((CategoryOfElements.π (wedgeHoms (Hbp.obj (□n)))).leftOp.map ι)).pre.map
      (artinBP.runGen k (action_atomRunAt k))))).symm
  refine HEq.trans ?_ (heq_of_eq (ιE_leg (Hbp.obj (□n)) artinBP.fam ι
    (artinBP.runGen k (action_atomRunAt k))).symm)
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
      GenObj ((colimit (elementsPoly (wedgeHoms (Hbp.obj (□n))) artinBP.fam)).op).Gen where
  obj := obCell
  map := genCell

/-- **…and it is an isomorphism of generating quivers**: the `n!` runs biject with the colimit's
0-cells, and each hom-set of Artin generators with the colimit's 1-cells there.  With
`artinColimMap` — the same data, naming the same arrows — the two presentations of
`Ch(Hbp □ⁿ)[W⁻¹]` agree in both generating dimensions. -/
theorem bijective_genQuiver (n : ℕ) :
    Function.Bijective (genQuiver n).obj ∧
      ∀ x y : GenObj (hLocArtinPoly n).Gen,
        Function.Bijective ((genQuiver n).map : (x ⟶ y) → _) :=
  ⟨bijective_obCell n, fun _ _ => bijective_genCell⟩

end ChainCat
