import CubeChains.Concurrency.Presentation.SliceInherit
import CubeChains.Machinery.Presentation.ColimitCells

/-!
# Concurrency/Presentation/GlueRun — a run's own 0-cell in `Br p K`

Every 0-cell of `Br p K` is a run's, read in the copy indexed by the run's own chain
(`exists_glueRunV`): a 0-cell of a copy over `d` is a run over `d`, and a run over `d` is the
identity run pushed along its own arrow, so the colimit's leg carries it down.

Nothing here is Artin- or Garside-specific — the base presentation is an arbitrary
`BraidPresentation`, and the only thing used of it is that a strand-`N` 0-cell *is* the run.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph Limits Localization

namespace ChainCat

/-- The chain of `K` a run of `n` events is. -/
def runCh {K : BPSet} {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) : Ch K := ⟨𝟙^n, z⟩

/-- A run, as a run-arrow over its own chain. -/
def runAtSelf (n : ℕ) : RunAt (zObj (𝟙^n)) n :=
  ⟨⟨Over.mk (𝟙 _), fun _ hd => List.eq_of_mem_replicate hd⟩, dimSum_replicate n⟩

@[simp] theorem perm_runAtSelf (n : ℕ) : (runAtSelf n).perm = 1 :=
  crossPerm_id (zObj (𝟙^n)) _

/-- **The comparison with the localized category of elements, at a `Q`-image.** -/
noncomputable def glueUnitIso (K : BPSet) (a : Ch K) :
    (locEquivElements K).inverse.obj
        (((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj
          ((toElements K).obj a))
      ≅ (W K).Q.obj a :=
  haveI : (toElements K ⋙
      ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q).IsLocalization
        (W K) :=
    Functor.IsLocalization.of_inverseImage (toElements K) _ _ (W K)
      (W_eq_inverseImage_elements K)
  (locEquivElements K).inverse.mapIso
      ((Localization.compUniqFunctor (W K).Q
        (toElements K ⋙ ((W Zbp).inverseImage
          (CategoryOfElements.π (wedgeHoms K)).leftOp).Q) (W K)).app a).symm ≪≫
    ((locEquivElements K).unitIso.app ((W K).Q.obj a)).symm

namespace BraidPresentation

variable (p : BraidPresentation)

/-! ## The cells of a copy, at a run -/

/-- **The 0-cell of a copy a run names.** -/
noncomputable def runPt {d : Ch Zbp} {N : ℕ} (u : RunAt d N) : (slicePolyRaw p.base d).V :=
  sliceRunPt p.rels p.e u

theorem sliceCellOver_runPt {d : Ch Zbp} {N : ℕ} (u : RunAt d N) :
    sliceCellOver (p.runPt u) = u.1.1 :=
  sliceCellOver_sliceRunPt _ _ u

theorem famV_runPt {d' d : Ch Zbp} (f : d' ⟶ d) {N : ℕ} (u : RunAt d' N) :
    Presents.famV p.base _ (partialFam_push f) (p.runPt u) = p.runPt (RunAt.push f u) :=
  famV_sliceRunPt p.strandSeparated f u

/-- **The 1-cell a letter acting on a run names.** -/
noncomputable def runGen {d : Ch Zbp} {N : ℕ} {u v : RunAt d N} (s : p.S N)
    (h : (sliceActionAt d N (p.braid s)).unop.val (some u) = some v) :
    (⟨p.runPt u⟩ : GenObj (slicePolyRaw p.base d).Gen) ⟶ ⟨p.runPt v⟩ :=
  sliceRunGen p.rels p.e s h

/-! ## …and of the colimit -/

/-- **The object a 0-cell of `Br p K` names** — `ChainCat.at_glueV`, at `p`'s own colimit. -/
theorem at_glueV (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a : (slicePolyRaw p.base (eltBase (wedgeHoms K) c)).V) :
    (p.presentsBr K).at' (glueV K p.fam c a)
      = (locEquivElements K).inverse.obj
          ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).obj
            ((slicePresentationOf p.base (eltBase (wedgeHoms K) c)).at' ⟨a⟩)) :=
  ChainCat.at_glueV K p.fam (slicePresentationOf p.base)
    (fun {_ _} f => slicePoly_hP p.base f) (sliceSkeleton p.base p.strandSeparated) c a

/-- …and the arrow a 1-cell names. -/
theorem arrow_glueE (K : BPSet) (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (a b : (slicePolyRaw p.base (eltBase (wedgeHoms K) c)).V)
    (g : (⟨a⟩ : GenObj (p.fam.obj (eltBase (wedgeHoms K) c)).Gen) ⟶ ⟨b⟩) :
    (p.presentsBr K).arrow (glueE K p.fam c g)
      = eqToHom (p.at_glueV K c a) ≫ (locEquivElements K).inverse.map
            ((glueSliceEval (wedgeHoms K) (W Zbp) (eltBase (wedgeHoms K) c) c.unop.2).map
              ((slicePresentationOf p.base (eltBase (wedgeHoms K) c)).arrow g))
          ≫ eqToHom (p.at_glueV K c b).symm :=
  ChainCat.arrow_glueE K p.fam (slicePresentationOf p.base)
    (fun {_ _} f => slicePoly_hP p.base f) (sliceSkeleton p.base p.strandSeparated) c g

/-- **The 0-cell of `Br p K` a run names**: itself, in its own copy. -/
noncomputable def glueRunV (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) : GenObj (p.Br K).Gen :=
  glueV K p.fam ((toElements K).obj (runCh z)) (p.runPt (runAtSelf n))

theorem at_glueRunV (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (p.presentsBr K).at' (p.glueRunV K z)
      = (locEquivElements K).inverse.obj
          (((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj
            ((toElements K).obj (runCh z))) := by
  refine (ChainCat.at_glueV K p.fam (slicePresentationOf p.base)
    (fun {_ _} f => slicePoly_hP p.base f) (sliceSkeleton p.base p.strandSeparated)
    ((toElements K).obj (runCh z)) (p.runPt (runAtSelf n))).trans
      (congrArg (locEquivElements K).inverse.obj ?_)
  refine Eq.trans (congrArg
    (glueSliceEval (wedgeHoms K) (W Zbp) (zObj (𝟙^n)) z).obj
    (congrArg ((W Zbp).over (X := zObj (𝟙^n))).Q.obj
      (p.sliceCellOver_runPt (runAtSelf n)))) ?_
  refine (Functor.congr_obj
    (glueSliceEval_fac (wedgeHoms K) (W Zbp) (zObj (𝟙^n)) z) (Over.mk (𝟙 _))).trans ?_
  exact congrArg (fun t => ((W Zbp).inverseImage
    (CategoryOfElements.π (wedgeHoms K)).leftOp).Q.obj (op ⟨op (zObj (𝟙^n)), t⟩))
    ((wedgeHoms K).map_id_apply (op (zObj (𝟙^n))) z)

/-- **The glue route names the localized run chain.** -/
noncomputable def glueRunIso (K : BPSet) {n : ℕ} (z : ⋁(𝟙^n) ⟶ K) :
    (p.presentsBr K).at' (p.glueRunV K z) ≅ (W K).Q.obj (runCh z) :=
  eqToIso (p.at_glueRunV K z) ≪≫ glueUnitIso K (runCh z)

/-- **Every 0-cell of a copy is a run's own 0-cell** — a run over `d` is entered from its own
chain, and the leg down to it is an arrow of the elements. -/
theorem exists_glueRunV (K : BPSet) {n : ℕ} (c : ((wedgeHoms K).Elements)ᵒᵖ)
    (hc : dimSum (eltBase (wedgeHoms K) c).dims = n)
    (a : (slicePolyRaw p.base (eltBase (wedgeHoms K) c)).V) :
    ∃ z : ⋁(𝟙^n) ⟶ K, glueV K p.fam c a = p.glueRunV K z := by
  obtain ⟨u, rfl⟩ := exists_sliceRunPt_of_strands p.rels p.e hc a
  obtain ⟨⟨⟨l, ⟨⟩, h⟩, hrun⟩, hN⟩ := u
  obtain rfl : l = zObj (𝟙^n) := RunOver.left_eq hc ⟨Over.mk h, hrun⟩
  refine ⟨(wedgeHoms K).map h.op c.unop.2, Eq.trans (congrArg (glueV K p.fam c) ?_)
    ((congrArg (glueV K p.fam c) (p.famV_runPt h (runAtSelf n)).symm).trans
      (glueV_leg K p.fam (eltLeg K h c.unop.2) (p.runPt (runAtSelf n))))⟩
  exact congrArg p.runPt
    (Subtype.ext (Subtype.ext (congrArg Over.mk (Category.id_comp h).symm)))

end BraidPresentation

end ChainCat
