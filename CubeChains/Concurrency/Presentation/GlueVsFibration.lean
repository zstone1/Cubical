import CubeChains.Concurrency.Presentation.SliceExchange
import CubeChains.Concurrency.Presentation.HAction
import CubeChains.Machinery.Presentation.Comparison
import CubeChains.Machinery.Presentation.Opposite

/-!
# Concurrency/Presentation/GlueVsFibration — the two presentations of `Ch(K)[W⁻¹]`, compared

The glue route names one 0-cell per **run of `K`** (`covered_iff_isRun`) and one 1-cell per
*witnessed* crossing — a run-step read inside a chain.  The fibration route names one 0-cell
per element of the fibre over the run and one 1-cell per base generator acting on it.  At
`K = Hbp □ⁿ` the fibre is the runs, so the 0-cells agree (`coveredVEquivPerm`).

What a 1-cell *does* is read by `eltBraid`, the positive braid an arrow of `Ch(K)[W⁻¹]` performs:
one crossing, undone by a merge (`overBraid_runStep`), and the crossing is an `adjT`
(`runStep_exists_adjT`) — an atom, which is what the fibration route's generators are.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Polygraph

namespace ChainCat

/-- **The objects of `Ch K` the copies name are exactly the runs.**  A copy contributes only runs,
and a run is a run over itself. -/
theorem covered_iff_isRun (K : BPSet) (v : GlueV (wedgeHoms K)) :
    Covered (wedgeHoms K) runLabels v ↔ IsRun Zbp v.1 := by
  constructor
  · rintro ⟨s, a, rfl⟩
    exact a.2
  · intro hv
    refine ⟨v, ⟨Over.mk (𝟙 v.1), hv⟩, ?_⟩
    simp only [gluePt, runLabels, Over.mk_left, Over.mk_hom, CategoryStruct.id]
    rfl

/-! ## The braid an arrow performs

`posGrade` reads a refinement's crossing permutation as a Garside simple and inverts the merges, so
it descends to `Ch(K)[W⁻¹]` along the projection to the base — with no hypothesis on `K`, and with
its value on a `Q`-image forced.  It is what says a 1-cell names an *atom*. -/

section Braid

variable (K : BPSet)

theorem eltBraid_inverts :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).IsInvertedBy
      ((CategoryOfElements.π (wedgeHoms K)).leftOp ⋙ posGrade) :=
  fun _ _ _ hf => posGrade_inverts _ hf

/-- **The positive braid an arrow of `Ch(K)[W⁻¹]` performs** — `posGrade`, descended along the
projection to the base. -/
noncomputable def eltBraid :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Localization ⥤
      FullPosBraid :=
  Localization.Construction.lift _ (eltBraid_inverts K)

theorem eltBraid_fac :
    ((W Zbp).inverseImage (CategoryOfElements.π (wedgeHoms K)).leftOp).Q ⋙ eltBraid K
      = (CategoryOfElements.π (wedgeHoms K)).leftOp ⋙ posGrade :=
  Localization.Construction.fac _ _

/-- The braid a slice performs. -/
noncomputable def overBraid (d : Ch Zbp) : ((W Zbp).over (X := d)).Localization ⥤ FullPosBraid :=
  Localization.Construction.lift (Over.forget d ⋙ posGrade) fun _ _ _ hf => posGrade_inverts _ hf

/-- **A slice's braid is the ambient one.**  The cartesian lift is a section of the projection
(`elementsLift_comp_π`, an equality on the nose), so the two descents agree — no comparison iso, and
in particular a 1-cell's braid may be read in its own slice. -/
theorem glueSliceEval_comp_eltBraid (d : Ch Zbp) (x : (wedgeHoms K).obj (op d)) :
    glueSliceEval (wedgeHoms K) (W Zbp) d x ⋙ eltBraid K = overBraid d :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, glueSliceEval_fac, Functor.assoc, eltBraid_fac, ← Functor.assoc,
      elementsLift_comp_π]
    exact (Localization.Construction.fac _ _).symm)

end Braid

/-! ## At the decorated cube: the 0-cells are the fibre

`Hbp □ⁿ` puts every chain at `n` strands, so a covered 0-cell is *the* run shape and its data is a
map out of `⋁1ⁿ` — the fibre over the run, which is what the fibration route's 0-cells are. -/

/-- **Every 0-cell of the glued polygraph of `Hbp □ⁿ` sits at the run.** -/
theorem covered_eq_run (n : ℕ) {v : GlueV (wedgeHoms (Hbp.obj (□n)))}
    (hv : Covered (wedgeHoms (Hbp.obj (□n))) runLabels v) : v.1 = zObj (𝟙^n) := by
  have hrun := (covered_iff_isRun (Hbp.obj (□n)) v).mp hv
  refine Obj.eq_of_dims ?_
  rw [zObj_dims, eq_replicate_of_ones hrun,
    ← dimSum_eq_length_of_ones hrun, hbpCubeStrands v.2]

/-- The 0-cell a map out of the run names. -/
def runToCoveredV (n : ℕ) (x : ⋁(𝟙^n) ⟶ Hbp.obj (□n)) :
    CoveredV (wedgeHoms (Hbp.obj (□n))) runLabels :=
  ⟨⟨zObj (𝟙^n), x⟩, (covered_iff_isRun _ _).mpr fun _ hd => List.eq_of_mem_replicate hd⟩

theorem bijective_runToCoveredV (n : ℕ) : Function.Bijective (runToCoveredV n) := by
  constructor
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
  · rintro ⟨⟨d, x⟩, hv⟩
    obtain rfl : d = zObj (𝟙^n) := covered_eq_run n hv
    exact ⟨x, rfl⟩

/-- **The 0-cells of the two presentations agree**: the glued polygraph's are the runs of `Hbp □ⁿ`,
which are the `n!` orderings of the axes — the fibre the fibration route indexes its 0-cells by. -/
noncomputable def coveredVEquivPerm (n : ℕ) :
    CoveredV (wedgeHoms (Hbp.obj (□n))) runLabels ≃ Equiv.Perm (Fin n) :=
  (Equiv.ofBijective _ (bijective_runToCoveredV n)).symm.trans (runFibreEquiv n)

/-! ## The 1-cells

A 1-cell of the glued polygraph is a `RunStep` inside a chain.  Two readings of it: what it
*is* — an adjacent transposition of the source run, absorbed by a merge from the target — and what
it *names* in the localized slice, which thinness pins with nothing chosen. -/

/-- **A 1-cell of the glued polygraph is an adjacent transposition.**  `RunStep` asks for one
crossing; a permutation with one inversion is an `adjT`. -/
theorem runStep_exists_adjT {d : Ch Zbp} {a b : RunOver d} (h : RunStep a b) :
    ∃ (e : Ch Zbp) (t : a.1.left ⟶ e) (m : b.1.left ⟶ e) (z : e ⟶ d)
      (k : Fin (dimSum a.1.left.dims - 1)),
      crossPerm rfl t = adjT k ∧ W Zbp m ∧ t ≫ z = a.1.hom ∧ m ≫ z = b.1.hom := by
  obtain ⟨e, t, m, z, ht, hm, hta, hmb⟩ := h
  obtain ⟨k, hk⟩ := eq_adjT_of_permLen_eq_one ht
  exact ⟨e, t, m, z, k, hk, hm, hta, hmb⟩

/-- **What a 1-cell names**: cross the pair, then undo the merge.  The localized slice is a poset,
so this is *the* arrow, not a choice of one. -/
theorem runSlicePresentation_arrow {d : Ch Zbp} {a b : RunOver d} (h : PLift (RunStep a b))
    {e : Ch Zbp} {t : a.1.left ⟶ e} {m : b.1.left ⟶ e} {z : e ⟶ d}
    (hm : W Zbp m) (hta : t ≫ z = a.1.hom) (hmb : m ≫ z = b.1.hom) :
    haveI : IsIso (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
      Localization.inverts ((W Zbp).over (X := d)).Q ((W Zbp).over (X := d)) _ hm
    (runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)
      = ((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z) ≫
        inv (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
  Subsingleton.elim _ _

theorem overBraid_Q {d : Ch Zbp} {y y' : Over d} (f : y ⟶ y') :
    (overBraid d).map (((W Zbp).over (X := d)).Q.map f) = posGrade.map f.left :=
  Category.id_comp _

/-- **The braid a 1-cell performs**: cross the one pair, then undo the merge.  With
`runStep_exists_adjT` — the crossing is an `adjT` — this says a 1-cell of the glued polygraph names
an **atom** of the braid monoid, which is what the fibration route's generators are. -/
theorem overBraid_runStep {d : Ch Zbp} {a b : RunOver d} (h : PLift (RunStep a b))
    {e : Ch Zbp} {t : a.1.left ⟶ e} {m : b.1.left ⟶ e} {z : e ⟶ d}
    (hm : W Zbp m) (hta : t ≫ z = a.1.hom) (hmb : m ≫ z = b.1.hom) :
    (overBraid d).map ((runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩))
        ≫ posGrade.map m = posGrade.map t := by
  haveI : IsIso (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
    Localization.inverts ((W Zbp).over (X := d)).Q ((W Zbp).over (X := d)) _ hm
  have h1 : (overBraid d).map
      (((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z)) = posGrade.map t :=
    overBraid_Q _
  have h2 : (overBraid d).map
      (((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) = posGrade.map m :=
    overBraid_Q _
  have key : (runSlicePresentation d).arrow (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)
        ≫ ((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)
      = ((W Zbp).over (X := d)).Q.map (Over.homMk t hta : a.1 ⟶ Over.mk z) := by
    rw [runSlicePresentation_arrow h hm hta hmb]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun w => ((W Zbp).over (X := d)).Q.map
      (Over.homMk t hta : a.1 ⟶ Over.mk z) ≫ w)
      (IsIso.inv_hom_id (((W Zbp).over (X := d)).Q.map
        (Over.homMk m hmb : b.1 ⟶ Over.mk z)))).trans ?_
    exact Category.comp_id _
  have step : (overBraid d).map ((runSlicePresentation d).arrow
        (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)) ≫ posGrade.map m
      = (overBraid d).map ((runSlicePresentation d).arrow
        (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩) ≫
        ((W Zbp).over (X := d)).Q.map (Over.homMk m hmb : b.1 ⟶ Over.mk z)) :=
    (congrArg (fun w => (overBraid d).map ((runSlicePresentation d).arrow
        (h : (⟨a⟩ : GenObj (runPoly d).Gen) ⟶ ⟨b⟩)) ≫ w) h2.symm).trans
      ((overBraid d).map_comp _ _).symm
  rw [step, key]
  exact h1

end ChainCat
