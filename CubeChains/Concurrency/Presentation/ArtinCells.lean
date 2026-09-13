import CubeChains.Concurrency.Presentation.RunCells
import CubeChains.Concurrency.Presentation.ArtinDegreeZero

/-!
# Concurrency/Presentation/ArtinCells — the geometric cells against Artin's own

`chCellPresentation Zbp` presents `Ch(Z)[W⁻¹]` on the cuts out of the runs, `runBP.base` on Artin's
generators, and the two 1-cell families agree atom for atom:

    atomGen x k  ═══▸  runBP.gen (runAtom (vStrands x) k)

The 2-cells do not agree in number — a `Cut.Cell` is an *ordered pair of two-step factorisations*,
so one codimension-two cut out of a run carries several where `artinBP` carries one per pair of
atoms — which is why the comparison is a `Presents.Map` and not an isomorphism of polygraphs.
-/

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains

namespace ChainCat

/-- **A kept 1-cell at the base names the atom loop it cuts.** -/
theorem chCell_arrow_atomGen (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    (chCellPresentation Zbp).arrow (atomGen x k)
      = (runIsoAt x).hom ≫ atomLoop (vStrands x) k ≫ (runIsoAt x).inv :=
  ((chRunPresentation Zbp).restrictCells_arrow (chRunCutSpans Zbp) (atomGen x k)).trans
    (arrow_atomCell x k)

/-! ## Against Artin's own polygraph -/

/-- The atom index a 1-cell carries. -/
noncomputable def genIdx {X Y : GenObj (chRunCutSpans Zbp).poly.Gen} (e : X ⟶ Y) :
    Fin (vStrands Y.as - 1) :=
  (keptEquiv Y.as).symm
    (cellCongr (keptGen (P := zCutContraction.poly) OutOfRun) (eq_of_gen e.1) rfl e)

@[simp] theorem genIdx_atomGen (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    genIdx (atomGen x k) = k := (keptEquiv x).symm_apply_apply k

theorem exists_atomGen {X : GenObj (chRunCutSpans Zbp).poly.Gen} (e : X ⟶ X) :
    ∃ k : Fin (vStrands X.as - 1), atomGen X.as k = e :=
  ⟨(keptEquiv X.as).symm e, (keptEquiv X.as).apply_symm_apply e⟩

/-- The Artin generator an atom names. -/
noncomputable def genRunBP {X Y : GenObj (chRunCutSpans Zbp).poly.Gen} (e : X ⟶ Y) :
    runBP.pt (vStrands X.as) ⟶ runBP.pt (vStrands Y.as) :=
  Quiver.homOfEq (runBP.gen (runAtom (vStrands Y.as) (genIdx e)))
    (congrArg runBP.pt (congrArg vStrands (eq_of_gen e.1))).symm rfl

theorem genRunBP_atomGen (x : zCutContraction.V) (k : Fin (vStrands x - 1)) :
    genRunBP (atomGen x k) = runBP.gen (runAtom (vStrands x) k) := by
  rw [genRunBP, genIdx_atomGen]; rfl

/-- **The cuts out of the runs and Artin's generators present one category, atom by atom.** -/
noncomputable def runBPComparison :
    Polygraph.Presents.Map (chCellPresentation Zbp) runBP.base :=
  Polygraph.Presents.Map.ofGenerators (fun V => runBP.pt (vStrands V.as))
    (fun {_ _} e => genRunBP e) (fun V => (runIsoAt V.as).symm)
    (fun {X Y} e => by
      obtain rfl : X = Y := GenObj.ext (eq_of_gen e.1)
      obtain ⟨k, rfl⟩ := exists_atomGen e
      have h1 : runBP.base.arrow (genRunBP (atomGen X.as k)) = atomLoop (vStrands X.as) k := by
        rw [genRunBP_atomGen, runBase_arrow_atomLoop, runAtomLoop_runAtom]
      refine Eq.trans h1 (Eq.trans ?_
        (congrArg (fun t => (runIsoAt X.as).inv ≫ t ≫ (runIsoAt X.as).hom)
          (chCell_arrow_atomGen X.as k)).symm)
      simp)

end ChainCat
