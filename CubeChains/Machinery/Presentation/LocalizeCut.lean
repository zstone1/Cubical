import CubeChains.Machinery.Presentation.Localize
import CubeChains.Concurrency.Presentation.CutPresentation
import CubeChains.Concurrency.Merge.MergeGenerate

/-!
# Machinery/Presentation/LocalizeCut — the bead cuts with the merges inverted

`Cut.poly` presents `(Ch Zbp)ᵒᵖ`, so both the class and the localization live on that side:
`zCutLocPresentation` reads `Machinery/Presentation/Localize` at the merge generators.  The only
reversal is `MorphismProperty.multiplicativeClosure_op`; the 0-cells need no transport, since
`zCutPresentation` names `A : (Ch Zbp)ᵒᵖ` by `op A.unop`, which is `A`.
-/

open CategoryTheory CubeChains BPSet Opposite

namespace ChainCat

/-- A cut generator, read as an arrow of `(Ch Zbp)ᵒᵖ`. -/
theorem zCutPresentation_arrow {x y : GenObj Cut.Refine} (e : x ⟶ y) :
    zCutPresentation.arrow e = e.1.op :=
  Paths.lift_toPath Cut.interp e

/-- **The bead merges, among the cut generators.** -/
def Cut.mergeGen {a b : Ch Zbp} (e : Cut.Refine a b) : Prop := merge Zbp e.1

/-- **…exactly the generators that cross nothing** — a generator is codimension one already. -/
theorem Cut.mergeGen_iff {a b : Ch Zbp} {N : ℕ} (h : dimSum b.dims = N) (e : Cut.Refine a b) :
    Cut.mergeGen e ↔ crossPerm h e.1 = 1 :=
  merge_iff_of_codim_one h e.2

/-- **The arrows the merge generators name are the merges**, reversed. -/
theorem pickedArrows_mergeGen :
    zCutPresentation.pickedArrows Cut.mergeGen = (merge Zbp).op := by
  ext A B f
  constructor
  · rintro ⟨e, he⟩
    change merge Zbp (zCutPresentation.arrow (Polygraph.cell e)).unop
    rw [zCutPresentation_arrow]
    exact he
  · intro hf
    have hc : codim f.unop = 1 := codim_eq_one_of_merge Zbp hf
    have hfe : zCutPresentation.arrow (Polygraph.cell (Cut.gen f.unop hc)) = f :=
      zCutPresentation_arrow _
    have hmk := Presents.Picked.mk (p := zCutPresentation) (S := Cut.mergeGen)
      (Cut.gen f.unop hc) hf
    rwa [hfe] at hmk

/-- **…so the merge generators generate the merges**, reversed. -/
theorem W_op_eq_multiplicativeClosure_mergeGen :
    (W Zbp).op = (zCutPresentation.pickedArrows Cut.mergeGen).multiplicativeClosure := by
  rw [pickedArrows_mergeGen, ← MorphismProperty.multiplicativeClosure_op]; rfl

/-- **`Ch Zbp` with the bead merges inverted is presented by the bead cuts plus a formal inverse for
each merge generator** — the cancellation 2-cells are the only new relations. -/
noncomputable def zCutLocPresentation :
    Presents (Polygraph.invPoly Cut.poly Cut.mergeGen) ((W Zbp).op).Localization :=
  zCutPresentation.presentsLocalization Cut.mergeGen W_op_eq_multiplicativeClosure_mergeGen

end ChainCat
