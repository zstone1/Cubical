import CubeChains.Concurrency.Presentation.PaperArtin
import CubeChains.Concurrency.Presentation.BaseDecomposition

/-!
# Concurrency/Presentation/BaseBraids — the localized base is the graded braid monoid

A **corollary** of the presentation, not an input to it.  `paperPresents Zbp` presents
`Ch Zbp[W⁻¹]` by the paper polygraph, `paperArtinIso` identifies that polygraph with `artinBP.poly`
cell for cell and word for word, and `artinBP.braids` presents `FullPosBraidᵒᵖ` by the same
polygraph — so the two categories are equivalent.

Nothing above this file mentions `FullPosBraid`: the route to `paperPresents` does not pass
through the braid monoid, and `Concurrency/Presentation/BasePresentation` is pure braid theory.
-/

open CategoryTheory Opposite CubeChains

namespace ChainCat

/-- **`Ch Zbp[W⁻¹]` *is* the graded positive braid monoid** — one object per strand count, its
endomorphisms the braids on that many strands.  Two presentations of one polygraph. -/
noncomputable def fullBaseEquiv : FullPosBraidᵒᵖ ≌ ((W Zbp).op).Localization :=
  artinBP.braids.equiv.symm.trans
    ((Polygraph.presentedEquiv Paper.paperArtinIso).symm.trans (Paper.paperPresents Zbp).equiv)

/-- **…so a braid presentation presents the localized base** — `braids`, carried across. -/
noncomputable def BraidPresentation.base (p : BraidPresentation) :
    Presents p.poly (((W Zbp).op).Localization) :=
  p.braids.transport fullBaseEquiv

/-- **The `k`-th Artin generator's braid is the `k`-th atom**, read at the run: the loop
`runBase N` names is the merge–unmerge square across the junction `k`. -/
theorem runBase_artinBP_braid (N : ℕ) (k : Fin (N - 1)) :
    (runBase N).map (posArrow N (artinBP.braid k)) = atomLoop N k := by
  rw [runBase_map_posArrow, artinBP_braid, runBraid_posPerm, runLoop_adjT]
  rfl

end ChainCat
