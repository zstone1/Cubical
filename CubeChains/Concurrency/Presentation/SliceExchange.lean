import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Concurrency.Presentation.SliceThin

/-!
# Concurrency/Presentation/SliceExchange — the runs are not all of the slice

Why the slice family of `Machinery/Presentation/SliceColimit` is not a levelwise *isomorphism* of
categories: a slice has objects that are not runs, so the retraction cannot be traded for one.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv Polygraph

namespace ChainCat

/-- **The runs are never all of the slice**: `Over (zObj [2])` has an object that is not a run —
`𝟙` on the one-bead chain of length `2`.  So the slice family is not a levelwise *isomorphism* of
categories, and the retraction of `Machinery/Presentation/SliceColimit` cannot be traded for one. -/
theorem exists_not_isRun_over :
    ∃ y : Over (zObj ([2] : List ℕ+)), ¬ IsRun Zbp y.left :=
  ⟨Over.mk (𝟙 _), fun h => absurd (h 2 (List.mem_singleton_self 2)) (by decide)⟩

end ChainCat
