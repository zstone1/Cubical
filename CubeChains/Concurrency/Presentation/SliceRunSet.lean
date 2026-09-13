import CubeChains.Concurrency.Presentation.SliceRuns

/-!
# Concurrency/Presentation/SliceRunSet — the runs over a chain, and the permutations they cross

The runs over `d` are the permutations `d`'s blocks allow (`RunSet`).  The fibre is the runs
themselves and not their permutations: postcomposition with `f : d' ⟶ d` leaves a run's source
untouched, so the strand count survives on the nose.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-- **The runs are never all of the slice**: `Over (zObj [2])` has an object that is not a run —
`𝟙` on the one-bead chain of length `2`. -/
theorem exists_not_isRun_over :
    ∃ y : Over (zObj ([2] : List ℕ+)), ¬ IsRun Zbp y.left :=
  ⟨Over.mk (𝟙 _), fun h => absurd (h 2 (List.mem_singleton_self 2)) (by decide)⟩

/-- The runs over `d` on `N` events. -/
abbrev RunAt (d : Ch Zbp) (N : ℕ) : Type := {u : RunOver d // dimSum u.1.left.dims = N}

/-- A run over `d` on `N` events knows `d`'s event count. -/
theorem RunAt.strands (u : RunAt d N) : dimSum d.dims = N :=
  (dimSum_eq_of_hom u.1.1.hom).symm.trans u.2

/-- **The crossing permutation of a run over `d`.** -/
noncomputable def RunAt.perm (u : RunAt d N) : Perm (Fin N) := RunOver.perm u.strands u.1

/-- **The permutations `d`'s blocks allow.** -/
def RunSet (d : Ch Zbp) (N : ℕ) : Perm (Fin N) → Prop := fun σ => ∃ u : RunAt d N, u.perm = σ

end ChainCat
