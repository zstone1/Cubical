import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Concurrency.Presentation.SliceThin

/-!
# Concurrency/Presentation/SliceRunSet — the runs over a chain, and their down-set

The runs over `d` are the permutations `d`'s blocks allow (`RunOver.perm`), and that set is closed
downwards in the right weak order: the **exchange** `exists_runOver_mul_adjT`, iterated.  That one
fact is the whole of the geometry the braid layer sees.

The fibre is the runs themselves and not their permutations: postcomposition with `f : d' ⟶ d`
leaves a run's source untouched, so the strand count survives on the nose.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-- **The runs are never all of the slice**: `Over (zObj [2])` has an object that is not a run —
`𝟙` on the one-bead chain of length `2`.  So the slice family of
`Machinery/Presentation/SliceColimit` is not a levelwise *isomorphism* of categories, and its
retraction cannot be traded for one. -/
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

/-! ## Pushing a run forward -/

/-- Postcomposition on the runs; it does not touch the source, so the strand count survives on the
nose. -/
def RunAt.push {d' d : Ch Zbp} (f : d' ⟶ d) (u : RunAt d' N) : RunAt d N :=
  ⟨RunOver.push f u.1, u.2⟩

theorem RunAt.push_perm {d' d : Ch Zbp} (f : d' ⟶ d) (hd : dimSum d'.dims = N) (u : RunAt d' N) :
    (RunAt.push f u).perm = crossPerm hd f * u.perm := crossPerm_comp _ u.1.1.hom f

theorem RunAt.push_permLen {d' d : Ch Zbp} (f : d' ⟶ d) (hd : dimSum d'.dims = N)
    (u : RunAt d' N) :
    permLen (RunAt.push f u).perm = permLen u.perm + permLen (crossPerm hd f) :=
  permLen_crossPerm_comp _ u.1.1.hom f

/-- **A merge's crossings are new above every run**, so translating by it is length-additive.  This
is the one fact that makes postcomposition act on the germ and on the weak order alike. -/
theorem RunAt.permLen_crossPerm_mul {d' d : Ch Zbp} (f : d' ⟶ d) (hd : dimSum d'.dims = N)
    (u : RunAt d' N) :
    permLen (crossPerm hd f * u.perm) = permLen (crossPerm hd f) + permLen u.perm := by
  rw [← RunAt.push_perm f hd u, RunAt.push_permLen f hd u]
  omega

/-- **A rise in the weak order survives postcomposition** — the translation cancels out of the gap
`x⁻¹y` and adds to both lengths. -/
theorem RunAt.push_le_push {d' d : Ch Zbp} (f : d' ⟶ d) {u v : RunAt d' N}
    (h : WeakOrder.of u.perm ≤ WeakOrder.of v.perm) :
    WeakOrder.of (RunAt.push f u).perm ≤ WeakOrder.of (RunAt.push f v).perm := by
  rw [RunAt.push_perm f u.strands u, RunAt.push_perm f u.strands v]
  exact WeakOrder.of_mul_le_of_mul _ (RunAt.permLen_crossPerm_mul f u.strands u)
    (RunAt.permLen_crossPerm_mul f u.strands v) h

end ChainCat
