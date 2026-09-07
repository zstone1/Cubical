import CubeChains.Concurrency.Executions.Runs
import CubeChains.Concurrency.Grading.CoordFunctor
import CubeChains.Concurrency.Grading.BlockDecomp
import Mathlib.CategoryTheory.Core

/-!
# Concurrency/Salvetti/EventPerm — the event relabelling of a `RunWedge` refinement

`eventEquiv f = coordMapEquiv (wedgeMap f)` : the bijection of atomic events a refinement induces,
read off its wedge map alone — no run.  It is a **contravariant functor** to finite sets and
bijections (`eventEquiv_comp`, from `coordMap_comp`).

The lexicographic flattening `pos` (`Concurrency/Grading/CoordFunctor`) orders the beads;
`chainBead_refine` is the cross-bead half of no-double-crossing, and is all of it that survives
run-freely — the within-bead half genuinely needs the run order (`Concurrency/Salvetti/EventBraid`).
-/

open CategoryTheory CubeChain

namespace CubeChains

namespace RunWedge

@[simp] theorem wedgeMap_id (X : RunWedge) : wedgeMap (𝟙 X) = 𝟙 (⋁X.dims) := rfl

theorem wedgeMap_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wedgeMap (f ≫ g) = wedgeMap g ≫ wedgeMap f := rfl

/-- The event relabelling `beadEvent Y.dims ≃ beadEvent X.dims` induced by a refinement — `coordMap`
of its wedge map. -/
def eventEquiv {X Y : RunWedge} (f : X ⟶ Y) : beadEvent Y.dims ≃ beadEvent X.dims :=
  coordMapEquiv (wedgeMap f)

@[simp] theorem eventEquiv_apply {X Y : RunWedge} (f : X ⟶ Y) (e : beadEvent Y.dims) :
    eventEquiv f e = coordMap (wedgeMap f) e := rfl

@[simp] theorem eventEquiv_id (X : RunWedge) : eventEquiv (𝟙 X) = Equiv.refl _ :=
  coordMapEquiv_id

/-- **`eventEquiv` is a contravariant functor**: a composite refinement relabels events by the
composite (reversed) relabelling.  This is `coordMapEquiv_comp`. -/
theorem eventEquiv_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eventEquiv (f ≫ g) = (eventEquiv g).trans (eventEquiv f) :=
  coordMapEquiv_comp (wedgeMap g) (wedgeMap f)

theorem eventEquiv_mk {X Y : RunWedge} (f : X ⟶ Y) (i : Fin Y.dims.length)
    (k : Fin (Y.dims.get i : ℕ)) :
    eventEquiv f ⟨i, k⟩
      = ⟨blockIdx (wedgeMap f).hom i, faceEmb (blockFace (wedgeMap f).hom i) k⟩ := by
  rw [eventEquiv_apply, coordMap_eq]

/-- **Cross-bead: a refinement strictly preserves the bead order** — `coordMapEquiv_symm_fst_lt`. -/
theorem chainBead_refine {Y Z : RunWedge} (g : Y ⟶ Z) {a b : beadEvent Y.dims}
    (h : (a.1 : ℕ) < b.1) : (((eventEquiv g).symm a).1 : ℕ) < ((eventEquiv g).symm b).1 :=
  coordMapEquiv_symm_fst_lt (wedgeMap g) h

end RunWedge
end CubeChains
