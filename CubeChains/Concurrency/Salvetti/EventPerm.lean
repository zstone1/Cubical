import CubeChains.Concurrency.Executions.Runs
import CubeChains.Concurrency.Grading.CoordFunctor
import CubeChains.Concurrency.Grading.BlockDecomp
import Mathlib.CategoryTheory.Core

/-!
# Concurrency/Salvetti/EventPerm — the event relabelling of a `RunWedge` refinement

`eventEquiv f = coordMapEquiv (wedgeMap f)` : the bijection of atomic events a refinement induces,
read off its wedge map alone — no run.  It is a **contravariant functor** to finite sets and
bijections (`eventEquiv_comp`, from `coordMap_comp`), packaged as `eventCore : RunWedge ⥤ Core _`.

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

/-- **The event-groupoid representation** `RunWedge ⥤ Core (Type)`: each execution to its set of
atomic events, each refinement to the (inverse) relabelling *as an isomorphism*.  It lands in the
groupoid `Core (Type)` — not merely `Type` — because a refinement's relabelling is invertible, and
that is what makes the events a `Sₙ`-torsor at an all-edges base with no `runOrder` choice. -/
def eventCore : RunWedge ⥤ Core (Type) where
  obj X := ⟨beadEvent X.dims⟩
  map f := ⟨(eventEquiv f).symm.toIso⟩
  map_id X := by refine Core.hom_ext ?_; rw [eventEquiv_id]; rfl
  map_comp f g := by refine Core.hom_ext ?_; rw [eventEquiv_comp]; rfl

/-! ## The bead half of no-double-crossing

`eventEquiv` reads off the block form (`coordMap_eq`): bead `i`, axis `k` ↦ bead `blockIdx i`, axis
`faceEmb (blockFace i) k`.  Monotonicity of `blockIdx` is what keeps a cross-bead pair crossed; the
within-bead half needs the run order, and lives in `Concurrency/Salvetti/EventBraid`. -/

/-- The block form of the relabelling: bead `i`, axis `k` lands in bead `blockIdx i`, axis
`faceEmb (blockFace i) k`. -/
theorem eventEquiv_mk {X Y : RunWedge} (f : X ⟶ Y) (i : Fin Y.dims.length)
    (k : Fin (Y.dims.get i : ℕ)) :
    eventEquiv f ⟨i, k⟩
      = ⟨blockIdx (wedgeMap f).hom i, faceEmb (blockFace (wedgeMap f).hom i) k⟩ := by
  rw [eventEquiv_apply, coordMap_eq]

/-- The bead of a relabelled event is `blockIdx` of its bead. -/
theorem eventEquiv_fst {X Y : RunWedge} (f : X ⟶ Y) (a : beadEvent Y.dims) :
    (eventEquiv f a).1 = blockIdx (wedgeMap f).hom a.1 := by
  rw [eventEquiv_apply, coordMap_fst]

/-- `blockIdx` of a refinement's wedge map is monotone. -/
theorem blockIdx_monotone {X Y : RunWedge} (f : X ⟶ Y) :
    Monotone (blockIdx (wedgeMap f).hom) :=
  serialWedge_blockIdx_monotone _ (wedgeMap f).app_init

/-- **Cross-bead: a refinement strictly preserves the bead order.** -/
theorem chainBead_refine {Y Z : RunWedge} (g : Y ⟶ Z) {a b : beadEvent Y.dims}
    (h : (a.1 : ℕ) < b.1) : (((eventEquiv g).symm a).1 : ℕ) < ((eventEquiv g).symm b).1 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hmono := blockIdx_monotone g (Fin.le_def.mpr hcon)
  rw [← eventEquiv_fst, ← eventEquiv_fst, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hmono
  exact absurd h (not_lt.mpr (Fin.le_def.mp hmono))

end RunWedge
end CubeChains
