import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Machinery/Skeletal — skeletality, generically

A partial order is skeletal, skeletality passes to the opposite, and an equivalence onto a skeletal
category meets every object on the nose.  Nothing here knows about cubes; it sits above mathlib so
that the poset, the chain and the Salvetti readings can all cite it.
-/

namespace CategoryTheory

/-- A partial order is `Skeletal`: an iso is a pair of inequalities. -/
theorem skeletal_of_partialOrder {α : Type*} [PartialOrder α] : Skeletal α :=
  fun _ _ h => h.elim fun e => le_antisymm (leOfHom e.hom) (leOfHom e.inv)

theorem Skeletal.op {D : Type*} [Category D] (hD : Skeletal D) : Skeletal Dᵒᵖ :=
  fun _ _ h => h.elim fun e => (Opposite.unop_injective (hD ⟨e.unop⟩)).symm

/-- **An equivalence onto a skeletal category meets every object on the nose** — the counit is an
equality, so no transport is needed to read the inverse off. -/
theorem Equivalence.functor_obj_inverse_obj {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) (hD : Skeletal D) (Y : D) : E.functor.obj (E.inverse.obj Y) = Y :=
  hD ⟨E.counitIso.app Y⟩

end CategoryTheory
