import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Thin

/-!
# Foundations/SkeletalEquiv — an equivalence of skeletal categories is a bijection on objects

Between skeletal categories an equivalence has no room to move: the unit and counit are isos
between objects, hence equalities.  `Equivalence.objEquivOfSkeletal` packages that as an `Equiv`
whose `toFun` is *definitionally* `e.functor.obj`, which is what lets a group action transported
along `e` stay computable.

Also: skeletality passes to opposites and to categories of elements over a thin base.
-/

namespace CategoryTheory

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Between skeletal categories, an equivalence is a bijection on objects; `toFun` is defeq to
`e.functor.obj`. -/
def Equivalence.objEquivOfSkeletal (e : C ≌ D) (hC : Skeletal C) (hD : Skeletal D) : C ≃ D where
  toFun := e.functor.obj
  invFun := e.inverse.obj
  left_inv X := (hC ⟨e.unitIso.app X⟩).symm
  right_inv Y := hD ⟨e.counitIso.app Y⟩

/-- An equivalence preserves and reflects the existence of a morphism, so it is an order iso
for the "`Nonempty` hom" preorder on either side. -/
theorem Equivalence.nonempty_hom_iff (e : C ≌ D) (X Y : C) :
    Nonempty (e.functor.obj X ⟶ e.functor.obj Y) ↔ Nonempty (X ⟶ Y) :=
  ⟨fun ⟨f⟩ => ⟨e.unitIso.hom.app X ≫ e.inverse.map f ≫ e.unitIso.inv.app Y⟩,
   fun ⟨f⟩ => ⟨e.functor.map f⟩⟩

/-- Skeletality passes to the opposite category. -/
theorem Skeletal.op (hC : Skeletal C) : Skeletal Cᵒᵖ := fun _ _ h =>
  h.elim fun e => (Opposite.unop_injective (hC ⟨e.unop⟩)).symm

/-- Thinness passes to the opposite category. -/
instance Quiver.isThin_op [Quiver.IsThin C] : Quiver.IsThin Cᵒᵖ := fun X Y =>
  inferInstanceAs (Subsingleton (Y.unop ⟶ X.unop)ᵒᵖ)

/-- Over a thin skeletal base the category of elements is skeletal: the base components agree by
skeletality, and thinness forces the connecting map to be the resulting `eqToHom`. -/
theorem Functor.elements_skeletal [Quiver.IsThin C] (hC : Skeletal C) (P : C ⥤ Type w) :
    Skeletal P.Elements := fun x y h =>
  h.elim fun e =>
    have h₁ : x.1 = y.1 := hC ⟨(CategoryOfElements.π P).mapIso e⟩
    Functor.Elements.ext x y h₁ <| by
      rw [Subsingleton.elim (eqToHom h₁) e.hom.val]
      exact e.hom.2

end CategoryTheory
