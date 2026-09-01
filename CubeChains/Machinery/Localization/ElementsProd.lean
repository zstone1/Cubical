import Mathlib.CategoryTheory.Types.Basic

/-!
# Machinery/Localization/ElementsProd — the external product of two `Type`-valued functors

For `F : C ⥤ Type` and `G : D ⥤ Type`, the external product `F ⊠ G : C × D ⥤ Type`,
`(F ⊠ G)(c,d) = F c × G d` — what `BPSet.prod` is the diagonal of.
-/

open CategoryTheory

namespace CategoryTheory.CategoryOfElements

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The **external product** of `F : C ⥤ Type` and `G : D ⥤ Type`, a functor on `C × D`
with `(F ⊠ G)(c,d) = F c × G d`. -/
def extProd (F : C ⥤ Type w) (G : D ⥤ Type w) : C × D ⥤ Type w where
  obj cd := F.obj cd.1 × G.obj cd.2
  map {X Y} f := TypeCat.ofHom (fun p => (F.map f.1 p.1, G.map f.2 p.2))
  map_id X := by
    apply ConcreteCategory.hom_ext; intro p
    rw [TypeCat.ofHom_apply, types_id_apply]
    exact Prod.ext (by simp) (by simp)
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext; intro p
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    exact Prod.ext (by simp) (by simp)

@[simp] theorem extProd_map_apply (F : C ⥤ Type w) (G : D ⥤ Type w) {X Y : C × D}
    (f : X ⟶ Y) (p : (extProd F G).obj X) :
    (extProd F G).map f p = (F.map f.1 p.1, G.map f.2 p.2) := rfl

end CategoryTheory.CategoryOfElements
