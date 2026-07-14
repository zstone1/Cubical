import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Types.Basic

/-!
# Arrangements/ElementsProd — the external product of two `Type`-valued functors

For `F : C ⥤ Type` and `G : D ⥤ Type`, the external product `F ⊠ G : C × D ⥤ Type`,
`(F ⊠ G)(c,d) = F c × G d`, has as its category of elements the product of the two:

> `extProdEquiv : (F ⊠ G).Elements ≌ F.Elements × G.Elements`.

Shared by the chamber side `Lines P ⊠ Lines Q` (`Salvetti/LinesWedge.lean`) and the Salvetti
side `salFunctor L₁ ⊠ salFunctor L₂` (`Arrangements/SalSum.lean`).
-/

open CategoryTheory

namespace CategoryTheory.CategoryOfElements

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ## The external product of two functors and its category of elements -/

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

/-- Forward functor of the external-product-of-elements equivalence: split an element of
`(F ⊠ G).Elements` into its two coordinates. -/
@[reducible] def extProdToProd (F : C ⥤ Type w) (G : D ⥤ Type w) :
    (extProd F G).Elements ⥤ F.Elements × G.Elements where
  obj Z := (⟨Z.1.1, Z.2.1⟩, ⟨Z.1.2, Z.2.2⟩)
  map {Z W} m :=
    (⟨m.1.1, by have h := m.2; rw [extProd_map_apply] at h; exact congrArg (·.1) h⟩,
     ⟨m.1.2, by have h := m.2; rw [extProd_map_apply] at h; exact congrArg (·.2) h⟩)
  map_id Z := by apply Prod.ext <;> · apply CategoryOfElements.ext; rfl
  map_comp {Z W V} m n := by apply Prod.ext <;> · apply CategoryOfElements.ext; rfl

/-- Backward functor of the external-product-of-elements equivalence: merge two coordinates. -/
@[reducible] def extProdOfProd (F : C ⥤ Type w) (G : D ⥤ Type w) :
    F.Elements × G.Elements ⥤ (extProd F G).Elements where
  obj Z := ⟨(Z.1.1, Z.2.1), (Z.1.2, Z.2.2)⟩
  map {Z W} m := ⟨(m.1.1, m.2.1), by
    rw [extProd_map_apply]; exact Prod.ext m.1.2 m.2.2⟩
  map_id Z := by apply CategoryOfElements.ext; rfl
  map_comp {Z W V} m n := by apply CategoryOfElements.ext; rfl

theorem extProdToProd_obj_ofProd_obj (F : C ⥤ Type w) (G : D ⥤ Type w)
    (x : F.Elements × G.Elements) :
    (extProdToProd F G).obj ((extProdOfProd F G).obj x) = x := by
  obtain ⟨⟨c, u⟩, ⟨d, v⟩⟩ := x; rfl

instance extProdToProd_faithful (F : C ⥤ Type w) (G : D ⥤ Type w) :
    (extProdToProd F G).Faithful where
  map_injective {Z W} {m m'} h := by
    have h1 : m.1.1 = m'.1.1 := congrArg (fun p => p.1.val) h
    have h2 : m.1.2 = m'.1.2 := congrArg (fun p => p.2.val) h
    exact Subtype.ext (Prod.ext h1 h2)

instance extProdToProd_full (F : C ⥤ Type w) (G : D ⥤ Type w) :
    (extProdToProd F G).Full where
  map_surjective {Z W} k :=
    ⟨⟨(k.1.val, k.2.val), by rw [extProd_map_apply]; exact Prod.ext k.1.2 k.2.2⟩,
     by apply Prod.ext <;> · apply CategoryOfElements.ext; rfl⟩

instance extProdToProd_essSurj (F : C ⥤ Type w) (G : D ⥤ Type w) :
    (extProdToProd F G).EssSurj where
  mem_essImage x :=
    ⟨(extProdOfProd F G).obj x, ⟨eqToIso (extProdToProd_obj_ofProd_obj F G x)⟩⟩

/-- **External product of categories of elements:**
`(F ⊠ G).Elements ≌ F.Elements × G.Elements`. -/
noncomputable def extProdEquiv (F : C ⥤ Type w) (G : D ⥤ Type w) :
    (extProd F G).Elements ≌ F.Elements × G.Elements :=
  haveI : (extProdToProd F G).IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  (extProdToProd F G).asEquivalence

end CategoryTheory.CategoryOfElements
