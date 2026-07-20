import CubeChains.Salvetti.Elements

/-!
# Salvetti/ElementsComp — computable base change for categories of elements

`CategoryOfElements.preEquivalence` inverts `pre P e.functor` through `EssSurj`, so its inverse
functor is `Classical.choice` data.  Here that inverse is written out —
`⟨X, x⟩ ↦ ⟨e.inverse.obj X, P.map (ε⁻¹ X) x⟩`, transporting the element along the counit — so the
resulting equivalence computes.
-/

open CategoryTheory

namespace CategoryTheory

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryOfElements

/-- The explicit inverse of `pre P e.functor`: an element `x` of `P` at `X` is carried to the
element of `e.functor ⋙ P` at `e.inverse.obj X` obtained by transporting `x` along the counit
`X ≅ e.functor.obj (e.inverse.obj X)`. -/
def preInv (P : C ⥤ Type w) (e : D ≌ C) : P.Elements ⥤ (e.functor ⋙ P).Elements where
  obj X := ⟨e.inverse.obj X.1, P.map (e.counitIso.inv.app X.1) X.2⟩
  map {X Y} k := ⟨e.inverse.map k.1, by
    have hn : e.counitIso.inv.app X.1 ≫ e.functor.map (e.inverse.map k.1)
        = k.1 ≫ e.counitIso.inv.app Y.1 := (e.counitIso.inv.naturality k.1).symm
    change P.map (e.functor.map (e.inverse.map k.1)) (P.map (e.counitIso.inv.app X.1) X.2)
        = P.map (e.counitIso.inv.app Y.1) Y.2
    calc P.map (e.functor.map (e.inverse.map k.1)) (P.map (e.counitIso.inv.app X.1) X.2)
        = P.map (e.counitIso.inv.app X.1 ≫ e.functor.map (e.inverse.map k.1)) X.2 :=
          (P.map_comp_apply _ _ _).symm
      _ = P.map (k.1 ≫ e.counitIso.inv.app Y.1) X.2 := by rw [hn]; rfl
      _ = P.map (e.counitIso.inv.app Y.1) (P.map k.1 X.2) := P.map_comp_apply _ _ _
      _ = P.map (e.counitIso.inv.app Y.1) Y.2 := by rw [k.2]⟩
  map_id X := CategoryOfElements.ext _ _ _ (e.inverse.map_id X.1)
  map_comp f g := CategoryOfElements.ext _ _ _ (e.inverse.map_comp f.1 g.1)

@[simp]
theorem preInv_obj_fst (P : C ⥤ Type w) (e : D ≌ C) (X : P.Elements) :
    ((preInv P e).obj X).1 = e.inverse.obj X.1 := rfl

@[simp]
theorem preInv_map_val (P : C ⥤ Type w) (e : D ≌ C) {X Y : P.Elements} (k : X ⟶ Y) :
    ((preInv P e).map k).val = e.inverse.map k.val := rfl

/-- **Base transport is an equivalence**, computably: for `e : D ≌ C`,
`pre P e.functor : (e.functor ⋙ P).Elements ≌ P.Elements`, with `preInv P e` as the inverse and
the unit/counit inherited componentwise from `e`. -/
def preEquivalenceComp (P : C ⥤ Type w) (e : D ≌ C) :
    (e.functor ⋙ P).Elements ≌ P.Elements where
  functor := pre P e.functor
  inverse := preInv P e
  unitIso := NatIso.ofComponents
    (fun Z => CategoryOfElements.isoMk _ _ (e.unitIso.app Z.1) (by
      change P.map (e.functor.map (e.unitIso.hom.app Z.1)) Z.2
          = P.map (e.counitIso.inv.app (e.functor.obj Z.1)) Z.2
      rw [← e.counitInv_app_functor]
      rfl))
    (fun k => CategoryOfElements.ext _ _ _ (e.unit_naturality k.1).symm)
  counitIso := NatIso.ofComponents
    (fun Z => CategoryOfElements.isoMk _ _ (e.counitIso.app Z.1) (by
      change P.map (e.counitIso.hom.app Z.1) (P.map (e.counitIso.inv.app Z.1) Z.2) = Z.2
      rw [← P.map_comp_apply, e.counitIso.inv_hom_id_app, P.map_id_apply]))
    (fun k => CategoryOfElements.ext _ _ _ (e.counit_naturality k.1))
  functor_unitIso_comp Z := CategoryOfElements.ext _ _ _ (e.functor_unit_comp Z.1)

@[simp]
theorem preEquivalenceComp_functor (P : C ⥤ Type w) (e : D ≌ C) :
    (preEquivalenceComp P e).functor = pre P e.functor := rfl

@[simp]
theorem preEquivalenceComp_inverse (P : C ⥤ Type w) (e : D ≌ C) :
    (preEquivalenceComp P e).inverse = preInv P e := rfl

end CategoryOfElements

end CategoryTheory
