import CubeChains.Foundations.GeoTensor.Hom
import CubeChains.Foundations.GeoTensor.Unit
import CubeChains.Foundations.GeoTensor.Assoc

/-!
# Foundations/GeoTensor/Monoidal — the computable geometric monoidal structure

Assembles the pieces (`Hom`, `Unit`, `Assoc`) into a `MonoidalCategory` on `PrecubicalSet` via
`MonoidalCategory.ofTensorHom`.  The only new content is `triangle`; the rest wires the already
bpMonoidal-shaped naturality/coherence lemmas.
-/

open CategoryTheory MonoidalCategory Opposite

namespace GeoTensor

/-- The triangle coherence, stated in the raw geometric defs (so the app `@[simp]` lemmas fire):
the unit half of `(X ⊗ 𝟙) ⊗ Y` collapses either way. -/
theorem geoTriangle (X Y : PrecubicalSet) :
    (associator X tensorUnit Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom
      = tensorHom (rightUnitor X).hom (𝟙 Y) := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro c
  obtain ⟨pq, r, hc, ⟨p, s, hw, x, u⟩, y⟩ := c
  have hs : s = 0 := unitCell_dim_zero u
  subst hs
  simp only [NatTrans.comp_app, types_comp_apply, associator_hom_app, tensorHom_app,
    assocFwd_p, assocFwd_q, assocFwd_x, assocFwd_y, NatTrans.id_app, CategoryTheory.id_apply,
    rightUnitor_hom_app]
  -- LHS `.y` is `(leftUnitor Y).hom.app _ (pair ..)`, defeq (rfl-lemma) to the transported cell.
  refine tensorCells_ext hw (Nat.zero_add r) ?_ ?_
  · exact (map_eqToHom_heq _ x).symm
  · exact map_eqToHom_heq _ _

/-- The geometric monoidal data on `PrecubicalSet`. -/
@[reducible] def geoStruct : MonoidalCategoryStruct PrecubicalSet where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft X _ _ g := whiskerLeft X g
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-- The geometric `MonoidalCategory` on `PrecubicalSet` (plain `def`; `PrecubicalSet` carries no
canonical product). -/
@[reducible] def geoMonoidal : MonoidalCategory PrecubicalSet :=
  letI := geoStruct
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensorHom_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => (tensorHom_comp_tensorHom f₁ g₁ f₂ g₂).symm)
    (associator_naturality := fun f₁ f₂ f₃ => associator_naturality f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => leftUnitor_naturality f)
    (rightUnitor_naturality := fun f => rightUnitor_naturality f)
    (pentagon := pentagon)
    (triangle := geoTriangle)

end GeoTensor
