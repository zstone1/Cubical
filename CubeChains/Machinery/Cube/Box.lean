import CubeChains.Precubical.Basic.StandardCube
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Machinery/Cube/Box

The box / precube category `Box` **is** sign-vector algebra: objects are dimensions, a morphism
`▫m ⟶ ▫n` *is* a cell `Cell n m` of `□ⁿ` with `m` free coordinates, the identity is the top cell
and composition is substitution.  The category laws are `subst_topCell`, `topCell_subst`,
`subst_assoc` — no peeling induction anywhere.

`PrecubicalSet := Boxᵒᵖ ⥤ Type` is the default model downstream.  As a functor category into
`Type` it is (co)complete, so all pushouts/colimits come **off the shelf**.
-/

open CategoryTheory CategoryTheory.Limits StdCube

/-- The box (precube) category: objects are dimensions; morphisms `▫m ⟶ ▫n` are
sign vectors `Cell n m`. -/
structure Box where
  /-- The dimension of this box object. -/
  dim : ℕ

namespace Box

/-- Morphisms of `Box` are sign vectors, composed by substitution. -/
instance : Category Box where
  Hom a b := Cell b.dim a.dim
  id a := topCell a.dim
  comp f g := subst g f
  id_comp f := subst_topCell f
  comp_id f := topCell_subst f
  assoc f g h := (subst_assoc h g f).symm

/-- The object `[n]` of `Box`. -/
abbrev ob (n : ℕ) : Box := ⟨n⟩

end Box

/-- `▫n` — the site object of dimension `n`.  Distinct from `□n` (`BPSet.cube n`, the *cube* as a
bi-pointed set): a presheaf is evaluated at `op ▫n`, not at `□n`. -/
notation:max "▫" n:max => Box.ob n

/-- **Precubical sets**, defined as the presheaf topos on the box category. -/
abbrev PrecubicalSet : Type 1 := Boxᵒᵖ ⥤ Type

namespace PrecubicalSet

/-- Precubical sets have all pushouts (a functor category into the cocomplete
category `Type`). -/
instance : HasPushouts PrecubicalSet := inferInstance
end PrecubicalSet

namespace CategoryTheory

/-- Two natural transformations of `Type`-valued functors agree when they agree on every element.
`NatTrans.ext` alone does not reach it: `ConcreteCategory` bundles the components. -/
theorem NatTrans.ext_apply {C : Type*} [Category C] {X Y : C ⥤ Type} {f g : X ⟶ Y}
    (h : ∀ (B : C) (c : X.obj B), f.app B c = g.app B c) : f = g := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro c
  exact h B c

end CategoryTheory
