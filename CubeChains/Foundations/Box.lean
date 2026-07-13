import CubeChains.Foundations.PrecubicalConstructions.StandardCube
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Foundations/Box

The box / precube category `Box` (objects = dimensions; morphisms `m ⟶ n` are the
precubical maps `□^m ⟶ □^n`, inherited from `PrecubicalConstructions`), and the
topos `PrecubicalSet := Boxᵒᵖ ⥤ Type` — the default model everywhere downstream.

As a functor category into `Type`, `PrecubicalSet` is (co)complete, so it has all
pushouts/colimits **off the shelf** — this is the payoff of the topos definition.
-/

open CategoryTheory CategoryTheory.Limits StdCube

/-- The box (precube) category: objects are dimensions; morphisms `m ⟶ n` are
precubical maps `□^m ⟶ □^n`. -/
structure Box where
  /-- The dimension of this box object. -/
  dim : ℕ

namespace Box

/-- Morphisms of `Box` are precubical maps between the standard cubes; the
category structure is inherited from `PrecubicalConstructions`. -/
instance : Category Box where
  Hom a b := stdPre a.dim ⟶ stdPre b.dim
  id a := 𝟙 (stdPre a.dim)
  comp f g := f ≫ g
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

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
category `Type`): this is the off-the-shelf cocompleteness we use to discharge
the temporary `HasPushouts PrecubicalConstructions` placeholder. -/
instance : HasPushouts PrecubicalSet := inferInstance

end PrecubicalSet
