import CubeChains.PrecubicalConstructions.StandardCube
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The box (precube) category and precubical sets as a presheaf topos

`Box` is the box / precube category: objects are dimensions `n : ℕ` and the
morphisms `m ⟶ n` are the precubical maps between standard cubes `□^m ⟶ □^n`.
Composition and identities are inherited from `PrecubicalConstructions`, so the
category axioms hold **for free** (no substitution-associativity bookkeeping).

`PrecubicalSet := Boxᵒᵖ ⥤ Type` is then the presheaf topos on `Box`.  As a
functor category into `Type` it is automatically (co)complete, so it has all
pushouts/colimits off the shelf — this is what discharges the temporary
`HasPushouts` placeholder once we transport along the equivalence
`PrecubicalSet ≌ PrecubicalConstructions`.
-/

open CategoryTheory CategoryTheory.Limits

/-- The box (precube) category: objects are dimensions; morphisms `m ⟶ n` are
precubical maps `□^m ⟶ □^n`. -/
structure Box where
  /-- The dimension of this box object. -/
  dim : ℕ

namespace Box

/-- Morphisms of `Box` are precubical maps between the standard cubes; the
category structure is inherited from `PrecubicalConstructions`. -/
instance : Category Box where
  Hom a b := StdCube.stdPre a.dim ⟶ StdCube.stdPre b.dim
  id a := 𝟙 (StdCube.stdPre a.dim)
  comp f g := f ≫ g
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

/-- The object `[n]` of `Box`. -/
abbrev ob (n : ℕ) : Box := ⟨n⟩

end Box

/-- **Precubical sets**, defined as the presheaf topos on the box category. -/
abbrev PrecubicalSet : Type 1 := Boxᵒᵖ ⥤ Type

namespace PrecubicalSet

/-- Precubical sets have all pushouts (a functor category into the cocomplete
category `Type`): this is the off-the-shelf cocompleteness we use to discharge
the temporary `HasPushouts PrecubicalConstructions` placeholder. -/
instance : HasPushouts PrecubicalSet := inferInstance

end PrecubicalSet
