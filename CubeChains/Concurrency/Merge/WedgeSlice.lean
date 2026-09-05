import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Merge.MergeGenerate
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Concurrency/Merge/WedgeSlice — a slice of `Ch Zbp` is the chains of a wedge

An object of `Ch Zbp` over `zObj d` is a shape together with a map of its wedge into `⋁d`
(`serialWedgeFullyFaithful`: the triangle over the terminal object is free), and that is an object
of `Ch (⋁d)` on the nose.  `overToWedgeChains` is that identification; it is bijective on objects
and fully faithful, which is what lets a cube slice be read as a chain category.
-/

open CategoryTheory BPSet CubeChains

namespace ChainCat

variable (d : List ℕ+)

/-- **The slice over a shape is the chains of its wedge** — the same data, reshuffled. -/
def overToWedgeChains : Over (zObj d) ⥤ Ch (⋁d) where
  obj a := ⟨a.left.dims, a.hom.φ⟩
  map {a _} f := ⟨f.left.φ, congrArg (fun g : a.left ⟶ zObj d => Hom.φ g) (Over.w f)⟩
  map_id _ := hom_ext' rfl
  map_comp _ _ := hom_ext' rfl

@[simp] theorem overToWedgeChains_obj_dims (a : Over (zObj d)) :
    ((overToWedgeChains d).obj a).dims = a.left.dims := rfl

@[simp] theorem overToWedgeChains_obj_map (a : Over (zObj d)) :
    ((overToWedgeChains d).obj a).map = a.hom.φ := rfl

@[simp] theorem overToWedgeChains_map_φ {a b : Over (zObj d)} (f : a ⟶ b) :
    Hom.φ ((overToWedgeChains d).map f) = f.left.φ := rfl

/-- Both sides have the same morphisms: a wedge map over `⋁d` is a triangle over `zObj d`. -/
def overToWedgeChainsFullyFaithful : (overToWedgeChains d).FullyFaithful where
  preimage {_ _} g := Over.homMk ⟨g.φ, Subsingleton.elim _ _⟩ (hom_ext' g.w)
  map_preimage _ := hom_ext' rfl
  preimage_map _ := Over.OverMorphism.ext (hom_ext' rfl)

instance : (overToWedgeChains d).Full := (overToWedgeChainsFullyFaithful d).full

instance : (overToWedgeChains d).Faithful := (overToWedgeChainsFullyFaithful d).faithful

/-- Every chain of `⋁d` is a slice object on the nose — `zHom` is the inverse on objects. -/
instance : (overToWedgeChains d).EssSurj where
  mem_essImage c := ⟨Over.mk (zHom c.map), ⟨Iso.refl _⟩⟩

instance : (overToWedgeChains d).IsEquivalence where

/-- **`Ch(Z)/d ≌ Ch (⋁d)`.** -/
noncomputable def overEquivWedgeChains : Over (zObj d) ≌ Ch (⋁d) :=
  (overToWedgeChains d).asEquivalence

/-- **The identification carries `W/d` to `W`** — both sides are `crossPerm = 1` on the same wedge
map, which is what makes the slice presentation a presentation of `Ch (⋁d)`. -/
theorem over_W_eq_inverseImage :
    (W Zbp).over (X := zObj d) = (W (⋁d)).inverseImage (overToWedgeChains d) :=
  MorphismProperty.ext _ _ fun _ _ f =>
    (W_iff_crossPerm_eq_one rfl f.left).trans
      (W_iff_crossPerm_eq_one rfl ((overToWedgeChains d).map f)).symm

end ChainCat
