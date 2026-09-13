import CubeChains.Concurrency.Merge.MergeGenerate
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Concurrency/Merge/WedgeSlice — a slice of `Ch Zbp` is the chains of a wedge

An object of `Ch Zbp` over `d` is a shape together with a map of its wedge into `⋁d.dims`
(`serialWedgeFullyFaithful`: the triangle over the terminal object is free), and that is an object
of `Ch (⋁d.dims)` on the nose.  `wedgeChainsToOver` is that, as a *named* equivalence so that it
computes on objects; `Functor.inv` is a choice, so the other direction is never spelled.
-/

open CategoryTheory BPSet CubeChains

namespace ChainCat

variable (d : Ch Zbp)

/-- **A chain of `Zbp` is the chain on its own shape** — `Zbp` is terminal, so only `dims` is data
and the comparison is the identity wedge map. -/
def zObjIso (a : Ch Zbp) : zObj a.dims ≅ a where
  hom := ⟨𝟙 _, Subsingleton.elim _ _⟩
  inv := ⟨𝟙 _, Subsingleton.elim _ _⟩
  hom_inv_id := hom_ext' (Category.comp_id _)
  inv_hom_id := hom_ext' (Category.comp_id _)

/-- **A chain of `⋁d.dims` is a chain of `Zbp` over `d`** — the same data, reshuffled. -/
def wedgeChainsToOver : Ch (⋁d.dims) ⥤ Over d where
  obj c := Over.mk (⟨c.map, Subsingleton.elim _ _⟩ : zObj c.dims ⟶ d)
  map {_ _} f := Over.homMk ⟨f.φ, Subsingleton.elim _ _⟩ (hom_ext' f.w)
  map_id _ := Over.OverMorphism.ext (hom_ext' rfl)
  map_comp _ _ := Over.OverMorphism.ext (hom_ext' rfl)

/-- Both sides have the same morphisms: a wedge map over `⋁d.dims` is a triangle over `d`. -/
def wedgeChainsToOverFullyFaithful : (wedgeChainsToOver d).FullyFaithful where
  preimage {_ _} g := ⟨g.left.φ, congrArg Hom.φ (Over.w g)⟩
  map_preimage _ := Over.OverMorphism.ext (hom_ext' rfl)
  preimage_map _ := hom_ext' rfl

instance : (wedgeChainsToOver d).Full := (wedgeChainsToOverFullyFaithful d).full

instance : (wedgeChainsToOver d).Faithful := (wedgeChainsToOverFullyFaithful d).faithful

/-- Every slice object is a chain of the wedge, up to renaming its shape by itself. -/
def wedgeChainsToOverEssIso (a : Over d) :
    (wedgeChainsToOver d).obj ⟨a.left.dims, a.hom.φ⟩ ≅ a :=
  Over.isoMk (zObjIso a.left) (hom_ext' (Category.id_comp _))

instance : (wedgeChainsToOver d).EssSurj where
  mem_essImage a := ⟨⟨a.left.dims, a.hom.φ⟩, ⟨wedgeChainsToOverEssIso d a⟩⟩

instance : (wedgeChainsToOver d).IsEquivalence where

theorem W_eq_inverseImage_wedgeChainsToOver :
    W (⋁d.dims) = ((W Zbp).over (X := d)).inverseImage (wedgeChainsToOver d) :=
  MorphismProperty.ext _ _ fun _ _ f =>
    (W_iff_crossPerm_eq_one rfl f).trans
      (W_iff_crossPerm_eq_one rfl ((wedgeChainsToOver d).map f).left).symm

end ChainCat
