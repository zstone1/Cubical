import CubeChains.Concurrency.Merge.MergeGenerate
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Concurrency/Merge/WedgeSlice — a slice of `Ch Zbp` is the chains of a wedge

An object of `Ch Zbp` over `d` is a shape together with a map of its wedge into `⋁d.dims`
(`serialWedgeFullyFaithful`: the triangle over the terminal object is free), and that is an object
of `Ch (⋁d.dims)` on the nose.  Both directions are written down — `overToWedgeChains` and
`wedgeChainsToOver` — because a client that has to compute needs the one it uses, and
`Functor.inv` is a choice.
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

/-- **The slice over a chain is the chains of its wedge** — the same data, reshuffled. -/
def overToWedgeChains : Over d ⥤ Ch (⋁d.dims) where
  obj a := ⟨a.left.dims, a.hom.φ⟩
  map {a _} f := ⟨f.left.φ, congrArg (fun g : a.left ⟶ d => Hom.φ g) (Over.w f)⟩
  map_id _ := hom_ext' rfl
  map_comp _ _ := hom_ext' rfl

@[simp] theorem overToWedgeChains_obj_dims (a : Over d) :
    ((overToWedgeChains d).obj a).dims = a.left.dims := rfl

@[simp] theorem overToWedgeChains_obj_map (a : Over d) :
    ((overToWedgeChains d).obj a).map = a.hom.φ := rfl

@[simp] theorem overToWedgeChains_map_φ {a b : Over d} (f : a ⟶ b) :
    Hom.φ ((overToWedgeChains d).map f) = f.left.φ := rfl

/-- **…and back**: a chain of `⋁d.dims` is a chain of `Zbp` over `d`. -/
def wedgeChainsToOver : Ch (⋁d.dims) ⥤ Over d where
  obj c := Over.mk (⟨c.map, Subsingleton.elim _ _⟩ : zObj c.dims ⟶ d)
  map {_ _} f := Over.homMk ⟨f.φ, Subsingleton.elim _ _⟩ (hom_ext' f.w)
  map_id _ := Over.OverMorphism.ext (hom_ext' rfl)
  map_comp _ _ := Over.OverMorphism.ext (hom_ext' rfl)

@[simp] theorem wedgeChainsToOver_obj_left (c : Ch (⋁d.dims)) :
    ((wedgeChainsToOver d).obj c).left = zObj c.dims := rfl

@[simp] theorem wedgeChainsToOver_obj_hom_φ (c : Ch (⋁d.dims)) :
    Hom.φ ((wedgeChainsToOver d).obj c).hom = c.map := rfl

@[simp] theorem wedgeChainsToOver_map_left_φ {c c' : Ch (⋁d.dims)} (f : c ⟶ c') :
    Hom.φ ((wedgeChainsToOver d).map f).left = f.φ := rfl

/-- Both sides have the same morphisms: a wedge map over `⋁d.dims` is a triangle over `d`. -/
def wedgeChainsToOverFullyFaithful : (wedgeChainsToOver d).FullyFaithful where
  preimage {_ _} g := ⟨g.left.φ, congrArg Hom.φ (Over.w g)⟩
  map_preimage _ := Over.OverMorphism.ext (hom_ext' rfl)
  preimage_map _ := hom_ext' rfl

instance : (wedgeChainsToOver d).Full := (wedgeChainsToOverFullyFaithful d).full

instance : (wedgeChainsToOver d).Faithful := (wedgeChainsToOverFullyFaithful d).faithful

/-- Every slice object is a chain of the wedge, up to renaming its shape by itself. -/
def wedgeChainsToOverEssIso (a : Over d) :
    (wedgeChainsToOver d).obj ((overToWedgeChains d).obj a) ≅ a :=
  Over.isoMk (zObjIso a.left) (hom_ext' (Category.id_comp _))

instance : (wedgeChainsToOver d).EssSurj where
  mem_essImage a := ⟨(overToWedgeChains d).obj a, ⟨wedgeChainsToOverEssIso d a⟩⟩

instance : (wedgeChainsToOver d).IsEquivalence where

/-- The same morphisms, read the other way round. -/
def overToWedgeChainsFullyFaithful : (overToWedgeChains d).FullyFaithful where
  preimage {_ _} g := Over.homMk ⟨g.φ, Subsingleton.elim _ _⟩ (hom_ext' g.w)
  map_preimage _ := hom_ext' rfl
  preimage_map _ := Over.OverMorphism.ext (hom_ext' rfl)

instance : (overToWedgeChains d).Full := (overToWedgeChainsFullyFaithful d).full

instance : (overToWedgeChains d).Faithful := (overToWedgeChainsFullyFaithful d).faithful

instance : (overToWedgeChains d).EssSurj where
  mem_essImage c := ⟨(wedgeChainsToOver d).obj c, ⟨Iso.refl _⟩⟩

instance : (overToWedgeChains d).IsEquivalence where

theorem over_W_eq_inverseImage :
    (W Zbp).over (X := d) = (W (⋁d.dims)).inverseImage (overToWedgeChains d) :=
  MorphismProperty.ext _ _ fun _ _ f =>
    (W_iff_crossPerm_eq_one rfl f.left).trans
      (W_iff_crossPerm_eq_one rfl ((overToWedgeChains d).map f)).symm

theorem W_eq_inverseImage_wedgeChainsToOver :
    W (⋁d.dims) = ((W Zbp).over (X := d)).inverseImage (wedgeChainsToOver d) :=
  MorphismProperty.ext _ _ fun _ _ f =>
    (W_iff_crossPerm_eq_one rfl f).trans
      (W_iff_crossPerm_eq_one rfl ((wedgeChainsToOver d).map f).left).symm

end ChainCat
