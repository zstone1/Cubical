import CubeChains.Chains.Category
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Chains/ChainSlice — the slice of `Ch K` over a chain is `Ch(□^∨(dims))`

For a cube chain `a : Ch K`, the slice over `a` is the cube-chain category of the serial
wedge on `a`'s dimension sequence:

      Over a  ────────────≌────────────▶  Ch(□^∨(a.dims))
        (b, f : b ⟶ a)   ↦   ⟨b.dims, f.φ⟩          (sliceForward / sliceEquiv)

`f.φ : □^∨(b.dims) ⟶ □^∨(a.dims)` *is* a cube chain of `□^∨(a.dims)`.  `sliceForward` is
fully faithful (slice morphisms over `a` are exactly `Ch(□^∨(a.dims))`-morphisms of the
images, via `hom_ext'`) and surjective on objects (`⟨d, m⟩` is hit by the push-forward
`⟨d, m ≫ a.map⟩ ⟶ a`, cf. `ChainCat.pushforward a.map`).
-/

open CategoryTheory Opposite

namespace ChainCat

variable {K : BPSet} (a : ChainCat.Obj K)

/-- `(b, f : b ⟶ a) ↦ ⟨b.dims, f.φ⟩`; a slice morphism to its underlying wedge map. -/
noncomputable def sliceForward : Over a ⥤ ChainCat.Obj (BPSet.serialWedge a.dims) where
  obj X := ⟨X.left.dims, X.hom.φ⟩
  map {_ _} g := ⟨g.left.φ, congrArg ChainCat.Hom.φ (Over.w g)⟩
  map_id _ := ChainCat.hom_ext' rfl
  map_comp _ _ := ChainCat.hom_ext' rfl

@[simp] theorem sliceForward_obj_dims (X : Over a) :
    ((sliceForward a).obj X).dims = X.left.dims := rfl

@[simp] theorem sliceForward_obj_map (X : Over a) :
    ((sliceForward a).obj X).map = X.hom.φ := rfl

@[simp] theorem sliceForward_map_φ {X Y : Over a} (g : X ⟶ Y) :
    ChainCat.Hom.φ ((sliceForward a).map g) = g.left.φ := rfl

/-- A slice morphism over `a` is determined by its underlying wedge map. -/
instance : (sliceForward a).Faithful where
  map_injective {X Y} {g₁ g₂} h := by
    have hφ := congrArg ChainCat.Hom.φ h
    exact Over.OverMorphism.ext (ChainCat.hom_ext' hφ)

/-- A `Ch(□^∨(a.dims))`-morphism between the images is a wedge map commuting over `a`,
i.e. exactly a slice morphism (the triangle over `K` is recovered by post-composing with
`a.map`). -/
instance : (sliceForward a).Full where
  map_surjective {X Y} h := by
    -- Ascribe `h.φ` to the clean type `□^∨(X.left.dims) ⟶ □^∨(Y.left.dims)` so that the
    -- `≫`-composites below carry syntactically-uniform object arguments (avoids the
    -- `(sliceForward a).obj Y).dims` vs `Y.left.dims` mismatch that blocks `rw`).
    let φ : (BPSet.serialWedge X.left.dims) ⟶ (BPSet.serialWedge Y.left.dims) := h.φ
    have hh : φ ≫ Y.hom.φ = X.hom.φ := h.w
    have w_f : φ ≫ Y.left.map = X.left.map := by
      rw [← X.hom.w, ← hh, Category.assoc, Y.hom.w]
    exact ⟨Over.homMk (⟨φ, w_f⟩ : X.left ⟶ Y.left) (ChainCat.hom_ext' hh),
      ChainCat.hom_ext' rfl⟩

/-- Every cube chain `⟨d, m⟩` of `□^∨(a.dims)` is `sliceForward a` of the push-forward
`Over.mk ⟨m, rfl⟩ : ⟨d, m ≫ a.map⟩ ⟶ a` (cf. `ChainCat.pushforward`). -/
instance : (sliceForward a).EssSurj :=
  Functor.essSurj_of_surj fun m =>
    ⟨Over.mk (⟨m.map, rfl⟩ : (⟨m.dims, m.map ≫ a.map⟩ : ChainCat.Obj K) ⟶ a), rfl⟩

instance : (sliceForward a).IsEquivalence where

/-- The slice of `Ch K` over a chain `a` is the cube-chain category of `□^∨(a.dims)`. -/
noncomputable def sliceEquiv : Over a ≌ ChainCat.Obj (BPSet.serialWedge a.dims) :=
  (sliceForward a).asEquivalence

@[simp] theorem sliceEquiv_functor : (sliceEquiv a).functor = sliceForward a := rfl

end ChainCat
