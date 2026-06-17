import CubeChains.Operations.GroupoidTarget

/-!
# Pointed endofunctors, and the categorical core of `cylinder ↦ pointed functor`

The **target** of the operations-from-cylinders functor (the user's piece 1) is the
category of *pointed endofunctors* of `ChP K`: an endofunctor `F` together with a
natural transformation `𝟭 ⟹ F` (the "point").  Such a pair is exactly a coherent
choice of homotopy `p ⇝ F p` for every chain — a `ChP K`-indexed family of zigzags.

This file builds:
* `PointedEndofunctor 𝒞` — the target category;
* `pointedOfTransf` — the cube-independent **core** of piece 1: from an equivalence
  `L`, a functor `R`, and a transformation `η : L ⟹ R`, produce the pointed
  endofunctor `(L⁻¹ ⋙ R, 𝟭 ⟹ L⁻¹⋙R)` via `transportTransf`.

The geometry — the category of cylinder maps `E ⊗ □¹ → K` and the comparison
`cylinder ↦ η` — is the foundational piece built on the path object `P K`, staged
separately (see the writeup); this file is the algebra it will land in.
-/

open CategoryTheory

namespace Operations

variable (𝒞 : Type*) [Category 𝒞]

/-- A **pointed endofunctor** of `𝒞`: an endofunctor with a transformation from the
identity.  (A monad without its multiplication.) -/
structure PointedEndofunctor where
  /-- The underlying endofunctor. -/
  F : 𝒞 ⥤ 𝒞
  /-- The point `𝟭 ⟹ F`. -/
  pt : 𝟭 𝒞 ⟶ F

variable {𝒞}

/-- A morphism of pointed endofunctors: a natural transformation commuting with the
points. -/
@[ext]
structure PointedEndofunctor.Hom (A B : PointedEndofunctor 𝒞) where
  /-- The underlying natural transformation. -/
  τ : A.F ⟶ B.F
  /-- Compatibility with the points. -/
  w : A.pt ≫ τ = B.pt

namespace PointedEndofunctor

instance : Category (PointedEndofunctor 𝒞) where
  Hom A B := PointedEndofunctor.Hom A B
  id A := ⟨𝟙 A.F, by simp⟩
  comp f g := ⟨f.τ ≫ g.τ, by rw [← Category.assoc, f.w, g.w]⟩
  id_comp f := PointedEndofunctor.Hom.ext (Category.id_comp f.τ)
  comp_id f := PointedEndofunctor.Hom.ext (Category.comp_id f.τ)
  assoc f g h := PointedEndofunctor.Hom.ext (Category.assoc f.τ g.τ h.τ)

@[simp] theorem id_τ (A : PointedEndofunctor 𝒞) : Hom.τ (𝟙 A) = 𝟙 A.F := rfl

@[simp] theorem comp_τ {A B C : PointedEndofunctor 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.τ (f ≫ g) = f.τ ≫ g.τ := rfl

end PointedEndofunctor

/-- **The core of `cylinder ↦ pointed functor`.**  From an equivalence `L`, a functor
`R`, and a transformation `η : L ⟶ R`, produce the pointed endofunctor
`(L⁻¹ ⋙ R, 𝟭 ⟹ L⁻¹⋙R)` — the transport `Φ` of `R` along `L`, pointed by
`transportTransf`.  When `L = ChP ℓ` and `R = ChP r` for a cylinder's two ends, and
`η` comes from the cylinder, this is the operation's action on `ChP K` as a coherent
family of d-path homotopies. -/
noncomputable def pointedOfTransf {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]
    (L R : 𝒜 ⥤ ℬ) [L.IsEquivalence] (η : L ⟶ R) : PointedEndofunctor ℬ where
  F := L.inv ⋙ R
  pt := transportTransf L R η

@[simp] theorem pointedOfTransf_F {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]
    (L R : 𝒜 ⥤ ℬ) [L.IsEquivalence] (η : L ⟶ R) :
    (pointedOfTransf L R η).F = L.inv ⋙ R := rfl

end Operations
