import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Cylinder/PointedFunctor

The categorical **target** of the cylinder ⟹ pointed-functor program: the category of
*pointed endofunctors* of a groupoid — an endofunctor `F` with a natural transformation
`𝟭 ⟹ F` (the "point").  For the d-path groupoid `DPathGrpdR K` such a pair is exactly a
coherent choice of homotopy `p ⇝ F p` for every chain (a family of zigzags).

This file builds:
* `PointedEndofunctor 𝒞` — the target category;
* `pointedOfPaths` — the cube-independent **core**: from an object-map and one chosen
  path per object, produce a pointed endofunctor of a free groupoid (no naturality
  chase, by the conjugation trick);
* `pointedFunctorOfObj`/`pointedHomOfGroupoid` — the groupoid conjugation API that
  forces the morphism map of `cylToPointedR`.

The geometry that lands in this algebra is built in `Cylinder/CylinderRefineCore`,
`CylinderSweep` and `CylinderRefine` (the deliverable `cylToPointedR`).

**Layer:** Cylinder.  **Imports:** mathlib `FreeGroupoid`.
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

/-! ### Pointed endofunctors of a groupoid: the point-determined morphisms

When the base `𝒢` is a **groupoid**, the point `A.pt : 𝟭 ⟹ A.F` of every pointed
endofunctor is a natural *isomorphism* (each component lands in `𝒢`, hence is invertible).
The morphism axiom `w : A.pt ≫ τ = B.pt` therefore *determines* `τ` uniquely:
`τ = (A.pt)⁻¹ ≫ B.pt`.  So between pointed endofunctors of a groupoid there is exactly
one morphism, namely this `pointedHomOfGroupoid`.  Any family of pointed endofunctors
indexed by a category assembles, via this forced morphism, into a functor — this is the
algebraic skeleton of the cylinder ⟹ pointed-functor *functor* (its morphism map is the
forced comparison, with `w`/functoriality free). -/

section Groupoid

variable {𝒢 : Type*} [Groupoid 𝒢]

/-- In a groupoid base every pointed endofunctor's point is a natural isomorphism: each
component lands in `𝒢`, hence is invertible (`IsIso.of_groupoid`), so the whole
transformation is `IsIso` (`NatIso.isIso_of_isIso_app`). -/
instance pt_isIso (A : PointedEndofunctor 𝒢) : IsIso A.pt :=
  NatIso.isIso_of_isIso_app A.pt

/-- **The point-determined morphism of pointed endofunctors of a groupoid.**  The unique
`τ` satisfying `A.pt ≫ τ = B.pt`, namely `(A.pt)⁻¹ ≫ B.pt`.  In a groupoid base this is the
*only* morphism `A ⟶ B` (the point axiom forces it), so it is what any indexing functor must
send morphisms to. -/
noncomputable def pointedHomOfGroupoid (A B : PointedEndofunctor 𝒢) : A ⟶ B where
  τ := inv A.pt ≫ B.pt
  w := by rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

@[simp] theorem pointedHomOfGroupoid_τ (A B : PointedEndofunctor 𝒢) :
    (pointedHomOfGroupoid A B).τ = inv A.pt ≫ B.pt := rfl

@[simp] theorem pointedHomOfGroupoid_id (A : PointedEndofunctor 𝒢) :
    pointedHomOfGroupoid A A = 𝟙 A :=
  PointedEndofunctor.Hom.ext (by simp)

@[simp] theorem pointedHomOfGroupoid_comp (A B C : PointedEndofunctor 𝒢) :
    pointedHomOfGroupoid A B ≫ pointedHomOfGroupoid B C = pointedHomOfGroupoid A C :=
  PointedEndofunctor.Hom.ext (by
    simp only [PointedEndofunctor.comp_τ, pointedHomOfGroupoid_τ]
    rw [Category.assoc, ← Category.assoc B.pt, IsIso.hom_inv_id, Category.id_comp])

/-- **A functor into pointed endofunctors of a groupoid, from an object family alone.**
Any object-assignment `obj : J → PointedEndofunctor 𝒢` extends to a functor by sending each
morphism to the forced point-determined comparison `pointedHomOfGroupoid (obj a) (obj b)`.
Functoriality is automatic (`pointedHomOfGroupoid_id`/`pointedHomOfGroupoid_comp`).  This is
the assembly used to turn the per-cylinder pointed endofunctor into a *functor* of cylinders. -/
@[simps]
noncomputable def pointedFunctorOfObj {J : Type*} [Category J]
    (obj : J → PointedEndofunctor 𝒢) : J ⥤ PointedEndofunctor 𝒢 where
  obj := obj
  map {a b} _ := pointedHomOfGroupoid (obj a) (obj b)
  map_id a := pointedHomOfGroupoid_id (obj a)
  map_comp {a b c} _ _ := (pointedHomOfGroupoid_comp (obj a) (obj b) (obj c)).symm

end Groupoid

/-! ## Pointed endofunctors from object-data only (the conjugation trick)

In a **groupoid** target a natural transformation is *free data*: an object-map together
with one chosen path per object assembles into a functor and a natural transformation,
with functoriality and naturality both automatic (by conjugation).  So producing a pointed
endofunctor of a free groupoid needs **no** naturality chase — only, for each object, where
it goes and a single path to there. -/

section Conjugation

variable {C : Type*} [Category C] {G : Type*} [Groupoid G]

/-- **The conjugation functor.**  From `j : C ⥤ G` into a groupoid, an object-map `F₀`, and
a chosen path `η x : j x ⟶ F₀ x` per object, the functor `C ⥤ G` with `obj = F₀` and
`map f = (η x)⁻¹ ≫ j f ≫ η y`.  Functoriality is automatic. -/
def conjFunctor (j : C ⥤ G) (F₀ : C → G) (η : ∀ x, j.obj x ⟶ F₀ x) : C ⥤ G where
  obj := F₀
  map {x y} f := Groupoid.inv (η x) ≫ j.map f ≫ η y
  map_id x := by simp
  map_comp {x y z} f g := by simp [Functor.map_comp]

/-- The **conjugation natural isomorphism** `j ≅ conjFunctor j F₀ η`, with components the
chosen paths `η x` (invertible since `G` is a groupoid).  Naturality is automatic. -/
def conjNatIso (j : C ⥤ G) (F₀ : C → G) (η : ∀ x, j.obj x ⟶ F₀ x) :
    j ≅ conjFunctor j F₀ η :=
  NatIso.ofComponents
    (fun x => ⟨η x, Groupoid.inv (η x), Groupoid.comp_inv _, Groupoid.inv_comp _⟩)
    (fun {x y} f => by
      change j.map f ≫ η y = η x ≫ Groupoid.inv (η x) ≫ j.map f ≫ η y
      rw [← Category.assoc (η x), Groupoid.comp_inv, Category.id_comp])

end Conjugation

/-- **A pointed endofunctor from object-data only.**  Choosing, for each object `x` of `C`,
a target `F₀ x` and a path `η x : of x ⟶ F₀ x` in `FreeGroupoid C` determines a pointed
endofunctor of `FreeGroupoid C` — and (since every such transformation is a conjugation)
*every* pointed endofunctor arises this way.  No naturality is ever checked: the functor is
the lift of the conjugation `conjFunctor (of C) F₀ η`, and the point is the `liftNatIso` of
the (automatically natural) family `η`. -/
noncomputable def pointedOfPaths {C : Type*} [Category C] (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) : PointedEndofunctor (FreeGroupoid C) where
  F := FreeGroupoid.lift (conjFunctor (FreeGroupoid.of C) F₀ η)
  pt := (FreeGroupoid.liftNatIso (𝟭 (FreeGroupoid C))
      (FreeGroupoid.lift (conjFunctor (FreeGroupoid.of C) F₀ η))
      (eqToIso (Functor.comp_id _) ≪≫ conjNatIso (FreeGroupoid.of C) F₀ η
        ≪≫ eqToIso (FreeGroupoid.lift_spec _).symm)).hom

end Operations
