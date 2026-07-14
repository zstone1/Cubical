import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Foundations/FreeGroupoidLift — the free groupoid's universal property, with parameters

`FreeGroupoid.lift` is **strict**: `lift_spec` and `lift_unique` are equalities.  That strictness is
lost if a functor out of a *product* of free groupoids goes through
`freeGroupoidProdEquiv = Localization.uniq`, which is pinned only up to natural iso.

The fix is to lift one variable at a time, keeping the other as a parameter.  A functor category
into a groupoid is a groupoid, so `lift` applies there too, and currying is *strictly* invertible
(`curryingEquiv` is an `Equiv`).  Hence `lift₂`, whose universal property is again an equality.

    lift₂ F : FreeGroupoid C × FreeGroupoid D ⥤ G      (of C).prod (of D) ⋙ lift₂ F = F
-/

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₂} [Category.{v₂} E] {G : Type u₃} [Groupoid.{v₃} G]

/-- Natural transformations into a groupoid are invertible, so a functor category into a groupoid
is a groupoid.  This is what lets `lift` be applied *with parameters*. -/
noncomputable instance functorGroupoid : Groupoid (D ⥤ G) :=
  Groupoid.ofIsIso fun α => NatIso.isIso_of_isIso_app α

namespace FreeGroupoid

/-- Two functors out of a free groupoid agreeing on the generators are **equal**. -/
theorem lift_ext {Φ Ψ : FreeGroupoid C ⥤ G} (h : of C ⋙ Φ = of C ⋙ Ψ) : Φ = Ψ :=
  (lift_unique _ Φ h).trans (lift_unique _ Ψ rfl).symm

/-- A natural transformation out of a free groupoid is pinned by its generator components
(`eq_mk` is `rfl`, so every object *is* a generator). -/
theorem natTrans_ext {Φ Ψ : FreeGroupoid D ⥤ G} {α β : Φ ⟶ Ψ}
    (h : ∀ X : D, α.app (mk X) = β.app (mk X)) : α = β := by
  ext Y
  exact h Y.as.as

/-- `lift`, as a functor of its input. -/
noncomputable def liftFunctor : (D ⥤ G) ⥤ (FreeGroupoid D ⥤ G) where
  obj F := lift F
  map {F₁ F₂} α := (liftNatIso (lift F₁) (lift F₂)
    (eqToIso (lift_spec F₁) ≪≫ asIso α ≪≫ eqToIso (lift_spec F₂).symm)).hom
  map_id F := by
    refine natTrans_ext fun X => ?_
    simp
  map_comp α β := by
    refine natTrans_ext fun X => ?_
    simp

@[simp] theorem liftFunctor_obj (F : D ⥤ G) : (liftFunctor (D := D) (G := G)).obj F = lift F := rfl

@[simp] theorem liftFunctor_map_app {F₁ F₂ : D ⥤ G} (α : F₁ ⟶ F₂) (X : D) :
    ((liftFunctor (D := D) (G := G)).map α).app (mk X) = α.app X := by
  simp [liftFunctor]

/-! ## Lifting out of a product -/

/-- **The product universal property, strictly**: lift the second variable with the first as a
parameter, then the first.  No `Localization.uniq`, so no loss of strictness. -/
noncomputable def lift₂ (F : C × D ⥤ G) : FreeGroupoid C × FreeGroupoid D ⥤ G :=
  Functor.uncurry.obj (lift (Functor.curry.obj F ⋙ liftFunctor))

@[simp] theorem lift₂_obj (F : C × D ⥤ G) (X : C) (Y : D) :
    (lift₂ F).obj (mk X, mk Y) = F.obj (X, Y) := rfl

@[simp] theorem lift₂_map_homMk (F : C × D ⥤ G) {X₁ X₂ : C} {Y₁ Y₂ : D}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (lift₂ F).map ((homMk f, homMk g) : (mk X₁, mk Y₁) ⟶ (mk X₂, mk Y₂))
      = F.map ((f, g) : (X₁, Y₁) ⟶ (X₂, Y₂)) := by
  have hsplit : ((f, g) : ((X₁, Y₁) : C × D) ⟶ (X₂, Y₂))
      = (show ((X₁, Y₁) : C × D) ⟶ (X₂, Y₁) from (f, 𝟙 Y₁))
        ≫ (show ((X₂, Y₁) : C × D) ⟶ (X₂, Y₂) from (𝟙 X₂, g)) := by
    rw [prod_comp]
    simp
  rw [hsplit, F.map_comp]
  simp [lift₂, Functor.uncurry, liftFunctor]

/-- **The universal property, and it is an equality** — unlike `Localization.uniq`. -/
theorem lift₂_spec (F : C × D ⥤ G) : (of C).prod (of D) ⋙ lift₂ F = F := by
  refine Functor.ext (fun X => rfl) fun X₁ X₂ f => ?_
  obtain ⟨c₁, d₁⟩ := X₁
  obtain ⟨c₂, d₂⟩ := X₂
  obtain ⟨u, v⟩ := f
  simp

/-- **Two functors out of a product of free groupoids agreeing on the generators are equal.** -/
theorem lift₂_ext {Φ Ψ : FreeGroupoid C × FreeGroupoid D ⥤ G}
    (h : (of C).prod (of D) ⋙ Φ = (of C).prod (of D) ⋙ Ψ) : Φ = Ψ := by
  -- agree on the generators of one variable, with the other held fixed
  have hfix : ∀ (X : C), (Functor.curry.obj Φ).obj (mk X) = (Functor.curry.obj Ψ).obj (mk X) := by
    intro X
    refine lift_ext (C := D) (G := G)
      (Functor.ext (fun Y => Functor.congr_obj h (X, Y)) fun Y₁ Y₂ g => ?_)
    simpa using Functor.congr_hom h (show ((X, Y₁) : C × D) ⟶ (X, Y₂) from (𝟙 X, g))
  refine Functor.curryingEquiv.symm.injective (lift_ext (C := C) (G := FreeGroupoid D ⥤ G) ?_)
  refine Functor.ext hfix fun X₁ X₂ f => ?_
  refine natTrans_ext fun Y => ?_
  simpa [eqToHom_app] using
    Functor.congr_hom h (show ((X₁, Y) : C × D) ⟶ (X₂, Y) from (f, 𝟙 Y))

theorem lift₂_unique (F : C × D ⥤ G) (Φ : FreeGroupoid C × FreeGroupoid D ⥤ G)
    (hΦ : (of C).prod (of D) ⋙ Φ = F) : Φ = lift₂ F :=
  lift₂_ext (Φ := Φ) (Ψ := lift₂ F) (hΦ.trans (lift₂_spec F).symm)

/-- A natural transformation out of a product of free groupoids is pinned by its components at the
generators. -/
theorem natTrans₂_ext {Φ Ψ : FreeGroupoid C × FreeGroupoid D ⥤ G} {α β : Φ ⟶ Ψ}
    (h : ∀ (X : C) (Y : D), α.app (mk X, mk Y) = β.app (mk X, mk Y)) : α = β := by
  ext ⟨X, Y⟩
  exact h X.as.as Y.as.as

/-- **Ext for a triple product** — what the enrichment's associativity axiom needs. -/
theorem lift₃_ext {E' : Type u₂} [Category.{v₂} E']
    {Φ Ψ : FreeGroupoid C × (FreeGroupoid D × FreeGroupoid E') ⥤ G}
    (h : (of C).prod ((of D).prod (of E')) ⋙ Φ
      = (of C).prod ((of D).prod (of E')) ⋙ Ψ) : Φ = Ψ := by
  have hfix : ∀ (X : C), (Functor.curry.obj Φ).obj (mk X) = (Functor.curry.obj Ψ).obj (mk X) := by
    intro X
    refine lift₂_ext (C := D) (D := E') (G := G) (Functor.ext (fun Y => ?_) fun Y₁ Y₂ g => ?_)
    · exact Functor.congr_obj h (X, Y)
    · simpa using Functor.congr_hom h
        (show ((X, Y₁) : C × (D × E')) ⟶ (X, Y₂) from (𝟙 X, g))
  refine Functor.curryingEquiv.symm.injective
    (lift_ext (C := C) (G := FreeGroupoid D × FreeGroupoid E' ⥤ G) ?_)
  refine Functor.ext hfix fun X₁ X₂ f => ?_
  refine natTrans₂_ext fun Y Z => ?_
  simpa [eqToHom_app] using
    Functor.congr_hom h (show ((X₁, Y, Z) : C × (D × E')) ⟶ (X₂, Y, Z) from (f, 𝟙 Y, 𝟙 Z))

end FreeGroupoid

end CategoryTheory
