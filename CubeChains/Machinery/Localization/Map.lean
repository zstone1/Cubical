import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Machinery/Localization/Map — a functor between localizations

A functor carrying one class into another descends, and `Localization.Construction.fac` makes the
square an *equality*; so the two functor laws are `uniq`, and nothing is transported.
-/

universe v u v₂ u₂ v₃ u₃

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- **A functor carrying one class into another, localized.** -/
noncomputable def localizedMap (W₁ : MorphismProperty C) (W₂ : MorphismProperty D) (F : C ⥤ D)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₂ (F.map f)) :
    W₁.Localization ⥤ W₂.Localization :=
  Localization.Construction.lift (F ⋙ W₂.Q) fun _ _ f hf =>
    Localization.inverts W₂.Q W₂ _ (hF f hf)

theorem Q_comp_localizedMap (W₁ : MorphismProperty C) (W₂ : MorphismProperty D) (F : C ⥤ D)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₂ (F.map f)) :
    W₁.Q ⋙ localizedMap W₁ W₂ F hF = F ⋙ W₂.Q :=
  Localization.Construction.fac _ _

/-- **Two functors out of a localization agree as soon as they agree upstairs** — the uniqueness
every functor law below is. -/
theorem eq_of_Q_comp_eq {W₁ : MorphismProperty C} {W₂ : MorphismProperty D}
    {Φ Ψ : W₁.Localization ⥤ W₂.Localization} (h : W₁.Q ⋙ Φ = W₁.Q ⋙ Ψ) : Φ = Ψ :=
  Localization.Construction.uniq _ _ h

theorem localizedMap_id (W₁ : MorphismProperty C)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₁ ((𝟭 C).map f)) :
    localizedMap W₁ W₁ (𝟭 C) hF = 𝟭 _ :=
  eq_of_Q_comp_eq ((Q_comp_localizedMap W₁ W₁ (𝟭 C) hF).trans rfl)

theorem localizedMap_comp (W₁ : MorphismProperty C) (W₂ : MorphismProperty D)
    (W₃ : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E)
    (hF : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₂ (F.map f))
    (hG : ∀ {X Y : D} (g : X ⟶ Y), W₂ g → W₃ (G.map g))
    (hFG : ∀ {X Y : C} (f : X ⟶ Y), W₁ f → W₃ ((F ⋙ G).map f)) :
    localizedMap W₁ W₃ (F ⋙ G) hFG = localizedMap W₁ W₂ F hF ⋙ localizedMap W₂ W₃ G hG :=
  eq_of_Q_comp_eq ((Q_comp_localizedMap W₁ W₃ (F ⋙ G) hFG).trans
    ((congrArg (fun H => F ⋙ H) (Q_comp_localizedMap W₂ W₃ G hG)).symm.trans
      (congrArg (fun H => H ⋙ localizedMap W₂ W₃ G hG)
        (Q_comp_localizedMap W₁ W₂ F hF)).symm))

end MorphismProperty

end CategoryTheory
