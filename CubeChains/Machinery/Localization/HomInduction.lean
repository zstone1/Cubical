import Mathlib.CategoryTheory.Localization.Construction

/-!
# Machinery/Localization/HomInduction — induction over the morphisms of a localization

`Localization.Construction.morphismProperty_eq_top` is indexed by the *localization's* objects, so
every use of it repeats the same bookkeeping: carry `eqToHom`s for the endpoints, then cancel them
against `objEquiv`.  `hom_induction` pays that once and hands the caller a predicate on
`W.Q.obj c ⟶ W.Q.obj c'` with no transport in sight.
-/

universe v u

namespace CategoryTheory.Localization.Construction

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- **`Q` is bijective on objects**, so every object of `C[W⁻¹]` is a `Q`-image. -/
theorem exists_Q_obj (X : W.Localization) : ∃ c : C, W.Q.obj c = X :=
  ⟨(objEquiv (W := W)).symm X, (objEquiv (W := W)).apply_symm_apply X⟩

/-- **Every morphism of `C[W⁻¹]` between images of objects is a composite of images and formal
inverses.**  Stated as an induction principle on a predicate indexed by the *source*'s objects. -/
theorem hom_induction (P : ∀ c c' : C, (W.Q.obj c ⟶ W.Q.obj c') → Prop)
    (hcomp : ∀ (c c' c'' : C) (g : W.Q.obj c ⟶ W.Q.obj c') (g' : W.Q.obj c' ⟶ W.Q.obj c''),
      P c c' g → P c' c'' g' → P c c'' (g ≫ g'))
    (hQ : ∀ {a b : C} (f : a ⟶ b), P a b (W.Q.map f))
    (hInv : ∀ {a b : C} (w : a ⟶ b) (hw : W w), P b a (wInv w hw))
    {c c' : C} (g : W.Q.obj c ⟶ W.Q.obj c') : P c c' g := by
  let Pr : MorphismProperty W.Localization := fun X Y u =>
    ∀ (a b : C) (hX : W.Q.obj a = X) (hY : W.Q.obj b = Y),
      P a b (eqToHom hX ≫ u ≫ eqToHom hY.symm)
  haveI : Pr.IsStableUnderComposition := by
    refine ⟨fun {X Y Z} u v hu hv a b hX hZ => ?_⟩
    obtain ⟨m, hm⟩ := exists_Q_obj W Y
    rw [show eqToHom hX ≫ (u ≫ v) ≫ eqToHom hZ.symm
        = (eqToHom hX ≫ u ≫ eqToHom hm.symm) ≫ (eqToHom hm ≫ v ≫ eqToHom hZ.symm) from by simp]
    exact hcomp a m b _ _ (hu a m hX hm) (hv m b hm hZ)
  have htop : Pr = ⊤ := by
    refine morphismProperty_eq_top Pr (fun a b f x y hX hY => ?_) (fun a b w hw x y hX hY => ?_)
    · obtain rfl := (objEquiv (W := W)).injective hX
      obtain rfl := (objEquiv (W := W)).injective hY
      simpa using hQ f
    · obtain rfl := (objEquiv (W := W)).injective hX
      obtain rfl := (objEquiv (W := W)).injective hY
      simpa using hInv w hw
  have hg : Pr g := by rw [htop]; trivial
  simpa using hg c c' rfl rfl

end CategoryTheory.Localization.Construction
