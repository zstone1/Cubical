import Mathlib.CategoryTheory.Localization.Construction

/-!
# Machinery/Localization/HomInduction — induction over the morphisms of a localization

`Localization.Construction.morphismProperty_eq_top` is indexed by the *localization's* objects,
where a caller's predicate is indexed by `C`'s.  Nothing has to be transported to bridge that:
`objEquiv` is a retraction **on the nose** — `Q.obj (objEquiv.symm X) = X` by structure eta
(`Q_obj_objEquiv_symm`) — so a predicate on `Q`-images already *is* a predicate on the
localization.
-/

universe v u

namespace CategoryTheory.Localization.Construction

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- **`Q` is bijective on objects**, so every object of `C[W⁻¹]` is a `Q`-image. -/
theorem exists_Q_obj (X : W.Localization) : ∃ c : C, W.Q.obj c = X :=
  ⟨(objEquiv (W := W)).symm X, (objEquiv (W := W)).apply_symm_apply X⟩

/-- **…and it is one on the nose**: an object of `C[W⁻¹]` is a one-field record holding a one-field
record holding an object of `C`, so structure eta rebuilds it.  This is what keeps every statement
below transport-free — a hom-set of the localization *is* a hom-set between `Q`-images. -/
@[simp] theorem Q_obj_objEquiv_symm (X : W.Localization) :
    W.Q.obj ((objEquiv (W := W)).symm X) = X := rfl

/-- **Every morphism of `C[W⁻¹]` is a composite of images and formal inverses**, on a predicate
indexed by `C`'s own objects. -/
theorem hom_induction (P : ∀ c c' : C, (W.Q.obj c ⟶ W.Q.obj c') → Prop)
    (hcomp : ∀ (c c' c'' : C) (g : W.Q.obj c ⟶ W.Q.obj c') (g' : W.Q.obj c' ⟶ W.Q.obj c''),
      P c c' g → P c' c'' g' → P c c'' (g ≫ g'))
    (hQ : ∀ {a b : C} (f : a ⟶ b), P a b (W.Q.map f))
    (hInv : ∀ {a b : C} (w : a ⟶ b) (hw : W w), P b a (wInv w hw))
    {c c' : C} (g : W.Q.obj c ⟶ W.Q.obj c') : P c c' g := by
  let Pr : MorphismProperty W.Localization := fun X Y u =>
    P ((objEquiv (W := W)).symm X) ((objEquiv (W := W)).symm Y) u
  haveI : Pr.IsStableUnderComposition :=
    ⟨fun {X Y Z} u v hu hv => hcomp _ ((objEquiv (W := W)).symm Y) _ u v hu hv⟩
  have htop : Pr = ⊤ :=
    morphismProperty_eq_top Pr (fun _ _ f => hQ f) (fun _ _ w hw => hInv w hw)
  have hg : Pr g := by rw [htop]; trivial
  exact hg

end CategoryTheory.Localization.Construction
