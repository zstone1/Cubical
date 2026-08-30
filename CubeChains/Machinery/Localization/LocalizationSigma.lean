import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Localization of a coproduct of categories

`Σ i, C i` is the coproduct in `Cat`: a functor out of it *is* a family of functors, on the
nose.  So the universal property of the localization is available in its **strict** form here
and `Functor.IsLocalization.mk'` applies directly — no `ContainsIdentities` hypothesis, unlike
the product case.

Also the dual decomposition: a category whose morphisms all preserve a grading `p : C → I`
is the coproduct of its fibres, so its localization splits as a coproduct.
-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Functor

namespace Sigma

variable {I : Type w} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

section

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]

/-- Restricting `desc` along an inclusion is an equality, not merely `Sigma.inclDesc`. -/
@[simp]
lemma incl_comp_desc (F : ∀ i, C i ⥤ D) (i : I) : incl i ⋙ desc F = F i := rfl

@[simp]
lemma desc_comp (F : ∀ i, C i ⥤ D) (G : D ⥤ E) : desc F ⋙ G = desc fun i => F i ⋙ G :=
  Functor.ext (fun _ => rfl) (by rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩; simp)

/-- The `Eq` form of `Sigma.natIso`, which is what a strict universal property needs. -/
lemma functor_ext {q₁ q₂ : (Σ i, C i) ⥤ D} (h : ∀ i, incl i ⋙ q₁ = incl i ⋙ q₂) : q₁ = q₂ :=
  Functor.ext (fun X => Functor.congr_obj (h X.1) X.2)
    (by rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩; exact Functor.congr_hom (h i) f)

end

namespace Functor

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] (F : ∀ i, C i ⥤ D i)

/-- `Sigma.Functor.sigma` with the two families in different universes — `(W i).Localization`
has bigger homs than `C i`, so the mathlib version does not apply to it. -/
def sigma' : (Σ i, C i) ⥤ Σ i, D i := desc fun i => F i ⋙ incl i

@[simp]
lemma incl_comp_sigma' (i : I) : incl i ⋙ sigma' F = F i ⋙ incl i := rfl

@[simp]
lemma sigma'_map_mk {i : I} {X Y : C i} (f : X ⟶ Y) :
    (sigma' F).map (SigmaHom.mk f) = SigmaHom.mk ((F i).map f) := rfl

instance faithful_sigma' [∀ i, (F i).Faithful] : (sigma' F).Faithful where
  map_injective := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩ ⟨g⟩ h
    obtain rfl := (F i).map_injective ((incl i).map_injective h)
    rfl

instance full_sigma' [∀ i, (F i).Full] : (sigma' F).Full where
  map_surjective := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨h⟩
    exact ⟨SigmaHom.mk ((F i).preimage h), by simp⟩

instance essSurj_sigma' [∀ i, (F i).EssSurj] : (sigma' F).EssSurj where
  mem_essImage := by
    rintro ⟨i, Y⟩
    exact ⟨⟨i, (F i).objPreimage Y⟩, ⟨(incl i).mapIso ((F i).objObjPreimageIso Y)⟩⟩

instance isEquivalence_sigma' [∀ i, (F i).IsEquivalence] : (sigma' F).IsEquivalence where

end Functor

section Grading

variable {C : Type u₁} [Category.{v₁} C] {I : Type w} (p : C → I)

/-- The `i`-th fibre of a grading `p : C → I` on the objects. -/
abbrev fibre (i : I) : ObjectProperty C := fun X => p X = i

/-- Reassembling the fibres of a grading; the coprojections are the inclusions. -/
abbrev descFibre : (Σ i, (fibre p i).FullSubcategory) ⥤ C := desc fun i => (fibre p i).ι

instance faithful_descFibre : (descFibre p).Faithful where
  map_injective := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩ ⟨g⟩ h
    have hfg : f = g := (fibre p i).ι.map_injective h
    rw [hfg]

instance essSurj_descFibre : (descFibre p).EssSurj where
  mem_essImage Y := ⟨⟨p Y, ⟨Y, rfl⟩⟩, ⟨Iso.refl Y⟩⟩

variable (hp : ∀ {X Y : C} (_ : X ⟶ Y), p X = p Y)
include hp

/-- Fullness is exactly the hypothesis that morphisms preserve the grading. -/
lemma full_descFibre : (descFibre p).Full where
  map_surjective := by
    rintro ⟨i, X⟩ ⟨j, Y⟩ h
    obtain rfl : i = j := by rw [← X.property, ← Y.property]; exact hp h
    exact ⟨SigmaHom.mk (ObjectProperty.homMk h), rfl⟩

/-- A category whose morphisms preserve a grading is the coproduct of the fibres. -/
noncomputable def gradedEquivalence : (Σ i, (fibre p i).FullSubcategory) ≌ C :=
  haveI := full_descFibre p hp
  haveI : (descFibre p).IsEquivalence := {}
  (descFibre p).asEquivalence

@[simp]
lemma gradedEquivalence_functor : (gradedEquivalence p hp).functor = descFibre p := rfl

end Grading

end Sigma

namespace MorphismProperty

variable {I : Type w} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

/-- The morphisms of `Σ i, C i` lying in one of the `W i` (there are no cross-index ones). -/
def sigma (W : ∀ i, MorphismProperty (C i)) : MorphismProperty (Σ i, C i) :=
  fun _ _ f => match f with | Sigma.SigmaHom.mk g => W _ g

variable (W : ∀ i, MorphismProperty (C i))

@[simp]
lemma sigma_mk_iff {i : I} {X Y : C i} (f : X ⟶ Y) :
    sigma W (Sigma.SigmaHom.mk f) ↔ W i f := Iff.rfl

instance sigma_containsIdentities [∀ i, (W i).ContainsIdentities] :
    (sigma W).ContainsIdentities where
  id_mem := by rintro ⟨i, X⟩; exact (W i).id_mem X

instance sigma_isStableUnderComposition [∀ i, (W i).IsStableUnderComposition] :
    (sigma W).IsStableUnderComposition where
  comp_mem := by rintro _ _ _ ⟨f⟩ ⟨g⟩ hf hg; exact (W _).comp_mem f g hf hg

instance sigma_isMultiplicative [∀ i, (W i).IsMultiplicative] : (sigma W).IsMultiplicative where

lemma sigma_inverseImage {D : Type u₂} [Category.{v₂} D] (P : MorphismProperty D)
    (F : ∀ i, C i ⥤ D) : sigma (fun i => P.inverseImage (F i)) = P.inverseImage (Sigma.desc F) := by
  ext ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩
  rfl

end MorphismProperty

namespace Localization

variable {I : Type w} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  (W : ∀ i, MorphismProperty (C i))

namespace StrictUniversalPropertyFixedTarget

variable {E : Type u₃} [Category.{v₃} E]

lemma sigma_inverts :
    (MorphismProperty.sigma W).IsInvertedBy (Sigma.Functor.sigma' fun i => (W i).Q) := by
  rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨f⟩ hf
  have : IsIso ((W i).Q.map f) := (W i).Q_inverts f hf
  change IsIso ((Sigma.incl (C := fun i => (W i).Localization) i).map ((W i).Q.map f))
  infer_instance

/-- Lift a functor out of `Σ i, C i` inverting `MorphismProperty.sigma W` componentwise. -/
noncomputable def sigmaLift (F : (Σ i, C i) ⥤ E)
    (hF : (MorphismProperty.sigma W).IsInvertedBy F) :
    (Σ i, (W i).Localization) ⥤ E :=
  Sigma.desc fun i =>
    Construction.lift (Sigma.incl i ⋙ F) fun _ _ f hf => hF (Sigma.SigmaHom.mk f) hf

variable (F : (Σ i, C i) ⥤ E) (hF : (MorphismProperty.sigma W).IsInvertedBy F)

lemma sigma_fac : (Sigma.Functor.sigma' fun i => (W i).Q) ⋙ sigmaLift W F hF = F :=
  Sigma.functor_ext fun i =>
    Construction.fac (Sigma.incl i ⋙ F) fun _ _ f hf => hF (Sigma.SigmaHom.mk f) hf

lemma sigma_uniq (F₁ F₂ : (Σ i, (W i).Localization) ⥤ E)
    (h : (Sigma.Functor.sigma' fun i => (W i).Q) ⋙ F₁ =
      (Sigma.Functor.sigma' fun i => (W i).Q) ⋙ F₂) : F₁ = F₂ := by
  refine Sigma.functor_ext fun i => Construction.uniq _ _ ?_
  exact congrArg (Sigma.incl i ⋙ ·) h

variable (E)

/-- Being a coproduct in `Cat`, `Σ i, C i` inherits the strict universal property. -/
noncomputable def sigma :
    StrictUniversalPropertyFixedTarget (Sigma.Functor.sigma' fun i => (W i).Q)
      (MorphismProperty.sigma W) E where
  inverts := sigma_inverts W
  lift := sigmaLift W
  fac := sigma_fac W
  uniq := sigma_uniq W

end StrictUniversalPropertyFixedTarget

lemma Construction.sigmaIsLocalization :
    (Sigma.Functor.sigma' fun i => (W i).Q).IsLocalization (MorphismProperty.sigma W) :=
  Functor.IsLocalization.mk' _ _
    (StrictUniversalPropertyFixedTarget.sigma W _)
    (StrictUniversalPropertyFixedTarget.sigma W _)

end Localization

namespace Functor.IsLocalization

variable {I : Type w} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  (W : ∀ i, MorphismProperty (C i))

section

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] (L : ∀ i, C i ⥤ D i)
  [∀ i, (L i).IsLocalization (W i)]

/-- The coproduct of localization functors localizes the coproduct. -/
instance sigma' : (Sigma.Functor.sigma' L).IsLocalization (MorphismProperty.sigma W) := by
  have := Localization.Construction.sigmaIsLocalization W
  refine of_equivalence_target (Sigma.Functor.sigma' fun i => (W i).Q) (MorphismProperty.sigma W)
    (Sigma.Functor.sigma' L)
    (Sigma.Functor.sigma' fun i => (Localization.uniq (W i).Q (L i) (W i)).functor).asEquivalence
    (Sigma.natIso fun i => ?_)
  exact Functor.isoWhiskerRight (Localization.compUniqFunctor (W i).Q (L i) (W i)) (Sigma.incl i)

end

section

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)] (L : ∀ i, C i ⥤ D i)
  [∀ i, (L i).IsLocalization (W i)]

/-- `IsLocalization.sigma'` in the spelling of mathlib's universe-restricted `Functor.sigma`. -/
instance sigma : (Sigma.Functor.sigma L).IsLocalization (MorphismProperty.sigma W) :=
  IsLocalization.sigma' W L

end

section Graded

variable {C : Type u₁} [Category.{v₁} C] {I : Type w} (p : C → I)
  (hp : ∀ {X Y : C} (_ : X ⟶ Y), p X = p Y) (W : MorphismProperty C) [W.RespectsIso]
  {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
  (L : ∀ i, (Sigma.fibre p i).FullSubcategory ⥤ D i)
  [∀ i, (L i).IsLocalization (W.inverseImage (Sigma.fibre p i).ι)]

/-- Localizing a graded category fibre by fibre; `RespectsIso` is needed to move `W` across
the counit of `gradedEquivalence`. -/
lemma graded :
    ((Sigma.gradedEquivalence p hp).inverse ⋙ Sigma.Functor.sigma' L).IsLocalization W := by
  have hW : W.IsInvertedBy ((Sigma.gradedEquivalence p hp).inverse ⋙ Sigma.Functor.sigma' L) := by
    intro X Y f hf
    refine Localization.inverts (Sigma.Functor.sigma' L)
      (MorphismProperty.sigma fun i => W.inverseImage (Sigma.fibre p i).ι) _ ?_
    rw [MorphismProperty.sigma_inverseImage]
    change W ((Sigma.gradedEquivalence p hp).functor.map
      ((Sigma.gradedEquivalence p hp).inverse.map f))
    rw [Equivalence.fun_inv_map]
    exact MorphismProperty.RespectsIso.precomp W
      ((Sigma.gradedEquivalence p hp).counitIso.app X).hom _
      (MorphismProperty.RespectsIso.postcomp W
        ((Sigma.gradedEquivalence p hp).counitIso.app Y).inv f hf)
  refine of_equivalence_source (Sigma.Functor.sigma' L)
    (MorphismProperty.sigma fun i => W.inverseImage (Sigma.fibre p i).ι) _ W
    (Sigma.gradedEquivalence p hp) ?_ hW
    (Equivalence.funInvIdAssoc (Sigma.gradedEquivalence p hp) (Sigma.Functor.sigma' L))
  rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨g⟩ hg
  exact W.le_isoClosure _ hg

end Graded

end Functor.IsLocalization

end CategoryTheory
