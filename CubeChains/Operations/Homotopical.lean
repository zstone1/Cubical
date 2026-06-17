import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Homotopical maps relative to a "homotopy functor" `Φ : C ⥤ Cat`

This is the **generic, reusable core** of the *operations-on-programs* thread.  The
intended instance is `C = PrecubicalSet`, `Φ = ChP` (the precubical cube-chain
functor, see `Operations/Precubical.lean`), but nothing here mentions precubical
sets — the layer is parametric in an arbitrary functor `Φ : C ⥤ Cat`.

Given `Φ`, a morphism `f : X ⟶ Y` of `C` is **`Φ`-homotopical** (a *weak
equivalence* for `Φ`) when `Φ` sends it to an *equivalence of categories*
`Φ X ≌ Φ Y`.  This is the formal content of design condition **(1)**: an operation
must induce a canonical equivalence `Ch K ≌ Ch FK`, *induced by the operation* (not
an ad-hoc identification), so that a chain `p` and its image `Fp` live in the same
category up to equivalence.

The class `Homotopical Φ` is packaged as a `MorphismProperty C`, which buys the
algebra that constrains the search for operations:

* `ContainsIdentities`     — relabelings/`𝟙` are operations;
* `IsMultiplicative`       — operations compose;
* `HasTwoOutOfThreeProperty` — if two of `f`, `g`, `f ≫ g` are operations, so is the
  third (this is what makes the class a genuine *weak-equivalence* class, and lets
  you build complex operations from elementary ones and reason compositionally).

The "homotopy classes of d-paths" layer is `π₀ ∘ Φ`; since equivalences are
bijective on connected components, a homotopical map induces a bijection of
homotopy classes.  We expose the stronger statement directly: the **equivalence of
categories** `Φ X ≌ Φ Y` (`Homotopical.equivalence`), from which the `π₀` bijection
is immediate.

Spans (the carrier for DPO-style rewrites) are built on top of this in
`Operations/Span.lean`.
-/

open CategoryTheory

namespace Operations

variable {C : Type*} [Category C] (Φ : C ⥤ Cat.{v, u})

/-- A morphism `f : X ⟶ Y` of `C` is **`Φ`-homotopical** (a *weak equivalence* for the
homotopy functor `Φ`) when `Φ` sends it to an equivalence of categories.  Packaged as
a `MorphismProperty C` so the weak-equivalence algebra below is available. -/
def Homotopical : MorphismProperty C :=
  fun _ _ f => (Φ.map f).toFunctor.IsEquivalence

theorem homotopical_iff {X Y : C} (f : X ⟶ Y) :
    Homotopical Φ f ↔ (Φ.map f).toFunctor.IsEquivalence := Iff.rfl

/-- `𝟙` is homotopical: `Φ` sends it to the identity functor, an equivalence. -/
instance : (Homotopical Φ).ContainsIdentities where
  id_mem X := by
    change (Φ.map (𝟙 X)).toFunctor.IsEquivalence
    rw [Φ.map_id, Cat.Hom.id_toFunctor]
    infer_instance

/-- Homotopical maps are closed under composition: `Φ` is a functor and a composite
of equivalences is an equivalence. -/
instance : (Homotopical Φ).IsStableUnderComposition where
  comp_mem f g hf hg := by
    haveI : (Φ.map f).toFunctor.IsEquivalence := hf
    haveI : (Φ.map g).toFunctor.IsEquivalence := hg
    change (Φ.map (f ≫ g)).toFunctor.IsEquivalence
    rw [Φ.map_comp, Cat.Hom.comp_toFunctor]
    infer_instance

instance : (Homotopical Φ).IsMultiplicative where

/-- If `g` and `f ≫ g` are homotopical, so is `f` (two-out-of-three, postcomp side). -/
instance : (Homotopical Φ).HasOfPostcompProperty (Homotopical Φ) where
  of_postcomp f g hg hfg := by
    change (Φ.map f).toFunctor.IsEquivalence
    haveI : (Φ.map g).toFunctor.IsEquivalence := hg
    haveI : ((Φ.map f).toFunctor ⋙ (Φ.map g).toFunctor).IsEquivalence := by
      have h : (Φ.map (f ≫ g)).toFunctor.IsEquivalence := hfg
      rwa [Φ.map_comp, Cat.Hom.comp_toFunctor] at h
    exact Functor.isEquivalence_of_comp_right (Φ.map f).toFunctor (Φ.map g).toFunctor

/-- If `f` and `f ≫ g` are homotopical, so is `g` (two-out-of-three, precomp side). -/
instance : (Homotopical Φ).HasOfPrecompProperty (Homotopical Φ) where
  of_precomp f g hf hfg := by
    change (Φ.map g).toFunctor.IsEquivalence
    haveI : (Φ.map f).toFunctor.IsEquivalence := hf
    haveI : ((Φ.map f).toFunctor ⋙ (Φ.map g).toFunctor).IsEquivalence := by
      have h : (Φ.map (f ≫ g)).toFunctor.IsEquivalence := hfg
      rwa [Φ.map_comp, Cat.Hom.comp_toFunctor] at h
    exact Functor.isEquivalence_of_comp_left (Φ.map f).toFunctor (Φ.map g).toFunctor

/-- **The weak-equivalence two-out-of-three property.**  Among `f`, `g`, `f ≫ g`, any
two being homotopical forces the third — the structural backbone of the class of
operations. -/
instance : (Homotopical Φ).HasTwoOutOfThreeProperty where

/-- **Isomorphisms are operations.**  `Φ` sends an iso to an iso of categories, which
is an equivalence — so relabelings/ambient isotopies are always homotopical. -/
theorem homotopical_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : Homotopical Φ f := by
  change (Φ.map f).toFunctor.IsEquivalence
  haveI : IsIso (Φ.map f) := inferInstance
  exact (Cat.equivOfIso (asIso (Φ.map f))).isEquivalence_functor

variable {Φ}

/-- **Condition (1), realized.**  A `Φ`-homotopical map induces an *equivalence of
categories* `Φ X ≌ Φ Y` (e.g. `Ch K ≌ Ch FK`), so a chain and its image live in the
same category up to equivalence.  The `π₀` bijection of homotopy classes follows by
`Functor.mapConnectedComponents` of this equivalence. -/
noncomputable def Homotopical.equivalence {X Y : C} {f : X ⟶ Y} (hf : Homotopical Φ f) :
    Φ.obj X ≌ Φ.obj Y :=
  haveI : (Φ.map f).toFunctor.IsEquivalence := hf
  (Φ.map f).toFunctor.asEquivalence

@[simp] theorem Homotopical.equivalence_functor {X Y : C} {f : X ⟶ Y} (hf : Homotopical Φ f) :
    hf.equivalence.functor = (Φ.map f).toFunctor := rfl

end Operations
