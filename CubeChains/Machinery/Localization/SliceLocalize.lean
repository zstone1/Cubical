import CubeChains.Machinery.Slice
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Machinery/Localization/SliceLocalize — postcomposition on a slice, localized

`overMapLoc` is a `Construction.lift`, so `overMapLocFac`, `overMapLoc_id` and `overMapLoc_comp`
are **equalities**.  Everything downstream turns on that; see the warning on `overMapLoc`.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-! ## Pulling a localization back along an equivalence -/

/-- **A localization pulls back along an equivalence of sources.** -/
theorem Functor.IsLocalization.of_inverseImage (G : C ⥤ D) [G.IsEquivalence] (L : D ⥤ E)
    (V : MorphismProperty D) [V.RespectsIso] [L.IsLocalization V]
    (U : MorphismProperty C) (hU : U = V.inverseImage G) :
    (G ⋙ L).IsLocalization U := by
  subst hU
  refine Functor.IsLocalization.of_equivalence_source L V (G ⋙ L) (V.inverseImage G)
    G.asEquivalence.symm (fun X Y f hf => ?_)
    (fun _ _ f hf => Localization.inverts L V _ hf)
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _)
  refine MorphismProperty.le_isoClosure _ _ ?_
  change V (G.asEquivalence.functor.map (G.asEquivalence.inverse.map f))
  rw [Equivalence.fun_inv_map]
  exact MorphismProperty.RespectsIso.precomp _ (G.asEquivalence.counitIso.app X).hom _
    (MorphismProperty.RespectsIso.postcomp _ (G.asEquivalence.counitIso.app Y).inv _ hf)

/-! ## Postcomposition -/

/-- Postcomposition on a slice, localized.  Strict, like `Over.map` itself.

**Do not weaken this to `Localization.lift`.**  Being a `Construction.lift` is what makes
`overMapLocFac`, `overMapLoc_id` and `overMapLoc_comp` *equalities*, and that is load-bearing
twice: `OverCoconeLoc.w` is statable as an equality, so `overCoconeLocEquiv` is an `Equiv` of types
rather than an equivalence of categories; and `SliceLabels.map_ob` is an equality of objects, so
`GlueRel.overlap` typechecks at all. -/
noncomputable def overMapLoc (W : MorphismProperty C) {X Y : C} (u : X ⟶ Y) :
    (W.over (X := X)).Localization ⥤ (W.over (X := Y)).Localization :=
  Localization.Construction.lift (Over.map u ⋙ (W.over (X := Y)).Q)
    (fun _ _ f hf => Localization.inverts (W.over (X := Y)).Q (W.over (X := Y))
      ((Over.map u).map f) hf)

/-- `overMapLoc` lifts postcomposition. -/
theorem overMapLocFac (W : MorphismProperty C) {X Y : C} (u : X ⟶ Y) :
    (W.over (X := X)).Q ⋙ overMapLoc W u = Over.map u ⋙ (W.over (X := Y)).Q :=
  Localization.Construction.fac _ _

noncomputable instance liftingOverMapLoc (W : MorphismProperty C) {X Y : C} (u : X ⟶ Y) :
    Localization.Lifting (W.over (X := X)).Q (W.over (X := X))
      (Over.map u ⋙ (W.over (X := Y)).Q) (overMapLoc W u) :=
  ⟨eqToIso (overMapLocFac W u)⟩

@[simp] theorem overMapLoc_id (W : MorphismProperty C) (X : C) : overMapLoc W (𝟙 X) = 𝟭 _ :=
  Localization.Construction.uniq _ _ (by rw [overMapLocFac, Over.mapId_eq]; rfl)

theorem overMapLoc_comp (W : MorphismProperty C) {X Y Z : C} (u : X ⟶ Y) (v : Y ⟶ Z) :
    overMapLoc W (u ≫ v) = overMapLoc W u ⋙ overMapLoc W v :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, overMapLocFac, overMapLocFac, Functor.assoc, overMapLocFac,
      Over.mapComp_eq, Functor.assoc])

end CategoryTheory
