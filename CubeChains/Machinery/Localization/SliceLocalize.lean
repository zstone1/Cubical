import CubeChains.Machinery.Slice
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Machinery/Localization/SliceLocalize — the slices of a discrete fibration, localized

A discrete fibration identifies `Over c` with `Over (F.obj c)`, and `over_inverseImage` says the
two carry the same class of morphisms, so localizing them gives the same category
(`sliceLocEquiv`).  `Over.post F` intertwines the two postcompositions (`Over.mapPost`), which is
what makes that identification natural in `c` (`sliceLocEquivNatIso`).

`W.RespectsIso` is a genuine hypothesis: transporting a `W`-arrow backwards along the slice
equivalence conjugates it by the counit.
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

instance respectsIso_over (W : MorphismProperty C) [W.RespectsIso] {X : C} :
    (W.over (X := X)).RespectsIso :=
  inferInstanceAs (W.inverseImage (Over.forget X)).RespectsIso

/-! ## Postcomposition -/

/-- `F` of a triangle over `u` is a triangle over `F.map u`. -/
@[simps!]
def Over.mapPost (F : C ⥤ D) {c' c : C} (u : c' ⟶ c) :
    Over.map u ⋙ Over.post F ≅ Over.post F ⋙ Over.map (F.map u) :=
  NatIso.ofComponents fun _ => Over.isoMk (Iso.refl _)

/-- Postcomposition on a slice, localized.  Strict, like `Over.map` itself.

**Do not weaken this to `Localization.lift`.**  Being a `Construction.lift` is what makes
`overMapLocFac`, `overMapLoc_id` and `overMapLoc_comp` *equalities*, and that is load-bearing five
times over: `OverCoconeLoc.w` is statable as an equality, so `overCoconeLocEquiv` is an `Equiv` of
types rather than an equivalence of categories; `SliceLabels.map_ob` is an equality of objects, so
`GlueRel.overlap` typechecks at all; `OverPseudoCoconeLoc`'s coherences are plain `eqToIso`s rather
than isos of isos; and `descLoc_fac` is strict, so a descended functor can be computed after `Q`. -/
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

/-! ## The localized slices agree -/

variable (F : C ⥤ D) [F.IsDiscreteFibration] (W : MorphismProperty D) [W.RespectsIso]

/-- Any localization of the slice below is one of the slice above. -/
theorem isLocalization_post_comp (c : C) (L : Over (F.obj c) ⥤ E) [L.IsLocalization W.over] :
    (Over.post (X := c) F ⋙ L).IsLocalization ((W.inverseImage F).over) :=
  Functor.IsLocalization.of_inverseImage _ L _ _ (MorphismProperty.over_inverseImage W F c)

instance isLocalization_post_comp_Q (c : C) :
    (Over.post (X := c) F ⋙ (W.over (X := F.obj c)).Q).IsLocalization
      ((W.inverseImage F).over) :=
  isLocalization_post_comp F W c _

/-- **The localized slices of a discrete fibration agree.** -/
noncomputable def sliceLocEquiv (c : C) :
    ((W.inverseImage F).over (X := c)).Localization ≌ (W.over (X := F.obj c)).Localization :=
  Localization.uniq ((W.inverseImage F).over (X := c)).Q
    (Over.post F ⋙ (W.over (X := F.obj c)).Q) ((W.inverseImage F).over)

/-- The comparison lifts `Over.post F`. -/
noncomputable def sliceLocEquivFac (c : C) :
    ((W.inverseImage F).over (X := c)).Q ⋙ (sliceLocEquiv F W c).functor ≅
      Over.post F ⋙ (W.over (X := F.obj c)).Q :=
  Localization.compUniqFunctor _ _ _

noncomputable instance liftingSliceLocEquiv (c : C) :
    Localization.Lifting ((W.inverseImage F).over (X := c)).Q ((W.inverseImage F).over (X := c))
      (Over.post F ⋙ (W.over (X := F.obj c)).Q) (sliceLocEquiv F W c).functor :=
  ⟨sliceLocEquivFac F W c⟩

/-! The two `Lifting`s are `instance`s rather than `letI`s inside the proof, so that
`Localization.liftNatTrans_app` can compute the comparison's components downstream: the coherence
of `sliceLocEquivNatIso` is checked component-wise after `Q`. -/

noncomputable instance liftingNatIsoSrc {c' c : C} (u : c' ⟶ c) :
    Localization.Lifting ((W.inverseImage F).over (X := c')).Q
      ((W.inverseImage F).over (X := c'))
      (Over.map u ⋙ Over.post F ⋙ (W.over (X := F.obj c)).Q)
      (overMapLoc (W.inverseImage F) u ⋙ (sliceLocEquiv F W c).functor) :=
  Localization.Lifting.ofIsos _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Over.map u) (sliceLocEquivFac F W c)) (Iso.refl _)

noncomputable instance liftingNatIsoTgt {c' c : C} (u : c' ⟶ c) :
    Localization.Lifting ((W.inverseImage F).over (X := c')).Q
      ((W.inverseImage F).over (X := c'))
      (Over.post F ⋙ Over.map (F.map u) ⋙ (W.over (X := F.obj c)).Q)
      ((sliceLocEquiv F W c').functor ⋙ overMapLoc W (F.map u)) :=
  Localization.Lifting.ofIsos _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Over.post F) (eqToIso (overMapLocFac W (F.map u)))) (Iso.refl _)

/-- …naturally in `c`, for postcomposition on both sides. -/
noncomputable def sliceLocEquivNatIso {c' c : C} (u : c' ⟶ c) :
    overMapLoc (W.inverseImage F) u ⋙ (sliceLocEquiv F W c).functor ≅
      (sliceLocEquiv F W c').functor ⋙ overMapLoc W (F.map u) :=
  Localization.liftNatIso ((W.inverseImage F).over (X := c')).Q
    ((W.inverseImage F).over (X := c'))
    (Over.map u ⋙ Over.post F ⋙ (W.over (X := F.obj c)).Q)
    (Over.post F ⋙ Over.map (F.map u) ⋙ (W.over (X := F.obj c)).Q) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Over.mapPost F u) _ ≪≫ Functor.associator _ _ _)

/-- **The comparison, component by component.**  Its coherence is checked here, after `Q`, where
`sliceLocEquivFac` and `overMapLocFac` make everything computable — `sliceLocEquiv` itself never has
to be evaluated on an object. -/
theorem sliceLocEquivNatIso_app {c' c : C} (u : c' ⟶ c) (Y : Over c') :
    (sliceLocEquivNatIso F W u).hom.app (((W.inverseImage F).over (X := c')).Q.obj Y) =
      (Localization.Lifting.iso ((W.inverseImage F).over (X := c')).Q
          ((W.inverseImage F).over (X := c'))
          (Over.map u ⋙ Over.post F ⋙ (W.over (X := F.obj c)).Q)
          (overMapLoc (W.inverseImage F) u ⋙ (sliceLocEquiv F W c).functor)).hom.app Y ≫
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Over.mapPost F u) _ ≪≫ Functor.associator _ _ _).hom.app Y ≫
        (Localization.Lifting.iso ((W.inverseImage F).over (X := c')).Q
          ((W.inverseImage F).over (X := c'))
          (Over.post F ⋙ Over.map (F.map u) ⋙ (W.over (X := F.obj c)).Q)
          ((sliceLocEquiv F W c').functor ⋙ overMapLoc W (F.map u))).inv.app Y :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ Y

end CategoryTheory
