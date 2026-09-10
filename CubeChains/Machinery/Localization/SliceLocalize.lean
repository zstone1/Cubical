import CubeChains.Machinery.Slice
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Machinery/Localization/SliceLocalize — the slices of a discrete fibration, localized

A discrete fibration identifies `Over c` with `Over (F.obj c)`, and `over_inverseImage` says the
two carry the same class, so localizing gives the same category (`sliceLocEquiv`).

`overMapLoc` is a `Construction.lift`, so `overMapLocFac`, `overMapLoc_id` and `overMapLoc_comp`
are **equalities**; see the warning on it.  `W.RespectsIso` is a genuine hypothesis: transporting
a `W`-arrow backwards along the slice equivalence conjugates it by the counit.
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

/-- **A named lift between two localizations of one class is an equivalence.**  Reach for this
rather than `Localization.uniq` whenever the object map is needed: `uniq`'s functor factors through
`Functor.inv`, whereas here the object map is whatever `F` was written to be. -/
theorem Localization.isEquivalence_of_fac (L₁ : C ⥤ D) (L₂ : C ⥤ E) (W : MorphismProperty C)
    [L₁.IsLocalization W] [L₂.IsLocalization W] (F : D ⥤ E) (h : L₁ ⋙ F = L₂) :
    F.IsEquivalence :=
  Functor.isEquivalence_of_iso (Localization.isoUniqFunctor L₁ L₂ W F (eqToIso h)).symm

/-! ## Postcomposition -/

/-- Postcomposition on a slice, localized.  Strict, like `Over.map` itself.

**Do not weaken this to `Localization.lift`.**  Being a `Construction.lift` is what makes
`overMapLocFac`, `overMapLoc_id` and `overMapLoc_comp` *equalities*, and that is load-bearing
twice: `OverCoconeLoc.w` is statable as an equality, so `overCoconeLocEquiv` is an `Equiv` of types
rather than an equivalence of categories; and the slice family's compatibility (`hP`) is an
equality of functors, which is what `presentsSliceColimit` consumes. -/
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

/-! ## `Over.post`, localized -/

/-- Postcomposition commutes with `Over.post` — `F.map_comp`, read on slices. -/
theorem Over.map_comp_post (F : C ⥤ D) {A B : C} (u : A ⟶ B) :
    Over.map u ⋙ Over.post F = Over.post F ⋙ Over.map (F.map u) :=
  Functor.ext (fun y => congrArg Over.mk (F.map_comp y.hom u)) fun _ _ _ => by ext; simp

/-- `Over.post` on the localized slices.  A `Construction.lift`, like `overMapLoc`, so its
naturality is an equality. -/
noncomputable def postLoc (F : C ⥤ D) (W : MorphismProperty D) (c : C) :
    ((W.inverseImage F).over (X := c)).Localization ⥤ (W.over (X := F.obj c)).Localization :=
  Localization.Construction.lift (Over.post F ⋙ (W.over (X := F.obj c)).Q)
    (fun _ _ f hf => Localization.inverts (W.over (X := F.obj c)).Q (W.over (X := F.obj c))
      ((Over.post F).map f) hf)

theorem postLocFac (F : C ⥤ D) (W : MorphismProperty D) (c : C) :
    ((W.inverseImage F).over (X := c)).Q ⋙ postLoc F W c
      = Over.post F ⋙ (W.over (X := F.obj c)).Q :=
  Localization.Construction.fac _ _

/-- **…and it is natural in the base object, on the nose.** -/
theorem postLoc_naturality (F : C ⥤ D) (W : MorphismProperty D) {A B : C} (u : A ⟶ B) :
    overMapLoc (W.inverseImage F) u ⋙ postLoc F W B
      = postLoc F W A ⋙ overMapLoc W (F.map u) :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, overMapLocFac, Functor.assoc, postLocFac, ← Functor.assoc,
      Over.map_comp_post, Functor.assoc,
      ← Functor.assoc ((W.inverseImage F).over (X := A)).Q, postLocFac, Functor.assoc,
      overMapLocFac])

/-! ## The localized slices agree

`Over.post F` is an equivalence and carries `W.inverseImage F` on the slice to `W` on the slice
below (`over_inverseImage`, `rfl`), so it is a localization of one at the other.  Only the
*existence* of the comparison is wanted: it is `Localization.uniq`, opaque on objects, and any
client that has to compute with the inverse should write that inverse down instead. -/

variable (F : C ⥤ D) [F.IsDiscreteFibration] (W : MorphismProperty D) [W.RespectsIso]

/-- Any localization of the slice below is one of the slice above. -/
theorem isLocalization_post_comp (c : C) (L : Over (F.obj c) ⥤ E) [L.IsLocalization W.over] :
    (Over.post (X := c) F ⋙ L).IsLocalization ((W.inverseImage F).over) :=
  Functor.IsLocalization.of_inverseImage _ L _ _ (MorphismProperty.over_inverseImage W F c)

instance isLocalization_post_comp_Q (c : C) :
    (Over.post (X := c) F ⋙ (W.over (X := F.obj c)).Q).IsLocalization
      ((W.inverseImage F).over) :=
  isLocalization_post_comp F W c _

/-- **…so `postLoc` is an equivalence** — the named lift, where `sliceLocEquiv` is `uniq`. -/
instance isEquivalence_postLoc (c : C) : (postLoc F W c).IsEquivalence :=
  Localization.isEquivalence_of_fac ((W.inverseImage F).over (X := c)).Q
    (Over.post F ⋙ (W.over (X := F.obj c)).Q) ((W.inverseImage F).over) (postLoc F W c)
    (postLocFac F W c)

/-- **The localized slices of a discrete fibration agree.** -/
noncomputable def sliceLocEquiv (c : C) :
    ((W.inverseImage F).over (X := c)).Localization ≌ (W.over (X := F.obj c)).Localization :=
  Localization.uniq ((W.inverseImage F).over (X := c)).Q
    (Over.post F ⋙ (W.over (X := F.obj c)).Q) ((W.inverseImage F).over)

end CategoryTheory
