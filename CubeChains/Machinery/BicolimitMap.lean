import CubeChains.Machinery.Bicolimit
import CubeChains.Machinery.Localization.SliceLocalize

/-!
# Machinery/BicolimitMap — levelwise equivalent diagrams have equivalent bicolimits

`Grothendieck.map α` is an equivalence as soon as every `α.app c` is, and it creates the fibrewise
isomorphisms, so it descends to `bicolimit F ≌ bicolimit G` (`bicolimitMapEquiv`).  Strict
naturality of `α` is what makes it a 1-cell of diagrams at all: a comparison natural only up to
isomorphism does not act on the Grothendieck constructions.
-/

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {I : Type u₁} [Category.{v₁} I] {F G : I ⥤ Cat.{v₂, u₂}}

namespace Grothendieck

/-! ## Isomorphisms have invertible fibres -/

instance isIso_base {X Y : Grothendieck F} (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  inferInstanceAs (IsIso ((Grothendieck.forget F).map f))

/-- The transition along an invertible base is invertible. -/
instance isIso_ιNatTrans_app {X Y : Grothendieck F} (f : X ⟶ Y) [IsIso f] :
    IsIso ((ιNatTrans f.base).app X.fiber) :=
  Iso.isIso_hom (X.transportIso (asIso f.base)).symm

/-- **An isomorphism has an invertible fibre**: it factors as a transition, invertible because its
base is, followed by a fibre arrow, and `ι` is faithful. -/
instance isIso_fiber {X Y : Grothendieck F} (f : X ⟶ Y) [IsIso f] : IsIso f.fiber := by
  haveI : IsIso ((ιNatTrans f.base).app X.fiber ≫ (ι F Y.base).map f.fiber) := by
    rw [ιNatTrans_app_comp_ι_map]; assumption
  haveI : IsIso ((ι F Y.base).map f.fiber) :=
    IsIso.of_isIso_comp_left ((ιNatTrans f.base).app X.fiber) _
  have hbase : (inv ((ι F Y.base).map f.fiber)).base = 𝟙 Y.base :=
    (Category.id_comp _).symm.trans
      (congrArg Hom.base (IsIso.hom_inv_id ((ι F Y.base).map f.fiber)))
  have hp : Y.fiber
      = (F.map (inv ((ι F Y.base).map f.fiber)).base).toFunctor.obj Y.fiber := by
    rw [hbase]; simp
  have hι : (ι F Y.base).map (eqToHom hp ≫ (inv ((ι F Y.base).map f.fiber)).fiber)
      = inv ((ι F Y.base).map f.fiber) :=
    ext _ _ hbase.symm (by
      simp only [ι_map]
      exact (eqToHom_comp₃_comp _ _ _ _ rfl).trans (Category.id_comp _))
  refine ⟨eqToHom hp ≫ (inv ((ι F Y.base).map f.fiber)).fiber,
    (ι F Y.base).map_injective (((ι F Y.base).map_comp _ _).trans ?_),
    (ι F Y.base).map_injective (((ι F Y.base).map_comp _ _).trans ?_)⟩
  · exact ((congrArg (fun z => (ι F Y.base).map f.fiber ≫ z) hι).trans
      (IsIso.hom_inv_id _)).trans ((ι F Y.base).map_id _).symm
  · exact ((congrArg (fun z => z ≫ (ι F Y.base).map f.fiber) hι).trans
      (IsIso.inv_hom_id _)).trans ((ι F Y.base).map_id _).symm

/-! ## What the bicolimit inverts, respects isomorphisms -/

instance respectsLeft_fibrewiseIsos :
    (fibrewiseIsos F).RespectsLeft (MorphismProperty.isomorphisms (Grothendieck F)) where
  precomp i hi f hf := by
    haveI : IsIso i := hi
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (inferInstanceAs (IsIso (eqToHom _)))
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (Functor.map_isIso (F.map f.base).toFunctor i.fiber) hf)

instance respectsRight_fibrewiseIsos :
    (fibrewiseIsos F).RespectsRight (MorphismProperty.isomorphisms (Grothendieck F)) where
  postcomp i hi f hf := by
    haveI : IsIso i := hi
    haveI : IsIso f.fiber := hf
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (inferInstanceAs (IsIso (eqToHom _)))
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (Functor.map_isIso (F.map i.base).toFunctor f.fiber) inferInstance)

/-! ## The comparison a levelwise equivalence induces -/

variable (α : F ⟶ G) [hα : ∀ c : I, ((α.app c).toFunctor).IsEquivalence]

omit hα in
/-- The comparison's fibre: the transport its naturality carries, then the equivalence's image. -/
theorem map_map_fiber_eq {X Y : Grothendieck F} (f : X ⟶ Y) :
    ((Grothendieck.map α).map f).fiber
      = eqToHom (Functor.congr_obj
          (congrArg Cat.Hom.toFunctor (α.naturality f.base).symm) X.fiber)
        ≫ (α.app Y.base).toFunctor.map f.fiber :=
  congrArg (· ≫ (α.app Y.base).toFunctor.map f.fiber) (Cat.eqToHom_app _ _ _ X.fiber)

instance isIso_map_map_fiber {X Y : Grothendieck F} (f : X ⟶ Y) [IsIso f.fiber] :
    IsIso (((Grothendieck.map α).map f).fiber) := by
  haveI := hα Y.base
  rw [map_map_fiber_eq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (inferInstanceAs (IsIso (eqToHom _)))
    (Functor.map_isIso (α.app Y.base).toFunctor f.fiber)

/-- **The comparison creates the fibrewise isomorphisms.** -/
theorem fibrewiseIsos_inverseImage :
    fibrewiseIsos F = (fibrewiseIsos G).inverseImage (Grothendieck.map α) := by
  funext X Y f
  haveI := hα Y.base
  refine propext ⟨fun hf => ?_, fun hf => ?_⟩
  · haveI : IsIso f.fiber := hf
    exact isIso_map_map_fiber α f
  · haveI : IsIso (eqToHom (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor (α.naturality f.base).symm) X.fiber)
        ≫ (α.app Y.base).toFunctor.map f.fiber) := by
      rw [← map_map_fiber_eq]; exact hf
    haveI : IsIso ((α.app Y.base).toFunctor.map f.fiber) :=
      IsIso.of_isIso_comp_left (eqToHom (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor (α.naturality f.base).symm) X.fiber)) _
    exact isIso_of_reflects_iso f.fiber (α.app Y.base).toFunctor

/-! ## …is an equivalence -/

instance faithful_map : (Grothendieck.map α).Faithful where
  map_injective {X Y} {f g} h := by
    haveI := hα Y.base
    obtain ⟨fb, ff⟩ := f
    obtain ⟨gb, gf⟩ := g
    have hb : fb = gb := congrArg Hom.base h
    subst hb
    have hfib := Grothendieck.congr h
    rw [map_map_fiber_eq, map_map_fiber_eq] at hfib
    exact congrArg (Hom.mk fb) ((α.app Y.base).toFunctor.map_injective
      ((Iso.cancel_iso_hom_left (eqToIso (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor (α.naturality fb).symm) X.fiber)) _ _).1
          (hfib.trans (Category.id_comp _))))

instance full_map : (Grothendieck.map α).Full where
  map_surjective {X Y} f := by
    haveI := hα Y.base
    refine ⟨⟨f.base, (α.app Y.base).toFunctor.preimage (eqToHom (Functor.congr_obj
      (congrArg Cat.Hom.toFunctor (α.naturality f.base)) X.fiber) ≫ f.fiber)⟩, ?_⟩
    refine ext _ _ rfl ?_
    rw [map_map_fiber_eq, Functor.map_preimage]
    exact (eqToHom_comp₃_comp _ _ _ _ rfl).trans (Category.id_comp _)

instance essSurj_map : (Grothendieck.map α).EssSurj where
  mem_essImage Z := by
    haveI := hα Z.base
    exact ⟨⟨Z.base, (α.app Z.base).toFunctor.objPreimage Z.fiber⟩,
      ⟨isoMk (Iso.refl Z.base) (eqToIso (by simp)
        ≪≫ (α.app Z.base).toFunctor.objObjPreimageIso Z.fiber)⟩⟩

instance isEquivalence_map : (Grothendieck.map α).IsEquivalence where

/-! ## …hence of bicolimits -/

instance isLocalization_map_comp_Q :
    (Grothendieck.map α ⋙ (fibrewiseIsos G).Q).IsLocalization (fibrewiseIsos F) :=
  Functor.IsLocalization.of_inverseImage _ _ _ _ (fibrewiseIsos_inverseImage α)

/-- **A levelwise equivalence of diagrams has equivalent bicolimits.** -/
noncomputable def bicolimitMapEquiv : bicolimit F ≌ bicolimit G :=
  Localization.uniq (fibrewiseIsos F).Q (Grothendieck.map α ⋙ (fibrewiseIsos G).Q)
    (fibrewiseIsos F)

end Grothendieck

end CategoryTheory
