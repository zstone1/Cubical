import CubeChains.Machinery.BicolimitMap
import CubeChains.Machinery.Presentation.SliceColimit
import CubeChains.Machinery.Presentation.Transition

/-!
# Machinery/Presentation/SliceTransition — the slice presentations, joined by transitions

The copies present the localized slices, so `Grothendieck.bicolimitMapEquiv` carries the bicolimit
of the copies to the bicolimit of the localized slices, which is `(∫X)[W⁻¹]`
(`isBicolimit_slicePseudoCocone`).  Against `presentsSliceColimit` this asks the same strict `hP`
and produces the bigger polygraph: a transition cell per arrow of the index, which the strict
colimit lacks (`isoComparison_not_enough`).
-/

universe u

namespace CategoryTheory

namespace Polygraph

open Opposite

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
  (V : MorphismProperty D) [V.RespectsIso]
  (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
  (hP : ∀ {d' d : D} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f)

include hP in
/-- **The slice presentations, as a comparison of diagrams** — strict `hP` is exactly its
naturality. -/
noncomputable def slicePresentedNat :
    elementsPoly X P ⋙ presentedFunctor.{u, u}
      ⟶ (CategoryOfElements.π X).leftOp ⋙ overLocFunctor V where
  app c := ((p (eltBase X c)).E).toCatHom
  naturality _ _ u := Cat.ext (hP ((CategoryOfElements.π X).leftOp.map u))

include hP in
/-- **The copies' bicolimit is `(∫X)[W⁻¹]`** — the copies, the slices of `D` and the slices of
`∫X` are three levelwise equivalent diagrams, each comparison strict. -/
noncomputable def bicolimitElementsEquiv :
    bicolimit (elementsPoly X P ⋙ presentedFunctor.{u, u})
      ≌ ((V.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  haveI : ∀ c : (X.Elements)ᵒᵖ,
      (((slicePresentedNat X V p hP).app c).toFunctor).IsEquivalence :=
    fun c => (p (eltBase X c)).isEquiv
  haveI : ∀ c : (X.Elements)ᵒᵖ,
      (((postLocNat (CategoryOfElements.π X).leftOp V).app c).toFunctor).IsEquivalence :=
    fun c => isEquivalence_postLoc _ V c
  (Grothendieck.bicolimitMapEquiv (slicePresentedNat X V p hP)).trans
    ((Grothendieck.bicolimitMapEquiv (postLocNat (CategoryOfElements.π X).leftOp V)).symm.trans
      ((isBicolimit_bicolimitCocone _).equiv isBicolimit_slicePseudoCocone))

include hP in
/-- **The transition polygraph of the slice presentations presents `(∫X)[W⁻¹]`.** -/
noncomputable def presentsSliceTransition :
    Presents (transitionPoly (elementsPoly X P))
      ((V.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  presentsBicolimit (elementsPoly X P)
    ((isBicolimit_bicolimitCocone _).precompose_equivalence (bicolimitElementsEquiv X V p hP))

end Polygraph

end CategoryTheory
