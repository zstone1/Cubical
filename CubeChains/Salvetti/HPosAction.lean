import CubeChains.Braid.PosAction
import CubeChains.Foundations.ElementsAction
import CubeChains.Chains.ElementsFibration
import CubeChains.Salvetti.ChStarSym

/-!
# Salvetti/HPosAction — `Ch (H □ⁿ)` localized at the merges is the positive braid action

`Ch (Hbp □ⁿ)` is the category of elements of `wedgeHoms (Hbp □ⁿ)` over `Ch Zbp`, so — once the
merges are inverted on the fibre — localizing it only localizes the base, and the base's
localization is `FullPosBraid`.  A chain of `Hbp □ⁿ` has `dimSum = n` (`und` reads its underlying
chain of `□ⁿ`), so only the degree-`n` component `degreeIncl n` carries anything.

What the fibre *is* there — `Perm (Fin n)`, with `β` restricting by `permHom β⁻¹` — is the
hypothesis `PermFibre`; everything else is theorem.
-/

open CategoryTheory Opposite BPSet Equiv CubeChains CategoryTheory.Localization

namespace ChainCat

variable {n : ℕ}

/-! ### The degree-`n` component of the localized serial wedges -/

/-- The degree-`n` component of the localized serial wedges: one object, `PosBraid n` on it. -/
noncomputable def degreeIncl (n : ℕ) :
    (SingleObj (PosBraid n))ᵒᵖ ⥤ ((Winf Zbp).op).Localization :=
  (Graded.single n).op ⋙ locFullOpEquiv.inverse

instance (n : ℕ) : (degreeIncl n).Full :=
  inferInstanceAs (((Graded.single n).op ⋙ locFullOpEquiv.inverse).Full)

instance (n : ℕ) : (degreeIncl n).Faithful :=
  inferInstanceAs (((Graded.single n).op ⋙ locFullOpEquiv.inverse).Faithful)

/-! ### The orderings, as a `PosBraid n`-set -/

/-- The presheaf on the degree-`n` component carried by the orderings: `β` restricts by
`permHom β⁻¹`, the variance `(∫ -)ᵒᵖ` needs. -/
abbrev permPresheaf (n : ℕ) : (SingleObj (PosBraid n))ᵒᵖ ⥤ Type :=
  invActionPresheaf (Perm (Fin n)) (posPermHom n)

/-- **`(∫ permPresheaf)ᵒᵖ` is the positive braid action.** -/
def permPresheafElementsEquiv : (((permPresheaf n).Elements)ᵒᵖ) ≌ PosBraidAction n :=
  elementsOpEquivActionCategory _ _ fun _ _ => rfl

/-! ### A decorated chain of `□ⁿ` has `n` events -/

/-- Forgetting the order leaves a chain of `□ⁿ`, whose events are the `n` coordinates. -/
theorem dimSum_of_hbpCubeHom {d : List ℕ+} (α : ⋁d ⟶ Hbp.obj (□n)) : dimSum d = n :=
  wedgeDimSum_eq (und (□n) α)

/-! ### The comparison -/

variable (h : InvertsMerges (Hbp.obj (□n)))

/-- Only the degree-`n` component of the localized base carries a fibre. -/
private theorem degreeIncl_cover (c : ((Winf Zbp).op).Localization)
    (x : (wedgeHomsDescend (Hbp.obj (□n)) h).obj c) :
    ∃ d, Nonempty ((degreeIncl n).obj d ≅ c) := by
  haveI := Localization.essSurj ((Winf Zbp).op).Q ((Winf Zbp).op)
  obtain ⟨b, ⟨e⟩⟩ : ∃ b, Nonempty (((Winf Zbp).op).Q.obj b ≅ c) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ c⟩⟩
  have hty : (wedgeHomsDescend (Hbp.obj (□n)) h).obj (((Winf Zbp).op).Q.obj b)
      = (wedgeHoms (Hbp.obj (□n))).obj b :=
    Functor.congr_obj (Localization.Construction.fac (wedgeHoms (Hbp.obj (□n))) h) b
  have hα : (wedgeHoms (Hbp.obj (□n))).obj b :=
    hty ▸ (wedgeHomsDescend (Hbp.obj (□n)) h).map e.inv x
  have hdim : dimSum (unop b).dims = n := dimSum_of_hbpCubeHom hα
  refine ⟨op (SingleObj.star (PosBraid n)), ⟨?_⟩⟩
  have hq : locFullOpEquiv.functor.obj (((Winf Zbp).op).Q.obj b) ≅ ((chPos Zbp).op).obj b :=
    (Localization.qCompEquivalenceFromModelFunctorIso ((chPos Zbp).op) ((Winf Zbp).op)).app b
  have hdeg : ((Graded.single n).op.obj (op (SingleObj.star (PosBraid n))) : FullPosBraidᵒᵖ)
      = ((chPos Zbp).op).obj b := congrArg op hdim.symm
  exact locFullOpEquiv.inverse.mapIso (eqToIso hdeg ≪≫ hq.symm) ≪≫
    (locFullOpEquiv.unitIso.app (((Winf Zbp).op).Q.obj b)).symm ≪≫ e

/-- **The fibre hypothesis**: on the degree-`n` component of the localized base, the descended
fibre presheaf is the `PosBraid n`-set of orderings. -/
def PermFibre (n : ℕ) (h : InvertsMerges (Hbp.obj (□n))) : Prop :=
  Nonempty (degreeIncl n ⋙ wedgeHomsDescend (Hbp.obj (□n)) h ≅ permPresheaf n)

/-- **`Ch (Hbp □ⁿ)` localized at the bead merges is the positive braid action**: objects the
orderings of the strands, arrows the positive braids realising the change of ordering. -/
noncomputable def localizationEquivPosBraidAction (hf : PermFibre n h) :
    (Winf (Hbp.obj (□n))).Localization ≌ PosBraidAction n := by
  haveI : (chDescent (Hbp.obj (□n)) h).IsLocalization (Winf (Hbp.obj (□n))) :=
    isLocalization_chDescent _ h
  haveI : (CategoryOfElements.pre (wedgeHomsDescend (Hbp.obj (□n)) h)
      (degreeIncl n)).IsEquivalence :=
    CategoryOfElements.isEquivalence_pre _ _ (degreeIncl_cover h)
  exact (Localization.uniq (Winf (Hbp.obj (□n))).Q (chDescent (Hbp.obj (□n)) h)
      (Winf (Hbp.obj (□n)))).trans
    ((((CategoryOfElements.pre (wedgeHomsDescend (Hbp.obj (□n)) h)
        (degreeIncl n)).asEquivalence.symm.op).trans
      ((CategoryOfElements.mapEquivalence hf.some).op)).trans permPresheafElementsEquiv)

/-- **The loops of the localization are the positive pure braids**: an ordering returns to itself
only along a braid that returns every strand to its own position. -/
noncomputable def endEquivPosPureOfLocalization (hf : PermFibre n h)
    (X : (Winf (Hbp.obj (□n))).Localization) : End X ≃* PosPureBraid n :=
  ((localizationEquivPosBraidAction h hf).fullyFaithfulFunctor.mulEquivEnd X).trans
    (endEquivPosPure _)

end ChainCat
