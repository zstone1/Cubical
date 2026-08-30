import CubeChains.Braid.GermPresentation
import CubeChains.Chains.GarsideChains
import CubeChains.Chains.MergeBraid
import CubeChains.Foundations.LocalizationSigma

/-!
# Chains/PosLocalization — the serial wedges, localized at the bead merges

`chPos Zbp` inverts the bead merges and nothing else: it *is* the localization, so
`Ch Zbp[Winf⁻¹]` is the intervals `1ⁿ ⟶ [n]`, degree by degree.

Two inputs.  A `Star` collapses a localization onto its basepoint, so `SingleObj (LocMonoid W)` is
a localization of `C` (`toLocMonoid_isLocalization`); with `Chains/GarsideChains` that names the
strand-`n` component's localization.  And a chain morphism preserves the event count, so `Ch Zbp`
is the coproduct of those components (`Foundations/LocalizationSigma`) — the same splitting the
grading has by degree.
-/

universe v u

open CategoryTheory CubeChains BPSet

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative] {x : C}

/-- Reading a loop back and putting it where it came from is the identity on `LocMonoid W`. -/
noncomputable def locSingleCounit (S : Star W x) :
    locSingleFunctor S ⋙ locFunctor W ≅ 𝟭 (SingleObj (LocMonoid W)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {_ _} p =>
    (Category.comp_id _).trans
      ((DFunLike.congr_fun (locFunctor_comp_locToEnd S) p).trans (Category.id_comp _).symm)

/-- **A star collapses the localization onto its basepoint.** -/
noncomputable def starEquivalence (S : Star W x) : W.Localization ≌ SingleObj (LocMonoid W) :=
  .mk (locFunctor W) (locSingleFunctor S)
    (asIso (Localization.Construction.natTransExtension (starNat S))).symm
    (locSingleCounit S)

/-- **`C ⥤ SingleObj (LocMonoid W)` is a localization at `W`**, whenever `W` has a star. -/
theorem toLocMonoid_isLocalization (S : Star W x) : (toLocMonoid W).IsLocalization W :=
  Functor.IsLocalization.of_equivalence_target W.Q W _ (starEquivalence S)
    (eqToIso (Localization.Construction.fac (toLocMonoid W) (toLocMonoid_inverts W)))

end CategoryTheory

namespace ChainCat

/-! ### One strand component -/

/-- **The positive-braid grading of one strand component**, read at that component's own strand
count: an arrow to the simple its crossing permutation names. -/
def chPosN (n : ℕ) : ChZn n ⥤ SingleObj (PosBraid n) where
  obj _ := SingleObj.star _
  map f := posPerm (crossPermN f)
  map_id A := posPerm_crossPermN_eq_one ((WinfN Zbp n).id_mem A)
  map_comp f g := (posPerm_crossPermN_comp f g).symm

/-- **Each strand component is localized by its grading** — the grading is `toLocMonoid` read
through the presentation, and a star makes `toLocMonoid` a localization. -/
theorem chPosN_isLocalization (n : ℕ) : (chPosN n).IsLocalization (WinfN Zbp n) := by
  haveI := toLocMonoid_isLocalization (starZ n)
  exact Functor.IsLocalization.of_equivalence_target (toLocMonoid (WinfN Zbp n)) (WinfN Zbp n)
    (chPosN n) (locEquivPosBraid n).toSingleObjEquiv
    (NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
      simp only [Functor.comp_map, Iso.refl_hom]
      exact locEquivPosBraid_locOf f)

/-! ### The merges respect isomorphisms

A chain isomorphism is an identity: it cannot change the bead count either way, and `Ch K` has no
non-trivial endomorphisms. -/

theorem eq_of_isIso {K : BPSet} {a b : Ch K} (f : a ⟶ b) [IsIso f] : a = b :=
  eq_of_hom_of_dims_length_eq f
    (Nat.le_antisymm (dims_length_le_of_hom (inv f)) (dims_length_le_of_hom f))

instance respectsIso_Winf (K : BPSet) : (Winf K).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf => by obtain rfl := eq_of_isIso e.hom; rwa [endo_eq_id e.hom, Category.id_comp])
    (fun e f hf => by obtain rfl := eq_of_isIso e.hom; rwa [endo_eq_id e.hom, Category.comp_id])

/-! ### The assembly -/

/-- The component grading and the total grading differ by the degree identification the component
carries. -/
noncomputable def chPosNIso (n : ℕ) :
    chPosN n ⋙ Graded.single n ≅ (StrandCount Zbp n).ι ⋙ chPos Zbp :=
  NatIso.ofComponents (fun A => asIso (Graded.ofDeg A.property.symm)) (by
    intro X Y f
    obtain ⟨A, hA⟩ := X
    obtain ⟨B, _⟩ := Y
    subst hA
    refine GradedHom.ext ?_
    change (1 : PosBraid (dimSum A.dims)) * posPerm (crossPerm f.hom)
      = posPerm (crossPerm f.hom) * 1
    rw [one_mul, mul_one])

/-- **The serial wedges are the coproduct of their strand components** — notation, not a
definition, so that the `Functor.IsLocalization.graded` instance matches on the nose. -/
local notation "strandFibres" =>
  Sigma.gradedEquivalence (fun a : Ch Zbp => dimSum (Obj.dims a)) fun {_ _} f => strandsEq f

/-- The two readings of the grading on the coproduct of the strand components. -/
noncomputable def sigmaChPosIso :
    Sigma.Functor.sigma' chPosN ⋙ Graded.sigmaDesc ≅ (strandFibres).functor ⋙ chPos Zbp :=
  Sigma.natIso chPosNIso

/-- The grading, transported back along the fibre decomposition. -/
noncomputable def chPosIso :
    ((strandFibres).inverse ⋙ Sigma.Functor.sigma' chPosN) ⋙ Graded.sigmaDesc ≅ chPos Zbp :=
  Functor.isoWhiskerLeft (strandFibres).inverse sigmaChPosIso ≪≫
    Equivalence.invFunIdAssoc _ (chPos Zbp)

/-- **The positive braid grading is the localization of the serial wedges at the bead merges.**
Fibre by fibre it is the endomorphism monoid of `Ch Zbp[Winf⁻¹]` at the coarsest chain
(`chPosN`), and `Ch Zbp` is the coproduct of those fibres. -/
instance chPos_isLocalization : (chPos Zbp).IsLocalization (Winf Zbp) := by
  haveI : ∀ n : ℕ, (chPosN n).IsLocalization
      ((Winf Zbp).inverseImage (Sigma.fibre (fun a : Ch Zbp => dimSum a.dims) n).ι) :=
    chPosN_isLocalization
  haveI := Functor.IsLocalization.graded (fun a : Ch Zbp => dimSum a.dims)
    (fun {_ _} f => strandsEq f) (Winf Zbp) chPosN
  exact Functor.IsLocalization.of_equivalence_target _ (Winf Zbp) (chPos Zbp)
    Graded.sigmaDesc.asEquivalence chPosIso

/-- **The serial wedges, localized at the bead merges, are the positive braid monoids** — one
degree per event count, and no morphisms between degrees. -/
noncomputable def localizationEquivFullPosBraid : (Winf Zbp).Localization ≌ FullPosBraid :=
  Localization.equivalenceFromModel (chPos Zbp) (Winf Zbp)

/-- The same, on the opposite — the variance `Ch K` sits in over `Ch Zbp`. -/
noncomputable def locFullOpEquiv : ((Winf Zbp).op).Localization ≌ FullPosBraidᵒᵖ :=
  Localization.equivalenceFromModel ((chPos Zbp).op) ((Winf Zbp).op)

/-- **`Ch(Zbp)[Winf⁻¹]ᵒᵖ` is presented by the germ relations**: one vertex per event count, a
generator for each permutation of the events, and the length-additive products. -/
noncomputable def locGermPresentation : Quotient germRel ≌ ((Winf Zbp).op).Localization :=
  germPresentation.trans locFullOpEquiv.symm

/-- **The Garside presentation of `Ch(Zbp)[Winf⁻¹]`**: in each degree the interval `1ⁿ ⟶ [n]`,
generators the chain morphisms and relations their factorisations. -/
noncomputable def localizationEquivGarside : (Winf Zbp).Localization
    ≌ Graded fun n => GarsideMonoid (WinfN Zbp n) (onesObj n) (topObj n) :=
  localizationEquivFullPosBraid.trans (Graded.congr fun n => (garsideEquivPosBraid n).symm)

end ChainCat
