import CubeChains.Machinery.Braid.BraidPresentation
import CubeChains.Concurrency.Presentation.GarsideChains
import CubeChains.Concurrency.Merge.MergeBraid
import CubeChains.Machinery.Localization.LocalizationSigma

/-!
# Concurrency/Presentation/PosLocalization — the serial wedges, localized at the bead merges

`chPosBraid Zbp` inverts the bead merges and nothing else: it *is* the localization, so
`Ch Zbp[W⁻¹]` is the intervals `1ⁿ ⟶ [n]`, degree by degree.

Two inputs.  A wide-terminal object collapses a localization onto its basepoint, so
`SingleObj (LocMonoid W)` is a localization of `C` (`toLocMonoid_isLocalization`); with
`Concurrency/Presentation/GarsideChains` that names the
strand-`n` component's localization.  And a chain morphism preserves the event count, so `Ch Zbp`
is the coproduct of those components (`Machinery/Localization/LocalizationSigma`) — the same
splitting the grading has by degree.
-/

universe v u

open CategoryTheory CubeChains BPSet

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative] {x : C}

/-- Reading a loop back and putting it where it came from is the identity on `LocMonoid W`. -/
noncomputable def locSingleCounit (S : IsWideTerminal W x) :
    locSingleFunctor S ⋙ locFunctor W ≅ 𝟭 (SingleObj (LocMonoid W)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {_ _} p =>
    (Category.comp_id _).trans
      ((DFunLike.congr_fun (locFunctor_comp_locToEnd S) p).trans (Category.id_comp _).symm)

/-- **A wide-terminal object collapses the localization onto its basepoint.** -/
noncomputable def locSingleEquivalence (S : IsWideTerminal W x) :
    W.Localization ≌ SingleObj (LocMonoid W) :=
  .mk (locFunctor W) (locSingleFunctor S)
    (asIso (Localization.Construction.natTransExtension (locInvNat S))).symm
    (locSingleCounit S)

/-- **`C ⥤ SingleObj (LocMonoid W)` is a localization at `W`**, whenever `W` is wide-terminal
somewhere. -/
theorem toLocMonoid_isLocalization (S : IsWideTerminal W x) : (toLocMonoid W).IsLocalization W :=
  Functor.IsLocalization.of_equivalence_target W.Q W _ (locSingleEquivalence S)
    (eqToIso (Localization.Construction.fac (toLocMonoid W) (toLocMonoid_inverts W)))

end CategoryTheory

namespace ChainCat

/-! ### One strand component -/

/-- **The positive-braid grading of one strand component**, read at that component's own strand
count: an arrow to the simple its crossing permutation names. -/
def chPosBraidStrands (n : ℕ) : ChStrands Zbp n ⥤ SingleObj (PosBraid n) where
  obj _ := SingleObj.star _
  map f := posPerm (crossPermN f)
  map_id A := posPerm_crossPermN_eq_one ((WStrands Zbp n).id_mem A)
  map_comp f g := (posPerm_crossPermN_comp f g).symm

/-- **Each strand component is localized by its grading** — the grading is `toLocMonoid` read
through the presentation, and a wide-terminal object makes `toLocMonoid` a localization. -/
theorem chPosBraidStrands_isLocalization (n : ℕ) :
    (chPosBraidStrands n).IsLocalization (WStrands Zbp n) := by
  haveI := toLocMonoid_isLocalization (topWideTerminal n)
  exact Functor.IsLocalization.of_equivalence_target (toLocMonoid (WStrands Zbp n)) (WStrands Zbp n)
    (chPosBraidStrands n) (locEquivPosBraid n).toSingleObjEquiv
    (NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
      simp only [Functor.comp_map, Iso.refl_hom]
      exact locEquivPosBraid_locOf f)

/-! ### The merges respect isomorphisms

A chain isomorphism is an identity: it cannot change the bead count either way, and `Ch K` has no
non-trivial endomorphisms. -/

theorem eq_of_isIso {K : BPSet} {a b : Ch K} (f : a ⟶ b) [IsIso f] : a = b :=
  eq_of_hom_of_dims_length_eq f
    (Nat.le_antisymm (dims_length_le_of_hom (inv f)) (dims_length_le_of_hom f))

instance respectsIso_W (K : BPSet) : (W K).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf => by obtain rfl := eq_of_isIso e.hom; rwa [endo_eq_id e.hom, Category.id_comp])
    (fun e f hf => by obtain rfl := eq_of_isIso e.hom; rwa [endo_eq_id e.hom, Category.comp_id])

/-! ### The assembly -/

/-- The component grading and the total grading differ by the degree identification the component
carries. -/
noncomputable def chPosBraidStrandsIso (n : ℕ) :
    chPosBraidStrands n ⋙ Graded.single n ≅ (HasStrands Zbp n).ι ⋙ chPosBraid Zbp :=
  NatIso.ofComponents (fun A => asIso (Graded.ofDeg A.property.symm)) (by
    intro X Y f
    obtain ⟨A, hA⟩ := X
    obtain ⟨B, _⟩ := Y
    subst hA
    refine GradedHom.ext ?_
    change (1 : PosBraid (dimSum A.dims)) * posPerm (crossPerm rfl f.hom)
      = posPerm (crossPerm rfl f.hom) * 1
    rw [one_mul, mul_one])

/-- **The serial wedges are the coproduct of their strand components** — notation, not a
definition, so that the `Functor.IsLocalization.graded` instance matches on the nose. -/
local notation "strandFibres" =>
  Sigma.gradedEquivalence (fun a : Ch Zbp => dimSum (Obj.dims a)) fun {_ _} f => strandsEq f

/-- The two readings of the grading on the coproduct of the strand components. -/
noncomputable def sigmaChPosBraidIso :
    Sigma.Functor.sigma' chPosBraidStrands ⋙ Graded.sigmaDesc
      ≅ (strandFibres).functor ⋙ chPosBraid Zbp :=
  Sigma.natIso chPosBraidStrandsIso

/-- The grading, transported back along the fibre decomposition. -/
noncomputable def chPosBraidIso :
    ((strandFibres).inverse ⋙ Sigma.Functor.sigma' chPosBraidStrands) ⋙ Graded.sigmaDesc
      ≅ chPosBraid Zbp :=
  Functor.isoWhiskerLeft (strandFibres).inverse sigmaChPosBraidIso ≪≫
    Equivalence.invFunIdAssoc _ (chPosBraid Zbp)

/-- **The positive braid grading is the localization of the serial wedges at the bead merges.**
Fibre by fibre it is the endomorphism monoid of `Ch Zbp[W⁻¹]` at the coarsest chain
(`chPosBraidStrands`), and `Ch Zbp` is the coproduct of those fibres. -/
instance chPosBraid_isLocalization : (chPosBraid Zbp).IsLocalization (W Zbp) := by
  haveI : ∀ n : ℕ, (chPosBraidStrands n).IsLocalization
      ((W Zbp).inverseImage (Sigma.fibre (fun a : Ch Zbp => dimSum a.dims) n).ι) :=
    chPosBraidStrands_isLocalization
  haveI := Functor.IsLocalization.graded (fun a : Ch Zbp => dimSum a.dims)
    (fun {_ _} f => strandsEq f) (W Zbp) chPosBraidStrands
  exact Functor.IsLocalization.of_equivalence_target _ (W Zbp) (chPosBraid Zbp)
    Graded.sigmaDesc.asEquivalence chPosBraidIso

/-- **The serial wedges, localized at the bead merges, are the positive braid monoids** — one
degree per event count, and no morphisms between degrees. -/
noncomputable def localizationEquivFullPosBraid : (W Zbp).Localization ≌ FullPosBraid :=
  Localization.equivalenceFromModel (chPosBraid Zbp) (W Zbp)

/-- The same, on the opposite — the variance `Ch K` sits in over `Ch Zbp`. -/
noncomputable def locFullOpEquiv : ((W Zbp).op).Localization ≌ FullPosBraidᵒᵖ :=
  Localization.equivalenceFromModel ((chPosBraid Zbp).op) ((W Zbp).op)

end ChainCat

namespace CubeChains.BraidPresentation

open ChainCat

/-- **`Ch(Zbp)[W⁻¹]ᵒᵖ` is presented by any generator family for `PosBraid`**: one vertex per event
count, that family's generators on it. -/
noncomputable def locEquiv (P : BraidPresentation) :
    Quotient P.pathRel ≌ ((W Zbp).op).Localization :=
  P.equiv.trans locFullOpEquiv.symm

end CubeChains.BraidPresentation
