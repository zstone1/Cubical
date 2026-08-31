import CubeChains.Concurrency.Presentation.GarsideChains

/-!
# Concurrency/Presentation/PosLocalization — a strand component, localized at the bead merges

The coarsest chain is wide-terminal for the merges (`topWideTerminal`), so a localization of
`ChStrands Zbp n` collapses onto it: `SingleObj (LocMonoid W)` is one
(`toLocMonoid_isLocalization`).  `Concurrency/Presentation/GarsideChains` names the monoid — it is
`PosBraid n`, by the crossing permutation — so `posBraidGrading n` is the localization functor of
the strand-`n` component.

The strand count is fixed throughout: nothing here splits `Ch Zbp` by degree.
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

/-! ### The strand component, localized -/

/-- **The positive-braid grading of the strand-`n` component**: an arrow to the simple its
crossing permutation names. -/
def posBraidGrading (n : ℕ) : ChStrands Zbp n ⥤ SingleObj (PosBraid n) where
  obj _ := SingleObj.star _
  map f := posPerm (crossPermN f)
  map_id A := posPerm_crossPermN_eq_one ((WStrands Zbp n).id_mem A)
  map_comp f g := (posPerm_crossPermN_comp f g).symm

/-- **The grading localizes the component** — it is `toLocMonoid` read through `locEquivPosBraid`,
and a wide-terminal object makes `toLocMonoid` a localization. -/
theorem posBraidGrading_isLocalization (n : ℕ) :
    (posBraidGrading n).IsLocalization (WStrands Zbp n) := by
  haveI := toLocMonoid_isLocalization (topWideTerminal n)
  exact Functor.IsLocalization.of_equivalence_target (toLocMonoid (WStrands Zbp n)) (WStrands Zbp n)
    (posBraidGrading n) (locEquivPosBraid n).toSingleObjEquiv
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

instance respectsIso_WStrands (K : BPSet) (n : ℕ) : (WStrands K n).RespectsIso :=
  inferInstanceAs ((W K).inverseImage (HasStrands K n).ι).RespectsIso

end ChainCat
