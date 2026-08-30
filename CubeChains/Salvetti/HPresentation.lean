import CubeChains.Chains.ArtinPresentation
import CubeChains.Salvetti.CrossCompare

/-!
# Salvetti/HPresentation — `Ch(Hbp □ⁿ)[W⁻¹]`, presented

`isSegal_H_cube` supplies the hypothesis, so both base presentations transport: the germ
one — generators all permutations of a chain's events, relations the length-additive products — and
the Artin one, generators an adjacent pair and relations commutation and braid.  Both readings are
literal: `Sigma.totalEdgeEquiv` for the generators, `Sigma.totalRel_word_iff` for the relations, and
`artin_comm`/`artin_braid` for the two families themselves.

⚠ An atom is one leg of a span: `wallCross w k` lies below both chambers it separates, so a
chamber-to-chamber `σₖ` exists only after inverting the other leg — the one `Salvetti/CrossCompare`
shows is a merge.
-/

open CategoryTheory Equiv Opposite BPSet ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## The two presentations -/

/-- The decorated cube's chains, as a presheaf on the germ presentation of the base. -/
noncomputable abbrev hbpGermPd (n : ℕ) : Quotient germRel ⥤ Type :=
  locGermPresentation.functor ⋙ wedgeHomsDescend (Hbp.obj (□n)) (isSegal_H_cube n)

/-- …and on the Artin presentation of the base. -/
noncomputable abbrev hbpArtinPd (n : ℕ) : Quotient artinPathRel ⥤ Type :=
  locArtinPresentation.functor ⋙ wedgeHomsDescend (Hbp.obj (□n)) (isSegal_H_cube n)

/-- **`Ch(Hbp □ⁿ)[W⁻¹]` is presented by the adjacent transpositions acting on a decorated
chain**, modulo commutation and braid. -/
noncomputable def hbpArtinPresentation (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌
      (Quotient (totalRel artinPathRel (hbpArtinPd n)))ᵒᵖ :=
  chLocArtinPresentation (Hbp.obj (□n)) (isSegal_H_cube n)

/-- **…and by the germ generators** — the Garside form: a permutation of a chain's events, modulo
the length-additive products. -/
noncomputable def hbpGermPresentation (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌
      (Quotient (totalRel germRel (hbpGermPd n)))ᵒᵖ :=
  chLocGermPresentation (Hbp.obj (□n)) (isSegal_H_cube n)

/-- **The positive braid action is presented by the atoms at each chamber** — objects the orderings
of the axes, generators an adjacent index at one of them, relations commutation and braid. -/
noncomputable def posBraidActionArtinPresentation (n : ℕ) :
    PosBraidAction n ≌ (Quotient (totalRel artinPathRel (hbpArtinPd n)))ᵒᵖ :=
  (localizationEquivPosBraidAction n).symm.trans (hbpArtinPresentation n)

/-- …and by the simples at each chamber — the Garside form. -/
noncomputable def posBraidActionGermPresentation (n : ℕ) :
    PosBraidAction n ≌ (Quotient (totalRel germRel (hbpGermPd n)))ᵒᵖ :=
  (localizationEquivPosBraidAction n).symm.trans (hbpGermPresentation n)

/-! ## The chain a generator sits at

At strand count `m` the fibre is the decorated chains of `□ⁿ` with `m` unit beads; at `m = n` those
are the runs — the chambers of the braid arrangement (`runHbpCubeEquivPerm`). -/

/-- **An Artin generator at strand count `m` sits at a decorated chain with `m` unit beads.** -/
noncomputable def hbpArtinFibreEquiv (n m : ℕ) :
    Sigma.wordFibre (hbpArtinPd n) m ≃ (⋁(𝟙^m) ⟶ Hbp.obj (□n)) :=
  artinFibreEquiv (Hbp.obj (□n)) (isSegal_H_cube n) m

/-- …and so does a germ generator. -/
noncomputable def hbpGermFibreEquiv (n m : ℕ) :
    Sigma.wordFibre (hbpGermPd n) m ≃ (⋁(𝟙^m) ⟶ Hbp.obj (□n)) :=
  germFibreEquiv (Hbp.obj (□n)) (isSegal_H_cube n) m

/-- **An Artin generator at strand count `n` sits at a chamber** — an ordering of the axes. -/
noncomputable def hbpArtinChamberEquiv (n : ℕ) :
    Sigma.wordFibre (hbpArtinPd n) n ≃ Perm (Fin n) :=
  (hbpArtinFibreEquiv n n).trans (fibreEquiv (onesObj n))

/-- **The Garside reading of a germ generator**: a *simple* — a morphism of the interval
`1ᵐ ⟶ [m]` — acting on a decorated chain. -/
noncomputable def hbpSimpleEdgeEquiv {m : ℕ} (c c' : Sigma.wordFibre (hbpGermPd n) m) :
    (Sigma.wordTotalVtx c ⟶ Sigma.wordTotalVtx c')
      ≃ {s : onesObj m ⟶ topObj m //
          Sigma.wordAct (hbpGermPd n) (FreeMonoid.of (simpleEquivPerm m s)) c = c'} :=
  (Sigma.totalEdgeEquiv c c').trans
    ((simpleEquivPerm m).symm.subtypeEquiv fun σ => by rw [Equiv.apply_symm_apply])

/-! ## Crossing a wall

    cellObj (wallCross w k)
        ↑ wallLeg w k              ↑ wallLegFlip w k
    chamber w                      chamber (w sₖ)

Both legs go *up* into the wall cell.  `topeCross_wallCross`/`topeCross_wallCross_flip` label them
`adjT k` and `1` in the arrangement's order, and `crossPermAt_eq_topeCross` carries those labels to
the flattening order `W` is defined by, so the far leg is a merge (`W_wallLegFlip`) and
inverting it turns the span into an arrow of chambers. -/

/-- The chamber `w`, as an object of the localized decorated chains. -/
noncomputable def chamberLoc (w : Perm (Fin n)) : (W (Hbp.obj (□n))).Localization :=
  (W (Hbp.obj (□n))).Q.obj (cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩))

/-- **Crossing the `k`-th wall of the chamber `w`**: the atom leg, then the merge leg inverted. -/
noncomputable def wallCrossLoc (w : Perm (Fin n)) (k : Fin (n - 1)) :
    chamberLoc w ⟶ chamberLoc (w * adjT k) :=
  letI hiso : IsIso ((W (Hbp.obj (□n))).Q.map (wallLegFlip w k)) :=
    (W (Hbp.obj (□n))).Q_inverts (wallLegFlip w k) (W_wallLegFlip w k)
  (W (Hbp.obj (□n))).Q.map (wallLeg w k) ≫ @inv _ _ _ _ _ hiso

end CubeChains
