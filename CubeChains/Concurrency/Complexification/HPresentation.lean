import CubeChains.Concurrency.Presentation.ArtinPresentation
import CubeChains.Concurrency.Presentation.LiftPresentation
import CubeChains.Concurrency.Salvetti.CrossCompare

/-!
# Concurrency/Complexification/HPresentation — `Ch(Hbp □ⁿ)[W⁻¹]`, presented

`isSegal_H_cube` supplies the hypothesis, so every `BraidPresentation` transports: the germ
one — generators all permutations of a chain's events, relations the length-additive products — and
the Artin one, generators an adjacent pair and relations commutation and braid.  Both readings are
literal: `Sigma.totalEdgeEquiv` for the generators, `Sigma.totalRel_word_iff` for the relations, and
`artin_comm`/`artin_braid` for the two families themselves.

⚠ An atom is one leg of a span: `wallCross w k` lies below both chambers it separates, so a
chamber-to-chamber `σₖ` exists only after inverting the other leg — the one
`Concurrency/Salvetti/CrossCompare` shows is a merge.
-/

open CategoryTheory Equiv Opposite BPSet ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## The decorated cube, presented -/

namespace BraidPresentation

variable (P : BraidPresentation)

/-- The decorated cube's chains, as a presheaf on the presented base. -/
noncomputable abbrev hbpPd (n : ℕ) : Quotient P.pathRel ⥤ Type :=
  P.pd (Hbp.obj (□n)) (isSegal_H_cube n)

/-- **`Ch(Hbp □ⁿ)[W⁻¹]` is presented by `P`'s generators acting on a decorated chain.** -/
noncomputable def hbpEquiv (n : ℕ) :
    (W (Hbp.obj (□n))).Localization ≌ (Quotient (totalRel P.pathRel (P.hbpPd n)))ᵒᵖ :=
  P.chLocEquiv (Hbp.obj (□n)) (isSegal_H_cube n)

/-- **The positive braid action is presented by `P`'s generators at each chamber** — objects the
orderings of the axes, generators one of `P`'s at one of them. -/
noncomputable def posBraidActionEquiv (n : ℕ) :
    PosBraidAction n ≌ (Quotient (totalRel P.pathRel (P.hbpPd n)))ᵒᵖ :=
  (localizationEquivPosBraidAction n).symm.trans (P.hbpEquiv n)

/-! ## The chain a generator sits at

At strand count `m` the fibre is the decorated chains of `□ⁿ` with `m` unit beads; at `m = n` those
are the runs — the chambers of the braid arrangement (`runHbpCubeEquivPerm`). -/

/-- **A generator at strand count `m` sits at a decorated chain with `m` unit beads.** -/
noncomputable def hbpFibreEquiv (n m : ℕ) :
    Sigma.wordFibre (P.hbpPd n) m ≃ (⋁(𝟙^m) ⟶ Hbp.obj (□n)) :=
  P.fibreEquiv (Hbp.obj (□n)) (isSegal_H_cube n) m

/-- **A generator at strand count `n` sits at a chamber** — an ordering of the axes. -/
noncomputable def hbpChamberEquiv (n : ℕ) : Sigma.wordFibre (P.hbpPd n) n ≃ Perm (Fin n) :=
  (P.hbpFibreEquiv n n).trans (CubeChains.fibreEquiv (onesObj n))

end BraidPresentation

/-- **The Garside reading of a germ generator**: a *simple* — a morphism of the interval
`1ᵐ ⟶ [m]` — acting on a decorated chain. -/
noncomputable def hbpSimpleEdgeEquiv {m : ℕ}
    (c c' : Sigma.wordFibre (germPresentation.hbpPd n) m) :
    (Sigma.wordTotalVtx c ⟶ Sigma.wordTotalVtx c')
      ≃ {s : onesObj m ⟶ topObj m //
          Sigma.wordAct (germPresentation.hbpPd n) (FreeMonoid.of (simpleEquivPerm m s)) c = c'} :=
  (Sigma.totalEdgeEquiv c c').trans
    ((simpleEquivPerm m).symm.subtypeEquiv fun σ => by rw [Equiv.apply_symm_apply])

/-! ## Crossing a wall

    cellObj (wallCross w k)
        ↑ wallLeg w k              ↑ wallLegFlip w k
    chamber w                      chamber (w sₖ)

Both legs go *up* into the wall cell.  `topeCross_wallCross`/`topeCross_wallCross_flip` label them
`adjT k` and `1` in the arrangement's order, and `crossPerm_eq_topeCross` carries those labels to
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
