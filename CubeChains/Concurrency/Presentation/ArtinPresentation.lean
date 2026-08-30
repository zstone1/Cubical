import CubeChains.Machinery.Braid.GermPresentation
import CubeChains.Machinery.Braid.Matsumoto

/-!
# Concurrency/Presentation/ArtinPresentation — the Artin presentation

`germPresentation` presents `PosBraid` by *all* permutations and the length-additive products;
Matsumoto replaces that by the `n-1` adjacent transpositions and the two Artin families.  Both are
`BraidPresentation`s, so the transport chain runs on either.

The two families are what the germ side has no counterpart for: `Sigma.totalRel_word_iff` says the
imposed relation is `ArtinRel` on the spelled word, and `artin_comm`/`artin_braid` are that
relation read forwards, on the paths that spell the four words.
-/

universe w

open CategoryTheory Equiv

namespace CubeChains

/-- **The Artin presentation**: the `n-1` adjacent transpositions, relators commutation and
braid. -/
noncomputable def artinPresentation : BraidPresentation where
  gen n := Fin (n - 1)
  rel := ArtinRel
  perm := fun {_} => adjT
  monoidEquiv n := (posBraid_equiv_artinPos n).symm
  monoidEquiv_gen _ := rfl

section Relations

variable {Pd : Quotient artinPresentation.pathRel ⥤ Type w} {m : ℕ}
variable {c c' : Sigma.wordFibre Pd m} {i j : Fin (m - 1)}

/-- **Far-apart generators commute**: `σᵢ` then `σⱼ` and `σⱼ` then `σᵢ` are one arrow. -/
theorem artin_comm (hij : (i : ℕ) + 1 < (j : ℕ))
    (h₁ : Sigma.wordAct Pd (FreeMonoid.of i * FreeMonoid.of j) c = c')
    (h₂ : Sigma.wordAct Pd (FreeMonoid.of j * FreeMonoid.of i) c = c') :
    (Quotient.functor (totalRel artinPresentation.pathRel Pd)).map (Sigma.totalPath _ h₁)
      = (Quotient.functor (totalRel artinPresentation.pathRel Pd)).map (Sigma.totalPath _ h₂) :=
  Sigma.quotient_map_totalPath (ArtinRel.comm i j hij) h₁ h₂

/-- **Consecutive generators braid**: `σᵢσⱼσᵢ` and `σⱼσᵢσⱼ` are one arrow. -/
theorem artin_braid (hij : (j : ℕ) = (i : ℕ) + 1)
    (h₁ : Sigma.wordAct Pd (FreeMonoid.of i * FreeMonoid.of j * FreeMonoid.of i) c = c')
    (h₂ : Sigma.wordAct Pd (FreeMonoid.of j * FreeMonoid.of i * FreeMonoid.of j) c = c') :
    (Quotient.functor (totalRel artinPresentation.pathRel Pd)).map (Sigma.totalPath _ h₁)
      = (Quotient.functor (totalRel artinPresentation.pathRel Pd)).map (Sigma.totalPath _ h₂) :=
  Sigma.quotient_map_totalPath (ArtinRel.braid i j hij) h₁ h₂

end Relations

end CubeChains
