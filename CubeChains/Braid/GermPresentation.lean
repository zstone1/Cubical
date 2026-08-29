import CubeChains.Braid.Graded
import CubeChains.Foundations.MonoidPresentation
import CubeChains.Foundations.SigmaPresentation

/-!
# Braid/GermPresentation — the positive braid monoids, presented

`FullPosBraid` is the coproduct over the strand counts of the one-object categories on
`PosBraid n = PresentedMonoid (PosGermRel n)`, so it is presented by the germ relations: one vertex
per strand count, a loop for each permutation, `σ` then `τ` equal to `στ` at every length-additive
product.  It is the **opposite** that is presented — a path spells its word in order only there.
-/

open CategoryTheory Equiv

namespace CubeChains

/-- The germ quiver: one vertex per strand count, a loop for each permutation. -/
abbrev GermQuiver : Type := Sigma.Quiv fun n : ℕ => SingleObj (Perm (Fin n))

/-- The germ relations, read on paths. -/
def germRel : HomRel (Paths GermQuiver) :=
  Sigma.pathRel fun n => SingleObj.pathRel (PosGermRel n)

/-- **The positive braid monoids are presented by the germ relations** — degreewise, and with no
morphisms between degrees.

    Quotient germRel ≌ Σₙ Quotient (pathRel (PosGermRel n))     -- Sigma.presentation
                     ≌ Σₙ (SingleObj (PosBraid n))ᵒᵖ            -- presentedMonoidPresentation
                     ≌ (Σₙ SingleObj (PosBraid n))ᵒᵖ            -- Sigma.opEquiv
                     ≌ FullPosBraidᵒᵖ                           -- Graded.sigmaEquivalence
-/
noncomputable def germPresentation : Quotient germRel ≌ FullPosBraidᵒᵖ :=
  (Sigma.presentation _).trans <|
    (((Sigma.Functor.sigma' fun n =>
          (SingleObj.presentedMonoidPresentation (PosGermRel n)).functor).asEquivalence.trans
        Sigma.opEquiv).trans
      Graded.sigmaEquivalence.op)

end CubeChains
