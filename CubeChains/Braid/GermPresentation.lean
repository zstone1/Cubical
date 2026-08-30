import CubeChains.Braid.Graded
import CubeChains.Foundations.WordQuiver

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
abbrev GermQuiver : Type := Sigma.WordQuiver fun n : ℕ => Perm (Fin n)

/-- The germ relations, read on paths. -/
def germRel : HomRel (Paths GermQuiver) := Sigma.wordPathRel PosGermRel

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

/-- **The generator is the simple of its permutation** — the identification the presentation is
for. -/
@[simp] theorem germPresentation_map_gen (m : ℕ) (σ : Perm (Fin m)) :
    germPresentation.functor.map
        ((Quotient.functor germRel).map (Sigma.wordPath (FreeMonoid.of σ)))
      = Quiver.Hom.op (Graded.ofVal (posPerm σ)) :=
  rfl

/-- **A transported germ generator's crossing permutation is its own permutation** — the arrow of
`∫Pd` it names lies over the simple of `σ`. -/
theorem germPresentation_val_gen {Pd : Quotient germRel ⥤ Type w} {m : ℕ}
    {c c' : Sigma.wordFibre Pd m} (σ : Perm (Fin m))
    (h : Sigma.wordAct Pd (FreeMonoid.of σ) c = c') :
    germPresentation.functor.map
        (((elementsPresentation germRel Pd).functor.map
          ((Quotient.functor (totalRel germRel Pd)).map (Sigma.totalPath _ h))).val)
      = Quiver.Hom.op (Graded.ofVal (posPerm σ)) := by
  refine Eq.trans ?_ (germPresentation_map_gen m σ)
  exact congrArg (fun g => germPresentation.functor.map g)
    (Sigma.val_elementsPresentation_totalPath (rel := PosGermRel) (Pd := Pd) (FreeMonoid.of σ) h)

end CubeChains
