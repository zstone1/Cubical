import CubeChains.Machinery.Graded
import CubeChains.Machinery.Localization.WordQuiver

/-!
# Machinery/Braid/BraidPresentation — the positive braid monoids, presented

A presentation of `PosBraid` is generators graded by strand count, each crossing a permutation,
with relators on words in them.  `FullPosBraid` is the coproduct over the strand counts of the
one-object categories on `PosBraid n`, so any such family presents it: one vertex per strand count,
a loop per generator, no morphisms between counts.  It is the **opposite** that is presented — a
path spells its word in order only there.  The whole transport chain, down to `Ch K[W⁻¹]` and the
chambers of the braid arrangement, is stated of an arbitrary one; `germPresentation` and
`artinPresentation` are the instances.
-/

universe w

open CategoryTheory Equiv

namespace CubeChains

/-- **A presentation of the positive braid monoids.** -/
structure BraidPresentation where
  /-- The generators at each strand count. -/
  gen : ℕ → Type
  /-- The relators, between words in the generators. -/
  rel : ∀ n, FreeMonoid (gen n) → FreeMonoid (gen n) → Prop
  /-- The permutation a generator crosses. -/
  perm : ∀ {n : ℕ}, gen n → Perm (Fin n)
  /-- The presented monoid is the positive braid monoid… -/
  monoidEquiv : ∀ n, PresentedMonoid (rel n) ≃* PosBraid n
  /-- …carrying each generator to the simple of its permutation. -/
  monoidEquiv_gen : ∀ {n : ℕ} (a : gen n),
    monoidEquiv n (PresentedMonoid.of _ a) = posPerm (perm a)

namespace BraidPresentation

variable (P : BraidPresentation)

/-- The relators, read on paths of the presenting quiver: one vertex per strand count, a loop for
each generator. -/
def pathRel : HomRel (Paths (Sigma.WordQuiver P.gen)) := Sigma.wordPathRel P.rel

/-- **The positive braid monoids are presented** — degreewise, and with no morphisms between
degrees.

    Quotient P.pathRel ≌ Σₙ Quotient (pathRel (P.rel n))       -- Sigma.presentation
                       ≌ Σₙ (SingleObj (PresentedMonoid _))ᵒᵖ  -- presentedMonoidPresentation
                       ≌ (Σₙ SingleObj (PresentedMonoid _))ᵒᵖ  -- Sigma.opEquiv
                       ≌ FullPosBraidᵒᵖ                        -- sigmaEquivalence, Graded.congr
-/
noncomputable def equiv : Quotient P.pathRel ≌ FullPosBraidᵒᵖ :=
  (Sigma.presentation _).trans <|
    (((Sigma.Functor.sigma' fun n =>
          (SingleObj.presentedMonoidPresentation (P.rel n)).functor).asEquivalence.trans
        Sigma.opEquiv).trans
      (Graded.sigmaEquivalence.trans (Graded.congr P.monoidEquiv)).op)

/-- **The generator is the simple of its permutation** — the identification the presentation is
for. -/
@[simp] theorem map_gen (m : ℕ) (a : P.gen m) :
    P.equiv.functor.map
        ((Quotient.functor P.pathRel).map (Sigma.wordPath (FreeMonoid.of a)))
      = Quiver.Hom.op (Graded.ofVal (posPerm (P.perm a))) :=
  congrArg (fun b : PosBraid m => Quiver.Hom.op (Graded.ofVal b)) (P.monoidEquiv_gen a)

/-- **A transported generator's crossing permutation is its own** — the arrow of `∫Pd` it names
lies over the simple of `P.perm a`. -/
theorem val_gen {Pd : Quotient P.pathRel ⥤ Type w} {m : ℕ} {c c' : Sigma.wordFibre Pd m}
    (a : P.gen m) (h : Sigma.wordAct Pd (FreeMonoid.of a) c = c') :
    P.equiv.functor.map
        (((elementsPresentation P.pathRel Pd).functor.map
          ((Quotient.functor (totalRel P.pathRel Pd)).map (Sigma.totalPath _ h))).val)
      = Quiver.Hom.op (Graded.ofVal (posPerm (P.perm a))) :=
  Eq.trans
    (congrArg P.equiv.functor.map
      (Sigma.val_elementsPresentation_totalPath (rel := P.rel) (Pd := Pd) (FreeMonoid.of a) h))
    (P.map_gen m a)

end BraidPresentation

end CubeChains
