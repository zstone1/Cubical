import CubeChains.Machinery.Localization.ElementsPresentation
import Mathlib.CategoryTheory.Action

/-!
# Machinery/Localization/ActionPresentation — a presented monoid presents its action category

`ActionCategory M A` **is** the category of elements of the action functor, so a presentation of
`M` is a presentation of it: vertices the points of `A`, one edge `a ⟶ s • a` per generator `s`,
relations the monoid's read at each point.  Nothing is asked of the action — in particular not
freeness, and not that the stabilizers are trivial.
-/

open CategoryTheory Opposite

namespace CategoryTheory

universe w v u

variable {V : Type u} [Quiver.{v} V] (r : HomRel (Paths V))
  {M : Type*} [Monoid M] {A : Type w} [MulAction M A]

/-- The action functor, read on a presentation of the acting monoid. -/
noncomputable abbrev actionPsh (e : Quotient r ≌ SingleObj M) : Quotient r ⥤ Type w :=
  e.functor ⋙ actionAsFunctor M A

/-- **A presented monoid presents its action category** — generators the monoid's generators
acting at each point, relations the monoid's relations read there.  The action is arbitrary: no
freeness, no triviality of stabilizers. -/
noncomputable def actionCategoryPresentation (e : Quotient r ≌ SingleObj M) :
    Quotient (totalRel r (actionPsh (A := A) r e)) ≌ ActionCategory M A :=
  (elementsPresentation r (actionPsh (A := A) r e)).trans
    (CategoryOfElements.preEquivalenceComp (actionAsFunctor M A) e)

/-! ## Transporting the acting monoid

An isomorphism of acting monoids carries the action category across, so a monoid *presented* by
generators and relations may replace an isomorphic one. -/

variable {N : Type*} [Monoid N] [MulAction N A]

/-- The two action functors agree when the actions do. -/
def actionAsFunctorIso (e : M ≃* N) (h : ∀ (m : M) (a : A), m • a = e m • a) :
    actionAsFunctor M A ≅ (MulEquiv.toSingleObjEquiv e).functor ⋙ actionAsFunctor N A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y f
    ext a
    exact h f a)

/-- **An isomorphism of acting monoids is an equivalence of action categories.** -/
noncomputable def actionCategoryCongr (e : M ≃* N) (h : ∀ (m : M) (a : A), m • a = e m • a) :
    ActionCategory M A ≌ ActionCategory N A :=
  (CategoryOfElements.mapEquivalence (actionAsFunctorIso e h)).trans
    (CategoryOfElements.preEquivalenceComp (actionAsFunctor N A) (MulEquiv.toSingleObjEquiv e))

end CategoryTheory
