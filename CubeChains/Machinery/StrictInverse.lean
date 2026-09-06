import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EqToHom

/-!
# Machinery/StrictInverse — inverting on the nose, between thin categories

`Functor.inv` is a choice, so an equivalence only inverts up to isomorphism.  Between thin
categories a pair of functors inverting each other *on objects* is already an equivalence: every
coherence is a `Subsingleton.elim`.
-/

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]

/-- **A strictly inverse pair between thin categories is an equivalence**: thinness makes every
coherence a `Subsingleton.elim`, so the two object round trips are the only data. -/
def Equivalence.ofStrictInverse [Quiver.IsThin C] [Quiver.IsThin E] (F : C ⥤ E) (G : E ⥤ C)
    (h₁ : ∀ X, G.obj (F.obj X) = X) (h₂ : ∀ Y, F.obj (G.obj Y) = Y) : C ≌ E where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents (fun X => eqToIso (h₁ X).symm) fun _ => Subsingleton.elim _ _
  counitIso := NatIso.ofComponents (fun Y => eqToIso (h₂ Y)) fun _ => Subsingleton.elim _ _
  functor_unitIso_comp _ := Subsingleton.elim _ _

end CategoryTheory
