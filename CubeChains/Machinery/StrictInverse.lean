import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EqToHom

/-!
# Machinery/StrictInverse — what an equivalence gives, and how to build one on the nose

`Functor.inv` is a choice, so an equivalence only inverts up to isomorphism.  Between thin
categories a pair of functors inverting each other *on objects* is already an equivalence: every
coherence is a `Subsingleton.elim`.

The two transports go the other way: thinness and inhabitedness of the hom-sets both cross an
equivalence, which mathlib does not record.
-/

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]

/-- **Thinness transports along an equivalence** — a hom-set of `E` is separated by the inverse
functor. -/
theorem isThin_of_equiv (e : C ≌ E) [Quiver.IsThin C] : Quiver.IsThin E :=
  fun _ _ => ⟨fun _ _ => e.inverse.map_injective (Subsingleton.elim _ _)⟩

/-- **Inhabitedness transports along an equivalence** — the functor is fully faithful, so a hom-set
of `E` has a preimage. -/
theorem nonempty_hom_of_equiv (e : C ≌ E) (h : ∀ X Y : C, Nonempty (X ⟶ Y)) (A B : E) :
    Nonempty (A ⟶ B) :=
  ⟨e.symm.fullyFaithfulFunctor.preimage (h _ _).some⟩

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
