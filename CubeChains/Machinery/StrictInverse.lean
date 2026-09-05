import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EqToHom

/-!
# Machinery/StrictInverse — a fully faithful functor bijective on objects is invertible

`Functor.inv` is a choice, so an equivalence only inverts up to isomorphism.  A functor that is
also **bijective on objects** inverts on the nose, and then a commuting square inverts to a
commuting square rather than to a mate.  That is what lets `Glue`'s retraction be a strict
`OverCoconeLoc` instead of a pseudo-cocone.
-/

universe v u v' u' v'' u''

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

/-- **The strict inverse** of a fully faithful functor that is bijective on objects. -/
noncomputable def strictInv (F : C ⥤ E) [F.Full] [F.Faithful]
    (h : Function.Bijective F.obj) : E ⥤ C where
  obj Y := (Equiv.ofBijective F.obj h).symm Y
  map {Y Y'} f :=
    F.preimage (eqToHom ((Equiv.ofBijective F.obj h).apply_symm_apply Y) ≫ f ≫
      eqToHom ((Equiv.ofBijective F.obj h).apply_symm_apply Y').symm)
  map_id _ := F.map_injective (by simp)
  map_comp _ _ := F.map_injective (by simp)

@[simp] theorem comp_strictInv (F : C ⥤ E) [F.Full] [F.Faithful]
    (h : Function.Bijective F.obj) : F ⋙ strictInv F h = 𝟭 C :=
  Functor.ext (fun X => (Equiv.ofBijective F.obj h).symm_apply_apply X) fun _ _ _ =>
    F.map_injective (by simp [strictInv, eqToHom_map])

@[simp] theorem strictInv_comp (F : C ⥤ E) [F.Full] [F.Faithful]
    (h : Function.Bijective F.obj) : strictInv F h ⋙ F = 𝟭 E :=
  Functor.ext (fun Y => (Equiv.ofBijective F.obj h).apply_symm_apply Y) fun _ _ _ => by
    simp [strictInv]

/-- Postcomposing with such an `F` is injective on functors — this is what lets a square be
inverted strictly. -/
theorem comp_right_injective {A : Type u''} [Category.{v''} A] (F : C ⥤ E) [F.Full] [F.Faithful]
    (h : Function.Bijective F.obj) {G G' : A ⥤ C} (hG : G ⋙ F = G' ⋙ F) : G = G' := by
  have hK : ∀ K : A ⥤ C, K = (K ⋙ F) ⋙ strictInv F h := fun K => by
    rw [Functor.assoc, comp_strictInv, Functor.comp_id]
  rw [hK G, hG, ← hK G']

/-- **A commuting square inverts to a commuting square.**  This is where `mateEquiv` would be
needed if the vertical functors were merely equivalences. -/
theorem strictInv_square {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
    {E₁ : A ⥤ A'} {E₂ : B ⥤ B'} [E₁.Full] [E₁.Faithful] [E₂.Full] [E₂.Faithful]
    (h₁ : Function.Bijective E₁.obj) (h₂ : Function.Bijective E₂.obj) (G : A ⥤ B) (H : A' ⥤ B')
    (hsq : G ⋙ E₂ = E₁ ⋙ H) :
    H ⋙ strictInv E₂ h₂ = strictInv E₁ h₁ ⋙ G :=
  comp_right_injective E₂ h₂ (by
    rw [Functor.assoc, strictInv_comp, Functor.comp_id, Functor.assoc, hsq, ← Functor.assoc,
      strictInv_comp, Functor.id_comp])

end CategoryTheory
