import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Products.Basic

/-!
# Machinery/StrictInverse — what an equivalence gives, and how to build one on the nose

`Functor.inv` is a choice, so an equivalence only inverts up to isomorphism.  Between thin
categories a pair of functors inverting each other *on objects* is already an equivalence: every
coherence is a `Subsingleton.elim`.

The two transports go the other way: thinness and inhabitedness of the hom-sets both cross an
equivalence, which mathlib does not record.

`eqToHom` chains live here too: the same strictness plumbing, stated with the objects free.
-/

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]

/-- **A hom-set of a product is a pair of hom-sets**, so a product of thin categories is thin. -/
instance instIsThinProd {D : Type*} [Category D] [Quiver.IsThin C] [Quiver.IsThin D] :
    Quiver.IsThin (C × D) :=
  fun X Y => inferInstanceAs (Subsingleton ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))

/-- **A hom-set of the opposite is a hom-set**, so the opposite of a thin category is thin. -/
instance instIsThinOp [Quiver.IsThin C] : Quiver.IsThin Cᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

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

/-- **…and so is one inverting only up to isomorphism**, which is what a localization gives when
its objects are named by representatives rather than by a normal form. -/
def Equivalence.ofThinInverse [Quiver.IsThin C] [Quiver.IsThin E] (F : C ⥤ E) (G : E ⥤ C)
    (h₁ : ∀ X, X ≅ G.obj (F.obj X)) (h₂ : ∀ Y, F.obj (G.obj Y) ≅ Y) : C ≌ E where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents h₁ fun _ => Subsingleton.elim _ _
  counitIso := NatIso.ofComponents h₂ fun _ => Subsingleton.elim _ _
  functor_unitIso_comp _ := Subsingleton.elim _ _

/-! ## Chains of transports

`eqToHom_trans` rewrites a chain one link at a time, which a bundled setting (`Cat`-coerced objects,
say) defeats: the objects are `rfl`-equal but not syntactically equal and `kabstract` will not
unfold the coercion.  These state a whole chain at once with the objects *free*, so `exact` unifies
them at default transparency where `rw` cannot. -/

/-- **A chain of transports is pinned by its endpoints.** -/
theorem eqToHom_comp₃ {C : Type*} [Category C] {W X Y Z : C} (p : W = X) (q : X = Y) (r : Y = Z)
    (s : W = Z) : eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom s := by
  subst p; subst q; subst r; simp

/-- **A transport there and back cancels.** -/
theorem eqToHom_comp_cancel {C : Type*} [Category C] {A B Z : C} (p : A = B) (q : B = A)
    (g : A ⟶ Z) : eqToHom p ≫ eqToHom q ≫ g = g := by
  subst p; simp

/-- …and a chain in front of an arrow is a transport. -/
theorem eqToHom_comp₃_comp {C : Type*} [Category C] {W X Y Z Z' : C} (p : W = X) (q : X = Y)
    (r : Y = Z) (g : Z ⟶ Z') (s : W = Z) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r ≫ g = eqToHom s ≫ g := by
  subst p; subst q; subst r; simp

/-- …and one behind it cancels. -/
theorem comp_eqToHom₂ {C : Type*} [Category C] {W X Y : C} (g : W ⟶ X) (p : X = Y) (q : Y = X) :
    g ≫ eqToHom p ≫ eqToHom q = g := by
  subst p; simp

/-- …so two chains in front of one arrow agree. -/
theorem eqToHom_comp₃_comp_eq {C : Type*} [Category C] {W X Y Z Z' X' Y' : C} (p : W = X)
    (q : X = Y) (r : Y = Z) (g : Z ⟶ Z') (p' : W = X') (q' : X' = Y') (r' : Y' = Z) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r ≫ g = eqToHom p' ≫ eqToHom q' ≫ eqToHom r' ≫ g := by
  subst p; subst q; subst r; subst p'; subst q'; simp

/-- **A 1-cell read at other names for its endpoints is a transport conjugate** — `Quiver.homOfEq`,
which is what a `Prefunctor` extensionality asks for, said with `eqToHom`. -/
theorem homOfEq_eq_eqToHom_conj {C : Type*} [Category C] {A B A' B' : C} (g : A' ⟶ B')
    (hA : A = A') (hB : B = B') :
    Quiver.homOfEq g hA.symm hB.symm = eqToHom hA ≫ g ≫ eqToHom hB.symm := by
  subst hA; subst hB; simp

/-- **The inverse of a transport conjugate is the conjugate of the inverse.** -/
theorem Iso.inv_eqToHom_conj {C : Type*} [Category C] {A B A' B' : C} (i : A ≅ B) (i' : A' ≅ B')
    (hA : A = A') (hB : B = B')
    (hf : i.hom = eqToHom hA ≫ i'.hom ≫ eqToHom hB.symm) :
    i.inv = eqToHom hB ≫ i'.inv ≫ eqToHom hA.symm := by
  subst hA; subst hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf ⊢
  exact (Iso.inv_eq_inv i i').mpr hf

/-- **A chain of transports around an identity is a transport.** -/
theorem eqToHom_map_id_chain {C D : Type*} [Category C] [Category D] (G : D ⥤ C) {X : D}
    {A B E Z : C} (p : A = B) (q : B = G.obj X) (r : G.obj X = E) (h : E ⟶ Z) (hAE : A = E) :
    eqToHom p ≫ eqToHom q ≫ G.map (𝟙 X) ≫ eqToHom r ≫ h = eqToHom hAE ≫ h := by
  subst p; subst q; subst r
  rw [Functor.map_id]
  simp

/-- …and one with nothing after it. -/
theorem eqToHom_map_id_conj {C D : Type*} [Category C] [Category D] (G : D ⥤ C) {X : D}
    {A B : C} (p : A = G.obj X) (q : G.obj X = B) (r : A = B) :
    eqToHom p ≫ G.map (𝟙 X) ≫ eqToHom q = eqToHom r := by
  subst p; subst q; rw [Functor.map_id]; simp

end CategoryTheory
