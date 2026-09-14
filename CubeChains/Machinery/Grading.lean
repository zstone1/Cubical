import Mathlib.Algebra.Group.Nat.TypeTags
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Localization.Construction

/-!
# Machinery/Grading — codimension, once

A **grading** is a functor to `Grade`, the delooping of `(ℕ, +)`; `codim` reads its value on a
morphism additively, so that `omega` can use it.  `ofRise` builds one from an object degree that
morphisms only ever raise; `op` carries one to the opposite category; the vanishing on isomorphisms
is then formal.
-/

universe v v' u u'

open CategoryTheory

/-- The delooping of `(ℕ, +)` — the receptacle of every grading. -/
abbrev Grade : Type := SingleObj (Multiplicative ℕ)

/-- A functor into a one-object category is determined by its action on morphisms. -/
theorem grade_ext {C : Type u} [Category.{v} C] {F G : C ⥤ Grade}
    (h : ∀ {X Y : C} (f : X ⟶ Y), F.map f = G.map f) : F = G := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  change F.map f = 𝟙 _ ≫ G.map f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, h f]

/-- Multiplication with both arguments pinned to `Multiplicative ℕ`; instance search will not
unfold `star ⟶ star` on its own. -/
def gradeMul (x y : Multiplicative ℕ) : Multiplicative ℕ := x * y

/-- Addition of grades. -/
def gradeAdd : Grade × Grade ⥤ Grade where
  obj _ := SingleObj.star _
  map {_ _} f := gradeMul f.1 f.2
  map_id _ := one_mul (1 : Multiplicative ℕ)
  map_comp f g := mul_mul_mul_comm (G := Multiplicative ℕ) g.1 f.1 g.2 f.2

/-- **A grading of a category**: a codimension for every morphism, vanishing on identities and
additive along composition — that is, a functor to `Grade`. -/
abbrev Grading (D : Type u) [Category.{v} D] : Type _ := D ⥤ Grade

namespace Grading

variable {D : Type u} [Category.{v} D] {E : Type u'} [Category.{v'} E]

/-- The codimension of a morphism. -/
def codim (G : Grading D) {a b : D} (f : a ⟶ b) : ℕ := Multiplicative.toAdd (G.map f)

theorem codim_id (G : Grading D) (a : D) : G.codim (𝟙 a) = 0 :=
  congrArg Multiplicative.toAdd (G.map_id a)

theorem codim_comp (G : Grading D) {a b c : D} (f : a ⟶ b) (g : b ⟶ c) :
    G.codim (f ≫ g) = G.codim f + G.codim g :=
  (congrArg Multiplicative.toAdd (G.map_comp f g)).trans (Nat.add_comm _ _)

/-- **The degree gained**, for an object degree that morphisms never lower. -/
def ofRise (deg : D → ℕ) (h : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b) : Grading D where
  obj _ := SingleObj.star (Multiplicative ℕ)
  map {a b} _ := Multiplicative.ofAdd (deg b - deg a)
  map_id a := congrArg Multiplicative.ofAdd (Nat.sub_self (deg a))
  map_comp {a b c} f g := congrArg Multiplicative.ofAdd
    (by have := h f; have := h g; omega : deg c - deg a = (deg c - deg b) + (deg b - deg a))

@[simp] theorem codim_ofRise (deg : D → ℕ) (h : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b)
    {a b : D} (f : a ⟶ b) : (ofRise deg h).codim f = deg b - deg a := rfl

/-- The grading of the opposite category — `map_comp` is `Nat.add_comm`, since instance search will
not see the `CommMagma` on a `star ⟶ star`. -/
def op (G : Grading D) : Grading Dᵒᵖ where
  obj _ := SingleObj.star (Multiplicative ℕ)
  map f := G.map f.unop
  map_id a := G.map_id a.unop
  map_comp f g := by
    change G.map (g.unop ≫ f.unop) = _
    rw [G.map_comp, SingleObj.comp_as_mul, SingleObj.comp_as_mul]
    exact Nat.add_comm _ _

/-- **An isomorphism has codimension zero** — its two halves' codimensions add to that of `𝟙`. -/
theorem codim_eq_zero_of_isIso (G : Grading D) {a b : D} (f : a ⟶ b) [IsIso f] :
    G.codim f = 0 := by
  have h := G.codim_comp f (inv f)
  rw [IsIso.hom_inv_id, G.codim_id] at h
  omega

/-- **A morphism of positive codimension is not invertible.** -/
theorem not_isIso_of_codim_ne_zero (G : Grading D) {a b : D} (f : a ⟶ b) (h : G.codim f ≠ 0) :
    ¬ IsIso f := fun _ => h (G.codim_eq_zero_of_isIso f)

end Grading

/-! ## A degree constant on `W` descends to the localization

An object degree in any preorder that arrows only ever lower, and that `W` leaves alone, survives
inverting `W`: a `W`-arrow cannot raise it either, so the degree is a functor on `C[W⁻¹]` and a
hom-set that would have to raise it is **empty**.  That is how a localization is shown disconnected
without computing any of its hom-sets, and — at a degree valued in the weak order rather than in
`ℕ` — how it is identified with a poset. -/

section Localized

variable {D : Type u} [Category.{v} D] {P : Type u'} [Preorder P] (deg : D → P)
  (hfall : ∀ {a b : D}, (a ⟶ b) → deg b ≤ deg a)

/-- A falling degree, as a functor to `Pᵒᵖ`. -/
def degFunctor : D ⥤ Pᵒᵖ where
  obj a := Opposite.op (deg a)
  map f := (homOfLE (hfall f)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable (W : MorphismProperty D) (hW : ∀ {a b : D} {f : a ⟶ b}, W f → deg a ≤ deg b)

include hW in
theorem degFunctor_inverts : W.IsInvertedBy (degFunctor deg hfall) :=
  fun _ _ _ hf => ⟨(homOfLE (hW hf)).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- **The degree, on the localization.** -/
noncomputable def degLoc : W.Localization ⥤ Pᵒᵖ :=
  Localization.Construction.lift _ (degFunctor_inverts deg hfall W hW)

include hfall hW in
theorem deg_le_of_loc_hom {a b : D} (g : W.Q.obj a ⟶ W.Q.obj b) : deg b ≤ deg a :=
  leOfHom ((degLoc deg hfall W hW).map g).unop

include hfall hW in
/-- **A hom-set of the localization is empty** when it would have to raise the degree — so a
strictly falling degree witnesses that the localization is disconnected. -/
theorem isEmpty_loc_hom_of_deg_lt {a b : D} (h : ¬ deg b ≤ deg a) :
    IsEmpty (W.Q.obj a ⟶ W.Q.obj b) :=
  ⟨fun g => absurd (deg_le_of_loc_hom deg hfall W hW g) h⟩

end Localized
