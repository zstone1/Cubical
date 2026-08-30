import Mathlib.Algebra.Group.Nat.TypeTags
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Opposites

/-!
# Machinery/Grading — codimension, once

A **grading** gives every morphism a natural number, additive along composition — that is, a functor
to `Grade`, the delooping of `(ℕ, +)`, spelled additively so that `omega` can use it.  `ofRise` and
`ofFall` build one from an object degree that morphisms only ever raise, or only ever lower; `op`
and `comap` carry one along a functor; the vanishing on isomorphisms is then formal.
-/

universe v v' u u'

open CategoryTheory

/-- The delooping of `(ℕ, +)` — the receptacle of every grading. -/
abbrev Grade : Type := SingleObj (Multiplicative ℕ)

/-- Multiplication with both arguments pinned to `Multiplicative ℕ`; instance search will not
unfold `star ⟶ star` on its own. -/
def gradeMul (x y : Multiplicative ℕ) : Multiplicative ℕ := x * y

/-- A functor into a one-object category is determined by its action on morphisms. -/
theorem grade_ext {C : Type u} [Category.{v} C] {F G : C ⥤ Grade}
    (h : ∀ {X Y : C} (f : X ⟶ Y), F.map f = G.map f) : F = G := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => ?_)
  change F.map f = 𝟙 _ ≫ G.map f ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id, h f]

/-- Addition of grades. -/
def gradeAdd : Grade × Grade ⥤ Grade where
  obj _ := SingleObj.star _
  map {_ _} f := gradeMul f.1 f.2
  map_id _ := one_mul (1 : Multiplicative ℕ)
  map_comp f g := mul_mul_mul_comm (G := Multiplicative ℕ) g.1 f.1 g.2 f.2

/-- **A grading of a category**: a codimension for every morphism, vanishing on identities and
additive along composition.  It *is* a functor to `Grade` (`functor`). -/
structure Grading (D : Type u) [Category.{v} D] where
  /-- The codimension of a morphism. -/
  codim : ∀ {a b : D}, (a ⟶ b) → ℕ
  codim_id : ∀ a : D, codim (𝟙 a) = 0
  codim_comp : ∀ {a b c : D} (f : a ⟶ b) (g : b ⟶ c), codim (f ≫ g) = codim f + codim g

namespace Grading

variable {D : Type u} [Category.{v} D] {E : Type u'} [Category.{v'} E]

/-- **The grading, delooped** — `codim_id` and `codim_comp` are exactly the two functor laws. -/
def functor (G : Grading D) : D ⥤ Grade where
  obj _ := SingleObj.star (Multiplicative ℕ)
  map f := Multiplicative.ofAdd (G.codim f)
  map_id a := congrArg Multiplicative.ofAdd (G.codim_id a)
  map_comp f g := by
    change Multiplicative.ofAdd (G.codim (f ≫ g))
      = Multiplicative.ofAdd (G.codim g) * Multiplicative.ofAdd (G.codim f)
    rw [G.codim_comp]
    exact congrArg Multiplicative.ofAdd (Nat.add_comm _ _)

/-- **The degree gained**, for an object degree that morphisms never lower. -/
def ofRise (deg : D → ℕ) (h : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b) : Grading D where
  codim {a b} _ := deg b - deg a
  codim_id _ := Nat.sub_self _
  codim_comp f g := by
    have := h f
    have := h g
    omega

/-- **…and the degree lost**, for one that morphisms never raise. -/
def ofFall (deg : D → ℕ) (h : ∀ {a b : D}, (a ⟶ b) → deg b ≤ deg a) : Grading D where
  codim {a b} _ := deg a - deg b
  codim_id _ := Nat.sub_self _
  codim_comp f g := by
    have := h f
    have := h g
    omega

/-- The same grading, read on the opposite category. -/
def op (G : Grading D) : Grading Dᵒᵖ where
  codim f := G.codim f.unop
  codim_id a := G.codim_id a.unop
  codim_comp f g := (G.codim_comp g.unop f.unop).trans (Nat.add_comm _ _)

/-- The grading pulled back along a functor. -/
def comap (G : Grading D) (F : E ⥤ D) : Grading E where
  codim f := G.codim (F.map f)
  codim_id a := by rw [F.map_id]; exact G.codim_id _
  codim_comp f g := by rw [F.map_comp]; exact G.codim_comp _ _

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
