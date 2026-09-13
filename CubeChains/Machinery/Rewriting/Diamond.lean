import CubeChains.Machinery.Rewriting.Newman
import Mathlib.CategoryTheory.Thin

/-!
# Machinery/Rewriting/Diamond — diamonds on codimension-one steps make a category thin

A `StepDiagram` is a `ℕ`-graded step relation with an object per vertex and an arrow per step; a
`Path` is a word of steps and `ev` its composite.  `HasDiamonds` says two distinct steps out of a
vertex are joined by paths spelling **one** arrow, over a join that absorbs everything both steps
reach.  Then two paths with the same endpoints spell one arrow, and a category whose objects are
covered by the vertices and whose arrows are all paths is thin.

    a ──▸ b ──▸ ⋯ ──▸ t    the two first steps close over the join `d`,
    └───▸ c ──▸ d ──▸ t    which reaches `t` because `b` and `c` both do

Absorption is strictly stronger than confluence: it is what a graded poset of classes supplies and
what Newman's lemma does not.  A step being a `Prop` is load-bearing — it is why two words with a
common first step have the *same* first arrow, with no index to compare.
-/

universe v u w

open CategoryTheory

namespace Relation

/-- A `ℕ`-graded relation with an object for each vertex and an arrow for each step. -/
structure StepDiagram (V : Type w) (C : Type u) [Category.{v} C] where
  /-- The object a vertex carries. -/
  obj : V → C
  /-- The codimension-one steps. -/
  Step : V → V → Prop
  /-- The arrow a step carries. -/
  arr : ∀ {a b : V}, Step a b → (obj a ⟶ obj b)
  /-- The grading a step drops. -/
  deg : V → ℕ
  deg_step : ∀ {a b : V}, Step a b → deg b < deg a

namespace StepDiagram

variable {V : Type w} {C : Type u} [Category.{v} C] (D : StepDiagram V C)

/-- A word of steps. -/
inductive Path (D : StepDiagram V C) : V → V → Type w
  | nil {a : V} : Path D a a
  | cons {a b c : V} (h : D.Step a b) (P : Path D b c) : Path D a c

namespace Path

variable {D}

/-- The arrow a word composes to. -/
def ev : ∀ {a b : V}, Path D a b → (D.obj a ⟶ D.obj b)
  | _, _, .nil => 𝟙 _
  | _, _, .cons h P => D.arr h ≫ ev P

@[simp] theorem ev_nil {a : V} : (Path.nil : Path D a a).ev = 𝟙 (D.obj a) := rfl

@[simp] theorem ev_cons {a b c : V} (h : D.Step a b) (P : Path D b c) :
    (Path.cons h P).ev = D.arr h ≫ P.ev := rfl

/-- Words concatenate. -/
def comp : ∀ {a b c : V}, Path D a b → Path D b c → Path D a c
  | _, _, _, .nil, Q => Q
  | _, _, _, .cons h P, Q => .cons h (P.comp Q)

theorem ev_comp : ∀ {a b c : V} (P : Path D a b) (Q : Path D b c),
    (P.comp Q).ev = P.ev ≫ Q.ev
  | _, _, _, .nil, Q => (Category.id_comp _).symm
  | _, _, _, .cons h P, Q => by
      rw [comp, ev_cons, ev_cons, ev_comp P Q, Category.assoc]

/-- **A word never raises the grading**, so it cannot return to its start after a step. -/
theorem deg_le {a b : V} (P : Path D a b) : D.deg b ≤ D.deg a := by
  induction P with
  | nil => exact Nat.le_refl _
  | cons h _ ih => exact Nat.le_trans ih (Nat.le_of_lt (D.deg_step h))

/-- **A word is a reduction.** -/
theorem toReflTransGen {a b : V} (P : Path D a b) : ReflTransGen D.Step a b := by
  induction P with
  | nil => exact .refl
  | cons h _ ih => exact ReflTransGen.head h ih

/-- **…and every reduction is spelled by one.** -/
theorem nonempty_of_reflTransGen {a b : V} (h : ReflTransGen D.Step a b) :
    Nonempty (Path D a b) := by
  induction h with
  | refl => exact ⟨.nil⟩
  | tail _ hbc ih => exact ih.elim fun P => ⟨P.comp (.cons hbc .nil)⟩

end Path

/-- **The diamond**: two distinct steps out of a vertex are joined by words spelling one arrow, and
the join reaches everything both steps reach. -/
def HasDiamonds : Prop :=
  ∀ ⦃a b c : V⦄ (hb : D.Step a b) (hc : D.Step a c), b ≠ c →
    ∃ (d : V) (P : Path D b d) (Q : Path D c d),
      D.arr hb ≫ P.ev = D.arr hc ≫ Q.ev ∧
      ∀ ⦃e : V⦄, ReflTransGen D.Step b e → ReflTransGen D.Step c e →
        ReflTransGen D.Step d e

variable {D}

/-- **Two words with the same endpoints spell one arrow** — induction on the source's grading: a
shared first step reduces (the steps being `Prop`s, the first arrows are literally equal), and
distinct first steps are closed over the diamond's join, which the common target is below. -/
theorem Path.ev_eq (hD : D.HasDiamonds) :
    ∀ (N : ℕ) {a b : V}, D.deg a ≤ N → ∀ P Q : Path D a b, P.ev = Q.ev := by
  intro N
  induction N with
  | zero =>
      intro a b hN P Q
      cases P with
      | nil => cases Q with
        | nil => rfl
        | cons h Q₀ => exact absurd (D.deg_step h) (by omega)
      | cons h P₀ => exact absurd (D.deg_step h) (by omega)
  | succ N ih =>
      intro a b hN P Q
      cases P with
      | nil =>
          cases Q with
          | nil => rfl
          | cons h Q₀ => exact absurd Q₀.deg_le (by have := D.deg_step h; omega)
      | @cons _ c _ hb P₀ =>
          cases Q with
          | nil => exact absurd P₀.deg_le (by have := D.deg_step hb; omega)
          | @cons _ c' _ hc Q₀ =>
              by_cases hcc : c = c'
              · subst hcc
                rw [ev_cons, ev_cons, ih (by have := D.deg_step hb; omega) P₀ Q₀]
              · obtain ⟨d, R, R', harr, habs⟩ := hD hb hc hcc
                obtain ⟨S⟩ := Path.nonempty_of_reflTransGen
                  (habs P₀.toReflTransGen Q₀.toReflTransGen)
                rw [ev_cons, ev_cons,
                  ih (by have := D.deg_step hb; omega) P₀ (R.comp S),
                  ih (by have := D.deg_step hc; omega) Q₀ (R'.comp S),
                  ev_comp, ev_comp, ← Category.assoc, ← Category.assoc, harr]

/-- **Diamonds make the category thin**: every object is some vertex's up to isomorphism, every
arrow between vertices' objects is some word's, and two words agree. -/
theorem isThin_of_hasDiamonds (hD : D.HasDiamonds)
    (hobj : ∀ X : C, ∃ a : V, Nonempty (D.obj a ≅ X))
    (hfull : ∀ (a b : V) (f : D.obj a ⟶ D.obj b), ∃ P : Path D a b, P.ev = f) :
    Quiver.IsThin C := by
  intro X Y
  obtain ⟨a, ⟨eX⟩⟩ := hobj X
  obtain ⟨b, ⟨eY⟩⟩ := hobj Y
  refine ⟨fun f g => ?_⟩
  obtain ⟨P, hP⟩ := hfull a b (eX.hom ≫ f ≫ eY.inv)
  obtain ⟨Q, hQ⟩ := hfull a b (eX.hom ≫ g ≫ eY.inv)
  have hkey : eX.hom ≫ f ≫ eY.inv = eX.hom ≫ g ≫ eY.inv := by
    rw [← hP, ← hQ, Path.ev_eq hD (D.deg a) (Nat.le_refl _) P Q]
  exact (cancel_mono eY.inv).mp ((cancel_epi eX.hom).mp hkey)

end StepDiagram

end Relation
