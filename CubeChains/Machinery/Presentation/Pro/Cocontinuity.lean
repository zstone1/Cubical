import CubeChains.Machinery.Presentation.Pro.Free
import CubeChains.Machinery.Presentation.Adjunction
import CubeChains.Machinery.Presentation.Coproduct
import Mathlib.CategoryTheory.Category.Cat.Colimit

/-!
# Machinery/Presentation/Pro/Cocontinuity — SCOPING PROTOTYPE: what a pro layer does to colimits

`unfoldFunctor` sends a pro-graph to the 2-polygraph its free 2-category is presented by, so a
diagram of pro-graphs *is* a diagram of polygraphs and `presentsProColimit` is `presentsColimit`
verbatim — the extra dimension buys no new engine and asks no weaker hypothesis.

What it does change is **which colimit** the statement is about.  `unfold` is constant in dimension
zero (`unfold_V`: a pro has one 0-cell, so every unfolded polygraph has `ℕ`) while a colimit of
polygraphs takes the colimit of the 0-cells (`Polygraph.coproduct` has `Σ i, (P i).V`).  So
`unfold (colim F)` is not `colim (unfold ∘ F)`, and a colimit taken in pros is not the colimit of
the underlying categories: `mixed_commute` exhibits the extra identification, two generators from
different copies commuting because `UnfoldRel.exch` is indexed by a **pair**.
-/

universe u

namespace CategoryTheory

namespace ProPrototype

open Limits

/-! ## Morphisms of pro-graphs

The 1-cells of a pro are the strand counts, so a morphism is identity there: only the 2- and
3-cells move.  That is exactly why exchange has nothing to be sent to — `unfoldTwo` carries
`UnfoldRel.exch` to `UnfoldRel.exch` with no choice and no data. -/

/-- A relabelling of the 2-generators, on the positioned generators. -/
def stepPre {P Q : ProGraph} (φ : ∀ {a b : ℕ}, P.Gen a b → Q.Gen a b) :
    GenObj (Step P.Gen) ⥤q GenObj (Step Q.Gen) where
  obj x := ⟨x.as⟩
  map {_ _} s := ⟨s.l, s.a, s.b, s.r, φ s.gen, s.src_eq, s.tgt_eq⟩

/-- **A morphism of pro-graphs**: 2-cells to 2-cells, 3-cells to 3-cells with their boundaries
pushed forward.  There is no field for exchange. -/
structure ProHom (P Q : ProGraph) where
  /-- the 2-cells -/
  gen : ∀ {a b : ℕ}, P.Gen a b → Q.Gen a b
  /-- the 3-cells -/
  rel : ∀ {m n : ℕ}, P.Rel m n → Q.Rel m n
  /-- …with the pushed-forward source -/
  src_rel : ∀ {m n : ℕ} (α : P.Rel m n), Q.src (rel α) = (stepPre gen).mapPath (P.src α)
  /-- …and target -/
  tgt_rel : ∀ {m n : ℕ} (α : P.Rel m n), Q.tgt (rel α) = (stepPre gen).mapPath (P.tgt α)

namespace ProHom

variable {P Q R : ProGraph}

/-- The identity. -/
def id (P : ProGraph) : ProHom P P where
  gen := _root_.id
  rel := _root_.id
  src_rel _ := (Prefunctor.mapPath_id _).symm
  tgt_rel _ := (Prefunctor.mapPath_id _).symm

/-- Composition. -/
def comp (F : ProHom P Q) (G : ProHom Q R) : ProHom P R where
  gen := G.gen ∘ F.gen
  rel := G.rel ∘ F.rel
  src_rel α := (G.src_rel (F.rel α)).trans
    ((congrArg (stepPre G.gen).mapPath (F.src_rel α)).trans
      (Prefunctor.mapPath_comp_apply (stepPre F.gen) (stepPre G.gen) (P.src α)).symm)
  tgt_rel α := (G.tgt_rel (F.rel α)).trans
    ((congrArg (stepPre G.gen).mapPath (F.tgt_rel α)).trans
      (Prefunctor.mapPath_comp_apply (stepPre F.gen) (stepPre G.gen) (P.tgt α)).symm)

end ProHom

instance : Category ProGraph where
  Hom := ProHom
  id := ProHom.id
  comp := ProHom.comp

/-! ## …unfolded

`unfoldTwo` is the whole of the 3-polygraph layer's dimension bookkeeping: a 3-cell goes to a
3-cell, and an exchange square goes to the exchange square of the images.  Nothing is chosen. -/

/-- **Relabelling commutes with positioning** — the two prefunctors touch disjoint fields of a
step, so a word may be positioned before or after it is relabelled. -/
theorem mapPath_stepPre_whisker {P Q : ProGraph} (φ : ∀ {a b : ℕ}, P.Gen a b → Q.Gen a b)
    (l r : ℕ) : ∀ {x y : GenObj (Step P.Gen)} (p : Quiver.Path x y),
    (whiskerLeftPre Q.Gen l).mapPath ((whiskerRightPre Q.Gen r).mapPath ((stepPre φ).mapPath p))
      = (stepPre φ).mapPath
          ((whiskerLeftPre P.Gen l).mapPath ((whiskerRightPre P.Gen r).mapPath p)) := by
  intro x y p
  induction p with
  | nil => rfl
  | cons p e ih => simp only [Prefunctor.mapPath_cons, ih]; rfl

/-- **A morphism, on the 2-cells of the unfolded polygraph** — exchange to exchange. -/
def unfoldTwo {P Q : ProGraph} (F : ProHom P Q) :
    ∀ {x y : GenObj (Step P.Gen)}, UnfoldRel P x y →
      UnfoldRel Q ((stepPre F.gen).obj x) ((stepPre F.gen).obj y)
  | _, _, .exch s t => .exch ((stepPre F.gen).map s) ((stepPre F.gen).map t)
  | _, _, .cell l r α => .cell l r (F.rel α)

/-- **A morphism of pro-graphs, unfolded.** -/
def unfoldMap {P Q : ProGraph} (F : ProHom P Q) : unfold P ⟶ unfold Q where
  pre := stepPre F.gen
  two := unfoldTwo F
  src_two α := by
    cases α with
    | exch s t => rfl
    | cell l r β =>
        change (whiskerLeftPre _ _).mapPath ((whiskerRightPre _ _).mapPath (Q.src (F.rel β))) = _
        rw [F.src_rel β]
        exact mapPath_stepPre_whisker F.gen l r (P.src β)
  tgt_two α := by
    cases α with
    | exch s t => rfl
    | cell l r β =>
        change (whiskerLeftPre _ _).mapPath ((whiskerRightPre _ _).mapPath (Q.tgt (F.rel β))) = _
        rw [F.tgt_rel β]
        exact mapPath_stepPre_whisker F.gen l r (P.tgt β)

/-- **The free 2-category on a pro-graph, read as a 2-polygraph, functorially.** -/
def unfoldFunctor : ProGraph ⥤ Polygraph.{0, 0, 0} where
  obj := unfold
  map := unfoldMap
  map_id _ := Polygraph.Hom.ext' rfl fun α => by cases α <;> exact HEq.rfl
  map_comp _ _ := Polygraph.Hom.ext' rfl fun α => by cases α <;> exact HEq.rfl

/-! ## Cocontinuity

The free pro's underlying category is `(unfold P).presented`, so a diagram of pro-graphs presents a
colimit exactly when its unfolding does.  That is today's theorem, at today's dimension, with
today's hypothesis: the shift up buys no new cocontinuity and asks no weaker naming. -/

/-- **Cocontinuity of `Presents`, one dimension up** — `presentsColimit` on the unfolded diagram.
The hypothesis is unchanged, because the statement is unchanged. -/
noncomputable def presentsProColimit {J : Type} [SmallCategory J] (F : J ⥤ ProGraph) :
    Presents (colimit (F ⋙ unfoldFunctor))
      ↥(colimit (F ⋙ unfoldFunctor ⋙ Polygraph.presentedFunctor.{0, 0})) :=
  Polygraph.presentsColimit (F ⋙ unfoldFunctor)

/-- **…but only for the colimit taken *after* unfolding.**  Every pro has one 0-cell, so `unfold`
is constant in dimension zero, while `Polygraph.coproduct` takes `Σ i, (P i).V`.  Hence `unfold`
does not preserve coproducts and the pro-level colimit is a different colimit. -/
theorem unfold_V (P : ProGraph) : (unfold P).V = ℕ := rfl

theorem coproduct_V {ι : Type} (P : ι → Polygraph.{0, 0, 0}) :
    (Polygraph.coproduct P).V = Σ i, (P i).V := rfl

/-! ## The identification the pro-level colimit creates

Two generators in different blocks commute in a free pro.  A colimit of *polygraphs* never relates
cells from two different legs (`Polygraph.colimit_rel_induction`: every 2-cell of the colimit is a
leg's), so this identification cannot come from a colimit of the unfolded polygraphs — it is
created by `UnfoldRel.exch`, whose index is a pair of 1-cells. -/

/-- Two 2-generators of width one. -/
def twoGen : ℕ → ℕ → Type := fun a b => PLift (a = 1 ∧ b = 1) × Bool

/-- The pro-graph on two 2-generators and no 3-cells — the coproduct of two copies of `onePro`. -/
def twoPro : ProGraph where
  Gen := twoGen
  Rel := fun _ _ => Empty
  src := fun e => e.elim
  tgt := fun e => e.elim

/-- The generator of copy `i`. -/
def twoGenCell (i : Bool) : Step twoPro.Gen 1 1 :=
  ⟨0, 1, 1, 0, (⟨⟨rfl, rfl⟩⟩, i), rfl, rfl⟩

/-- Copy `false`, in the left block of the 1-cell `1 + 1`. -/
def leftA : (⟨1 + 1⟩ : GenObj (Step twoPro.Gen)) ⟶ ⟨1 + 1⟩ :=
  (twoGenCell false).whiskerRight 1

/-- Copy `true`, in the right block. -/
def rightB : (⟨1 + 1⟩ : GenObj (Step twoPro.Gen)) ⟶ ⟨1 + 1⟩ :=
  Step.whiskerLeft 1 (twoGenCell true)

/-- **Generators from two different copies commute in the free pro** — the identification a colimit
of the unfolded polygraphs cannot make, because its 2-cells are the legs' 2-cells. -/
theorem mixed_commute :
    (unfold twoPro).quot.map ((Quiver.Hom.toPath leftA).comp (Quiver.Hom.toPath rightB))
      = (unfold twoPro).quot.map ((Quiver.Hom.toPath rightB).comp (Quiver.Hom.toPath leftA)) :=
  (unfold twoPro).quot_src_tgt (UnfoldRel.exch (twoGenCell false) (twoGenCell true))

/-- **…and the two words are genuinely different**, so the identification has content: the free
*category* on the positioned generators keeps them apart. -/
theorem leftA_ne_rightB : leftA ≠ rightB := by
  intro h
  exact absurd (congrArg Step.l h) (by decide)

theorem word_ne :
    (Quiver.Hom.toPath leftA).comp (Quiver.Hom.toPath rightB)
      ≠ (Quiver.Hom.toPath rightB).comp (Quiver.Hom.toPath leftA) := fun h =>
  leftA_ne_rightB
    (eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons
      (show (Quiver.Hom.toPath leftA).cons rightB
          = (Quiver.Hom.toPath rightB).cons leftA from h))).symm

end ProPrototype

end CategoryTheory
