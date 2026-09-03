import CubeChains.Machinery.Presentation.Basic
import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Machinery/Presentation/Monoid — a presented monoid presents its one-object category

`PresentedMonoid` and `Presentation` are two spellings of "generators and relations"; this is the
translation, on the one-object category.

The `ᵒᵖ` is the composition order, not a choice: a word composes source-first and `SingleObj`
composes backwards, so no word is ever reversed.
-/

universe u

namespace CategoryTheory

open Quiver

variable {S : Type u} (rels : FreeMonoid S → FreeMonoid S → Prop)

/-- A generating set of a monoid, as a generating family for its one-object category. -/
def monoidGens : Gens ((SingleObj (PresentedMonoid rels))ᵒᵖ) where
  V := SingleObj (PresentedMonoid rels)
  ob := Opposite.op
  Gen _ _ := S
  arrow s := Hom.op (PresentedMonoid.mk rels (FreeMonoid.of s))

/-- The one vertex. -/
abbrev monoidPt : GenObj (monoidGens rels).Gen := ⟨SingleObj.star (PresentedMonoid rels)⟩

namespace MonoidGens

variable {rels}

/-- A generator, as an edge. -/
def edge (s : S) : monoidPt rels ⟶ monoidPt rels := s

/-- An edge, as a generator — the quiver's `Hom` is the generating set on the nose. -/
def gen {x y : GenObj (monoidGens rels).Gen} (e : x ⟶ y) : S := e

/-! ## Words -/

/-- The word a generating path spells, source first. -/
def word {x y : GenObj (monoidGens rels).Gen} (P : Path x y) : FreeMonoid S :=
  Path.rec (motive := fun _ _ => FreeMonoid S) 1
    (fun _ e ih => ih * FreeMonoid.of (gen e)) P

theorem word_nil {x : GenObj (monoidGens rels).Gen} : word (Path.nil : Path x x) = 1 := rfl

theorem word_cons {x y z : GenObj (monoidGens rels).Gen} (P : Path x y) (e : y ⟶ z) :
    word (P.cons e) = word P * FreeMonoid.of (gen e) := rfl

theorem word_comp {x y z : GenObj (monoidGens rels).Gen} (P : Path x y) (Q : Path y z) :
    word (P.comp Q) = word P * word Q := by
  induction Q with
  | nil => rw [Path.comp_nil, word_nil, mul_one]
  | cons Q e ih => rw [Path.comp_cons, word_cons, word_cons, ih, mul_assoc]

/-- The path a word spells. -/
def path (w : FreeMonoid S) : Path (monoidPt rels) (monoidPt rels) :=
  FreeMonoid.recOn w Path.nil fun s _ P => (Path.nil.cons (edge s)).comp P

theorem path_one : path (rels := rels) 1 = Path.nil := rfl

theorem path_cons (s : S) (w : FreeMonoid S) :
    path (rels := rels) (FreeMonoid.of s * w) = (Path.nil.cons (edge s)).comp (path w) := rfl

theorem path_of (s : S) : path (rels := rels) (FreeMonoid.of s) = Path.nil.cons (edge s) := by
  rw [show FreeMonoid.of s = FreeMonoid.of s * 1 from (mul_one _).symm, path_cons, path_one,
    Path.comp_nil]

theorem path_mul (w₁ w₂ : FreeMonoid S) :
    path (rels := rels) (w₁ * w₂) = (path w₁).comp (path w₂) := by
  refine FreeMonoid.inductionOn' w₁ ?_ ?_
  · rw [one_mul, path_one, Path.nil_comp]
  · intro s w ih
    rw [mul_assoc, path_cons, path_cons, ih, Path.comp_assoc]

theorem word_path (w : FreeMonoid S) : word (path (rels := rels) w) = w := by
  refine FreeMonoid.inductionOn' w ?_ ?_
  · rfl
  · intro s w ih
    rw [path_cons, word_comp, ih, word_cons, word_nil, one_mul]
    rfl

theorem path_word {x y : GenObj (monoidGens rels).Gen} (P : Path x y) : path (word P) = P := by
  induction P with
  | nil => rfl
  | cons Q e ih =>
      rw [word_cons, path_mul, ih, path_of, Path.comp_cons, Path.comp_nil]
      rfl

/-- **A generating word evaluates to the element it spells.** -/
theorem eval_unop {x y : GenObj (monoidGens rels).Gen} (P : Path x y) :
    ((monoidGens rels).eval.map P).unop = PresentedMonoid.mk rels (word P) := by
  induction P with
  | nil =>
      rw [Gens.eval_nil, word_nil, map_one]
      exact SingleObj.id_as_one (M := PresentedMonoid rels) x.as
  | cons Q e ih => rw [Gens.eval_cons, word_cons, map_mul, ← ih]; rfl

end MonoidGens

open MonoidGens

/-- The relations a monoid presentation imposes on generating words. -/
def monoidRel : HomRel (Paths (GenObj (monoidGens rels).Gen)) :=
  fun _ _ P Q => rels (word P) (word Q)

/-- Two words whose paths agree in the quotient — a congruence, so it absorbs `conGen`. -/
private def pathCon : Con (FreeMonoid S) where
  r w₁ w₂ := (Quotient.functor (monoidRel rels)).map (path w₁)
    = (Quotient.functor (monoidRel rels)).map (path w₂)
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  mul' {w x y z} h₁ h₂ := by
    show (Quotient.functor (monoidRel rels)).map (path (w * y))
      = (Quotient.functor (monoidRel rels)).map (path (x * z))
    rw [path_mul, path_mul]
    exact ((Quotient.functor (monoidRel rels)).map_comp (path w) (path y)).trans
      ((congrArg₂ (· ≫ ·) h₁ h₂).trans
        ((Quotient.functor (monoidRel rels)).map_comp (path x) (path z)).symm)

private theorem pathCon_of_rels (w₁ w₂ : FreeMonoid S) (h : rels w₁ w₂) :
    (Quotient.functor (monoidRel rels)).map (path w₁)
      = (Quotient.functor (monoidRel rels)).map (path w₂) :=
  Quotient.sound _ (by
    change rels (word (path w₁)) (word (path w₂))
    rwa [word_path, word_path])

private theorem eq_of_conGen {w₁ w₂ : FreeMonoid S} (h : ConGen.Rel rels w₁ w₂) :
    (Quotient.functor (monoidRel rels)).map (path w₁)
      = (Quotient.functor (monoidRel rels)).map (path w₂) :=
  Con.conGen_le (c := pathCon rels) (pathCon_of_rels rels) h

/-- **A presented monoid presents its one-object category** — generators the generating set,
relations the monoid's, read on the words a path spells. -/
def presentedMonoidPresentation : Presentation ((SingleObj (PresentedMonoid rels))ᵒᵖ) where
  toGens := monoidGens rels
  rel := monoidRel rels
  sound h := Quiver.Hom.unop_inj (by
    rw [eval_unop, eval_unop]
    exact PresentedMonoid.mk_eq_mk_iff.mpr (ConGen.Rel.of _ _ h))
  spans f := by
    obtain ⟨w, hw⟩ := PresentedMonoid.surjective_mk (Quiver.Hom.unop f)
    exact ⟨path w, Quiver.Hom.unop_inj ((eval_unop _).trans ((congrArg _ (word_path w)).trans hw))⟩
  complete {x y} {P Q} h := by
    have hw : PresentedMonoid.mk rels (word P) = PresentedMonoid.mk rels (word Q) := by
      rw [← eval_unop, ← eval_unop, h]
    have hp := eq_of_conGen rels (PresentedMonoid.mk_eq_mk_iff.mp hw)
    rwa [path_word, path_word] at hp
  covers _ := ⟨monoidPt rels, ⟨Iso.refl _⟩⟩

end CategoryTheory
