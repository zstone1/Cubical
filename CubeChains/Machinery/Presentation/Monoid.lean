import CubeChains.Machinery.Presentation.Basic
import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Machinery/Presentation/Monoid — a presented monoid presents its one-object category

`PresentedMonoid` and `Polygraph` are two spellings of "generators and relations"; this is the
translation, on the one-object category.

The `ᵒᵖ` is the composition order, not a choice: a word composes source-first and `SingleObj`
composes backwards, so no word is ever reversed.
-/

universe u

namespace CategoryTheory

open Quiver

variable {S : Type u} (rels : FreeMonoid S → FreeMonoid S → Prop)

/-- The 1-cells: the generating set, at the one vertex. -/
abbrev monoidGen : SingleObj (PresentedMonoid rels) → SingleObj (PresentedMonoid rels) → Type u :=
  fun _ _ => S

/-- The one vertex. -/
abbrev monoidPt : GenObj (monoidGen rels) := ⟨SingleObj.star (PresentedMonoid rels)⟩

namespace MonoidPoly

variable {rels}

/-- A generator, as an edge. -/
def edge (s : S) : monoidPt rels ⟶ monoidPt rels := s

/-- An edge, as a generator — the quiver's `Hom` is the generating set on the nose. -/
def gen {x y : GenObj (monoidGen rels)} (e : x ⟶ y) : S := e

/-! ## Words -/

/-- The word a generating path spells, source first. -/
def word {x y : GenObj (monoidGen rels)} (P : Path x y) : FreeMonoid S :=
  Path.rec (motive := fun _ _ => FreeMonoid S) 1
    (fun _ e ih => ih * FreeMonoid.of (gen e)) P

theorem word_nil {x : GenObj (monoidGen rels)} : word (Path.nil : Path x x) = 1 := rfl

theorem word_cons {x y z : GenObj (monoidGen rels)} (P : Path x y) (e : y ⟶ z) :
    word (P.cons e) = word P * FreeMonoid.of (gen e) := rfl

theorem word_comp {x y z : GenObj (monoidGen rels)} (P : Path x y) (Q : Path y z) :
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

theorem path_word {x y : GenObj (monoidGen rels)} (P : Path x y) : path (word P) = P := by
  induction P with
  | nil => rfl
  | cons Q e ih =>
      rw [word_cons, path_mul, ih, path_of, Path.comp_cons, Path.comp_nil]
      rfl

end MonoidPoly

open MonoidPoly

/-- The 2-cells: a parallel pair of paths whose words the presentation relates.  Paths and not
words, because `src` reads its endpoints off the 2-cell's own type. -/
def monoidRel (x y : GenObj (monoidGen rels)) : Type u :=
  {p : Path x y × Path x y // rels (word p.1) (word p.2)}

/-- **The one-object polygraph of a monoid presentation.** -/
def monoidPoly : Polygraph where
  V := SingleObj (PresentedMonoid rels)
  Gen := monoidGen rels
  Rel := monoidRel rels
  src α := α.1.1
  tgt α := α.1.2

/-- **A relation is its pair of words** — the 2-cells carry no data beyond their boundary. -/
theorem boundaryDetermined_monoidPoly : (monoidPoly rels).BoundaryDetermined :=
  fun _ _ hs ht => Subtype.ext (Prod.ext hs ht)

/-- A generator names left multiplication by itself. -/
def monoidInterp : GenObj (monoidGen rels) ⥤q (SingleObj (PresentedMonoid rels))ᵒᵖ where
  obj x := Opposite.op x.as
  map s := Hom.op (PresentedMonoid.mk rels (FreeMonoid.of s))

/-- Two words whose paths agree in the quotient — a congruence, so it absorbs `conGen`. -/
private def pathCon : Con (FreeMonoid S) where
  r w₁ w₂ := (monoidPoly rels).quot.map (path (rels := rels) w₁)
    = (monoidPoly rels).quot.map (path (rels := rels) w₂)
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  mul' {w x y z} h₁ h₂ := by
    show (monoidPoly rels).quot.map (path (rels := rels) (w * y))
      = (monoidPoly rels).quot.map (path (rels := rels) (x * z))
    rw [path_mul, path_mul]
    exact ((monoidPoly rels).quot.map_comp (path (rels := rels) w) (path y)).trans
      ((congrArg₂ (· ≫ ·) h₁ h₂).trans
        ((monoidPoly rels).quot.map_comp (path (rels := rels) x) (path z)).symm)

private theorem pathCon_of_rels (w₁ w₂ : FreeMonoid S) (h : rels w₁ w₂) :
    (monoidPoly rels).quot.map (path (rels := rels) w₁)
      = (monoidPoly rels).quot.map (path (rels := rels) w₂) :=
  Quotient.sound _ ⟨⟨(path w₁, path w₂), by rwa [word_path, word_path]⟩, rfl, rfl⟩

private theorem eq_of_conGen {w₁ w₂ : FreeMonoid S} (h : ConGen.Rel rels w₁ w₂) :
    (monoidPoly rels).quot.map (path (rels := rels) w₁)
      = (monoidPoly rels).quot.map (path (rels := rels) w₂) :=
  Con.conGen_le (c := pathCon rels) (pathCon_of_rels rels) h

/-! ## The obligations

Stated on `monoidGen`, the spelling the word machinery uses; `ofDesc` reads them through
`(monoidPoly rels).Gen`, which is the same type. -/

section Obligations

variable {rels}

/-- **A generating word evaluates to the element it spells.** -/
theorem eval_unop {x y : GenObj (monoidGen rels)} (P : Path x y) :
    ((Paths.lift (monoidInterp rels)).map P).unop = PresentedMonoid.mk rels (word P) := by
  induction P with
  | nil =>
      rw [Paths.lift_nil, word_nil, map_one]
      exact SingleObj.id_as_one (M := PresentedMonoid rels) x.as
  | cons Q e ih => rw [Paths.lift_cons, word_cons, map_mul, ← ih]; rfl

theorem monoid_sound {x y : GenObj (monoidGen rels)} (α : monoidRel rels x y) :
    (Paths.lift (monoidInterp rels)).map ((monoidPoly rels).src α)
      = (Paths.lift (monoidInterp rels)).map ((monoidPoly rels).tgt α) :=
  Quiver.Hom.unop_inj (by
    rw [eval_unop, eval_unop]
    exact PresentedMonoid.mk_eq_mk_iff.mpr (ConGen.Rel.of _ _ α.2))

theorem monoid_complete {x y : GenObj (monoidGen rels)} {P Q : Path x y}
    (h : (Paths.lift (monoidInterp rels)).map P = (Paths.lift (monoidInterp rels)).map Q) :
    (monoidPoly rels).quot.map P = (monoidPoly rels).quot.map Q := by
  have hw : PresentedMonoid.mk rels (word P) = PresentedMonoid.mk rels (word Q) := by
    rw [← eval_unop, ← eval_unop, h]
  have hp := eq_of_conGen rels (PresentedMonoid.mk_eq_mk_iff.mp hw)
  rwa [path_word, path_word] at hp

theorem monoidFull : (Paths.lift (monoidInterp rels)).Full where
  map_surjective {x y} f := by
    obtain ⟨w, hw⟩ := PresentedMonoid.surjective_mk (Quiver.Hom.unop f)
    exact ⟨path w, Quiver.Hom.unop_inj ((eval_unop _).trans ((congrArg _ (word_path w)).trans hw))⟩

theorem monoidEssSurj : (Paths.lift (monoidInterp rels)).EssSurj where
  mem_essImage _ := ⟨monoidPt rels, ⟨Iso.refl _⟩⟩

end Obligations

/-- **A presented monoid presents its one-object category** — 1-cells the generating set, 2-cells
the monoid's relations, read on the words a path spells. -/
def presentedMonoidPresentation :
    Presents (monoidPoly rels) ((SingleObj (PresentedMonoid rels))ᵒᵖ) :=
  Presents.ofDesc (monoidInterp rels) monoid_sound monoid_complete monoidFull monoidEssSurj

end CategoryTheory
