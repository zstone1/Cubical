import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.SingleObj

/-!
# Machinery/Localization/PathPresentation — a presented monoid as a quotient of a path category

`PresentedMonoid` and `CategoryTheory.Quotient` are two spellings of "generators and relations".
Lifting a presentation along a fibration consumes the second; monoids are given in the first.
`pathQuotientEquiv` is the translation, on the one-vertex quiver.

The `ᵒᵖ` is the composition order, not a choice: a path composes source-first and `SingleObj`
composes backwards, so no word is ever reversed.
-/

namespace CategoryTheory

universe u

open Quiver

/-- The one-vertex quiver on a generating set. -/
def GenQuiver (_S : Type u) : Type := PUnit

instance genQuiver (S : Type u) : Quiver (GenQuiver S) := ⟨fun _ _ => S⟩

namespace GenQuiver

variable {S : Type u}

/-- The unique vertex. -/
def pt (S : Type u) : GenQuiver S := PUnit.unit

/-- A generator, as an edge. -/
def edge (e : S) : pt S ⟶ pt S := e

/-- An edge, as a generator — the quiver's `Hom` is the generating set on the nose. -/
def gen {a b : GenQuiver S} (e : a ⟶ b) : S := e

@[simp] theorem gen_edge (e : S) : gen (edge e) = e := rfl

@[simp] theorem edge_gen {a b : GenQuiver S} (e : a ⟶ b) : edge (gen e) = e := rfl

/-! ## Paths are words -/

/-- The word a path spells, source first. -/
def word {a b : GenQuiver S} (p : Path a b) : FreeMonoid S :=
  Path.rec (motive := fun _ _ => FreeMonoid S) 1
    (fun _ e ih => ih * FreeMonoid.of (gen e)) p

theorem word_nil {a : GenQuiver S} : word (Path.nil : Path a a) = 1 := rfl

theorem word_cons {a b c : GenQuiver S} (p : Path a b) (e : b ⟶ c) :
    word (p.cons e) = word p * FreeMonoid.of (gen e) := rfl

theorem word_comp {a b c : GenQuiver S} (p : Path a b) (q : Path b c) :
    word (p.comp q) = word p * word q := by
  induction q with
  | nil => rw [Path.comp_nil, word_nil, mul_one]
  | cons q e ih => rw [Path.comp_cons, word_cons, word_cons, ih, mul_assoc]

/-- The path a word spells. -/
def path (w : FreeMonoid S) : Path (pt S) (pt S) :=
  FreeMonoid.recOn w Path.nil fun e _ p => (Path.nil.cons (edge e)).comp p

theorem path_one : path (1 : FreeMonoid S) = Path.nil := rfl

theorem path_cons (e : S) (w : FreeMonoid S) :
    path (FreeMonoid.of e * w) = (Path.nil.cons (edge e)).comp (path w) := rfl

theorem path_of (e : S) : path (FreeMonoid.of e) = Path.nil.cons (edge e) := by
  rw [show FreeMonoid.of e = FreeMonoid.of e * 1 from (mul_one _).symm, path_cons, path_one,
    Path.comp_nil]

theorem path_mul (w₁ w₂ : FreeMonoid S) : path (w₁ * w₂) = (path w₁).comp (path w₂) := by
  refine FreeMonoid.inductionOn' w₁ ?_ ?_
  · rw [one_mul, path_one, Path.nil_comp]
  · intro e w ih
    rw [mul_assoc, path_cons, path_cons, ih, Path.comp_assoc]

theorem word_path (w : FreeMonoid S) : word (path w) = w := by
  refine FreeMonoid.inductionOn' w ?_ ?_
  · rfl
  · intro e w ih
    rw [path_cons, word_comp, ih, word_cons, word_nil, one_mul, gen_edge]

theorem path_word {a b : GenQuiver S} (p : Path a b) : path (word p) = p := by
  induction p with
  | nil => rfl
  | cons q e ih =>
      rw [word_cons, path_mul, ih, path_of, Path.comp_cons, Path.comp_nil, edge_gen]
      rfl

end GenQuiver

/-! ## The translation -/

open GenQuiver

variable {S : Type u} (rels : FreeMonoid S → FreeMonoid S → Prop)

/-- The relations a monoid presentation imposes on paths. -/
def pathRel : HomRel (Paths (GenQuiver S)) := fun _ _ P Q => rels (word P) (word Q)

/-- A path, read as an element of the presented monoid. -/
def toPresented : Paths (GenQuiver S) ⥤ (SingleObj (PresentedMonoid rels))ᵒᵖ where
  obj _ := Opposite.op (SingleObj.star _)
  map P := Quiver.Hom.op (PresentedMonoid.mk rels (word P))
  map_id _ := by
    refine Quiver.Hom.unop_inj ?_
    change PresentedMonoid.mk rels (word (Path.nil : Path _ _)) = _
    rw [word_nil, map_one]
    rfl
  map_comp P Q := by
    refine Quiver.Hom.unop_inj ?_
    change PresentedMonoid.mk rels (word (P.comp Q))
      = PresentedMonoid.mk rels (word P) * PresentedMonoid.mk rels (word Q)
    rw [word_comp, map_mul]

/-- The comparison functor, on the quotient. -/
noncomputable def presentedFunctor :
    Quotient (pathRel rels) ⥤ (SingleObj (PresentedMonoid rels))ᵒᵖ :=
  Quotient.lift (pathRel rels) (toPresented rels) fun _ _ _ _ h =>
    Quiver.Hom.unop_inj (PresentedMonoid.mk_eq_mk_iff.mpr (ConGen.Rel.of _ _ h))

theorem presentedFunctor_map {a b : Paths (GenQuiver S)} (P : a ⟶ b) :
    ((presentedFunctor rels).map ((Quotient.functor (pathRel rels)).map P)).unop
      = PresentedMonoid.mk rels (word P) := rfl

/-- Two words whose paths agree in the quotient — a congruence, so it absorbs `conGen`. -/
private def pathCon : Con (FreeMonoid S) where
  r w₁ w₂ := (Quotient.functor (pathRel rels)).map (path w₁)
    = (Quotient.functor (pathRel rels)).map (path w₂)
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  mul' {w x y z} h₁ h₂ := by
    show (Quotient.functor (pathRel rels)).map (path (w * y))
      = (Quotient.functor (pathRel rels)).map (path (x * z))
    rw [path_mul, path_mul]
    exact ((Quotient.functor (pathRel rels)).map_comp (path w) (path y)).trans
      ((congrArg₂ (· ≫ ·) h₁ h₂).trans
        ((Quotient.functor (pathRel rels)).map_comp (path x) (path z)).symm)

private theorem pathCon_of_rels (w₁ w₂ : FreeMonoid S) (h : rels w₁ w₂) :
    (Quotient.functor (pathRel rels)).map (path w₁)
      = (Quotient.functor (pathRel rels)).map (path w₂) :=
  Quotient.sound _ (by
    change rels (word (path w₁)) (word (path w₂))
    rwa [word_path, word_path])

private theorem eq_of_conGen {w₁ w₂ : FreeMonoid S} (h : ConGen.Rel rels w₁ w₂) :
    (Quotient.functor (pathRel rels)).map (path w₁)
      = (Quotient.functor (pathRel rels)).map (path w₂) :=
  Con.conGen_le (c := pathCon rels) (pathCon_of_rels rels) h

instance : (presentedFunctor rels).Full where
  map_surjective {_ _} g := by
    obtain ⟨w, hw⟩ := PresentedMonoid.surjective_mk (Quiver.Hom.unop g)
    refine ⟨(Quotient.functor (pathRel rels)).map (path w), Quiver.Hom.unop_inj ?_⟩
    change PresentedMonoid.mk rels (word (path w)) = Quiver.Hom.unop g
    rw [word_path]
    exact hw

instance : (presentedFunctor rels).Faithful where
  map_injective {_ _} P Q h := by
    obtain ⟨P, rfl⟩ := (Quotient.functor (pathRel rels)).map_surjective P
    obtain ⟨Q, rfl⟩ := (Quotient.functor (pathRel rels)).map_surjective Q
    have hw : PresentedMonoid.mk rels (word P) = PresentedMonoid.mk rels (word Q) :=
      congrArg Quiver.Hom.unop h
    have hp := eq_of_conGen rels (PresentedMonoid.mk_eq_mk_iff.mp hw)
    have e1 : path (word P) = P := path_word P
    have e2 : path (word Q) = Q := path_word Q
    rwa [e1, e2] at hp

instance : (presentedFunctor rels).EssSurj where
  mem_essImage _ := ⟨{ as := pt S }, ⟨eqToIso rfl⟩⟩

instance : (presentedFunctor rels).IsEquivalence where

/-- **A presented monoid is the path category of its generators modulo its relations.** -/
noncomputable def pathQuotientEquiv :
    Quotient (pathRel rels) ≌ (SingleObj (PresentedMonoid rels))ᵒᵖ :=
  (presentedFunctor rels).asEquivalence

end CategoryTheory
