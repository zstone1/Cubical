import CubeChains.Operations.Deformation
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Types.Basic

/-!
# Weak equivalences relative to a homotopy invariant

The strong notion `Homotopical Φ` (`Φ` sends `f` to an *equivalence of categories*)
is too strict for directed homotopy theory: the inclusion of a boundary path into a
filled square is a directed-homotopy equivalence of path spaces, yet `ChP` does **not**
send it to an equivalence of categories (the square's `[2]`-chain is never in the
essential image — `pushforward` preserves dimension sequences).

The fix is to measure `f` against a **homotopy invariant** `H : Cat ⥤ 𝒯` and only ask
that `H (Φ f)` be an *isomorphism* in `𝒯`.  This is `(isomorphisms 𝒯).inverseImage`,
so it inherits the whole weak-equivalence algebra for free.

* The honest invariant is the **nerve** `N : Cat ⥤ SSet` followed by localization at
  simplicial weak homotopy equivalences (a *Thomason* weak equivalence).  mathlib has
  `nerve` but no constructed Kan–Quillen/Thomason model structure yet, so that target
  is not available sorry-free.
* The coarsest invariant — available **now** — is `π₀ = Cat.connectedComponents`.  It
  already strictly weakens `Homotopical` and captures the square example.

This file is parametric in `H`, so the nerve/`π₁`/Thomason invariants drop in later
with no rework; only the instance changes.

`InvertedBy` is generic; `WeakSpan` is the span carrier against it; the comparison
`homotopical_le_connectedComponents` shows the π₀ class genuinely contains the old one.
-/

open CategoryTheory

namespace Operations

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- Maps **inverted by** a homotopy invariant `Ψ : C ⥤ D`: those `f` with `Ψ.map f` an
isomorphism.  Defined as `(isomorphisms D).inverseImage Ψ`, so it inherits the
weak-equivalence algebra (identities, isos, multiplicative, two-out-of-three) from
mathlib's `inverseImage` instances. -/
abbrev InvertedBy (Ψ : C ⥤ D) : MorphismProperty C :=
  (MorphismProperty.isomorphisms D).inverseImage Ψ

theorem invertedBy_iff (Ψ : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    InvertedBy Ψ f ↔ IsIso (Ψ.map f) := Iff.rfl

-- The weak-equivalence algebra is inherited, not re-proved:
example (Ψ : C ⥤ D) : (InvertedBy Ψ).ContainsIdentities := inferInstance
example (Ψ : C ⥤ D) : (InvertedBy Ψ).IsMultiplicative := inferInstance
example (Ψ : C ⥤ D) : (InvertedBy Ψ).HasTwoOutOfThreeProperty := inferInstance

/-- An operation presented by a span whose legs are both inverted by `Ψ`.  Carries the
same DPO-ready shape as `Span`, but against the *weaker* invariant. -/
structure WeakSpan (Ψ : C ⥤ D) (X Y : C) where
  /-- The apex of the span. -/
  apex : C
  /-- The leg into the source. -/
  left : apex ⟶ X
  /-- The leg into the target. -/
  right : apex ⟶ Y
  /-- The left leg is a weak equivalence. -/
  left_inverted : InvertedBy Ψ left
  /-- The right leg is a weak equivalence. -/
  right_inverted : InvertedBy Ψ right

namespace WeakSpan

variable {Ψ : C ⥤ D} {X Y : C}

/-- A single weak equivalence as a weak span. -/
def ofHom (f : X ⟶ Y) (hf : InvertedBy Ψ f) : WeakSpan Ψ X Y where
  apex := X
  left := 𝟙 X
  right := f
  left_inverted := (InvertedBy Ψ).id_mem X
  right_inverted := hf

/-- The reverse operation. -/
def symm (s : WeakSpan Ψ X Y) : WeakSpan Ψ Y X where
  apex := s.apex
  left := s.right
  right := s.left
  left_inverted := s.right_inverted
  right_inverted := s.left_inverted

/-- **The invariant is transported.**  A weak operation induces an isomorphism
`Ψ X ≅ Ψ Y` in the target `𝒯`: invert the left leg, compose with the right.  For
`Ψ = Φ ⋙ π₀` this is the bijection of homotopy classes of d-paths. -/
noncomputable def iso (s : WeakSpan Ψ X Y) : Ψ.obj X ≅ Ψ.obj Y :=
  haveI : IsIso (Ψ.map s.left) := s.left_inverted
  haveI : IsIso (Ψ.map s.right) := s.right_inverted
  (asIso (Ψ.map s.left)).symm ≪≫ asIso (Ψ.map s.right)

end WeakSpan

section HomotopyInvariant

variable {Φ : C ⥤ Cat.{v, u}}

/-- **Strong ⟹ weak.**  A categorical equivalence is in particular a π₀-weak
equivalence: `Homotopical Φ` is contained in `InvertedBy (Φ ⋙ Cat.connectedComponents)`.
So weakening to π₀ genuinely *enlarges* the class of operations. -/
theorem homotopical_le_connectedComponents {X Y : C} {f : X ⟶ Y} (hf : Homotopical Φ f) :
    InvertedBy (Φ ⋙ Cat.connectedComponents) f := by
  rw [invertedBy_iff, Functor.comp_map]
  haveI : (Φ.map f).toFunctor.IsEquivalence := hf
  refine (CategoryTheory.isIso_iff_bijective _).mpr ?_
  simpa using (connectedComponentsEquiv (Φ.map f).toFunctor.asEquivalence).bijective

/-- The homotopy-class bijection `π₀(Ch K) ≃ π₀(Ch L)` from a π₀-weak operation — the
same conclusion as `Span.homotopyClassEquiv`, now from the weaker hypotheses that only
the *components* (not the whole category) be preserved. -/
noncomputable def WeakSpan.homotopyClassEquiv {K L : C}
    (s : WeakSpan (Φ ⋙ Cat.connectedComponents) K L) :
    ConnectedComponents (Φ.obj K) ≃ ConnectedComponents (Φ.obj L) :=
  s.iso.toEquiv

end HomotopyInvariant
end Operations
