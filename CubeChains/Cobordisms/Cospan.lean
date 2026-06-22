import CubeChains.Foundations.Box
import CubeChains.Foundations.Bipointed
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Adhesive.Basic

/-!
# Cobordisms/Cospan — cospans of precubical sets + pushout composition (M2)

The bare cospan / pushout backbone of directed cobordisms.  **No directedness or
flags yet** (those arrive in later milestones); this is pure category theory on
`PrecubicalSet`.

A *cospan* `X ⇒ Y` is a third precubical set `mid` with two **monic** legs
`X ⟶ mid ⟵ Y` (condition C1).  Cospans compose by gluing along the shared `Y`
(pushout), and the new outer legs are again monic by adhesivity.  The central M2
theorem is that *disjointness of the legs* (the images `i X` and `j Y` meet only in
the empty set) is preserved by composition — this uses the van Kampen property of
the adhesive presheaf topos `PrecubicalSet`: a pushout of a mono is a pullback, so a
cell in both outer images must factor through the glued `Y`, contradicting the
componentwise disjointness hypotheses.

**Layer:** Cobordisms.  **Imports:** `Foundations.Box`, `Foundations.Bipointed`,
mathlib `Pushouts`/`Pullbacks`/`Adhesive`.

`PrecubicalSet` is adhesive (`adhesive_functor`: a functor category into the
adhesive category `Type`) and has all pushouts (`Box.lean`), so every categorical
ingredient here is off the shelf.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace PrecubicalSet

universe u

variable {X Y Z W : PrecubicalSet}

/-! ### Cospans -/

/-- A **cospan** `X ⇒ Y` of precubical sets: a middle object `mid` together with two
monic legs `inl : X ⟶ mid` and `inr : Y ⟶ mid` (condition C1: both legs mono). -/
structure Cospan (X Y : PrecubicalSet) where
  /-- The apex / middle object of the cospan. -/
  mid : PrecubicalSet
  /-- The left leg `X ⟶ mid`. -/
  inl : X ⟶ mid
  /-- The right leg `Y ⟶ mid`. -/
  inr : Y ⟶ mid
  /-- C1: the left leg is a monomorphism. -/
  [mono_inl : Mono inl]
  /-- C1: the right leg is a monomorphism. -/
  [mono_inr : Mono inr]

attribute [instance] Cospan.mono_inl Cospan.mono_inr

namespace Cospan

/-- Build a cospan from a chosen apex `W` and two monos into it. -/
def of (inl : X ⟶ W) (inr : Y ⟶ W) [Mono inl] [Mono inr] : Cospan X Y where
  mid := W
  inl := inl
  inr := inr

@[simp] theorem of_mid (inl : X ⟶ W) (inr : Y ⟶ W) [Mono inl] [Mono inr] :
    (Cospan.of inl inr).mid = W := rfl

@[simp] theorem of_inl (inl : X ⟶ W) (inr : Y ⟶ W) [Mono inl] [Mono inr] :
    (Cospan.of inl inr).inl = inl := rfl

@[simp] theorem of_inr (inl : X ⟶ W) (inr : Y ⟶ W) [Mono inl] [Mono inr] :
    (Cospan.of inl inr).inr = inr := rfl

/-! ### Disjoint legs -/

/-- The legs of a cospan are **disjoint** when their images never meet: no `n`-cell
of `X` and `n`-cell of `Y` are sent to the same `n`-cell of `mid`.  This is the
intersection condition `i X ∩ j Y = ∅`. -/
def LegsDisjoint (C : Cospan X Y) : Prop :=
  ∀ {n : ℕ} (x : X.cells n) (y : Y.cells n),
    C.inl.app (op (Box.ob n)) x ≠ C.inr.app (op (Box.ob n)) y

end Cospan

/-! ### Pushout composition

Given `C₁ : Cospan X Y` and `C₂ : Cospan Y Z`, glue along the shared `Y`: the sink
of `C₁` is `C₁.inr : Y ⟶ mid₁`, the source of `C₂` is `C₂.inl : Y ⟶ mid₂`; the
composite middle is `pushout C₁.inr C₂.inl`.  Because `C₁.inr` and `C₂.inl` are
mono and `PrecubicalSet` is adhesive, the pushout injections are mono, so the new
outer legs (a mono composed with a pushout injection) are mono. -/

/-- The pushout injection `pushout.inl C₁.inr C₂.inl : mid₁ ⟶ pushout` is a mono:
`C₂.inl` is a mono and `PrecubicalSet` is adhesive. -/
instance comp_pushout_inl_mono (C₁ : Cospan X Y) (C₂ : Cospan Y Z) :
    Mono (pushout.inl C₁.inr C₂.inl) :=
  Adhesive.mono_of_isPushout_of_mono_right (IsPushout.of_hasPushout _ _)

/-- The pushout injection `pushout.inr C₁.inr C₂.inl : mid₂ ⟶ pushout` is a mono:
`C₁.inr` is a mono and `PrecubicalSet` is adhesive. -/
instance comp_pushout_inr_mono (C₁ : Cospan X Y) (C₂ : Cospan Y Z) :
    Mono (pushout.inr C₁.inr C₂.inl) :=
  Adhesive.mono_of_isPushout_of_mono_left (IsPushout.of_hasPushout _ _)

/-- **Composition of cospans** by pushout along the shared object `Y`.  The new
middle is `pushout C₁.inr C₂.inl`; the outer legs are the old outer legs followed
by the pushout injections.  Both new legs are mono (composite of monos). -/
noncomputable def Cospan.comp (C₁ : Cospan X Y) (C₂ : Cospan Y Z) : Cospan X Z where
  mid := pushout C₁.inr C₂.inl
  inl := C₁.inl ≫ pushout.inl C₁.inr C₂.inl
  inr := C₂.inr ≫ pushout.inr C₁.inr C₂.inl
  mono_inl := mono_comp _ _
  mono_inr := mono_comp _ _

@[simp] theorem Cospan.comp_mid (C₁ : Cospan X Y) (C₂ : Cospan Y Z) :
    (C₁.comp C₂).mid = pushout C₁.inr C₂.inl := rfl

@[simp] theorem Cospan.comp_inl (C₁ : Cospan X Y) (C₂ : Cospan Y Z) :
    (C₁.comp C₂).inl = C₁.inl ≫ pushout.inl C₁.inr C₂.inl := rfl

@[simp] theorem Cospan.comp_inr (C₁ : Cospan X Y) (C₂ : Cospan Y Z) :
    (C₁.comp C₂).inr = C₂.inr ≫ pushout.inr C₁.inr C₂.inl := rfl

/-! ### The composite gluing square is a pullback (van Kampen)

`PrecubicalSet` is adhesive, so the defining pushout of `pushout C₁.inr C₂.inl`
(along the mono `C₁.inr`) is also a **pullback**.  Evaluating at each level `n`
turns this into a `Type`-level pullback, whose universal property says: any cell of
`mid₁` and cell of `mid₂` that become equal in the pushout factor through a common
cell of `Y`.  This is the key input for outer-leg disjointness. -/

/-- The defining gluing square `Y ⟶ mid₁, Y ⟶ mid₂ ⟶ pushout ⟵ mid₁` is a
pullback, evaluated at level `n` in `Type`.  (Pushout of the mono `C₁.inr` in the
adhesive topos, transported by the colimit-preserving evaluation functor and made a
pullback by `Types.isPullback_of_isPushout`, since the mono leg is injective.) -/
theorem comp_isPullback_app (C₁ : Cospan X Y) (C₂ : Cospan Y Z) (n : ℕ) :
    IsPullback (C₁.inr.app (op (Box.ob n))) (C₂.inl.app (op (Box.ob n)))
      ((pushout.inl C₁.inr C₂.inl).app (op (Box.ob n)))
      ((pushout.inr C₁.inr C₂.inl).app (op (Box.ob n))) := by
  -- The presheaf-level pushout, evaluated at level `n`.
  have hpush : IsPushout (C₁.inr.app (op (Box.ob n))) (C₂.inl.app (op (Box.ob n)))
      ((pushout.inl C₁.inr C₂.inl).app (op (Box.ob n)))
      ((pushout.inr C₁.inr C₂.inl).app (op (Box.ob n))) :=
    (IsPushout.of_hasPushout C₁.inr C₂.inl).map
      (F := (evaluation Boxᵒᵖ Type).obj (op (Box.ob n)))
  -- `C₁.inr` is mono, hence injective on `n`-cells; a pushout of an injection in
  -- `Type` is a pullback.
  refine Types.isPullback_of_isPushout hpush ?_
  rw [← mono_iff_injective]
  exact (NatTrans.mono_iff_mono_app C₁.inr).1 C₁.mono_inr (op (Box.ob n))

/-! ### Outer-leg disjointness of a composite (the M2 theorem) -/

/-- **M2.**  Composition preserves leg-disjointness: if both `C₁` and `C₂` have
disjoint legs, then so does `C₁.comp C₂`.

Proof: suppose an `n`-cell `x : X` and `z : Z` collide in the composite, i.e.
`pushout.inl (C₁.inl x) = pushout.inr (C₂.inr z)`.  By the van Kampen pullback
(`comp_isPullback_app`) there is a common `y : Y` with `C₁.inr y = C₁.inl x` and
`C₂.inl y = C₂.inr z`.  The first equality contradicts `C₁.LegsDisjoint`. -/
theorem Cospan.LegsDisjoint.comp {C₁ : Cospan X Y} {C₂ : Cospan Y Z}
    (h₁ : C₁.LegsDisjoint) (_h₂ : C₂.LegsDisjoint) : (C₁.comp C₂).LegsDisjoint := by
  intro n x z hcollide
  -- Unfold the outer legs of the composite to the glued form.
  rw [Cospan.comp_inl, Cospan.comp_inr] at hcollide
  simp only [NatTrans.comp_app] at hcollide
  -- `hcollide : pushout.inl (C₁.inl x) = pushout.inr (C₂.inr z)`.
  -- The gluing square is a pullback at level `n`, so these factor through a common
  -- `y : Y.cells n`.
  obtain ⟨y, hy₁, hy₂⟩ :=
    Types.exists_of_isPullback (comp_isPullback_app C₁ C₂ n)
      (C₁.inl.app (op (Box.ob n)) x) (C₂.inr.app (op (Box.ob n)) z) hcollide
  -- `hy₁ : C₁.inr y = C₁.inl x` contradicts disjointness of `C₁`'s legs.
  exact h₁ x y hy₁.symm

/-! ### Associativity of composition

Associativity of `Cospan.comp` up to a leg-compatible iso of the middle object is
**pushout associativity**.  It is genuinely a coherence statement (the canonical
`pushout`-of-`pushout` associator), and is deferred to **M5**; we do not develop it
here. -/

end PrecubicalSet
