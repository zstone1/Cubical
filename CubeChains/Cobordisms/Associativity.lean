import CubeChains.Cobordisms.Composition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Cobordisms/Associativity — the pushout associator of `DirectedCobordism.comp` (M5)

The **associativity-flavoured coherence** of the directed-cobordism composition
`DirectedCobordism.comp` (`Cobordisms/Composition.lean`).  Composition of cobordisms
is associative only *up to a boundary-fixing iso of the middle objects* — the
canonical **pushout associator** — because the two parenthesizations of a triple
composite glue the shared boundaries in a different order and so produce *isomorphic*
but not *equal* iterated pushouts.

This is a genuinely off-the-shelf statement: the iso is mathlib's
`CategoryTheory.Limits.pushoutAssoc` and the leg-compatibility is
`inl_inl_pushoutAssoc_hom` / `inr_pushoutAssoc_hom`.  It is stated **rawly** here
(only `DirectedCobordism.comp`, `.mid`/`.inl`/`.inr`, `≅`, `≫`, and the mathlib
pushout API) so that it carries no dependency on the `CobIso`/`CompCoherence` bundles
that consume it in `Cobordisms/DCob.lean`.

**Layer:** Cobordisms.  **Imports:** `Cobordisms.Composition` (the bundle +
`DirectedCobordism.comp` and its cospan simp lemmas).
-/

open CategoryTheory Opposite

namespace PrecubicalSet

/-! ## The pushout associator (M5) -/

variable {X Y Z W : PrecubicalSet}

/-- **The pushout associator (M5).**  A boundary-fixing iso of the middle objects of
the two parenthesizations of a triple `comp`-composite, commuting with both outer
legs.  This is the canonical mathlib `pushoutAssoc`:

* `((U.comp V).comp T).mid = pushout (V.inr ≫ pushout.inr U.inr V.inl) T.inl`,
* `(U.comp (V.comp T)).mid = pushout U.inr (V.inl ≫ pushout.inl V.inr T.inl)`,

so with `g₁ := U.inr`, `g₂ := V.inl`, `g₃ := V.inr`, `g₄ := T.inl` the iso is
`pushoutAssoc g₁ g₂ g₃ g₄`, and the leg-compatibility is `inl_inl_pushoutAssoc_hom` /
`inr_pushoutAssoc_hom`.

This is the associator the directed-cobordism category `dCob`
(`Cobordisms/DCob.lean`) consumes (as `compAssociator`) to discharge the category
law `assoc` and the unit/junction-move descent congruences. -/
theorem dcob_pushout_associator (U : X ⇒c Y) (V : Y ⇒c Z) (T : Z ⇒c W) :
    ∃ e : ((U.comp V).comp T).mid ≅ (U.comp (V.comp T)).mid,
      (((U.comp V).comp T).inl ≫ e.hom = (U.comp (V.comp T)).inl) ∧
      (((U.comp V).comp T).inr ≫ e.hom = (U.comp (V.comp T)).inr) := by
  -- Expose the bare pushout forms of the mids and legs.
  simp only [DirectedCobordism.comp_toCospan, Cospan.comp_mid, Cospan.comp_inl,
    Cospan.comp_inr]
  -- The mathlib pushout associator with `g₁ = U.inr, g₂ = V.inl, g₃ = V.inr, g₄ = T.inl`.
  refine ⟨CategoryTheory.Limits.pushoutAssoc U.inr V.inl V.inr T.inl, ?_, ?_⟩
  · -- source leg: reassociate and apply `inl_inl_pushoutAssoc_hom`.
    rw [Category.assoc, Category.assoc,
      CategoryTheory.Limits.inl_inl_pushoutAssoc_hom U.inr V.inl V.inr T.inl]
  · -- sink leg: reassociate and apply `inr_pushoutAssoc_hom`.
    rw [Category.assoc, CategoryTheory.Limits.inr_pushoutAssoc_hom U.inr V.inl V.inr T.inl,
      ← Category.assoc]

end PrecubicalSet
