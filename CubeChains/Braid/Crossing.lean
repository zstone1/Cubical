import CubeChains.Salvetti.Normalize
import CubeChains.Salvetti.SalBraidChamberRank
import CubeChains.Chains.ChainSkeletal

/-!
# Braid/Crossing — a pair of events is crossed exactly when its bead is split

The germ relation of the braid functor, from the chain/line semantics alone: no arrangement, no
Salvetti cell, no `salCross`.

A morphism of executions *refines* the chain and **restricts** the line — the finer line is not a
choice, it is `linesRestrict` of the coarse one.  So the order of two events can only change by the
refinement **splitting the bead that held them**, into two beads whose order contradicts the coarse
chamber.  Both other cases are forced:

* different coarse beads — the bead order is monotone (`serialWedge_blockIdx_monotone`), so the
  causal order is preserved;
* same fine bead — the fine chamber *is* the coarse one restricted (`Chamber.restrict_lt`, which is
  `rfl`), so the order is preserved.

Once split, a pair sits in different beads and is causally ordered, so no further refinement can
cross it again.  That is `permLen` additivity, and hence the germ relation `[σ][τ] = [στ]`.
-/

open CategoryTheory Opposite BPSet

namespace CubeChains

open ChainCat CubeChain

variable {K : BPSet}

/-- The refinement underlying a morphism of executions: `y`'s chain refines `x`'s. -/
def concRef {x y : ConcCat K} (f : x ⟶ y) : y.chain ⟶ x.chain := f.1.unop

/-- **The line is restricted, not chosen** — this is what forces the crossing criterion. -/
theorem concRef_line {x y : ConcCat K} (f : x ⟶ y) :
    linesRestrict (concRef f) x.line = y.line := f.2

/-- The coarse (`x`-) bead holding a fine (`y`-) event. -/
def coarseBead {x y : ConcCat K} (f : x ⟶ y) (e : EventObj y.chain) :
    Bead x.chain := blockIdx (concRef f)ᵂ e.1

theorem eventMap_concRef {x y : ConcCat K} (f : x ⟶ y) (e : EventObj y.chain) :
    eventMap (concRef f) e
      = ⟨coarseBead f e, faceEmb (blockFace (concRef f)ᵂ e.1) e.2⟩ := rfl

/-- The bead order is monotone: a refinement never reorders beads. -/
theorem coarseBead_monotone {x y : ConcCat K} (f : x ⟶ y) :
    Monotone (blockIdx (concRef f)ᵂ) :=
  serialWedge_blockIdx_monotone (concRef f)ᵂ (concRef f).φ.app_init

/-- **The crossing criterion.**  A refinement changes the order of two events *only* by splitting
the bead that held them: same coarse bead, different fine beads.  In every other case the two
`evKey` orders agree. -/
theorem evKey_lt_iff_of_not_split {x y : ConcCat K} (f : x ⟶ y) (e e' : EventObj y.chain)
    (h : e.1 = e'.1 ∨ coarseBead f e ≠ coarseBead f e') :
    (evKey y.line e < evKey y.line e' ↔
      evKey x.line (eventMap (concRef f) e) < evKey x.line (eventMap (concRef f) e')) := by
  obtain ⟨i, δ⟩ := e
  obtain ⟨i', δ'⟩ := e'
  rcases h with hbead | hcoarse
  · -- same fine bead: the fine chamber IS the coarse one restricted
    subst hbead
    have hline : y.line i
        = (x.line (blockIdx (concRef f)ᵂ i)).restrict
            (faceEmb (blockFace (concRef f)ᵂ i))
            (faceEmb (blockFace (concRef f)ᵂ i)).injective := by
      rw [← concRef_line f]; rfl
    simp only [evKey, eventMap, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, false_or, true_and]
    rw [chamberRank_lt_iff, chamberRank_lt_iff, hline, Chamber.restrict_lt]
  · -- different coarse beads: hence different fine beads, and the bead order is monotone
    have hne : i ≠ i' := fun hc => hcoarse (congrArg (blockIdx (concRef f)ᵂ) hc)
    have hmono := coarseBead_monotone f
    have hcb : blockIdx (concRef f)ᵂ i ≠ blockIdx (concRef f)ᵂ i' := hcoarse
    have key : ((i : ℕ) < (i' : ℕ))
        ↔ ((blockIdx (concRef f)ᵂ i : ℕ) < (blockIdx (concRef f)ᵂ i' : ℕ)) := by
      constructor
      · intro hlt
        exact Fin.lt_def.mp
          (lt_of_le_of_ne (hmono (le_of_lt (Fin.lt_def.mpr hlt))) hcb)
      · intro hlt
        by_contra hc
        exact absurd (hmono (Fin.le_def.mpr (Nat.le_of_not_lt hc)))
          (not_le.mpr (Fin.lt_def.mpr hlt))
    simp only [evKey, eventMap, Prod.Lex.toLex_lt_toLex]
    constructor
    · rintro (hlt | ⟨heq, -⟩)
      · exact Or.inl (key.mp hlt)
      · exact absurd (Fin.ext heq) hne
    · rintro (hlt | ⟨heq, -⟩)
      · exact Or.inl (key.mpr hlt)
      · exact absurd (Fin.ext heq) hcb

end CubeChains
