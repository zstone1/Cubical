import CubeChains.Braid.BraidWord
import CubeChains.Braid.ElementaryBraiding
import CubeChains.Braid.ChGrading

/-!
# Testing/CubeRefineBraid — `braidGrading` on a real cube refinement

The refinement machinery is now **computable**: the partition refinement `prefine` finds each
block's bead by a finite `preimEvent` search over the (finitely many) events, not by the
choice-based `Function.surjInv`.  So the braid of an actual `ConcCat` refinement `#eval`s end to
end — no abstract stand-in.

**The harness.**  Choose a bi-pointed cube `K`, an execution `x = ⟨chain, line⟩`, and any reordering
`M` of its concurrent events; then `braidWordZ (seqMor x M)` is the braid `braidGrading` assigns to
the sequentialization refinement `x ⟶ run(M)`, as a signed Artin word.

Here `K = ⋁[3]` (the 3-cube) and reversing its three events yields the half-twist `σ₁σ₂σ₁`.
Not built by `lake build CubeChains`.
-/

open CubeChains CategoryTheory Opposite BPSet

-- ── define `K` and an execution of it ──
/-- The 3-cube as an execution of `⋁[3]`: one bead `[3]` (three concurrent events), standard line. -/
def cube3exec : ConcCat (⋁([3] : List ℕ+)) := ⟨op ⟨[3], 𝟙 _⟩, stdLine _⟩

-- ── reorder the events and read off the braid ──
/-- Fire the three events in the reverse of the standard order. -/
def revLine : LinesObj cube3exec.chain := fun i => revChamber (ChainCat.beadDim _ i)

#eval nEvents cube3exec                                           -- 3
#eval (List.finRange 3).map (evPerm' (seqMor cube3exec revLine))  -- [2, 1, 0]  (the reversal)
#eval braidWordZ (seqMor cube3exec revLine)                       -- [1, 2, 1]  = σ₁σ₂σ₁

/-- Machine-checked: reversing the 3-cube's three events is the half-twist `σ₁σ₂σ₁`. -/
example : braidWordZ (seqMor cube3exec revLine) = [1, 2, 1] := by native_decide

/-- This word **is** `braidGrading`'s value on the refinement: `braidGrading.map (seqMor …)` is
`braidHom` of the braid `braidWord …` represents (the braid itself is an opaque `PresentedGroup`
element with no `#eval`; the word is how it is read). -/
example :
    (braidGrading (⋁([3] : List ℕ+))).map (seqMor cube3exec revLine)
      = CategoryTheory.CategoryStruct.comp
          (braidHom (wordToBraid (braidWord (seqMor cube3exec revLine))))
          (CategoryTheory.eqToHom (congrArg strands (nEvents_eq (seqMor cube3exec revLine)))) :=
  braidGrading_map_braidWord _

-- The trivial reordering (the execution's own line) gives the empty braid.
#eval braidWordZ (seqMor cube3exec cube3exec.line)               -- []
