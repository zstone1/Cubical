import CubeChains.Chains.BlockDecomp
import CubeChains.Braid.ChGrading
import CubeChains.Salvetti.SalBraidChamberRank

/-!
# Testing/EventsCompute

The events/lines layer computes.  `blockIdx` (which target block a source bead maps
into) `#eval`s off the `Glue` `Quot`; `chamberRank` (the core of `evKey` — a direction's
number of order-predecessors) `#eval`s via the decidable `Chamber.decLt`.  Both keep their
noncomputable specs and run through `@[csimp]`.  Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite StdCube BPSet CubeChain CubeChains

-- The identity wedge map sends block `i` to block `i`.
#eval blockIdx (𝟙 (⋁([2, 2] : List ℕ+)).toPsh) 0                       -- 0
#eval blockIdx (𝟙 (⋁([2, 2] : List ℕ+)).toPsh) 1                       -- 1

-- Chamber rank in the standard order on `□³`: direction `i` has `i` predecessors.
#eval (List.finRange 3).map (chamberRank (stdChamber 3))     -- [0, 1, 2]

/-- Machine-checked: the standard chamber ranks the directions in order. -/
example : (List.finRange 3).map (chamberRank (stdChamber 3)) = [0, 1, 2] := by
  native_decide
