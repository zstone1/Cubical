import CubeChains.Chains.BlockDecomp
import CubeChains.Braid.ChGrading
import CubeChains.Salvetti.SalBraidChamberRank

/-!
# Testing/EventsCompute

The events/lines layer computes.  `blockIdx`/`blockFace` (which target block a source bead maps
into, and the cube-face it occupies) `#eval` off the `Glue` `Quot` decomposition
(`serialWedgeCell`); `chamberRank` (the core of `evKey` — a direction's number of order-
predecessors) `#eval`s via the decidable `Chamber.decLt` through its `@[csimp]` spec.  Not built
by `lake build CubeChains`.
-/

open CategoryTheory Opposite StdCube BPSet CubeChain CubeChains

-- The identity wedge map sends block `i` to block `i`.
#eval blockIdx (𝟙 (⋁([2, 2] : List ℕ+)).toPsh) 0                       -- 0
#eval blockIdx (𝟙 (⋁([2, 2] : List ℕ+)).toPsh) 1                       -- 1

-- Its block-face data also computes: bead `0` occupies the identity face, so the free-coordinate
-- embedding `faceEmb ∘ blockFace` (the direction transport behind `eventMap`) is the identity.
#eval (List.finRange 2).map
  (fun d => (faceEmb (blockFace (𝟙 (⋁([2, 2] : List ℕ+)).toPsh) 0) d).val)   -- [0, 1]

-- Chamber rank in the standard order on `□³`: direction `i` has `i` predecessors.
#eval (List.finRange 3).map (chamberRank (stdChamber 3))     -- [0, 1, 2]

/-- Machine-checked: the standard chamber ranks the directions in order. -/
example : (List.finRange 3).map (chamberRank (stdChamber 3)) = [0, 1, 2] := by
  native_decide

/-- Machine-checked: the identity wedge map's block-face is the identity direction embedding. -/
example : (List.finRange 2).map
    (fun d => (faceEmb (blockFace (𝟙 (⋁([2, 2] : List ℕ+)).toPsh) 0) d).val) = [0, 1] := by
  native_decide
