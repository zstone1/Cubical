import CubeChains.Testing.Skeleton

/-! Scratch probe: connected branching `K` with a 4-cell — `TwoSquares.S ∘ □⁴`. -/

namespace CubeTest
namespace Skel

/-- Branching + connected, has a 4-cell. -/
abbrev sqCube4 : FinBPSet (TwoSquares.Cell ⊕ List (Option Bool)) := serial TwoSquares.S (cube 4)

#eval (sqCube4.wellFormed, (ordOf sqCube4).1)
#eval betti01 (skel 3 sqCube4)   -- 4-cell deleted
#eval betti01 sqCube4            -- full

end Skel
end CubeTest
