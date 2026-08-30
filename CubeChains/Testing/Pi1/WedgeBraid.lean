import CubeChains.Testing.Enumerate.Morphisms
import CubeChains.Concurrency.Grading.WedgeBraid

/-!
# Testing/Pi1/WedgeBraid — the crossing permutation of `Ch (□n)`, evaluated

`crossPerm` is computable, so the grading can be read off the hom-sets directly.  At `⋁[1,1] ⟶ ⋁[2]`
the hom-set is the two staircases of the square, and their permutations are the two elements of
`S₂` — the braid generator is the staircase that takes the second coordinate first.

At `n = 3` the hom-sets out of a run exhaust `S₃` (`runRows`), while those out of a two-bead chain
give the three minimal-length coset representatives of a Young subgroup (`cosetRows`) — the shape
`Machinery/Braid/PosGerm`'s atom relations consume.

Not built by `lake build CubeChains`.
-/

open CategoryTheory BPSet CubeChain ChainCat

namespace CubeChains

/-- Every morphism of `Ch (□n)`: source dims, target dims, crossing permutation, its length. -/
def crossRows (n : ℕ) : Multiset (List ℕ × List ℕ × List ℕ × ℕ) :=
  (Finset.univ : Finset (Ch (cube n))).val.bind fun a =>
    (Finset.univ : Finset (Ch (cube n))).val.bind fun b =>
      (Finset.univ : Finset (a ⟶ b)).val.map fun g =>
        (a.dims.map (fun d : ℕ+ => (d : ℕ)), b.dims.map (fun d : ℕ+ => (d : ℕ)),
          (List.finRange (dimSum a.dims)).map (fun i => (crossPerm g i : ℕ)),
          permLen (crossPerm g))

/-- The crossing permutations of the morphisms of shape `src ⟶ tgt`, with their lengths. -/
def rowsOfShape (n : ℕ) (src tgt : List ℕ) : Multiset (List ℕ × ℕ) :=
  ((crossRows n).filter fun r => r.1 = src ∧ r.2.1 = tgt).map fun r => r.2.2

/-- The two staircases of the square, and the permutations they perform. -/
def staircases : Multiset (List ℕ × ℕ) := rowsOfShape 2 [1, 1] [2]

/-- Out of the run of `□³`, every permutation of `S₃` occurs — the whole `Δ`-interval. -/
def runRows : Multiset (List ℕ × ℕ) := rowsOfShape 3 [1, 1, 1] [3]

/-- Out of a two-bead chain, only the minimal-length coset representatives occur. -/
def cosetRows : Multiset (List ℕ × ℕ) := rowsOfShape 3 [1, 2] [3]

#eval staircases   -- {([0, 1], 0), ([1, 0], 1)}
#eval runRows      -- all six of S₃, lengths 0,1,1,2,2,3
#eval cosetRows    -- {([0,1,2], 0), ([1,0,2], 1), ([2,0,1], 2)}

end CubeChains
