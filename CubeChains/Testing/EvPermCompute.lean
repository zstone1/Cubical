import CubeChains.Braid.ChGrading

/-!
# Testing/EvPermCompute

The event permutation `evPerm'` of a refinement `#eval`s on a concrete execution.  With
`keyEquiv`/`eventEquiv` given explicit `Fintype.bijInv` inverses, `evIdx'`/`evPerm'` run both ways.
Here `K = ⋁[2]` (a single 2-cube), the execution is the identity chain under the standard line, and
the identity refinement's permutation is the identity of its two events.  Not built by
`lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChain CubeChains

/-- The identity chain of the single 2-cube `⋁[2]`. -/
def chainK2 : Ch (⋁([2] : List ℕ+)) := ⟨[2], 𝟙 _⟩

/-- A concrete execution of `K = ⋁[2]`: `chainK2` under its standard line. -/
def execK2 : ConcCat (⋁([2] : List ℕ+)) := ⟨op chainK2, stdLine chainK2⟩

#eval nEvents execK2                                              -- 2
#eval (List.finRange (nEvents execK2)).map (evPerm' (𝟙 execK2))   -- [0, 1]

/-- Machine-checked: the identity refinement's event permutation fixes every event. -/
example : (List.finRange (nEvents execK2)).map (evPerm' (𝟙 execK2))
    = List.finRange (nEvents execK2) := by native_decide
