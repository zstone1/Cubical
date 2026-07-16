import CubeChains.Braid.BraidWord
import CubeChains.Braid.ChGrading
import CubeChains.Testing.BraidTest

/-!
# Testing/BraidWordCompute

The Artin word emitter `#eval`s.  `permWord σ` bubble-sorts `σ` into a reduced word of adjacent
transpositions; `wordToBraid (permWord σ) = ofPerm σ` (proven, so it also names the braid content
of `braidGrading.map`) and its length is the writhe `permLen σ`.  Here `σ = swap 0 2` on `Fin 3`
(three inversions), so the word has three letters.  `braidWordZ` is the signed GAP form.  Not built
by `lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChains.BraidTest

/-- A concrete non-identity permutation: `swap 0 2` on `Fin 3`, with three inversions. -/
def revPerm3 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

#eval permLen revPerm3                       -- 3
#eval (permWord revPerm3).map Fin.val        -- a length-3 reduced word of generator indices
#eval permWordZ revPerm3                      -- the signed (1-based, all-positive) GAP word

/-- Machine-checked: the emitted word has writhe-many letters. -/
example : (permWord revPerm3).length = permLen revPerm3 := by native_decide

-- The reduced word of every permutation of `Fin 3` at once, via `Testing/BraidTest`:
#eval (allPerms 3).map permWordZ     -- [[], [2], [1], [1,2], [1,2,1], [2,1]]  (all 6 of S₃)

/-- The emitted word always realises the germ generator — the braid content of `braidGrading.map`.
(A proof, not a `#eval`: `Braid n` is a `PresentedGroup`, with no `DecidableEq`.) -/
example (σ : Equiv.Perm (Fin 3)) : wordToBraid (permWord σ) = ofPerm σ := wordToBraid_permWord σ

/-- The concrete execution from the evPerm witness (`K = ⋁[2]`, identity chain, standard line). -/
def exec2 : ConcCat (⋁([2] : List ℕ+)) := ⟨op ⟨[2], 𝟙 _⟩, stdLine _⟩

-- The identity refinement is trivial, so its braid word is empty (evPerm' = 1); a nonempty word
-- from a genuine reordering refinement awaits gvp.7's concrete cross-block refinement.
#eval braidWordZ (𝟙 exec2)                    -- []
