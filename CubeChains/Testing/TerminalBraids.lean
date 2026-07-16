import CubeChains.Braid.BraidWord
import CubeChains.Braid.ElementaryBraiding
import CubeChains.Braid.ChGrading
import CubeChains.Foundations.Terminal
import CubeChains.Testing.BraidTest

/-!
# Testing/TerminalBraids — braidGrading on the terminal precubical set (paths of length 4)

`Zbp` is the terminal precubical set (one cell per dimension).  A path of length 4 is the chain
`[4]` — one 4-cube bead, four concurrent events.  Its events carry no refinement-invariant axis
name (unlike `□⁴`), so reordering them realizes the **whole braid group `B₄`**: `lineOf σ` orders
the events by `σ`, and `braidGrading` sends the sequentialization to the simple braid `ofPerm σ`
— the germ generators of `B₄`.  Uses the `Testing/BraidTest` library throughout.
Not built by `lake build CubeChains`.
-/

open CubeChains CubeChains.BraidTest CategoryTheory Opposite BPSet

/-- A path of length 4 in the terminal set: the single 4-cube chain (map to `Z` is forced). -/
def cZ4 : Ch Zbp := ⟨[4], ⟨toZ _, rfl, rfl⟩⟩

/-- The 4-cube execution: `cZ4` with the standard event order. -/
def execZ4 : ConcCat Zbp := ⟨op cZ4, stdLine _⟩

/-- Reorder the four events by `σ` (single bead → `Fin.cons` at the literal index `0`, where
`beadDim` reduces to `4`). -/
def lineOf (σ : Equiv.Perm (Fin 4)) : LinesObj execZ4.chain :=
  Fin.cons (chamberOfPerm σ) (fun i => i.elim0)

/-- **The harness**: the braid `braidGrading` assigns to reordering the four events by `σ`. -/
def bword (σ : Equiv.Perm (Fin 4)) : List ℤ := braidWordZ (seqMor execZ4 (lineOf σ))

#eval nEvents execZ4                              -- 4

/-! ## The whole braid group `B₄` is realized -/

#eval bword (Equiv.refl _)                        -- 1  = []
#eval bword (Equiv.swap 0 1)                      -- σ₁ = [1]
#eval bword (Equiv.swap 1 2)                      -- σ₂ = [2]
#eval bword (Equiv.swap 2 3)                      -- σ₃ = [3]
#eval bword (Equiv.swap 0 3)                      -- [1, 2, 3, 2, 1]
#eval bword (Equiv.swap 0 3 * Equiv.swap 1 2)     -- the reversal w₀ = [1, 2, 3, 1, 2, 1]

-- Every reordering at once — all `4! = 24`, via the library:
#eval (allBraids execZ4).length                   -- 24
#eval allBraids execZ4                            -- the 24 braid words of B₄

/-- **Injectivity over all of `S₄`** (machine-checked): the 24 reorderings give 24 *distinct* braid
words.  This is the easy retraction direction — `wordShadow` recovers `σ` (below). -/
example : (allBraids execZ4).Nodup := by native_decide

#eval wordShadow 4 (bword (Equiv.swap 0 1))       -- [1, 0, 2, 3]  (recovers swap 0 1)
#eval wordShadow 4 (bword (Equiv.swap 0 3))       -- [3, 1, 2, 0]  (recovers swap 0 3)

/-! ## A few loops — sanity check

"Out via `σ`, back via `τ`" is `ofPerm σ · (ofPerm τ)⁻¹`, monodromy `σ·τ⁻¹`; `σ = τ` is trivial. -/

/-- The braid word of the loop "out via `σ`, back via `τ`". -/
def loopWord (σ τ : Equiv.Perm (Fin 4)) : List ℤ := bword σ ++ invWordZ (bword τ)

#eval loopWord (Equiv.swap 0 1) (Equiv.swap 0 1)              -- [1, -1]  (reduces to 1)
#eval wordShadow 4 (loopWord (Equiv.swap 0 1) (Equiv.swap 0 1))  -- [0,1,2,3]  identity
#eval loopWord (Equiv.swap 0 3) (Equiv.swap 0 1)              -- [1, 2, 3, 2, 1, -1]
#eval wordShadow 4 (loopWord (Equiv.swap 0 3) (Equiv.swap 0 1))  -- [1,3,2,0]  = σ·τ⁻¹

/-- Sanity: a loop out-and-back the same way has trivial monodromy. -/
example : wordShadow 4 (loopWord (Equiv.swap 0 3) (Equiv.swap 0 3)) = List.finRange 4 := by
  native_decide

/-- Sanity: the `(swap 0 3, swap 0 1)` loop's monodromy is `swap 0 3 · swap 0 1 = [1,3,2,0]`, not
garbage. -/
example : wordShadow 4 (loopWord (Equiv.swap 0 3) (Equiv.swap 0 1)) = [1, 3, 2, 0] := by
  native_decide
