import CubeChains.Braid.BraidWord
import CubeChains.Braid.ElementaryBraiding
import CubeChains.Braid.ChGrading
import CubeChains.Foundations.Terminal

/-!
# Testing/TerminalBraids — braidGrading on the terminal precubical set (paths of length 4)

`Zbp` is the terminal precubical set (one cell per dimension).  A path of length 4 is the chain
`[4]` — one 4-cube bead, four concurrent events.  Its events carry no refinement-invariant axis
name (unlike `□⁴`), so reordering them realizes the **whole braid group `B₄`**: `lineOfPerm σ`
orders the events by `σ`, and `braidGrading` sends the sequentialization to the simple braid
`ofPerm σ` — the germ generators of `B₄`.

The map `σ ↦ braidGrading(seqMor …)` is injective: `evPerm'` recovers `σ`.
Not built by `lake build CubeChains`.
-/

open CubeChains CategoryTheory Opposite BPSet

/-- A path of length 4 in the terminal set: the single 4-cube chain (map to `Z` is forced). -/
def cZ4 : Ch Zbp := ⟨[4], ⟨toZ _, rfl, rfl⟩⟩

/-- The 4-cube execution: `cZ4` with the standard event order. -/
def execZ4 : ConcCat Zbp := ⟨op cZ4, stdLine _⟩

/-- The chamber of a permutation `σ`: order the events by `σ`. -/
def chamberOfPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Chamber d :=
  (stdChamber d).restrict (fun i => σ i) (Equiv.injective σ)

/-- Reorder the four events by `σ` (the chain has a single bead, so `Fin.cons` places the chamber
at the literal index `0`, where `beadDim` reduces to `4`). -/
def lineOfPerm (σ : Equiv.Perm (Fin 4)) : LinesObj execZ4.chain :=
  Fin.cons (chamberOfPerm σ) (fun i => i.elim0)

/-- **The harness**: the braid `braidGrading` assigns to reordering the four events by `σ`. -/
def bword (σ : Equiv.Perm (Fin 4)) : List ℤ := braidWordZ (seqMor execZ4 (lineOfPerm σ))

/-- Its underlying permutation (the recovered reordering — the injectivity witness). -/
def shadow (σ : Equiv.Perm (Fin 4)) : List (Fin 4) :=
  (List.finRange 4).map (evPerm' (seqMor execZ4 (lineOfPerm σ)))

#eval nEvents execZ4                              -- 4

/-! ## The whole braid group `B₄` is realized -/

#eval bword (Equiv.refl _)          -- 1        = []
#eval bword (Equiv.swap 0 1)        -- σ₁       = [1]
#eval bword (Equiv.swap 1 2)        -- σ₂       = [2]
#eval bword (Equiv.swap 2 3)        -- σ₃       = [3]
#eval bword (Equiv.swap 0 3)        -- σ₁σ₂σ₃σ₂σ₁ = [1, 2, 3, 2, 1]
#eval bword (Equiv.swap 0 1 * Equiv.swap 2 3)              -- a product
#eval bword (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3)  -- a 4-cycle

-- The longest element `w₀` — the positive half-twist of `B₄` (writhe 6).
#eval braidWordZ (seqMor execZ4 (fun i => revChamber (ChainCat.beadDim _ i)))  -- [1,2,3,1,2,1]

/-! ## Injectivity: `braidGrading` distinguishes the reorderings

`shadow σ` is the underlying permutation of the braid — it recovers `σ`, so distinct orderings give
distinct braids.  Below, the three adjacent transpositions produce three distinct simple braids. -/

#eval shadow (Equiv.swap 0 1)       -- [1, 0, 2, 3]
#eval shadow (Equiv.swap 2 3)       -- [0, 1, 3, 2]

/-- Machine-checked injectivity on a sample: distinct reorderings ↦ distinct braid words. -/
example :
    [bword (Equiv.refl _), bword (Equiv.swap 0 1), bword (Equiv.swap 1 2),
      bword (Equiv.swap 2 3), bword (Equiv.swap 0 3)].Nodup := by native_decide
