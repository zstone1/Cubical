import CubeChains.Braid.BraidWord
import CubeChains.Braid.ElementaryBraiding
import CubeChains.Braid.ChGrading
import Mathlib.GroupTheory.Perm.Fin

/-!
# Testing/BraidTest — a little library for constructing braidGrading tests

Enumerate *all* orderings automatically instead of picking lines by hand.  For an execution `x`,
`allBraids x` is the braid word `braidGrading` assigns to **every** reordering of its events.
Everything here is computable (`#eval`/`native_decide`); intended for ≤ 10 events.

Pipeline: `allPerms n` (all `n!` permutations) → `allChambers` (orderings of one bead) → `allLines`
(orderings of every bead, a dependent product) → `allBraids` (a braid word per line).
-/

namespace CubeChains.BraidTest

open CubeChains

/-- Every permutation of `Fin n`, computably (via `Equiv.Perm.decomposeFin`). -/
def allPerms : (n : ℕ) → List (Equiv.Perm (Fin n))
  | 0 => [Equiv.refl _]
  | n + 1 => (List.finRange (n + 1)).flatMap fun i =>
      (allPerms n).map fun p => Equiv.Perm.decomposeFin.symm (i, p)

/-- A permutation as a chamber: order the directions by `σ`. -/
def chamberOfPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Chamber d :=
  (stdChamber d).restrict (fun i => σ i) (Equiv.injective σ)

/-- The underlying permutation of a signed braid word (`Bₙ ↠ Sₙ`, computed directly — the
generators are involutions, so signs are irrelevant).  The injectivity/monodromy witness. -/
def wordPerm {n : ℕ} (w : List ℤ) : Equiv.Perm (Fin n) :=
  (w.map fun a => if h : a.natAbs - 1 < n - 1 then adjT ⟨a.natAbs - 1, h⟩ else 1).prod

/-- The permutation of a word as an image list `[w·0, w·1, …]` — the readable form. -/
def wordShadow (n : ℕ) (w : List ℤ) : List (Fin n) := (List.finRange n).map (wordPerm w)

/-- Every chamber (strict total order) of `Fin d`. -/
def allChambers (d : ℕ) : List (Chamber d) := (allPerms d).map chamberOfPerm

/-- Every dependent section, given a choice-list at each index (a computable dependent product). -/
def piList : (L : ℕ) → {β : Fin L → Type} → (∀ i, List (β i)) → List (∀ i, β i)
  | 0, _, _ => [fun i => i.elim0]
  | _ + 1, _, ch => (ch 0).flatMap fun c =>
      (piList _ (fun i => ch i.succ)).map fun t => Fin.cons c t

/-- Every line of a chain: an independent ordering for each bead's events. -/
def allLines {K : BPSet} (a : Ch K) : List (LinesObj a) :=
  piList a.dims.length (fun i => allChambers (ChainCat.beadDim a i))

/-- **braidGrading on every reordering**: the braid word of `seqMor x M` for every line `M`. -/
def allBraids {K : BPSet} (x : ConcCat K) : List (List ℤ) :=
  (allLines x.chain).map fun M => braidWordZ (seqMor x M)

end CubeChains.BraidTest

section Sanity
open CubeChains CubeChains.BraidTest
#eval (allPerms 3).length      -- 6
#eval (allPerms 4).length      -- 24
end Sanity
