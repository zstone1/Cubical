import CubeChains.Concurrency.Salvetti.SalExec

/-!
# Concurrency/Salvetti/SalBraid — a Salvetti cell's tope is a run word

A cell's tope is a chamber, and a chamber *is* the run word it spells (`wordTopeEquiv`), so a cell
names a word (`cellWord`) and a Salvetti edge names the reordering between two
(`topeCross` — the arrangement's crossing permutation, against `ChainCat.crossPerm`'s wedge-map
reading).  `Concurrency/Salvetti/WallCrossing` reads the walls off it.
-/

open CategoryTheory Opposite CubeChain BPSet

namespace CubeChains

open COM ChStar

variable {n : ℕ}

/-- The run word of a Salvetti cell: the word its tope names. -/
abbrev cellWord (a : Sal (braidCOM n)) : Equiv.Perm (Fin n) :=
  wordTopeEquiv.symm ⟨a.tope, a.2.2.1⟩

/-- A cell's word is pinned by its tope. -/
theorem cellWord_of_tope (a : Sal (braidCOM n)) (w : Equiv.Perm (Fin n)) (h : a.tope = wordTope w) :
    cellWord a = w :=
  wordTope_injective ((wordTope_symm ⟨a.tope, a.2.2.1⟩).trans h)

/-- **The crossing permutation of a Salvetti edge** `a ⟶ b`: the reordering from `a`'s word to
`b`'s. -/
def topeCross (a b : Sal (braidCOM n)) : Equiv.Perm (Fin n) := (cellWord b)⁻¹ * cellWord a

@[simp] theorem topeCross_self (a : Sal (braidCOM n)) : topeCross a a = 1 := inv_mul_cancel _

end CubeChains
