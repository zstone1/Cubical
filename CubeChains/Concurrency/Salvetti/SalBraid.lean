import CubeChains.Machinery.SortPerm
import CubeChains.Concurrency.Salvetti.SalExec
import CubeChains.Concurrency.Salvetti.SalvettiConstruction

/-!
# Concurrency/Salvetti/SalBraid — a Salvetti cell's tope order is its run word

A cell's `topePerm` is the word its tope spells, inverted (`topePerm_eq`), because `topeRank`
counts predecessors and a run word's predecessor count at `p` is the step `w⁻¹ p` at which `p`
fires.  `Concurrency/Salvetti/WallCrossing` reads the walls off that.
-/

open CategoryTheory Opposite CubeChain BPSet

namespace CubeChains

open COM ChStar

variable {n : ℕ}

/-! ## The rank of a run word -/


/-- `topeRank_eq_card` off a bare tope rather than a cell. -/
theorem topeRank_eq_card' {T : SignVec (BraidGround n)} (hT : (braidCOM n).IsTope T)
    {σ : Fin n → ℤ} (h : T = braidSign σ) (i : Fin n) :
    (topeRank T i : ℕ) = (Finset.univ.filter (fun j => σ j < σ i)).card :=
  topeRank_eq_card (a := topeCell ⟨T, hT⟩) h i

/-- **The tope rank of a run word is the step at which the coordinate fires.**  `topeRank` counts
predecessors in the tope's order, and a run word's order *is* `w⁻¹`. -/
theorem topeRank_wordTope (w : Equiv.Perm (Fin n)) (p : Fin n) :
    topeRank (wordTope w) p = w.symm p := by
  refine Fin.ext ?_
  rw [topeRank_eq_card' (isTope_wordTope w) (wordTope_eq_braidSign w) p]
  simp only [Nat.cast_lt, ← Fin.lt_def]
  exact Equiv.Perm.card_filter_lt w.symm (w.symm p)

/-! ## The dictionary -/

/-- The run word of a Salvetti cell: the word its tope names. -/
abbrev cellWord (a : Sal (braidCOM n)) : Equiv.Perm (Fin n) :=
  wordTopeEquiv.symm ⟨a.tope, a.2.2.1⟩

/-- **A cell's permutation is its run word, inverted.** -/
theorem topePerm_eq (a : Sal (braidCOM n)) : topePerm a = (cellWord a).symm := by
  have hw : wordTope (cellWord a) = a.tope := wordTope_symm _
  refine Equiv.ext fun p => ?_
  rw [topePerm_apply, ← hw, topeRank_wordTope]

end CubeChains
