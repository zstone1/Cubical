import CubeChains.Chains.Correspondence
import CubeChains.Chains.CoordFunctor
import Mathlib.Data.Fintype.Pi

/-!
# Testing/Enumerate — verified finite enumeration of `Ch (□n)`

For the standard cube `□n` — finite and loop-free — `Ch (□n)` is a finite category, so its objects
and (thin) hom-sets can be enumerated with a completeness proof.  Bottom-up:

* `Cell N k` is a decidable finite subtype (`Fin N → Option Bool` with `k` free coordinates);
* hence `(cube n).cells k ≃ Cell n k` is finite and decidable (cube Yoneda);
* a chain of `□n` has `dimSum = n` (`wedgeDimSum_eq`), so `length ≤ n` — the bound that makes the
  object set finite.

Loops are the only obstruction: with a directed cycle `CubeChain K` is genuinely infinite.  The
cube's altitude (`cube_admitsAltitude`) rules that out.

Not built by `lake build CubeChains`.
-/

open CategoryTheory StdCube

namespace StdCube

instance instDecidableEqCell (N k : ℕ) : DecidableEq (Cell N k) :=
  inferInstanceAs (DecidableEq {c : Fin N → Option Bool // (noneSet c).card = k})

instance instFintypeCell (N k : ℕ) : Fintype (Cell N k) :=
  inferInstanceAs (Fintype {c : Fin N → Option Bool // (noneSet c).card = k})

/-- A cube has no `k`-cell above its dimension: `Cell N k` is empty for `k > N`. -/
instance instIsEmptyCell {N k : ℕ} (h : N < k) : IsEmpty (Cell N k) :=
  ⟨fun c => absurd (c.prop ▸ (Finset.card_le_univ _).trans_eq (Finset.card_fin N)) (by omega)⟩

end StdCube

open StdCube BPSet

/-- Cube Yoneda: a `k`-cell of `□n` is a `Cell n k` (a `k`-face of the `n`-cube). -/
def cubeCellEquiv (n k : ℕ) : (cube n).cells k ≃ Cell n k := cubeRepr (stdPre n) k

instance instFintypeCubeCells (n k : ℕ) : Fintype ((cube n).cells k) :=
  Fintype.ofEquiv (Cell n k) (cubeCellEquiv n k).symm

instance instDecidableEqCubeCells (n k : ℕ) : DecidableEq ((cube n).cells k) :=
  (cubeCellEquiv n k).decidableEq

/-! ## The chain-length bound: a chain of `□n` has `dimSum = n`, so `length ≤ n` -/

/-- Each bead has dimension `≥ 1`, so a dimension list is at least as long as its total. -/
theorem length_le_dimSum : ∀ l : List ℕ+, l.length ≤ dimSum l
  | [] => by simp [dimSum]
  | d :: ds => by
    have ih := length_le_dimSum ds
    have hd : 0 < (d : ℕ) := d.pos
    simp only [dimSum, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- **A cube chain of `□n` has total dimension `n`** — it traverses every direction exactly once
(`wedgeDimSum_eq`). -/
theorem CubeChain.dimSum_cube (n : ℕ) (C : CubeChain (cube n)) : dimSum C.dims = n :=
  CubeChains.wedgeDimSum_eq (CubeChain.wedgeOfChain C).2

/-- **A cube chain of `□n` has at most `n` cubes.** -/
theorem CubeChain.length_le_cube (n : ℕ) (C : CubeChain (cube n)) : C.cubes.length ≤ n := by
  have h := length_le_dimSum C.dims
  rw [CubeChain.dimSum_cube n C] at h
  simpa [CubeChain.dims] using h

/-! ## Decidability: chains and refinements are decidable data -/

/-- `IsCubeChain` is decidable — a fold of decidable vertex equalities. -/
instance decIsCubeChain (K : BPSet) [DecidableEq (K.cells 0)] :
    ∀ (a : K.cells 0) (l : List (Σ n : ℕ+, K.cells (n : ℕ))) (b : K.cells 0),
      Decidable (IsCubeChain a l b)
  | a, [], b => decEq a b
  | a, ⟨_, c⟩ :: rest, b =>
      have := decIsCubeChain K (K.toPsh.vertex₁ c) rest b
      inferInstanceAs (Decidable (K.toPsh.vertex₀ c = a ∧ IsCubeChain (K.toPsh.vertex₁ c) rest b))

instance instDecidableEqCubeOf (n : ℕ) : DecidableEq (Σ k : ℕ+, (cube n).cells k) :=
  inferInstance

instance instDecidableEqCubeChain (n : ℕ) : DecidableEq (CubeChain (cube n)) :=
  inferInstanceAs (DecidableEq {l : List (Σ k : ℕ+, (cube n).cells k) //
    IsCubeChain (cube n).init l (cube n).final})

/-! ## `Fintype (CubeChain (cube n))` — dimensions `1..n`, chains bounded by length `n` -/

/-- The cubes of `□n`: dimensions run `1..n`, so finitely many. -/
instance instFintypeCubeOf (n : ℕ) : Fintype (Σ k : ℕ+, (cube n).cells k) :=
  Fintype.ofEquiv {p : Σ k : Fin (n + 1), Cell n (k : ℕ) // 0 < (p.1 : ℕ)}
    { toFun := fun q => ⟨⟨(q.1.1 : ℕ), q.2⟩, (cubeCellEquiv n (q.1.1 : ℕ)).symm q.1.2⟩
      invFun := fun p => ⟨⟨⟨(p.1 : ℕ), by
          by_cases h : (p.1 : ℕ) < n + 1
          · exact h
          · exact ((instIsEmptyCell (N := n) (k := (p.1 : ℕ)) (by omega)).false
              (cubeCellEquiv n (p.1 : ℕ) p.2)).elim⟩,
          cubeCellEquiv n (p.1 : ℕ) p.2⟩, p.1.pos⟩
      left_inv := by
        rintro ⟨⟨kf, cell⟩, hpos⟩
        exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Equiv.apply_symm_apply _ _)))
      right_inv := by
        rintro ⟨k, c⟩
        exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Equiv.symm_apply_apply _ _)) }
