import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Braid/BlockPerm — juxtaposition of permutations

`blockPerm σ τ` runs `σ` on the first `n` strands and `τ` on the last `m`, so no strand ever leaves
its block.  This is the permutation shadow of braid juxtaposition, and it is where the `+` on strand
counts comes from.

Associativity is strict only after the `Fin`-recast along `Nat.add_assoc` (`blockPerm_assoc`).
-/

namespace CubeChains

variable {n m k : ℕ}

/-- The **block permutation**: `σ` on the first `n` strands, `τ` on the last `m`. -/
def blockPerm (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (n + m)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)

@[simp] theorem blockPerm_castAdd (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (i : Fin n) :
    blockPerm σ τ (Fin.castAdd m i) = Fin.castAdd m (σ i) := by
  simp [blockPerm, Equiv.permCongr_apply]

@[simp] theorem blockPerm_natAdd (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    blockPerm σ τ (Fin.natAdd n j) = Fin.natAdd n (τ j) := by
  simp [blockPerm, Equiv.permCongr_apply]

theorem blockPerm_one : blockPerm (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin m)) = 1 := by
  apply Equiv.ext
  intro a
  induction a using Fin.addCases with
  | left i => simp
  | right j => simp

theorem blockPerm_mul (σ σ' : Equiv.Perm (Fin n)) (τ τ' : Equiv.Perm (Fin m)) :
    blockPerm (σ * σ') (τ * τ') = blockPerm σ τ * blockPerm σ' τ' := by
  apply Equiv.ext
  intro a
  induction a using Fin.addCases with
  | left i => simp [Equiv.Perm.mul_apply]
  | right j => simp [Equiv.Perm.mul_apply]

theorem blockPerm_inv (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    (blockPerm σ τ)⁻¹ = blockPerm σ⁻¹ τ⁻¹ :=
  inv_eq_of_mul_eq_one_left (by rw [← blockPerm_mul, inv_mul_cancel, inv_mul_cancel, blockPerm_one])

/-- The block permutation acts blockwise: a strand of block 1 stays in block 1. -/
theorem blockPerm_val_lt (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (a : Fin (n + m))
    (i : Fin n) (h : (a : ℕ) = (i : ℕ)) :
    ((blockPerm σ τ a : Fin (n + m)) : ℕ) = (σ i : ℕ) := by
  have ha : a = Fin.castAdd m i := Fin.ext h
  rw [ha, blockPerm_castAdd]
  rfl

theorem blockPerm_val_ge (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (a : Fin (n + m))
    (j : Fin m) (h : (a : ℕ) = n + (j : ℕ)) :
    ((blockPerm σ τ a : Fin (n + m)) : ℕ) = n + (τ j : ℕ) := by
  have ha : a = Fin.natAdd n j := Fin.ext (by simpa using h)
  rw [ha, blockPerm_natAdd]
  simp

theorem blockPerm_inv_castAdd (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (i : Fin n) :
    (blockPerm σ τ)⁻¹ (Fin.castAdd m i) = Fin.castAdd m (σ⁻¹ i) := by
  rw [blockPerm_inv, blockPerm_castAdd]

theorem blockPerm_inv_natAdd (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    (blockPerm σ τ)⁻¹ (Fin.natAdd n j) = Fin.natAdd n (τ⁻¹ j) := by
  rw [blockPerm_inv, blockPerm_natAdd]

/-- The block permutation acts blockwise: a strand of block 1 stays in block 1. -/
theorem blockPerm_inv_val_lt (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (a : Fin (n + m))
    (i : Fin n) (h : (a : ℕ) = (i : ℕ)) :
    (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) = (σ⁻¹ i : ℕ) := by
  have ha : a = Fin.castAdd m i := Fin.ext h
  rw [ha, blockPerm_inv_castAdd]
  rfl

theorem blockPerm_inv_val_ge (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) (a : Fin (n + m))
    (j : Fin m) (h : (a : ℕ) = n + (j : ℕ)) :
    (((blockPerm σ τ)⁻¹ a : Fin (n + m)) : ℕ) = n + (τ⁻¹ j : ℕ) := by
  have ha : a = Fin.natAdd n j := Fin.ext (by simpa using h)
  rw [ha, blockPerm_inv_natAdd]
  simp

/-- Associativity, strict after the `Fin`-recast along `Nat.add_assoc`. -/
theorem blockPerm_assoc (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m))
    (ρ : Equiv.Perm (Fin k)) :
    (finCongr (Nat.add_assoc n m k)).permCongr (blockPerm (blockPerm σ τ) ρ)
      = blockPerm σ (blockPerm τ ρ) := by
  refine Equiv.ext fun c => Fin.ext ?_
  rw [Equiv.permCongr_apply]
  set c' : Fin (n + m + k) := (finCongr (Nat.add_assoc n m k)).symm c with hc'def
  have hcv : (c' : ℕ) = (c : ℕ) := rfl
  have hstrip : ((finCongr (Nat.add_assoc n m k) (blockPerm (blockPerm σ τ) ρ c') :
      Fin (n + (m + k))) : ℕ) = ((blockPerm (blockPerm σ τ) ρ c' : Fin (n + m + k)) : ℕ) := rfl
  rw [hstrip]
  have hc := c.isLt
  by_cases h1 : (c : ℕ) < n
  · rw [blockPerm_val_lt (blockPerm σ τ) ρ c' (⟨(c : ℕ), by omega⟩ : Fin (n + m)) rfl,
      blockPerm_val_lt σ τ _ (⟨(c : ℕ), h1⟩ : Fin n) rfl,
      blockPerm_val_lt σ (blockPerm τ ρ) c (⟨(c : ℕ), h1⟩ : Fin n) rfl]
  · by_cases h2 : (c : ℕ) < n + m
    · rw [blockPerm_val_lt (blockPerm σ τ) ρ c' (⟨(c : ℕ), h2⟩ : Fin (n + m)) rfl,
        blockPerm_val_ge σ τ _ (⟨(c : ℕ) - n, by omega⟩ : Fin m)
          (by exact (show (c : ℕ) = n + ((c : ℕ) - n) by omega)),
        blockPerm_val_ge σ (blockPerm τ ρ) c (⟨(c : ℕ) - n, by omega⟩ : Fin (m + k))
          (by exact (show (c : ℕ) = n + ((c : ℕ) - n) by omega)),
        blockPerm_val_lt τ ρ _ (⟨(c : ℕ) - n, by omega⟩ : Fin m) rfl]
    · rw [blockPerm_val_ge (blockPerm σ τ) ρ c' (⟨(c : ℕ) - n - m, by omega⟩ : Fin k)
          (by exact (show (c : ℕ) = n + m + ((c : ℕ) - n - m) by omega)),
        blockPerm_val_ge σ (blockPerm τ ρ) c (⟨(c : ℕ) - n, by omega⟩ : Fin (m + k))
          (by exact (show (c : ℕ) = n + ((c : ℕ) - n) by omega)),
        blockPerm_val_ge τ ρ _ (⟨(c : ℕ) - n - m, by omega⟩ : Fin k)
          (by exact (show (c : ℕ) - n = m + ((c : ℕ) - n - m) by omega))]
      omega

end CubeChains
