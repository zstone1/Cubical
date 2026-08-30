import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Perm.Basic

/-!
# Machinery/Blocks — consecutive blocks of a composition, and their parabolic subgroup

A composition `ds : List ℕ` cuts `Fin n` into consecutive blocks; `blockOfPos ds` names the block
a position falls in, and `parabolic n ds` is the subgroup of permutations preserving every block —
the Young subgroup `S_{d₁} × ⋯ × S_{d_k}`.
-/

variable {n : ℕ}

/-- Which block of the composition `ds` the position `p` falls in. -/
def blockOfPos : List ℕ → ℕ → ℕ
  | [], _ => 0
  | d :: ds, p => if p < d then 0 else blockOfPos ds (p - d) + 1

@[simp] theorem blockOfPos_nil (p : ℕ) : blockOfPos [] p = 0 := rfl

theorem blockOfPos_cons_of_lt {d p : ℕ} (ds : List ℕ) (h : p < d) : blockOfPos (d :: ds) p = 0 :=
  if_pos h

theorem blockOfPos_cons_of_le {d p : ℕ} (ds : List ℕ) (h : d ≤ p) :
    blockOfPos (d :: ds) p = blockOfPos ds (p - d) + 1 :=
  if_neg (Nat.not_lt.2 h)

theorem blockOfPos_cons_add (d : ℕ) (ds : List ℕ) (p : ℕ) :
    blockOfPos (d :: ds) (d + p) = blockOfPos ds p + 1 := by
  rw [blockOfPos_cons_of_le ds (Nat.le_add_right d p), Nat.add_sub_cancel_left]

/-- The parabolic subgroup of permutations preserving each consecutive block of sizes `ds`. -/
def parabolic (n : ℕ) (ds : List ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i : Fin n, blockOfPos ds ((σ i : Fin n) : ℕ) = blockOfPos ds (i : ℕ)}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb i := by rw [Equiv.Perm.mul_apply, ha (b i), hb i]
  inv_mem' {a} ha i := by
    have h := ha (a⁻¹ i)
    rw [show a (a⁻¹ i) = i by simp] at h
    exact h.symm

theorem mem_parabolic {ds : List ℕ} {σ : Equiv.Perm (Fin n)} :
    σ ∈ parabolic n ds ↔ ∀ i : Fin n, blockOfPos ds ((σ i : Fin n) : ℕ) = blockOfPos ds (i : ℕ) :=
  Iff.rfl

/-- A transposition lies in the parabolic exactly when it stays inside one block. -/
theorem mem_parabolic_swap {ds : List ℕ} {i j : Fin n} :
    Equiv.swap i j ∈ parabolic n ds ↔ blockOfPos ds (i : ℕ) = blockOfPos ds (j : ℕ) := by
  constructor
  · intro h
    have h' := h i
    rwa [Equiv.swap_apply_left, eq_comm] at h'
  · intro h k
    by_cases hki : k = i
    · subst hki; rw [Equiv.swap_apply_left]; exact h.symm
    · by_cases hkj : k = j
      · subst hkj; rw [Equiv.swap_apply_right]; exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
