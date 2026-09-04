import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Perm.Basic

/-!
# Machinery/Composition — `Composition.index` against the prefix sums

Mathlib pins `Composition.index` by a sandwich, `sizeUpTo (index p) ≤ p < sizeUpTo (index p + 1)`.
Stated as one order relation (`index_lt_iff`) it carries no side condition, and everything about
blocks below follows: monotonicity, which block a junction starts, and the Young subgroup of
permutations preserving every block.
-/

/-- A `List.sum` of a map read as a `Fin`-indexed `Finset.sum`; the bridge between the two ways
this repo counts a list of block sizes. -/
theorem List.sum_map_eq_sum_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    (l.map f).sum = ∑ k : Fin l.length, f (l.get k) := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

namespace Composition

variable {n : ℕ} (c : Composition n)

/-- **The block index against the prefix sums**: a position lies before the `j`-th junction exactly
when its block does. -/
theorem index_lt_iff (p : Fin n) (j : ℕ) : (c.index p : ℕ) < j ↔ (p : ℕ) < c.sizeUpTo j := by
  refine ⟨fun h => lt_of_lt_of_le (c.lt_sizeUpTo_index_succ p) (c.monotone_sizeUpTo h),
    fun h => ?_⟩
  by_contra hc
  exact absurd (le_trans (c.monotone_sizeUpTo (not_lt.mp hc)) (c.sizeUpTo_index_le p)) (by omega)

/-- **Blocks are consecutive**: the block index rises with the position. -/
theorem index_monotone : Monotone fun p : Fin n => (c.index p : ℕ) := fun p q hpq => by
  show (c.index p : ℕ) ≤ (c.index q : ℕ)
  by_contra hc
  have hlt : (c.index q : ℕ) < (c.index p : ℕ) := by omega
  exact absurd (lt_of_lt_of_le ((c.index_lt_iff q ((c.index p : ℕ))).mp hlt)
    (c.sizeUpTo_index_le p)) (not_lt.mpr (Fin.le_def.mp hpq))

/-- **The block a position lies in, from the bracket around it.** -/
theorem index_eq_of_bracket {j : ℕ} (p : Fin n) (h1 : c.sizeUpTo j ≤ (p : ℕ))
    (h2 : (p : ℕ) < c.sizeUpTo (j + 1)) : (c.index p : ℕ) = j := by
  have k1 : ¬ ((c.index p : ℕ) < j) := fun hc => absurd ((c.index_lt_iff p j).mp hc) (by omega)
  have k2 : (c.index p : ℕ) < j + 1 := (c.index_lt_iff p (j + 1)).mpr h2
  omega

/-- The first position lies in the first block. -/
theorem index_zero {p : Fin n} (hp : (p : ℕ) = 0) : (c.index p : ℕ) = 0 := by
  have hs := c.sizeUpTo_strict_mono (c.length_pos_iff.mpr (Nat.pos_of_ne_zero fun h =>
    absurd p.isLt (by omega)))
  simp only [sizeUpTo_zero] at hs
  exact c.index_eq_of_bracket p (by simp [hp]) (by rw [hp]; exact hs)

/-- Consecutive positions lie in the same block or in adjacent ones. -/
theorem index_succ_le {p q : Fin n} (hpq : (q : ℕ) = (p : ℕ) + 1) :
    (c.index q : ℕ) ≤ (c.index p : ℕ) + 1 := by
  have hlt : (p : ℕ) < c.sizeUpTo ((c.index p : ℕ) + 1) := c.lt_sizeUpTo_index_succ p
  have key : (q : ℕ) < c.sizeUpTo ((c.index p : ℕ) + 1 + 1) := by
    rcases Nat.lt_or_ge ((c.index p : ℕ) + 1) c.length with hc | hc
    · have := c.sizeUpTo_strict_mono hc
      omega
    · have h1 : c.sizeUpTo ((c.index p : ℕ) + 1 + 1) = n :=
        c.sizeUpTo_ofLength_le _ (by omega)
      have := q.isLt
      omega
  have := (c.index_lt_iff q ((c.index p : ℕ) + 1 + 1)).mpr key
  omega

/-- **The prefix sums count the positions below them.** -/
theorem sizeUpTo_eq_card {j : ℕ} :
    (Finset.univ.filter fun p : Fin n => (c.index p : ℕ) < j).card = c.sizeUpTo j := by
  have hfil : (Finset.univ.filter fun p : Fin n => (c.index p : ℕ) < j)
      = Finset.univ.filter fun p : Fin n => (p : ℕ) < c.sizeUpTo j :=
    Finset.filter_congr fun p _ => c.index_lt_iff p j
  rw [hfil, Fin.card_filter_val_lt, min_eq_right (c.sizeUpTo_le j)]

/-- The last position lies in the last block. -/
theorem length_eq_index_succ (p : Fin n) (hp : (p : ℕ) + 1 = n) :
    c.length = (c.index p : ℕ) + 1 := by
  have h1 : (c.index p : ℕ) < c.length := (c.index p).isLt
  by_contra hc
  have h2 : (c.index p : ℕ) + 1 < c.length := by omega
  have h3 : (p : ℕ) < c.sizeUpTo ((c.index p : ℕ) + 1) := c.lt_sizeUpTo_index_succ p
  have h4 := c.sizeUpTo_strict_mono h2
  have h5 := c.sizeUpTo_le ((c.index p : ℕ) + 1 + 1)
  omega

/-- **A composition is determined by the partition of `Fin n` it cuts.** -/
theorem eq_of_index_iff {c c' : Composition n}
    (h : ∀ i j : Fin n, c.index i = c.index j ↔ c'.index i = c'.index j) : c = c' := by
  -- The two block indices agree, position by position.
  have hval : ∀ p : Fin n, (c.index p : ℕ) = (c'.index p : ℕ) := by
    intro p
    induction hp : (p : ℕ) using Nat.strong_induction_on generalizing p with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [c.index_zero hp, c'.index_zero hp]
      · obtain ⟨u, hu⟩ : ∃ u : Fin n, (u : ℕ) = k - 1 := ⟨⟨k - 1, by have := p.isLt; omega⟩, rfl⟩
        have ihu := ih (k - 1) (by omega) u hu
        have hpu : (p : ℕ) = (u : ℕ) + 1 := by omega
        have hc := c.index_succ_le hpu
        have hc' := c'.index_succ_le hpu
        have hmc := c.index_monotone (show u ≤ p from Fin.le_def.mpr (by omega))
        have hmc' := c'.index_monotone (show u ≤ p from Fin.le_def.mpr (by omega))
        simp only [] at hmc hmc'
        have hsame := h p u
        by_cases heq : c.index p = c.index u
        · rw [congrArg Fin.val heq, congrArg Fin.val (hsame.mp heq), ihu]
        · have h1 : (c.index p : ℕ) = (c.index u : ℕ) + 1 := by
            have : (c.index p : ℕ) ≠ (c.index u : ℕ) := fun hh => heq (Fin.ext hh)
            omega
          have h2 : (c'.index p : ℕ) = (c'.index u : ℕ) + 1 := by
            have : (c'.index p : ℕ) ≠ (c'.index u : ℕ) := fun hh =>
              heq (hsame.mpr (Fin.ext hh))
            omega
          omega
  -- Hence the prefix sums agree, and with them the blocks.
  have hsize : ∀ j, c.sizeUpTo j = c'.sizeUpTo j := fun j => by
    rw [← c.sizeUpTo_eq_card, ← c'.sizeUpTo_eq_card]
    exact congrArg Finset.card (Finset.filter_congr fun p _ => by rw [hval p])
  have hlen : c.length = c'.length := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : ∀ x : Composition 0, x.length = 0 := fun x =>
        Nat.eq_zero_of_not_pos fun h => absurd (x.length_pos_iff.mp h) (lt_irrefl 0)
      rw [h0 c, h0 c']
    · obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) + 1 = n := ⟨⟨n - 1, by omega⟩, by simp; omega⟩
      rw [c.length_eq_index_succ p hp, c'.length_eq_index_succ p hp, hval]
  refine Composition.ext (List.ext_get (by rw [c.blocks_length, c'.blocks_length, hlen]) ?_)
  intro j h1 h2
  rw [c.blocks_length] at h1
  rw [c'.blocks_length] at h2
  have e1 := c.sizeUpTo_succ h1
  have e2 := c'.sizeUpTo_succ h2
  have s1 := hsize j
  have s2 := hsize (j + 1)
  simp only [List.get_eq_getElem] at *
  omega

/-- The **Young subgroup** `S_{c₁} × ⋯ × S_{c_k}`: the permutations preserving every block. -/
def parabolic : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i : Fin n, c.index (σ i) = c.index i}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb i := by rw [Equiv.Perm.mul_apply, ha (b i), hb i]
  inv_mem' {a} ha i := by
    have h := ha (a⁻¹ i)
    rw [show a (a⁻¹ i) = i by simp] at h
    exact h.symm

theorem mem_parabolic {σ : Equiv.Perm (Fin n)} :
    σ ∈ c.parabolic ↔ ∀ i : Fin n, c.index (σ i) = c.index i := Iff.rfl

/-- A transposition lies in the parabolic exactly when its pair shares a block. -/
theorem mem_parabolic_swap {i j : Fin n} :
    Equiv.swap i j ∈ c.parabolic ↔ c.index i = c.index j := by
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

end Composition
