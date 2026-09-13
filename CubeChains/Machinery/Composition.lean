import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Machinery/Composition — `Composition.index` against the prefix sums

Mathlib pins `Composition.index` by a sandwich, `sizeUpTo (index p) ≤ p < sizeUpTo (index p + 1)`.
Stated as one order relation (`index_lt_iff`) it carries no side condition, and everything about
blocks below follows: monotonicity, the block a bracket pins, and the prefix sums as counts.
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
theorem index_monotone : Monotone fun p : Fin n => (c.index p : ℕ) := fun p q hpq =>
  not_lt.mp fun hlt => absurd (lt_of_lt_of_le ((c.index_lt_iff q ((c.index p : ℕ))).mp hlt)
    (c.sizeUpTo_index_le p)) (not_lt.mpr (Fin.le_def.mp hpq))

/-- **The block a position lies in, from the bracket around it.** -/
theorem index_eq_of_bracket {j : ℕ} (p : Fin n) (h1 : c.sizeUpTo j ≤ (p : ℕ))
    (h2 : (p : ℕ) < c.sizeUpTo (j + 1)) : (c.index p : ℕ) = j := by
  have k1 : ¬ ((c.index p : ℕ) < j) := fun hc => absurd ((c.index_lt_iff p j).mp hc) (by omega)
  have k2 : (c.index p : ℕ) < j + 1 := (c.index_lt_iff p (j + 1)).mpr h2
  omega

/-- **The prefix sums count the positions below them.** -/
theorem sizeUpTo_eq_card {j : ℕ} :
    (Finset.univ.filter fun p : Fin n => (c.index p : ℕ) < j).card = c.sizeUpTo j := by
  have hfil : (Finset.univ.filter fun p : Fin n => (c.index p : ℕ) < j)
      = Finset.univ.filter fun p : Fin n => (p : ℕ) < c.sizeUpTo j :=
    Finset.filter_congr fun p _ => c.index_lt_iff p j
  rw [hfil, Fin.card_filter_val_lt, min_eq_right (c.sizeUpTo_le j)]

end Composition
