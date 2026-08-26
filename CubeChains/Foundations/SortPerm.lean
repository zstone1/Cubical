import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Foundations/SortPerm — sorting pins the permutation

An injective tuple is put in order by exactly one permutation, so any `σ` making `f ∘ σ⁻¹`
monotone *is* the inverse of `Tuple.sort f`.  This is the rank-map characterisation shared by the
sorting permutation of a symmetric box map and the step order of a restricted run.
-/

namespace Tuple

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- **The rank map of an injective tuple.**  If `σ` re-indexes `f` into increasing order it *is*
`(Tuple.sort f)⁻¹` — injectivity of `f` is what rules out the ties. -/
theorem eq_sort_inv {f : Fin n → α} (hf : Function.Injective f) {σ : Equiv.Perm (Fin n)}
    (h : Monotone (f ∘ ⇑σ⁻¹)) : σ = (sort f)⁻¹ :=
  inv_eq_iff_eq_inv.mp
    (Equiv.coe_fn_injective (hf.comp_left (comp_sort_eq_comp_iff_monotone.mpr h)))

end Tuple

namespace Equiv.Perm

/-- A permutation of `Fin n` has exactly `k` values below `k`. -/
theorem card_filter_lt {n : ℕ} (e : Equiv.Perm (Fin n)) (k : Fin n) :
    (Finset.univ.filter (fun j => e j < k)).card = (k : ℕ) := by
  have h : Finset.univ.filter (fun j => e j < k) = (Finset.Iio k).map e.symm.toEmbedding := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Iio,
      Equiv.coe_toEmbedding]
    exact ⟨fun hj => ⟨e j, hj, e.symm_apply_apply j⟩,
      by rintro ⟨i, hi, rfl⟩; rwa [e.apply_symm_apply]⟩
  rw [h, Finset.card_map, Fin.card_Iio]

end Equiv.Perm
