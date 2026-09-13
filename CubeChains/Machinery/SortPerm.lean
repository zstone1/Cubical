import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Machinery/SortPerm — orderings of a finite set, and the permutations between them

An injective tuple is put in order by exactly one permutation, so any `σ` making `f ∘ σ⁻¹`
monotone *is* the inverse of `Tuple.sort f`.  This is the rank-map characterisation shared by the
sorting permutation of a symmetric box map and the step order of a restricted run.

`conjPerm oa ob φ` reads a relabelling `φ : A ≃ B` through an ordering at each end.  Every
permutation the development produces is one of these, so `conjPerm_trans` (the cocycle law) and
`conjPerm_mul_pullback` are the only functoriality any of them needs.
-/

namespace Tuple

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- **The rank map of an injective tuple.**  If `σ` re-indexes `f` into increasing order it *is*
`(Tuple.sort f)⁻¹` — injectivity of `f` is what rules out the ties. -/
theorem eq_sort_inv {f : Fin n → α} (hf : Function.Injective f) {σ : Equiv.Perm (Fin n)}
    (h : Monotone (f ∘ ⇑σ⁻¹)) : σ = (sort f)⁻¹ :=
  inv_eq_iff_eq_inv.mp
    (Equiv.coe_fn_injective (hf.comp_left (comp_sort_eq_comp_iff_monotone.mpr h)))

/-- **The sorting permutation's inverse is the rank map** — it compares two indices exactly as the
tuple does.  Injectivity upgrades `monotone_sort` to strict monotonicity; that is the whole
content. -/
theorem sort_inv_lt_iff {f : Fin n → α} (hf : Function.Injective f) (x y : Fin n) :
    (sort f)⁻¹ x < (sort f)⁻¹ y ↔ f x < f y := by
  have hstrict : StrictMono (f ∘ ⇑(sort f)) :=
    (monotone_sort f).strictMono_of_injective (hf.comp (sort f).injective)
  simpa using (hstrict.lt_iff_lt (a := (sort f)⁻¹ x) (b := (sort f)⁻¹ y)).symm

/-- **Sorting sees only a tuple's order type**: two tuples comparing the same way sort the same.
This is what makes rank transitive — a rank map may replace the tuple it ranks. -/
theorem sort_congr {β : Type*} [LinearOrder β] {f : Fin n → α} {g : Fin n → β}
    (hf : Function.Injective f) (h : ∀ x y, f x < f y ↔ g x < g y) : sort f = sort g := by
  refine (inv_injective (eq_sort_inv hf (σ := (sort g)⁻¹) ?_)).symm
  intro a b hab
  simp only [Function.comp_apply, inv_inv]
  exact not_lt.mp fun hlt => absurd ((h _ _).mp hlt) (not_lt.mpr (monotone_sort g hab))

/-- **Order-reversing a tuple reverses its sorting permutation.**  Reading `f` through a strictly
antitone `g` exchanges increasing for decreasing, so the sorted order is the old one read backwards.
Injectivity is what rules out the ties `sort` would otherwise break by index. -/
theorem sort_comp_strictAnti {β : Type*} [LinearOrder β] {f : Fin n → α}
    (hf : Function.Injective f) {g : α → β} (hg : StrictAnti g) :
    sort (g ∘ f) = sort f * Fin.revPerm := by
  refine (inv_injective (eq_sort_inv (hg.injective.comp hf)
    (σ := (sort f * Fin.revPerm)⁻¹) ?_)).symm
  intro i j hij
  simp only [Function.comp_apply, inv_inv, Equiv.Perm.coe_mul, Fin.revPerm_apply]
  exact hg.antitone (monotone_sort f (Fin.rev_le_rev.mpr hij))

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

namespace CubeChains

/-! ## A relabelling read through two orderings

Every permutation this development produces has one shape: a bijection `φ : A ≃ B` of some
finite set of *events*, read at each end through an ordering of them.  The crossing permutation of
a chain morphism orders both ends lexicographically; a chain's firing order compares the cube's own
coordinate order with the lexicographic one (`φ = 1`); the run order of `Concurrency/Salvetti`
orders by the run.  `conjPerm_refl`/`conjPerm_trans` are all the functoriality any of them has. -/

/-- A relabelling `φ`, read through an ordering at each end. -/
def conjPerm {A B : Type*} {N : ℕ} (oa : A ≃ Fin N) (ob : B ≃ Fin N) (φ : A ≃ B) :
    Equiv.Perm (Fin N) := oa.equivCongr ob φ

theorem conjPerm_apply {A B : Type*} {N : ℕ} (oa : A ≃ Fin N) (ob : B ≃ Fin N) (φ : A ≃ B)
    (x : A) : conjPerm oa ob φ (oa x) = ob (φ x) := by
  rw [conjPerm, Equiv.equivCongr_apply_apply, Equiv.symm_apply_apply]

theorem conjPerm_refl {A : Type*} {N : ℕ} (oa : A ≃ Fin N) :
    conjPerm oa oa (Equiv.refl A) = 1 :=
  Equiv.ext fun x => by obtain ⟨u, rfl⟩ := oa.surjective x; rw [conjPerm_apply]; rfl

/-- **The cocycle law**: relabelling in two steps multiplies, the middle ordering shared. -/
theorem conjPerm_trans {A B C : Type*} {N : ℕ} (oa : A ≃ Fin N) (ob : B ≃ Fin N) (oc : C ≃ Fin N)
    (φ : A ≃ B) (ψ : B ≃ C) :
    conjPerm oa oc (φ.trans ψ) = conjPerm ob oc ψ * conjPerm oa ob φ :=
  Equiv.ext fun x => by
    obtain ⟨u, rfl⟩ := oa.surjective x
    rw [conjPerm_apply, Equiv.Perm.mul_apply, conjPerm_apply, conjPerm_apply, Equiv.trans_apply]

/-- **Re-reading the source through the relabelling** turns the relabelling into the identity: an
ordering of `A` pulled back from one of `B` compares with any `B`-ordering exactly as `1` does. -/
theorem conjPerm_trans_left {A B : Type*} {N : ℕ} (oa : B ≃ Fin N) (ob : B ≃ Fin N) (φ : A ≃ B) :
    conjPerm (φ.trans oa) ob φ = conjPerm oa ob (Equiv.refl B) :=
  Equiv.ext fun x => by
    obtain ⟨u, rfl⟩ := (φ.trans oa).surjective x
    rw [conjPerm_apply, Equiv.trans_apply, conjPerm_apply]
    rfl

/-- **A second ordering transforms by the relabelling's own permutation.**  If the source's extra
ordering is the target's pulled back along `ψ`, the two comparisons `conjPerm _ _ 1` differ by
exactly `conjPerm oa ob ψ` — the cocycle law with one leg trivial.  This is why a crossing
permutation *is* the comparison of the two firing orders it sits between. -/
theorem conjPerm_mul_pullback {A B : Type*} {N : ℕ} (oa : A ≃ Fin N) (ob : B ≃ Fin N)
    (cb : B ≃ Fin N) (ψ : A ≃ B) :
    conjPerm oa ob ψ * conjPerm (ψ.trans cb) oa (Equiv.refl A)
      = conjPerm cb ob (Equiv.refl B) :=
  ((conjPerm_trans (ψ.trans cb) oa ob (Equiv.refl A) ψ).symm.trans
    (congrArg (conjPerm (ψ.trans cb) ob) (Equiv.refl_trans ψ))).trans
    (conjPerm_trans_left cb ob ψ)

end CubeChains
