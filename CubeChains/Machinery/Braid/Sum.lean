import CubeChains.Machinery.Braid.Generated
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# Machinery/Braid/Sum — juxtaposition of permutations

A permutation of `m` letters set beside one of `n` letters is the block-diagonal
`permSum : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n))` (first `m` coordinates by `σ`, last
`n` by `τ`, transported along `finSumFinEquiv`).

The crossing count adds — `permLen_permSum` — because the two blocks never interact: a low strand
and a high strand keep their order, so no cross-block pair is ever inverted.  That is what makes
the crossing permutation of a concatenation a block sum (`Concurrency/Grading/WedgeBraid`).
-/

namespace CubeChains

open Equiv

variable {m n : ℕ}

/-! ## The block-diagonal permutation -/

/-- The block-diagonal permutation: `σ` on the first `m` strands, `τ` on the last `n`. -/
def permSum (m n : ℕ) : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n)) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin m) (Fin n))

theorem permSum_apply_inl (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin m) :
    permSum m n (σ, τ) (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (σ i)) := by
  simp only [permSum, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.Perm.sumCongrHom_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inl]

theorem permSum_apply_inr (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin n) :
    permSum m n (σ, τ) (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inr (τ i)) := by
  simp only [permSum, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
    Equiv.Perm.sumCongrHom_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inr]

theorem permSum_apply_castAdd (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin m) :
    permSum m n (σ, τ) (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  have := permSum_apply_inl σ τ i
  rwa [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left] at this

theorem permSum_apply_natAdd (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin n) :
    permSum m n (σ, τ) (Fin.natAdd m i) = Fin.natAdd m (τ i) := by
  have := permSum_apply_inr σ τ i
  rwa [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right] at this

/-- **The blocks never interact**: a block-diagonal permutation is trivial exactly when both
blocks are. -/
theorem permSum_eq_one_iff {σ : Perm (Fin m)} {τ : Perm (Fin n)} :
    permSum m n (σ, τ) = 1 ↔ σ = 1 ∧ τ = 1 := by
  refine ⟨fun h => ⟨Equiv.ext fun i => ?_, Equiv.ext fun i => ?_⟩, ?_⟩
  · have hi := Equiv.ext_iff.mp h (Fin.castAdd n i)
    rw [permSum_apply_castAdd] at hi
    exact Fin.castAdd_injective m n hi
  · have hi := Equiv.ext_iff.mp h (Fin.natAdd m i)
    rw [permSum_apply_natAdd] at hi
    exact Fin.natAdd_injective _ _ hi
  · rintro ⟨rfl, rfl⟩
    exact map_one _

/-- The pair `(x, y)` is an inversion of `ρ` iff `x < y` yet `ρ` reverses them. -/
theorem mem_inversions {N : ℕ} {ρ : Perm (Fin N)} {x y : Fin N} :
    (x, y) ∈ inversions ρ ↔ x < y ∧ ρ y < ρ x := by
  simp [inversions]

theorem castAdd_lt_castAdd_iff {i j : Fin m} :
    (Fin.castAdd n i : Fin (m + n)) < Fin.castAdd n j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; simp

/-- **The crossing count adds.**  The inversions of the block-diagonal permutation split as the
`σ`-inversions (both strands low) and the `τ`-inversions (both high); no cross-block pair inverts,
because every low strand stays below every high one. -/
theorem permLen_permSum (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    permLen (permSum m n (σ, τ)) = permLen σ + permLen τ := by
  classical
  set gL : Fin m × Fin m → Fin (m + n) × Fin (m + n) :=
    fun p => (Fin.castAdd n p.1, Fin.castAdd n p.2) with hgL
  set gR : Fin n × Fin n → Fin (m + n) × Fin (m + n) :=
    fun p => (Fin.natAdd m p.1, Fin.natAdd m p.2) with hgR
  have hinjL : Function.Injective gL := fun ⟨a, b⟩ ⟨c, d⟩ h => by
    simp only [hgL, Prod.mk.injEq] at h
    exact Prod.ext (Fin.castAdd_injective _ _ h.1) (Fin.castAdd_injective _ _ h.2)
  have hinjR : Function.Injective gR := fun ⟨a, b⟩ ⟨c, d⟩ h => by
    simp only [hgR, Prod.mk.injEq] at h
    exact Prod.ext (Fin.natAdd_injective _ _ h.1) (Fin.natAdd_injective _ _ h.2)
  have hset : inversions (permSum m n (σ, τ)) =
      (inversions σ).image gL ∪ (inversions τ).image gR := by
    ext ⟨x, y⟩
    constructor
    · intro hxy
      rw [mem_inversions] at hxy
      obtain ⟨hlt, hinv⟩ := hxy
      revert hlt hinv
      refine x.addCases (fun a => ?_) (fun a => ?_)
      · refine y.addCases (fun b => ?_) (fun b => ?_) <;> intro hlt hinv
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩)
          rw [mem_inversions]
          rw [permSum_apply_castAdd, permSum_apply_castAdd, castAdd_lt_castAdd_iff] at hinv
          exact ⟨castAdd_lt_castAdd_iff.mp hlt, hinv⟩
        · exfalso
          rw [permSum_apply_castAdd, permSum_apply_natAdd, Fin.lt_def] at hinv
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hinv
          have := (σ a).2; omega
      · refine y.addCases (fun b => ?_) (fun b => ?_) <;> intro hlt hinv
        · exfalso
          rw [Fin.lt_def] at hlt
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hlt
          have := b.2; omega
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩)
          rw [mem_inversions]
          rw [permSum_apply_natAdd, permSum_apply_natAdd, Fin.natAdd_lt_natAdd_iff] at hinv
          exact ⟨(Fin.natAdd_lt_natAdd_iff m).mp hlt, hinv⟩
    · intro h
      rw [Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨⟨a, b⟩, hp, hgp⟩ := Finset.mem_image.mp h
        rw [mem_inversions] at hp
        obtain ⟨hlt, hinv⟩ := hp
        simp only [hgL] at hgp
        rw [← hgp, mem_inversions, permSum_apply_castAdd, permSum_apply_castAdd,
          castAdd_lt_castAdd_iff, castAdd_lt_castAdd_iff]
        exact ⟨hlt, hinv⟩
      · obtain ⟨⟨a, b⟩, hp, hgp⟩ := Finset.mem_image.mp h
        rw [mem_inversions] at hp
        obtain ⟨hlt, hinv⟩ := hp
        simp only [hgR] at hgp
        rw [← hgp, mem_inversions, permSum_apply_natAdd, permSum_apply_natAdd,
          Fin.natAdd_lt_natAdd_iff, Fin.natAdd_lt_natAdd_iff]
        exact ⟨hlt, hinv⟩
  have hdisj : Disjoint ((inversions σ).image gL) ((inversions τ).image gR) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxL hxR
    obtain ⟨⟨a, b⟩, -, hx⟩ := Finset.mem_image.mp hxL
    obtain ⟨⟨c, d⟩, -, hx'⟩ := Finset.mem_image.mp hxR
    simp only [hgL, hgR, Prod.mk.injEq] at hx hx'
    have hval : (Fin.castAdd n a : Fin (m + n)).val = (Fin.natAdd m c : Fin (m + n)).val := by
      rw [hx.1, ← hx'.1]
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    have := a.2; omega
  rw [permLen, hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinjL, Finset.card_image_of_injective _ hinjR]
  rfl

end CubeChains
