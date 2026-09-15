import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Machinery/Braid/Length — the pairs a permutation crosses

`permLen σ` counts the inversions of `σ`.  A product crosses at most what its factors do, and the
lengths add exactly when the product keeps every crossing of its right factor
(`permLen_mul_of_inversions_subset`); the reversal crosses every pair.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

/-- The inversions of `σ`: the strand pairs it crosses. -/
def inversions (σ : Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ σ p.2 < σ p.1

/-- The length of `σ`: how many pairs it crosses. -/
def permLen (σ : Perm (Fin n)) : ℕ := (inversions σ).card

/-- **Induction on the writhe**: prove `P σ` from `P` at every strictly shorter permutation. -/
theorem permLen_strongRec {P : Perm (Fin n) → Prop}
    (ih : ∀ σ : Perm (Fin n), (∀ τ : Perm (Fin n), permLen τ < permLen σ → P τ) → P σ)
    (σ : Perm (Fin n)) : P σ := by
  suffices H : ∀ k, ∀ σ : Perm (Fin n), permLen σ < k → P σ from H _ σ (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => exact fun _ h => absurd h (Nat.not_lt_zero _)
  | succ k hk => exact fun σ h => ih σ fun τ hτ => hk τ (by omega)

@[simp] theorem permLen_one : permLen (1 : Perm (Fin n)) = 0 := by
  rw [permLen, inversions, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  simp only [Perm.coe_one, id_eq] at h2
  exact absurd h1 (asymm h2)

/-- Recounting the strands changes no crossing: `Fin.cast` is an order isomorphism. -/
@[simp] theorem permLen_permCongr_finCongr {m n : ℕ} (h : m = n) (σ : Perm (Fin m)) :
    permLen ((finCongr h).permCongr σ) = permLen σ := by
  subst h
  exact congrArg permLen ((Equiv.apply_eq_iff_eq_symm_apply (finCongr rfl).permCongr).mpr rfl)

/-- A permutation and its inverse cross the same pairs, read from the other end. -/
theorem permLen_inv (σ : Perm (Fin n)) : permLen σ⁻¹ = permLen σ := by
  classical
  refine Finset.card_bij' (fun p _ => (σ⁻¹ p.2, σ⁻¹ p.1)) (fun q _ => (σ q.2, σ q.1)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2, by simpa using hp.1⟩
  · rintro ⟨a, b⟩ hq
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact ⟨hq.2, by simpa using hq.1⟩
  · rintro ⟨a, b⟩ -
    simp
  · rintro ⟨a, b⟩ -
    simp

/-- **Crossings only cancel, never appear**: a pair inverted by `α * β` is inverted by `β`, or its
`β`-image is inverted by `α`. -/
theorem inversions_mul_subset (α β : Perm (Fin n)) :
    inversions (α * β)
      ⊆ inversions β ∪ (inversions α).image (fun q => (β⁻¹ q.1, β⁻¹ q.2)) := by
  classical
  rintro ⟨i, j⟩ hp
  simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Perm.mul_apply] at hp
  obtain ⟨hij, hαβ⟩ := hp
  rcases lt_trichotomy (β i) (β j) with hlt | heq | hgt
  · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(β i, β j), ?_, ?_⟩)
    · simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hlt, hαβ⟩
    · simp
  · exact absurd (β.injective heq) (ne_of_lt hij)
  · refine Finset.mem_union_left _ ?_
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hij, hgt⟩

private theorem card_inversions_image_le (α β : Perm (Fin n)) :
    ((inversions α).image (fun q : Fin n × Fin n => (β⁻¹ q.1, β⁻¹ q.2))).card
      ≤ (inversions α).card := Finset.card_image_le

theorem permLen_mul_le (α β : Perm (Fin n)) : permLen (α * β) ≤ permLen α + permLen β := by
  classical
  have h1 := Finset.card_le_card (inversions_mul_subset α β)
  have h2 := Finset.card_union_le (inversions β)
    ((inversions α).image (fun q : Fin n × Fin n => (β⁻¹ q.1, β⁻¹ q.2)))
  have h3 := card_inversions_image_le α β
  simp only [permLen]
  omega

/-- **A length-additive product keeps every crossing of its right factor**: the two inversion sets
combine without overlap, so there is no room to lose one. -/
theorem inversions_subset_of_permLen_add {α β : Perm (Fin n)}
    (h : permLen (α * β) = permLen α + permLen β) : inversions β ⊆ inversions (α * β) := by
  classical
  have h2 := Finset.card_union_le (inversions β)
    ((inversions α).image (fun q : Fin n × Fin n => (β⁻¹ q.1, β⁻¹ q.2)))
  have h3 := card_inversions_image_le α β
  have heq := Finset.eq_of_subset_of_card_le (inversions_mul_subset α β)
    (by simp only [permLen] at h; omega)
  exact heq ▸ Finset.subset_union_left

/-- **Lengths add when the composite keeps every crossing of its right factor.**  `hsub` says the
inversion sets of `σ` and `ρ` combine without overlap — the composite never *un*-crosses a pair `σ`
crosses.  This is the whole content of the germ relation `[σ][τ] = [στ]`; the geometry only has to
supply `hsub`. -/
theorem permLen_mul_of_inversions_subset {σ ρ : Perm (Fin n)}
    (hsub : inversions σ ⊆ inversions (ρ * σ)) :
    permLen (ρ * σ) = permLen σ + permLen ρ := by
  classical
  -- The extra `ρσ`-inversions biject with the `ρ`-inversions via `σ`.
  have hbij : (inversions (ρ * σ) \ inversions σ).card = (inversions ρ).card := by
    refine Finset.card_bij' (fun p _ => (σ p.1, σ p.2)) (fun q _ => (σ⁻¹ q.1, σ⁻¹ q.2)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_sdiff, inversions, Finset.mem_filter, Finset.mem_univ, true_and,
        Perm.mul_apply, not_and, not_lt] at hp ⊢
      obtain ⟨⟨hab, hρ⟩, hσ⟩ := hp
      exact ⟨lt_of_le_of_ne (hσ hab) (σ.injective.ne (ne_of_lt hab)), hρ⟩
    · rintro ⟨a, b⟩ hq
      have hsa : σ (σ⁻¹ a) = a := σ.apply_symm_apply a
      have hsb : σ (σ⁻¹ b) = b := σ.apply_symm_apply b
      simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨hab, hρ⟩ := hq
      have hlt : σ⁻¹ a < σ⁻¹ b := by
        by_contra hc
        rw [not_lt] at hc
        have hne : σ⁻¹ b ≠ σ⁻¹ a := fun h => (ne_of_lt hab) (σ⁻¹.injective h).symm
        have hmem : ((σ⁻¹ b, σ⁻¹ a) : Fin n × Fin n) ∈ inversions σ := by
          simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, hsa, hsb]
          exact ⟨lt_of_le_of_ne hc hne, hab⟩
        have hcross := hsub hmem
        simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Perm.mul_apply,
          hsa, hsb] at hcross
        exact absurd hρ (asymm hcross.2)
      simp only [Finset.mem_sdiff, inversions, Finset.mem_filter, Finset.mem_univ, true_and,
        Perm.mul_apply, hsa, hsb, not_and, not_lt]
      exact ⟨⟨hlt, hρ⟩, fun _ => le_of_lt hab⟩
    · rintro ⟨a, b⟩ -
      simp
    · rintro ⟨a, b⟩ -
      simp
  rw [permLen, permLen, permLen, ← hbij, add_comm, Finset.card_sdiff_add_card_eq_card hsub]

/-- …read pairwise: `H` says every pair `σ` crosses stays crossed by `ρσ`. -/
theorem permLen_mul_of_noDoubleCross {σ ρ : Perm (Fin n)}
    (H : ∀ i j : Fin n, i < j → σ j < σ i → ρ (σ j) < ρ (σ i)) :
    permLen (ρ * σ) = permLen σ + permLen ρ :=
  permLen_mul_of_inversions_subset (by
    rintro ⟨a, b⟩ hp
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Perm.mul_apply] at hp ⊢
    exact ⟨hp.1, H a b hp.1 hp.2⟩)

/-- **The reversal crosses every pair**, so any factorisation of it is length-additive — the
length-additivity behind Garside's `Δ`. -/
theorem permLen_mul_of_eq_rev {σ τ : Perm (Fin n)} (h : σ * τ = Fin.revPerm) :
    permLen (σ * τ) = permLen σ + permLen τ :=
  (permLen_mul_of_noDoubleCross (σ := τ) (ρ := σ) fun i j hij _ => by
    have hk : ∀ k, σ (τ k) = k.rev := fun k => by
      rw [← Perm.mul_apply, h, Fin.revPerm_apply]
    rw [hk, hk]
    exact Fin.rev_strictAnti hij).trans (Nat.add_comm _ _)

/-! ### The longest permutation

`Fin.revPerm` crosses every pair, so the previous lemma says it is the **top** of the right weak
order and that `σ` and `σ⁻¹ * w₀` split its length.  There is no `w₀` alias: the reversal *is* it.
-/

theorem revPerm_mul_self : (Fin.revPerm * Fin.revPerm : Perm (Fin n)) = 1 :=
  Equiv.ext fun i => Fin.rev_rev i

theorem revPerm_inv : (Fin.revPerm : Perm (Fin n))⁻¹ = Fin.revPerm :=
  inv_eq_of_mul_eq_one_right revPerm_mul_self

/-- **Nothing is longer than the reversal**: `σ` and its complement split `permLen Fin.revPerm`. -/
theorem permLen_add_inv_mul_revPerm (σ : Perm (Fin n)) :
    permLen σ + permLen (σ⁻¹ * Fin.revPerm) = permLen (Fin.revPerm : Perm (Fin n)) :=
  have h : σ * (σ⁻¹ * Fin.revPerm) = Fin.revPerm := mul_inv_cancel_left σ Fin.revPerm
  (permLen_mul_of_eq_rev h).symm.trans (congrArg permLen h)

/-! ## The crossing bound

A permutation crosses a *set* of pairs, so it crosses at most the `n.choose 2` pairs there are; the
reversal crosses all of them, and nothing else does.  Tensored over a wedge these three are the
whole of the crossing capacity — the bound on every refinement, the greatest refinement attaining
it, and nothing else attaining it — with no comparison against a reversal in the bound itself. -/

/-- The pairs of strands. -/
def ltPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2

theorem mem_ltPairs {n : ℕ} {p : Fin n × Fin n} : p ∈ ltPairs n ↔ p.1 < p.2 := by
  simp [ltPairs]

/-- **There are `n.choose 2` pairs** — counted at the larger member. -/
theorem card_ltPairs (n : ℕ) : (ltPairs n).card = n.choose 2 := by
  have hsplit : ltPairs n = Finset.univ.biUnion fun j : Fin n => (Finset.Iio j).image (·, j) := by
    ext p
    simp only [ltPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_Iio]
    refine ⟨fun h => ⟨p.2, p.1, h, rfl⟩, ?_⟩
    rintro ⟨j, i, hij, rfl⟩
    exact hij
  have hdisj : ∀ j ∈ (Finset.univ : Finset (Fin n)), ∀ j' ∈ (Finset.univ : Finset (Fin n)),
      j ≠ j' → Disjoint ((Finset.Iio j).image (·, j)) ((Finset.Iio j').image (·, j')) := by
    intro j _ j' _ hne
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_Iio]
    rintro p ⟨i, -, rfl⟩ ⟨i', -, h⟩
    exact hne (congrArg Prod.snd h).symm
  rw [hsplit, Finset.card_biUnion hdisj,
    Finset.sum_congr rfl (fun j _ => (Finset.card_image_of_injective (Finset.Iio j)
      (fun _ _ h => congrArg Prod.fst h)).trans (Fin.card_Iio j)),
    Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

theorem inversions_subset_ltPairs (σ : Perm (Fin n)) : inversions σ ⊆ ltPairs n := by
  intro p hp
  simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact mem_ltPairs.mpr hp.1

/-- **A permutation crosses at most the pairs there are.**  The bound on a crossing count is this,
tensored over the beads — not a comparison with the reversal. -/
theorem permLen_le_choose (σ : Perm (Fin n)) : permLen σ ≤ n.choose 2 :=
  (Finset.card_le_card (inversions_subset_ltPairs σ)).trans_eq (card_ltPairs n)

/-- **The reversal crosses every pair.** -/
theorem inversions_revPerm (n : ℕ) : inversions (Fin.revPerm : Perm (Fin n)) = ltPairs n := by
  ext p
  simp only [inversions, ltPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.revPerm_apply, Fin.rev_lt_rev]
  exact ⟨And.left, fun h => ⟨h, h⟩⟩

/-- **…so it attains the bound**, which is the equality half of `permLen_le_choose`. -/
theorem permLen_revPerm (n : ℕ) : permLen (Fin.revPerm : Perm (Fin n)) = n.choose 2 :=
  (congrArg Finset.card (inversions_revPerm n)).trans (card_ltPairs n)

/-- …and the same on the left, which is the form the *right* weak order's duality needs. -/
theorem permLen_revPerm_mul_add (σ : Perm (Fin n)) :
    permLen (Fin.revPerm * σ) + permLen σ = permLen (Fin.revPerm : Perm (Fin n)) := by
  have h : (Fin.revPerm * σ) * σ⁻¹ = Fin.revPerm := mul_inv_cancel_right _ _
  rw [← permLen_inv σ]
  exact (permLen_mul_of_eq_rev h).symm.trans (congrArg permLen h)

/-- …and on the *right*, which is how reversing a run's order acts on the word it spells. -/
theorem permLen_mul_revPerm_add (σ : Perm (Fin n)) :
    permLen σ + permLen (σ * Fin.revPerm) = permLen (Fin.revPerm : Perm (Fin n)) := by
  rw [← permLen_inv σ, ← permLen_inv (σ * Fin.revPerm), mul_inv_rev, revPerm_inv, Nat.add_comm]
  exact permLen_revPerm_mul_add σ⁻¹

end CubeChains
