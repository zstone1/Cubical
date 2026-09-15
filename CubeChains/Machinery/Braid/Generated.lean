import CubeChains.Machinery.Braid.Artin
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Machinery/Braid/Generated — peeling an adjacent descent

Only the identity has no adjacent descent, so `permLen` recursion reaches every permutation one
descent at a time, each step length-additive, and the length alone says which way a swap goes.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

/-- Adjacent ascent at every step upgrades to full strict monotonicity. -/
theorem strictMono_of_adjacent (σ : Perm (Fin n))
    (h : ∀ i : Fin (n - 1), σ (adjLo i) < σ (adjHi i)) : StrictMono (⇑σ : Fin n → Fin n) := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m =>
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hi := h i
    rwa [show (adjLo i : Fin (m + 1)) = Fin.castSucc i from Fin.ext rfl,
      show (adjHi i : Fin (m + 1)) = Fin.succ i from Fin.ext rfl] at hi

/-- No adjacent descent forces the identity. -/
theorem eq_one_of_no_adjacent_descent (σ : Perm (Fin n))
    (h : ∀ i : Fin (n - 1), ¬ σ (adjHi i) < σ (adjLo i)) : σ = 1 :=
  (Equiv.Perm.monotone_iff σ).mp (strictMono_of_adjacent σ fun i =>
    lt_of_le_of_ne (not_lt.mp (h i)) fun heq => adjLo_ne_adjHi i (σ.injective heq)).monotone

/-- A permutation of length `0` is the identity. -/
theorem eq_one_of_permLen_eq_zero (σ : Perm (Fin n)) (h : permLen σ = 0) : σ = 1 := by
  apply eq_one_of_no_adjacent_descent
  intro i hcon
  have hmem : (adjLo i, adjHi i) ∈ inversions σ := by
    simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨adjLo_lt_adjHi i, hcon⟩
  exact absurd h (Finset.card_ne_zero_of_mem hmem)

/-- A permutation of positive length has an adjacent descent. -/
theorem exists_adjacent_descent (σ : Perm (Fin n)) (h : 0 < permLen σ) :
    ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i) := by
  by_contra hcon
  rw [not_exists] at hcon
  rw [eq_one_of_no_adjacent_descent σ hcon, permLen_one] at h
  exact lt_irrefl 0 h

/-- Undoing a descent leaves an ascent: `σ * adjT i` rises across the swapped pair. -/
theorem adjT_ascent_of_descent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (hdesc : σ (adjHi i) < σ (adjLo i)) :
    (σ * adjT i) (adjLo i) < (σ * adjT i) (adjHi i) := by
  simp only [Perm.mul_apply, adjT_lo, adjT_hi]; exact hdesc

/-- Facing a descent `σ (adjHi i) < σ (adjLo i)` off the right drops the length by one. -/
theorem permLen_mul_adjT_of_descent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (hdesc : σ (adjHi i) < σ (adjLo i)) : permLen σ = permLen (σ * adjT i) + 1 := by
  have h := permLen_mul_adjT (adjT_ascent_of_descent hdesc)
  rwa [mul_adjT_adjT] at h

/-- **A simple swap is an ascent or a descent**: its two endpoints are distinct. -/
theorem ascent_or_descent (σ : Perm (Fin n)) (i : Fin (n - 1)) :
    σ (adjLo i) < σ (adjHi i) ∨ σ (adjHi i) < σ (adjLo i) :=
  lt_or_gt_of_ne fun h => adjLo_ne_adjHi i (σ.injective h)

/-- **The length decides the direction of a simple swap.** -/
theorem ascent_of_permLen_mul_adjT {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (h : permLen (σ * adjT i) = permLen σ + 1) : σ (adjLo i) < σ (adjHi i) :=
  (ascent_or_descent σ i).resolve_right fun hd => by
    have := permLen_mul_adjT_of_descent hd; omega

theorem descent_of_permLen_drop {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (h : permLen (σ * adjT i) + 1 = permLen σ) : σ (adjHi i) < σ (adjLo i) :=
  (ascent_or_descent σ i).resolve_left fun ha => by
    have := permLen_mul_adjT ha; omega

end CubeChains
