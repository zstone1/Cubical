import CubeChains.Machinery.Braid.Generated
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Group

/-!
# Machinery/Braid/WeakOrder — the right weak order on `Sₙ`

`x ≤ y` when `y` factors as `x` followed by something with the crossing counts adding.  Only
subadditivity of `permLen` and "length zero means identity" go into the poset laws; `Fin.revPerm`
is the top.  A cover is one adjacent crossing undone (`covBy_iff`), and a descent of the residue
`x⁻¹σ` is a step of the order that keeps `x` below (`le_mul_adjT_of_residue`).
`WeakOrder n` is a type synonym — the order is not an instance on `Perm` itself.
-/

namespace CubeChains

variable {n : ℕ}

/-- `Perm (Fin n)` under the **right weak (Bruhat) order**: `x ≤ y` when `y` factors as `x`
followed by something, with the crossing counts adding. -/
def WeakOrder (n : ℕ) : Type := Equiv.Perm (Fin n)

namespace WeakOrder

/-- A permutation, read in the weak order. -/
def of (σ : Equiv.Perm (Fin n)) : WeakOrder n := σ

/-- An element of the weak order, read as a permutation. -/
def perm (x : WeakOrder n) : Equiv.Perm (Fin n) := x

@[simp] theorem perm_of (σ : Equiv.Perm (Fin n)) : perm (of σ) = σ := rfl

@[simp] theorem of_perm (x : WeakOrder n) : of (perm x) = x := rfl

instance : PartialOrder (WeakOrder n) where
  le x y := permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y)
  le_refl x := by simp
  le_trans x y z hxy hyz := by
    have hsplit : (perm x)⁻¹ * perm z = ((perm x)⁻¹ * perm y) * ((perm y)⁻¹ * perm z) := by
      group
    have hfac : perm z = perm x * ((perm x)⁻¹ * perm z) := by group
    have h₁ := permLen_mul_le ((perm x)⁻¹ * perm y) ((perm y)⁻¹ * perm z)
    have h₂ := permLen_mul_le (perm x) ((perm x)⁻¹ * perm z)
    rw [← hsplit] at h₁
    rw [← hfac] at h₂
    change permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y) at hxy
    change permLen (perm y) + permLen ((perm y)⁻¹ * perm z) = permLen (perm z) at hyz
    change permLen (perm x) + permLen ((perm x)⁻¹ * perm z) = permLen (perm z)
    omega
  le_antisymm x y hxy hyx := by
    change permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y) at hxy
    change permLen (perm y) + permLen ((perm y)⁻¹ * perm x) = permLen (perm x) at hyx
    exact (inv_mul_eq_one.mp (eq_one_of_permLen_eq_zero _ (by omega)) : perm x = perm y)

theorem le_def {x y : WeakOrder n} :
    x ≤ y ↔ permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y) := Iff.rfl

/-- **The order is graded**: below and of the same length means equal. -/
theorem eq_of_le_of_permLen_eq {x y : WeakOrder n} (h : x ≤ y)
    (hlen : permLen (perm x) = permLen (perm y)) : perm x = perm y :=
  inv_mul_eq_one.mp (eq_one_of_permLen_eq_zero _ (by rw [le_def] at h; omega))

/-- The identity is the bottom: it crosses nothing. -/
theorem one_le (σ : Equiv.Perm (Fin n)) : of 1 ≤ of σ := by
  rw [le_def]
  simp only [perm_of, permLen_one, inv_one, one_mul, Nat.zero_add]

/-- **The witnessing factorisation, named at the product** — the shape a crossing cocycle
produces: an arrow factors the class on the right and the lengths add. -/
theorem le_of_mul_eq {σ τ π : Equiv.Perm (Fin n)} (hmul : τ * π = σ)
    (hlen : permLen σ = permLen π + permLen τ) : of τ ≤ of σ := by
  subst hmul
  rw [le_def]
  simpa [inv_mul_cancel_left] using (by omega : permLen τ + permLen π = permLen (τ * π))

/-- Strictly below means strictly shorter — only the identity has length zero. -/
theorem permLen_lt_of_lt {x y : WeakOrder n} (h : x < y) :
    permLen (perm x) < permLen (perm y) := by
  have hle := le_def.mp h.le
  rcases Nat.eq_zero_or_pos (permLen ((perm x)⁻¹ * perm y)) with hz | _
  · exact absurd (inv_mul_eq_one.mp (eq_one_of_permLen_eq_zero _ hz)) h.ne
  · omega

/-- The reversal is the top: `σ` and its complement split `permLen Fin.revPerm`. -/
instance : OrderTop (WeakOrder n) where
  top := of Fin.revPerm
  le_top x := permLen_add_inv_mul_revPerm (perm x)

/-- **…and only the top attains the bound**: its complement below the reversal has length zero. -/
theorem eq_revPerm_of_permLen {σ : Equiv.Perm (Fin n)} (h : permLen σ = n.choose 2) :
    σ = Fin.revPerm := by
  have h0 := permLen_add_inv_mul_revPerm σ
  rw [permLen_revPerm, h] at h0
  exact (inv_mul_eq_one.mp (eq_one_of_permLen_eq_zero _ (by omega)))

theorem of_mul_adjT_le {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (adjHi i) < σ (adjLo i)) : of (σ * adjT i) ≤ of σ := by
  have hinv : (σ * adjT i)⁻¹ * σ = adjT i := by
    rw [mul_inv_rev, adjT_inv, inv_mul_cancel_right]
  rw [le_def]
  simp only [perm_of, hinv, permLen_adjT]
  exact (permLen_mul_adjT_of_descent h).symm

/-- **Below a lower cover, the drop shows up in the residue**: the crossing the cover undoes is
one the residue `x⁻¹σ` must undo itself. -/
theorem residue_descent {σ : Equiv.Perm (Fin n)} {k : Fin (n - 1)} {x : WeakOrder n}
    (hd : σ (adjHi k) < σ (adjLo k)) (hx : x ≤ of (σ * adjT k)) :
    ((perm x)⁻¹ * σ) (adjHi k) < ((perm x)⁻¹ * σ) (adjLo k) := by
  have hxσ := hx.trans (of_mul_adjT_le hd)
  rw [le_def] at hx hxσ
  simp only [perm_of, ← mul_assoc] at hx hxσ
  exact descent_of_permLen_drop (by have := permLen_mul_adjT_of_descent hd; omega)

/-- …and conversely a descent of the residue is one of `σ`, of the same single crossing: `x` is
too short to have undone it. -/
theorem permLen_mul_adjT_of_residue {σ : Equiv.Perm (Fin n)} {k : Fin (n - 1)} {x : WeakOrder n}
    (hx : x ≤ of σ) (hd : ((perm x)⁻¹ * σ) (adjHi k) < ((perm x)⁻¹ * σ) (adjLo k)) :
    permLen (σ * adjT k) + 1 = permLen σ := by
  rw [le_def] at hx
  simp only [perm_of] at hx
  have hres := permLen_mul_adjT_of_descent hd
  have hup := permLen_mul_le (perm x) ((perm x)⁻¹ * σ * adjT k)
  rw [← mul_assoc, mul_inv_cancel_left] at hup
  have hdown := permLen_mul_le (σ * adjT k) (adjT k)
  rw [mul_adjT_adjT, permLen_adjT] at hdown
  omega

/-- **A descent of the residue is a step of the order**: peeling it off `σ` keeps `x` below.  The
whole confluence of the descent recursion is this, iterated. -/
theorem le_mul_adjT_of_residue {σ : Equiv.Perm (Fin n)} {k : Fin (n - 1)} {x : WeakOrder n}
    (hx : x ≤ of σ) (hd : ((perm x)⁻¹ * σ) (adjHi k) < ((perm x)⁻¹ * σ) (adjLo k)) :
    x ≤ of (σ * adjT k) := by
  have htop := permLen_mul_adjT_of_residue hx hd
  have hres := permLen_mul_adjT_of_descent hd
  rw [le_def] at hx ⊢
  simp only [perm_of, ← mul_assoc] at hx ⊢
  omega

/-- **Below and not equal means below a lower cover**: the residue is not the identity, so it has
an adjacent descent, and a descent of the residue is a step. -/
theorem exists_cover_of_lt {σ : Equiv.Perm (Fin n)} {x : WeakOrder n}
    (hle : x ≤ of σ) (hne : perm x ≠ σ) :
    ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i) ∧ x ≤ of (σ * adjT i) := by
  obtain ⟨i, hdi⟩ := exists_adjacent_descent ((perm x)⁻¹ * σ)
    (Nat.pos_of_ne_zero fun hc => hne (inv_mul_eq_one.mp (eq_one_of_permLen_eq_zero _ hc)))
  exact ⟨i, descent_of_permLen_drop (permLen_mul_adjT_of_residue hle hdi),
    le_mul_adjT_of_residue hle hdi⟩

/-- **The Hasse diagram**: a cover is one adjacent crossing undone.  Below a cover
`exists_cover_of_lt` already produces a peel, and gradedness leaves it nowhere else to land. -/
theorem covBy_iff {x y : WeakOrder n} :
    x ⋖ y ↔ ∃ k : Fin (n - 1), perm y (adjHi k) < perm y (adjLo k) ∧ perm x = perm y * adjT k := by
  constructor
  · intro h
    obtain ⟨k, hd, hle⟩ := exists_cover_of_lt h.le fun hc => h.ne (congrArg of hc)
    refine ⟨k, hd, ?_⟩
    rcases h.eq_or_eq hle (of_mul_adjT_le hd) with heq | heq
    · exact congrArg perm heq.symm
    · have h1 : permLen (perm y * adjT k) = permLen (perm y) := congrArg permLen (congrArg perm heq)
      have h2 : permLen (perm y) = permLen (perm y * adjT k) + 1 :=
        permLen_mul_adjT_of_descent hd
      omega
  · rintro ⟨k, hd, hx⟩
    have hlen : permLen (perm x) + 1 = permLen (perm y) := by
      rw [hx]; exact (permLen_mul_adjT_of_descent hd).symm
    have hle : x ≤ y := by rw [show x = of (perm y * adjT k) from congrArg of hx]
                           exact of_mul_adjT_le hd
    exact ⟨hle.lt_of_ne fun hc => by rw [hc] at hlen; omega,
      fun _ hxc hcy => by have := permLen_lt_of_lt hxc; have := permLen_lt_of_lt hcy; omega⟩

/-- **The order is its Hasse diagram's reachability** — it is finite. -/
theorem le_iff_reflTransGen {x y : WeakOrder n} : x ≤ y ↔ Relation.ReflTransGen (· ⋖ ·) x y := by
  classical
  letI : Fintype (WeakOrder n) := inferInstanceAs (Fintype (Equiv.Perm (Fin n)))
  letI := Fintype.toLocallyFiniteOrder (α := WeakOrder n)
  exact le_iff_reflTransGen_covBy

/-- **Closed under covers is closed downwards.** -/
theorem isLowerSet_of_covBy {S : Set (WeakOrder n)}
    (h : ∀ ⦃x y : WeakOrder n⦄, x ⋖ y → y ∈ S → x ∈ S) : IsLowerSet S := fun _ _ hle hy => by
  replace hle := le_iff_reflTransGen.mp hle
  induction hle using Relation.ReflTransGen.head_induction_on with
  | refl => exact hy
  | head hc _ ih => exact h hc ih

end WeakOrder

end CubeChains
