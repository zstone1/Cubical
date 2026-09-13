import CubeChains.Machinery.Braid.Generated
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Cover
import Mathlib.Tactic.Group

/-!
# Machinery/Braid/WeakOrder — the right weak order on `Sₙ`

`x ≤ y` when `y` factors as `x` followed by something with the crossing counts adding.  Only
subadditivity of `permLen` and "length zero means identity" go into the poset laws; `Fin.revPerm`
is the top, and `σ ↦ w₀σ` is the order-reversing involution.

The two lemmas a confluence argument needs are `le_mul_adjT_mul_adjT` and `le_mul_adjT_braid`:
whatever lies below two lower covers lies below the square, resp. the hexagon, they span.
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

theorem of_injective : Function.Injective (of (n := n)) := fun _ _ h => h

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
    have hz : permLen ((perm x)⁻¹ * perm y) = 0 := by omega
    have := eq_one_of_permLen_eq_zero _ hz
    have hxy' : perm x = perm y := by
      rw [← mul_one (perm x), ← this, mul_inv_cancel_left]
    exact hxy'

theorem le_def {x y : WeakOrder n} :
    x ≤ y ↔ permLen (perm x) + permLen ((perm x)⁻¹ * perm y) = permLen (perm y) := Iff.rfl

/-- Below in the weak order means no longer. -/
theorem permLen_le_of_le {x y : WeakOrder n} (h : x ≤ y) : permLen (perm x) ≤ permLen (perm y) := by
  rw [le_def] at h; omega

/-- **The order is graded**: below and of the same length means equal. -/
theorem eq_of_le_of_permLen_eq {x y : WeakOrder n} (h : x ≤ y)
    (hlen : permLen (perm x) = permLen (perm y)) : perm x = perm y := by
  rw [le_def] at h
  rw [← mul_one (perm x), ← eq_one_of_permLen_eq_zero ((perm x)⁻¹ * perm y) (by omega),
    mul_inv_cancel_left]

/-- The witnessing factorisation. -/
theorem le_of_mul {σ β : Equiv.Perm (Fin n)}
    (h : permLen σ + permLen β = permLen (σ * β)) : of σ ≤ of (σ * β) := by
  rw [le_def]
  simpa [inv_mul_cancel_left] using h

/-- **…named at the product rather than at the factors** — the shape a crossing cocycle produces:
an arrow factors the class on the right and the lengths add. -/
theorem le_of_mul_eq {σ τ π : Equiv.Perm (Fin n)} (hmul : τ * π = σ)
    (hlen : permLen σ = permLen π + permLen τ) : of τ ≤ of σ := by
  subst hmul
  exact le_of_mul (by omega)

/-- **Length-additive left translation is monotone**: `w` cancels out of the gap `x⁻¹y` and adds to
both lengths. -/
theorem of_mul_le_of_mul (w : Equiv.Perm (Fin n)) {x y : Equiv.Perm (Fin n)}
    (hx : permLen (w * x) = permLen w + permLen x)
    (hy : permLen (w * y) = permLen w + permLen y) (h : of x ≤ of y) :
    of (w * x) ≤ of (w * y) := by
  rw [le_def] at h ⊢
  simp only [perm_of] at h ⊢
  rw [show (w * x)⁻¹ * (w * y) = x⁻¹ * y by group]
  omega

/-- Strictly below means strictly shorter — only the identity has length zero. -/
theorem permLen_lt_of_lt {x y : WeakOrder n} (h : x < y) :
    permLen (perm x) < permLen (perm y) := by
  have hle := le_def.mp h.le
  rcases Nat.eq_zero_or_pos (permLen ((perm x)⁻¹ * perm y)) with hz | _
  · exact absurd (show perm x = perm y by
      rw [← mul_one (perm x), ← eq_one_of_permLen_eq_zero _ hz, mul_inv_cancel_left]) h.ne
  · omega

/-- **The weak order is graded by `permLen`**, so one extra crossing is a covering. -/
theorem covBy_of_permLen_succ {x y : WeakOrder n} (hle : x ≤ y)
    (h : permLen (perm x) + 1 = permLen (perm y)) : x ⋖ y := by
  refine ⟨lt_of_le_of_ne hle fun he => by rw [he] at h; omega, fun z hxz hzy => ?_⟩
  have h1 := permLen_lt_of_lt hxz
  have h2 := permLen_lt_of_lt hzy
  omega

/-! ### Self-duality

The reversal is the top (`permLen_add_inv_mul_revPerm`), and `σ ↦ w₀σ` is an involution reversing
the order: `w₀` cancels out of the difference `x⁻¹y`, while each length is complemented.  This is
the **orientation bridge** — it is what turns a presentation of `Ch(□n)[W⁻¹]ᵒᵖ` into one of
`Ch(□n)[W⁻¹]`. -/

instance : OrderTop (WeakOrder n) where
  top := of Fin.revPerm
  le_top x := permLen_add_inv_mul_revPerm (perm x)

/-- The order-reversing involution `σ ↦ w₀σ`, `w₀` the reversal. -/
def rev (x : WeakOrder n) : WeakOrder n := of (Fin.revPerm * perm x)

@[simp] theorem perm_rev (x : WeakOrder n) : perm (rev x) = Fin.revPerm * perm x := rfl

@[simp] theorem rev_rev (x : WeakOrder n) : rev (rev x) = x := by
  change of (Fin.revPerm * (Fin.revPerm * perm x)) = x
  rw [← mul_assoc, revPerm_mul_self, one_mul, of_perm]

theorem rev_le_rev {x y : WeakOrder n} (h : x ≤ y) : rev y ≤ rev x := by
  have hcancel : (Fin.revPerm * perm y)⁻¹ * (Fin.revPerm * perm x) = (perm y)⁻¹ * perm x := by
    rw [mul_inv_rev, revPerm_inv, mul_assoc, ← mul_assoc (Fin.revPerm : Equiv.Perm (Fin n)),
      revPerm_mul_self, one_mul]
  have h3 : permLen ((perm y)⁻¹ * perm x) = permLen ((perm x)⁻¹ * perm y) := by
    rw [← permLen_inv ((perm x)⁻¹ * perm y), mul_inv_rev, inv_inv]
  have h1 := permLen_revPerm_mul_add (perm x)
  have h2 := permLen_revPerm_mul_add (perm y)
  rw [le_def] at h ⊢
  simp only [perm_rev, hcancel]
  omega

theorem rev_le_rev_iff {x y : WeakOrder n} : rev y ≤ rev x ↔ x ≤ y :=
  ⟨fun h => by simpa using rev_le_rev h, rev_le_rev⟩

/-- **The right weak order is self-dual**, by `σ ↦ w₀σ`. -/
def revOrderIso (n : ℕ) : WeakOrder n ≃o (WeakOrder n)ᵒᵈ where
  toFun x := OrderDual.toDual (rev x)
  invFun x := rev (OrderDual.ofDual x)
  left_inv := rev_rev
  right_inv := rev_rev
  map_rel_iff' := rev_le_rev_iff

theorem of_mul_adjT_le {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (h : σ (adjHi i) < σ (adjLo i)) : of (σ * adjT i) ≤ of σ := by
  have hinv : (σ * adjT i)⁻¹ * σ = adjT i := by
    have hs : (adjT i)⁻¹ = adjT i := by rw [adjT, Equiv.swap_inv]
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, hs]
  rw [le_def]
  simp only [perm_of, hinv, permLen_adjT]
  exact (permLen_mul_adjT_of_descent h).symm

/-- Below a lower cover, the drop shows up in the residue `x⁻¹σ` as well. -/
theorem permLen_residue_drop {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} {x : WeakOrder n}
    (hd : σ (adjHi i) < σ (adjLo i)) (hx : x ≤ of (σ * adjT i)) :
    permLen ((perm x)⁻¹ * σ * adjT i) + 1 = permLen ((perm x)⁻¹ * σ) := by
  have hxσ := hx.trans (of_mul_adjT_le hd)
  rw [le_def] at hx hxσ
  simp only [perm_of, ← mul_assoc] at hx hxσ
  have hstep := permLen_mul_adjT_of_descent hd
  omega

/-- **Two far-apart lower covers**: whatever lies below both lies below the doubly sorted
permutation. -/
theorem le_mul_adjT_mul_adjT {σ : Equiv.Perm (Fin n)} {i j : Fin (n - 1)} {x : WeakOrder n}
    (hij : (i : ℕ) + 1 < (j : ℕ))
    (hi : σ (adjHi i) < σ (adjLo i)) (hj : σ (adjHi j) < σ (adjLo j))
    (hxi : x ≤ of (σ * adjT i)) (hxj : x ≤ of (σ * adjT j)) :
    x ≤ of (σ * adjT i * adjT j) := by
  have h1 := permLen_mul_adjT_of_descent hi
  have h2 := permLen_mul_adjT_of_descent
    (descent_mul_adjT_of_far (k := i) (l := j) (by omega) (by omega) (by omega) hj)
  have h3 := permLen_residue_drop hi hxi
  have h4 := permLen_mul_adjT_of_descent (descent_mul_adjT_of_far (k := i) (l := j) (by omega)
    (by omega) (by omega) (descent_of_permLen_drop (permLen_residue_drop hj hxj)))
  have hxσ : x ≤ of σ := hxi.trans (of_mul_adjT_le hi)
  rw [le_def] at hxσ ⊢
  simp only [perm_of, ← mul_assoc] at hxσ ⊢
  omega

/-- **Two consecutive lower covers**: whatever lies below both lies below the sorted
three-window. -/
theorem le_mul_adjT_braid {σ : Equiv.Perm (Fin n)} {i j : Fin (n - 1)} {x : WeakOrder n}
    (hij : (j : ℕ) = (i : ℕ) + 1)
    (hi : σ (adjHi i) < σ (adjLo i)) (hj : σ (adjHi j) < σ (adjLo j))
    (hxi : x ≤ of (σ * adjT i)) (hxj : x ≤ of (σ * adjT j)) :
    x ≤ of (σ * adjT i * adjT j * adjT i) := by
  have hdwi := descent_of_permLen_drop (permLen_residue_drop hi hxi)
  have hdwj := descent_of_permLen_drop (permLen_residue_drop hj hxj)
  have h1 := permLen_mul_adjT_of_descent hi
  have h2 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₁ hij hi hj)
  have h3 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₂ hij hj)
  have h4 := permLen_mul_adjT_of_descent hdwi
  have h5 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₁ hij hdwi hdwj)
  have h6 := permLen_mul_adjT_of_descent (descent_mul_adjT_braid₂ hij hdwj)
  have hxσ : x ≤ of σ := hxi.trans (of_mul_adjT_le hi)
  rw [le_def] at hxσ ⊢
  simp only [perm_of, ← mul_assoc] at hxσ ⊢
  omega

/-- **Below and not equal means below a lower cover.**  Peel an adjacent descent off the residue
`x⁻¹σ`; length-additivity survives it, so the cut it names is a descent of `σ` too. -/
theorem exists_cover_of_lt {σ : Equiv.Perm (Fin n)} {x : WeakOrder n}
    (hle : x ≤ of σ) (hne : perm x ≠ σ) :
    ∃ i : Fin (n - 1), σ (adjHi i) < σ (adjLo i) ∧ x ≤ of (σ * adjT i) := by
  rw [le_def] at hle
  simp only [perm_of] at hle
  set β : Equiv.Perm (Fin n) := (perm x)⁻¹ * σ with hβ
  have hσβ : perm x * β = σ := by rw [hβ, mul_inv_cancel_left]
  have hβ1 : β ≠ 1 := fun hc => hne (by rw [← hσβ, hc, mul_one])
  have hpos : 0 < permLen β := Nat.pos_of_ne_zero fun hc => hβ1 (eq_one_of_permLen_eq_zero β hc)
  obtain ⟨i, hdi⟩ := exists_adjacent_descent β hpos
  have hstep := permLen_mul_adjT_of_descent hdi
  have hup : permLen (perm x * (β * adjT i)) ≤ permLen (perm x) + permLen (β * adjT i) :=
    permLen_mul_le _ _
  have hassoc : perm x * (β * adjT i) = σ * adjT i := by rw [← mul_assoc, hσβ]
  rw [hassoc] at hup
  have hdown : permLen σ ≤ permLen (σ * adjT i) + 1 := by
    have h := permLen_mul_le (σ * adjT i) (adjT i)
    rw [mul_adjT_adjT, permLen_adjT] at h
    exact h
  have hkey : permLen (σ * adjT i) + 1 = permLen σ := by omega
  refine ⟨i, descent_of_permLen_drop hkey, ?_⟩
  rw [le_def]
  simp only [perm_of]
  rw [show (perm x)⁻¹ * (σ * adjT i) = β * adjT i by rw [hβ, mul_assoc]]
  omega

end WeakOrder

end CubeChains
