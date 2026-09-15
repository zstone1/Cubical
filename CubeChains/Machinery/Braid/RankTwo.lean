import CubeChains.Machinery.Braid.WeakOrder

/-!
# Machinery/Braid/RankTwo — the polygon two crossings span

A permutation `u` undoing two crossings `i ≠ k` inverts every pair they can reach, so it absorbs
every alternating word in them (`permLen_mul_altWord`).  The alternating word is reduced up to the
Coxeter exponent — at a first failure it would itself undo both crossings and absorb the other word
of its length, giving the pair's product a shorter period.  So the two walks down from `u` descend
at every letter and meet at the foot after `cox` steps, with no reference to the pair's species:

    u ──i──▸ · ──k──▸ ⋯ ──▸ polyFoot u i k
      └──k──▸ · ──i──▸ ⋯ ────────┘
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

/-! ## A double descent absorbs the alternating word -/

/-- A cut the pair does not cross is kept by every word it spells. -/
theorem altProd_lt_iff {i k : Fin (n - 1)} {c : ℕ} (hi : c ≠ i + 1) (hk : c ≠ k + 1) :
    ∀ (t : ℕ) (x : Fin n), ((altProd adjT i k t x : Fin n) : ℕ) < c ↔ (x : ℕ) < c
  | 0, _ => Iff.rfl
  | t + 1, x => by
      rw [altProd, Perm.mul_apply, adjT_val, ← altProd_lt_iff hi hk t x]
      unfold altIdx
      split_ifs <;> omega

/-- **A double descent inverts every pair the two crossings reach**, so it keeps every crossing of
the alternating word. -/
theorem inversions_altProd_subset {u : Perm (Fin n)} {i k : Fin (n - 1)}
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) (t : ℕ) :
    inversions (altProd adjT i k t) ⊆ inversions u := by
  rintro ⟨p, q⟩ h
  simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  refine ⟨h.1, rel_of_span (P := fun c => c = i + 1 ∨ c = k + 1) (R := fun x y => u y < u x)
    (fun _ _ _ h₁ h₂ => h₂.trans h₁) (fun j hj => ?_) p q h.1 fun c hpc hcq => ?_⟩
  · rcases hj with hj | hj
    · rwa [show j = i from Fin.ext (by omega)]
    · rwa [show j = k from Fin.ext (by omega)]
  · by_contra hc
    have hp := (altProd_lt_iff (not_or.mp hc).1 (not_or.mp hc).2 t p).mpr hpc
    have hq := (altProd_lt_iff (not_or.mp hc).1 (not_or.mp hc).2 t q).not.mpr (by omega)
    exact absurd (Fin.lt_def.mp h.2) (by omega)

/-- **A double descent absorbs the alternating word**: peeling it off costs its whole length. -/
theorem permLen_mul_altWord {u : Perm (Fin n)} {i k : Fin (n - 1)}
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) (t : ℕ) :
    permLen (u * altWord i k t) + permLen (altWord i k t) = permLen u := by
  have h := permLen_mul_of_inversions_subset (σ := altProd adjT i k t) (ρ := u * altWord i k t)
    (by rw [altWord, inv_mul_cancel_right]; exact inversions_altProd_subset hi hk t)
  rw [altWord, inv_mul_cancel_right] at h
  rw [altWord, permLen_inv]
  omega

theorem altIdx_ne {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ)) (t : ℕ) :
    (altIdx i k t : ℕ) ≠ (altIdx k i t : ℕ) := by
  unfold altIdx; split_ifs <;> omega

theorem cox_altIdx (i k : Fin (n - 1)) (t : ℕ) :
    cox (altIdx i k t) (altIdx k i t) = cox i k := by
  unfold altIdx; split_ifs; exacts [rfl, cox_comm k i]

/-- **The alternating word is reduced up to the exponent**: at a first failure it undoes both of
its letters, so it absorbs the other word of its length, and the pair's product has that period. -/
theorem permLen_altWord_of_le : ∀ {t : ℕ} {i k : Fin (n - 1)}, (i : ℕ) ≠ (k : ℕ) →
    t ≤ cox i k → permLen (altWord i k t) = t
  | 0, _, _, _, _ => by rw [altWord_zero, permLen_one]
  | 1, _, _, _, _ => by rw [altWord_one, permLen_adjT]
  | s + 2, i, k, hik, ht => by
      have h1 := permLen_altWord_of_le hik (by omega : s + 1 ≤ cox i k)
      rw [altWord_succ]
      rcases ascent_or_descent (altWord i k (s + 1)) (altIdx i k (s + 1)) with ha | hd
      · rw [permLen_mul_adjT ha, h1]
      · have hb : altWord i k (s + 1) (adjHi (altIdx k i (s + 1)))
            < altWord i k (s + 1) (adjLo (altIdx k i (s + 1))) := by
          refine descent_of_permLen_drop ?_
          rw [altIdx_succ, altWord_succ, mul_adjT_adjT, ← altWord_succ, h1,
            permLen_altWord_of_le hik (by omega : s ≤ cox i k)]
        have h := permLen_mul_altWord hd hb (s + 1)
        rw [h1, permLen_altWord_of_le (t := s + 1) (altIdx_ne hik (s + 1))
          (by rw [cox_altIdx]; omega), ← altWord_inv, altWord_mul_inv] at h
        exact (pow_ne_one_of_lt_orderOf (x := adjT i * adjT k) (by omega : s + 1 ≠ 0) ht
          (eq_one_of_permLen_eq_zero _ (by omega))).elim

theorem permLen_altProd_of_le {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ)) {t : ℕ}
    (ht : t ≤ cox i k) : permLen (altProd adjT i k t) = t :=
  (permLen_inv _).symm.trans (permLen_altWord_of_le hik ht)

/-! ## The walk -/

variable {u : Perm (Fin n)} {i k : Fin (n - 1)}

/-- **The polygon two crossings span**: the alternating word out of a double descent descends at
every one of its `cox` letters. -/
theorem descent_altWord (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) :
    ∀ t < cox i k, (u * altWord i k t) (adjHi (altIdx i k t))
      < (u * altWord i k t) (adjLo (altIdx i k t)) := fun t ht =>
  descent_of_permLen_drop (by
    have h₀ := permLen_mul_altWord hi hk t
    have h₁ := permLen_mul_altWord hi hk (t + 1)
    rw [permLen_altWord_of_le hik ht.le] at h₀
    rw [permLen_altWord_of_le hik ht, altWord_succ, ← mul_assoc] at h₁
    omega)

/-- **…and the polygon word is pinned by its two crossings**: an element of the full length undoing
both *is* the alternating word. -/
theorem eq_altProd_of_descents (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) (hlen : permLen u = cox i k) :
    u = altProd adjT i k (cox i k) := by
  have h := permLen_mul_altWord hi hk (cox i k)
  rw [permLen_altWord_of_le hik le_rfl] at h
  exact (mul_eq_one_iff_eq_inv.mp (eq_one_of_permLen_eq_zero (u * altWord i k (cox i k))
    (by omega))).trans (inv_inv _)

/-- **A map multiplicative across ascents reads the alternating word letter by letter.** -/
theorem map_altProd_of_atom {M : Type*} [Monoid M] {g : Perm (Fin n) → M}
    (hatom : ∀ (A : Perm (Fin n)) (k : Fin (n - 1)), A (adjLo k) < A (adjHi k) →
      g A * g (adjT k) = g (A * adjT k)) :
    ∀ {t : ℕ} {i k : Fin (n - 1)}, (i : ℕ) ≠ (k : ℕ) → t + 1 ≤ cox i k →
      g (altProd adjT i k (t + 1)) = altProd (fun j => g (adjT j)) i k (t + 1)
  | 0, _, _, _, _ => (congrArg g (mul_one _)).trans (mul_one _).symm
  | t + 1, i, k, hik, ht => by
      have hki : t + 1 ≤ cox k i := by rw [cox_comm]; omega
      rw [← altProd_succ_right adjT i k (t + 1), ← altProd_succ_right _ i k (t + 1),
        ← map_altProd_of_atom hatom (Ne.symm hik) hki, hatom]
      refine ascent_of_permLen_mul_adjT ?_
      rw [altProd_succ_right, permLen_altProd_of_le hik ht, permLen_altProd_of_le (Ne.symm hik) hki]

/-- **Every germ carries an Artin family** — multiplicativity across an ascent is the only input,
because both alternating words of length `cox` are reduced words of one permutation. -/
theorem isArtinFamily_of_atom {M : Type*} [Monoid M] {g : Perm (Fin n) → M}
    (hatom : ∀ (A : Perm (Fin n)) (k : Fin (n - 1)), A (adjLo k) < A (adjHi k) →
      g A * g (adjT k) = g (A * adjT k)) :
    IsArtinFamily fun i : Fin (n - 1) => g (adjT i) :=
  ⟨fun {i k} hik => by
    obtain ⟨t, ht⟩ : ∃ t, cox i k = t + 1 := ⟨cox i k - 1, by have := two_le_cox hik; omega⟩
    have ht' : cox k i = t + 1 := (cox_comm k i).trans ht
    rw [ht, ← map_altProd_of_atom hatom hik ht.ge, ← map_altProd_of_atom hatom (Ne.symm hik) ht'.ge,
      ← ht]
    exact congrArg g (isArtinFamily_adjT.altProd_cox hik)⟩

/-! ## The foot -/

/-- **The foot of the polygon**: `u` with both crossings, and everything they force, undone. -/
noncomputable def polyFoot (u : Perm (Fin n)) (i k : Fin (n - 1)) : Perm (Fin n) :=
  u * altWord i k (cox i k)

/-- **The two walks meet** — which is the Coxeter relation, transported to `u`. -/
theorem polyFoot_comm (u : Perm (Fin n)) :
    polyFoot u i k = polyFoot u k i := by
  rw [polyFoot, polyFoot, altWord_cox, cox_comm i k]

/-- **The walk is `cox` steps long.** -/
theorem permLen_polyFoot (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) : permLen (polyFoot u i k) + cox i k = permLen u := by
  have h := permLen_mul_altWord hi hk (cox i k)
  rwa [permLen_altWord_of_le hik le_rfl] at h

/-- A drop of the full length along an alternating word is a step down the weak order. -/
theorem of_mul_altWord_le {v : Perm (Fin n)} (hik : (i : ℕ) ≠ (k : ℕ)) {t : ℕ}
    (ht : t ≤ cox i k) (h : permLen (v * altWord i k t) + t = permLen v) :
    WeakOrder.of (v * altWord i k t) ≤ WeakOrder.of v :=
  WeakOrder.le_of_mul_eq (π := altProd adjT i k t) (inv_mul_cancel_right v _)
    (by rw [permLen_altProd_of_le hik ht]; omega)

/-- …and below `u` itself. -/
theorem polyFoot_le (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) : WeakOrder.of (polyFoot u i k) ≤ WeakOrder.of u :=
  of_mul_altWord_le hik le_rfl (permLen_polyFoot hik hi hk)

/-- **The foot lies below the cover the walk leaves by.** -/
theorem polyFoot_le_mul_adjT (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) :
    WeakOrder.of (polyFoot u i k) ≤ WeakOrder.of (u * adjT i) := by
  obtain ⟨s, hs⟩ : ∃ s, cox i k = s + 1 := ⟨cox i k - 1, by have := two_le_cox hik; omega⟩
  have h := permLen_polyFoot hik hi hk
  have hd := permLen_mul_adjT_of_descent hi
  rw [polyFoot, hs, altWord_succ_left, ← mul_assoc] at h ⊢
  exact of_mul_altWord_le (Ne.symm hik) (by rw [cox_comm]; omega) (by omega)

/-- **The foot is as far down as a lower bound of `u` reaches**, when the residue undoes both. -/
theorem le_polyFoot {x : WeakOrder n} (hik : (i : ℕ) ≠ (k : ℕ)) (hx : x ≤ WeakOrder.of u)
    (hi : ((WeakOrder.perm x)⁻¹ * u) (adjHi i) < ((WeakOrder.perm x)⁻¹ * u) (adjLo i))
    (hk : ((WeakOrder.perm x)⁻¹ * u) (adjHi k) < ((WeakOrder.perm x)⁻¹ * u) (adjLo k)) :
    x ≤ WeakOrder.of (polyFoot u i k) := by
  rw [WeakOrder.le_def, WeakOrder.perm_of] at hx ⊢
  have hr := permLen_mul_altWord hi hk (cox i k)
  have h₁ := permLen_mul_le (WeakOrder.perm x) ((WeakOrder.perm x)⁻¹ * u * altWord i k (cox i k))
  have h₂ := permLen_mul_le (u * altWord i k (cox i k)) (altWord i k (cox i k))⁻¹
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h₁
  rw [mul_inv_cancel_right, permLen_inv, permLen_altWord_of_le hik le_rfl] at h₂
  rw [permLen_altWord_of_le hik le_rfl] at hr
  rw [polyFoot, ← mul_assoc]
  omega

end CubeChains
