import CubeChains.Machinery.Braid.WeakOrder

/-!
# Machinery/Braid/RankTwo — the polygon two crossings span

Two distinct crossings a permutation can undo span a **rank-two interval** of the right weak order:
a `2·cox`-gon, `cox` being the pair's Coxeter exponent (`Machinery/Braid/Artin`).  Undoing them
alternately walks down one side, and the two sides meet at the foot after `cox` steps.

    u ──i──▸ · ──k──▸ ⋯        `cox` letters either way, the same foot,
      └──k──▸ · ──i──▸ ⋯        and every prefix again a step

`descent_altWord` is that walk and `altWord_cox` is the meeting; the rest of the file is that walk
read as steps of the order, and none of it sees the value of `cox`.
`Concurrency/Presentation/PairChain` reads `cox` off the *shape* the two cuts share
(`cox_eq_crossCap_pairChain`), which is where the exponent acquires its geometric meaning: the
crossing capacity of a degree-two chain.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

/-- **Lemma A — the polygon two crossings span.**  If `u` undoes both `i` and `k`, then the
alternating word out of `u` is a descent at every one of its `cox` letters: each prefix is again a
step of the right weak order, and the walk stops exactly where the two orders meet.  This is the
statement both Matsumoto proofs were rebuilding by hand. -/
theorem descent_altWord {u : Perm (Fin n)} {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) :
    ∀ t < cox i k, (u * altWord i k t) (adjHi (altIdx i k t))
      < (u * altWord i k t) (adjLo (altIdx i k t)) := by
  have hzero : (u * altWord i k 0) (adjHi (altIdx i k 0))
      < (u * altWord i k 0) (adjLo (altIdx i k 0)) := by
    rw [altWord_zero, mul_one, altIdx_zero]; exact hi
  rcases orderOf_adjT_mul_adjT_cases hik with ⟨hfar, hc⟩ | ⟨hadj, hc⟩
  · intro t ht
    rw [cox, hc] at ht
    match t, ht with
    | 0, _ => exact hzero
    | 1, _ =>
        rw [altWord_one, altIdx_one]
        exact descent_mul_adjT_of_far (by omega) (by omega) (by omega) hk
  · intro t ht
    rw [cox, hc] at ht
    match t, ht with
    | 0, _ => exact hzero
    | 1, _ =>
        rw [altWord_one, altIdx_one]
        rcases hadj with h | h
        · exact descent_mul_adjT_braid₁ h hi hk
        · exact descent_mul_adjT_braid₃ h hk hi
    | 2, _ =>
        rw [altWord_two, altIdx_two, ← mul_assoc]
        rcases hadj with h | h
        · exact descent_mul_adjT_braid₂ h hk
        · exact descent_mul_adjT_braid₄ h hk

/-! ## The walk, as steps of the weak order

Everything below is `descent_altWord` iterated; none of it sees the two species. -/

/-- Each letter drops the crossing count by one. -/
theorem permLen_altWord {u : Perm (Fin n)} {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) :
    ∀ t ≤ cox i k, permLen (u * altWord i k t) + t = permLen u
  | 0, _ => by rw [altWord_zero, mul_one, Nat.add_zero]
  | t + 1, ht => by
      have hprev := permLen_altWord hik hi hk t (by omega)
      have hd := descent_altWord hik hi hk t (by omega)
      have := permLen_mul_adjT_of_descent hd
      rw [altWord_succ, ← mul_assoc]
      omega

/-- **…and the polygon word is pinned by its two crossings**: an element of the full length undoing
both *is* the alternating word.  Uniform in `cox`, because the walk uses the length up: what is left
after it is the identity. -/
theorem eq_altProd_of_descents {u : Perm (Fin n)} {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k))
    (hlen : permLen u = cox i k) : u = altProd adjT i k (cox i k) := by
  have h := permLen_altWord hik hi hk (cox i k) le_rfl
  have h0 : u * altWord i k (cox i k) = 1 := eq_one_of_permLen_eq_zero _ (by omega)
  rw [mul_eq_one_iff_eq_inv.mp h0, altWord, inv_inv]

/-- **Every prefix of the walk is a step down.** -/
theorem of_altWord_le {u : Perm (Fin n)} {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ))
    (hi : u (adjHi i) < u (adjLo i)) (hk : u (adjHi k) < u (adjLo k)) :
    ∀ {s t : ℕ}, s ≤ t → t ≤ cox i k →
      WeakOrder.of (u * altWord i k t) ≤ WeakOrder.of (u * altWord i k s) := by
  have step : ∀ t < cox i k, WeakOrder.of (u * altWord i k (t + 1))
      ≤ WeakOrder.of (u * altWord i k t) := by
    intro t ht
    rw [altWord_succ, ← mul_assoc]
    exact WeakOrder.of_mul_adjT_le (descent_altWord hik hi hk t ht)
  intro s t hst
  induction t with
  | zero => intro _; rw [Nat.le_zero.mp hst]
  | succ t ih =>
      intro ht
      rcases Nat.eq_or_lt_of_le hst with rfl | hlt
      · exact le_rfl
      · exact (step t (by omega)).trans (ih (by omega) (by omega))

/-- **The walk stays above anything the top already lay above**: a lower bound of `u` whose residue
undoes both crossings is a lower bound of every prefix, the foot included. -/
theorem le_of_altWord {u : Perm (Fin n)} {i k : Fin (n - 1)} {x : WeakOrder n}
    (hik : (i : ℕ) ≠ (k : ℕ)) (hx : x ≤ WeakOrder.of u)
    (hi : ((WeakOrder.perm x)⁻¹ * u) (adjHi i) < ((WeakOrder.perm x)⁻¹ * u) (adjLo i))
    (hk : ((WeakOrder.perm x)⁻¹ * u) (adjHi k) < ((WeakOrder.perm x)⁻¹ * u) (adjLo k)) :
    ∀ t ≤ cox i k, x ≤ WeakOrder.of (u * altWord i k t)
  | 0, _ => by rw [altWord_zero, mul_one]; exact hx
  | t + 1, ht => by
      have hprev := le_of_altWord hik hx hi hk t (by omega)
      have hd := descent_altWord (u := (WeakOrder.perm x)⁻¹ * u) hik hi hk t (by omega)
      rw [altWord_succ, ← mul_assoc]
      refine WeakOrder.le_mul_adjT_of_residue hprev ?_
      simpa only [WeakOrder.perm_of, ← mul_assoc] using hd

/-! ## The foot

The permutation the two walks meet at — named by the pair and nothing else. -/

/-- **The foot of the polygon**: `u` with both crossings, and everything they force, undone. -/
noncomputable def polyFoot (u : Perm (Fin n)) (i k : Fin (n - 1)) : Perm (Fin n) :=
  u * altWord i k (cox i k)

/-- **The two walks meet** — which is the Coxeter relation, transported to `u`. -/
theorem polyFoot_comm {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ)) (u : Perm (Fin n)) :
    polyFoot u i k = polyFoot u k i := by
  rw [polyFoot, polyFoot, altWord_cox hik, cox_comm i k]

variable {u : Perm (Fin n)} {i k : Fin (n - 1)}

/-- **The foot lies below the cover the walk leaves by.** -/
theorem polyFoot_le_mul_adjT (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) :
    WeakOrder.of (polyFoot u i k) ≤ WeakOrder.of (u * adjT i) := by
  have h1 : 1 ≤ cox i k := by have := two_le_cox hik; omega
  simpa only [altWord_one] using of_altWord_le hik hi hk h1 le_rfl

/-- …and below `u` itself. -/
theorem polyFoot_le (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) : WeakOrder.of (polyFoot u i k) ≤ WeakOrder.of u := by
  simpa only [altWord_zero, mul_one] using
    of_altWord_le hik hi hk (Nat.zero_le (cox i k)) (le_rfl (a := cox i k))

/-- **The foot is as far down as a lower bound of `u` reaches** — so the polygon closes over
anything already below both covers. -/
theorem le_polyFoot {x : WeakOrder n} (hik : (i : ℕ) ≠ (k : ℕ)) (hx : x ≤ WeakOrder.of u)
    (hi : ((WeakOrder.perm x)⁻¹ * u) (adjHi i) < ((WeakOrder.perm x)⁻¹ * u) (adjLo i))
    (hk : ((WeakOrder.perm x)⁻¹ * u) (adjHi k) < ((WeakOrder.perm x)⁻¹ * u) (adjLo k)) :
    x ≤ WeakOrder.of (polyFoot u i k) :=
  le_of_altWord hik hx hi hk _ le_rfl

/-- **The walk is `cox` steps long** — the crossing count drops by one at each letter. -/
theorem permLen_polyFoot (hik : (i : ℕ) ≠ (k : ℕ)) (hi : u (adjHi i) < u (adjLo i))
    (hk : u (adjHi k) < u (adjLo k)) : permLen (polyFoot u i k) + cox i k = permLen u :=
  permLen_altWord hik hi hk _ le_rfl

end CubeChains
