import CubeChains.Machinery.Braid.Germ
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Machinery/Braid/Artin — the adjacent transpositions, and the Artin presentation

`adjT k` swaps `k` and `k+1`.  `cox i k = orderOf (adjT i * adjT k)` is the Coxeter matrix, and
`IsArtinFamily` is **one** clause in it: the two alternating words of that length agree.
`isArtinFamily_iff` reads the clause as the two oriented relations of `ArtinRel`, which present
`ArtinBraid n`; its comparison with the germ `Braid n` is `Machinery/Braid/Matsumoto`.

Not mathlib's `GroupTheory/Coxeter`: it is stated for a `CoxeterSystem` and constructs none for
`Sₙ`, and its length is a minimal word length, not the inversion count `permLen` reads.
-/

namespace CubeChains

open Equiv

/-- The Garside (germ) braid group, under a name that pairs with `ArtinBraid`. -/
abbrev GarsideBraid (n : ℕ) : Type := Braid n

variable {n : ℕ}

/-! ## Adjacent transpositions -/

/-- Low endpoint of the `k`-th adjacent transposition. -/
def adjLo (k : Fin (n - 1)) : Fin n := ⟨k.1, by have := k.2; omega⟩

/-- High endpoint of the `k`-th adjacent transposition. -/
def adjHi (k : Fin (n - 1)) : Fin n := ⟨k.1 + 1, by have := k.2; omega⟩

@[simp] theorem adjLo_val (k : Fin (n - 1)) : (adjLo k).1 = k.1 := rfl
@[simp] theorem adjHi_val (k : Fin (n - 1)) : (adjHi k).1 = k.1 + 1 := rfl

/-- Consecutive indices share an endpoint. -/
theorem adjLo_eq_adjHi {i j : Fin (n - 1)} (h : (j : ℕ) = (i : ℕ) + 1) : adjLo j = adjHi i :=
  Fin.ext (by rw [adjLo_val, adjHi_val, h])

theorem adjLo_lt_adjHi (k : Fin (n - 1)) : adjLo k < adjHi k :=
  Fin.lt_def.mpr (by rw [adjLo_val, adjHi_val]; omega)

theorem adjLo_ne_adjHi (k : Fin (n - 1)) : adjLo k ≠ adjHi k := (adjLo_lt_adjHi k).ne

/-- **A relation holding across every adjacent pair inside a stretch holds across the stretch.**
`P` marks the pairs it is given at, an index being named by the coordinate `k + 1` it separates. -/
theorem rel_of_span {P : ℕ → Prop} {R : Fin n → Fin n → Prop}
    (htrans : ∀ a b c : Fin n, R a b → R b c → R a c)
    (hstep : ∀ k : Fin (n - 1), P ((k : ℕ) + 1) → R (adjLo k) (adjHi k)) :
    ∀ x y : Fin n, (x : ℕ) < (y : ℕ) →
      (∀ t : ℕ, (x : ℕ) < t → t ≤ (y : ℕ) → P t) → R x y := by
  have one : ∀ x y : Fin n, (y : ℕ) = (x : ℕ) + 1 → P ((x : ℕ) + 1) → R x y := by
    intro x y hy hP
    have hk : (x : ℕ) < n - 1 := by have := y.isLt; omega
    have e1 : x = adjLo ⟨(x : ℕ), hk⟩ := Fin.ext rfl
    have e2 : y = adjHi ⟨(x : ℕ), hk⟩ := Fin.ext (by rw [adjHi_val]; omega)
    rw [e1, e2]
    exact hstep _ hP
  have key : ∀ (l : ℕ) (x y : Fin n), (y : ℕ) = (x : ℕ) + l + 1 →
      (∀ t : ℕ, (x : ℕ) < t → t ≤ (y : ℕ) → P t) → R x y := by
    intro l
    induction l with
    | zero =>
        exact fun x y hy hall => one x y (by omega) (hall ((x : ℕ) + 1) (by omega) (by omega))
    | succ l ih =>
        intro x y hy hall
        have hlt : (x : ℕ) + l + 1 < n := by have := y.isLt; omega
        exact htrans x ⟨(x : ℕ) + l + 1, hlt⟩ y
          (ih x ⟨(x : ℕ) + l + 1, hlt⟩ rfl fun t h1 h2 =>
            hall t h1 (by have h2' : t ≤ (x : ℕ) + l + 1 := h2; omega))
          (one _ y (by omega) (hall ((x : ℕ) + l + 1 + 1) (by omega) (by omega)))
  exact fun x y hxy hall => key ((y : ℕ) - (x : ℕ) - 1) x y (by omega) hall

/-- The `k`-th adjacent transposition, swapping `k` and `k+1`. -/
def adjT (k : Fin (n - 1)) : Perm (Fin n) := Equiv.swap (adjLo k) (adjHi k)

theorem adjT_lo (k : Fin (n - 1)) : adjT k (adjLo k) = adjHi k := swap_apply_left _ _
theorem adjT_hi (k : Fin (n - 1)) : adjT k (adjHi k) = adjLo k := swap_apply_right _ _

@[simp] theorem adjT_adjT (k : Fin (n - 1)) (x : Fin n) : adjT k (adjT k x) = x :=
  swap_apply_self _ _ _

theorem adjT_of_ne (k : Fin (n - 1)) {x : Fin n} (h1 : x.1 ≠ k.1) (h2 : x.1 ≠ k.1 + 1) :
    adjT k x = x :=
  swap_apply_of_ne_of_ne (fun heq => h1 (congrArg Fin.val heq))
    (fun heq => h2 (congrArg Fin.val heq))

/-- The value of `adjT k x`: it swaps the values `k` and `k+1`, and fixes everything else. -/
theorem adjT_val (k : Fin (n - 1)) (x : Fin n) :
    (adjT k x).1 = if x.1 = k.1 then k.1 + 1 else if x.1 = k.1 + 1 then k.1 else x.1 := by
  by_cases h1 : x.1 = k.1
  · rw [if_pos h1, show x = adjLo k from Fin.ext h1, adjT_lo, adjHi_val]
  · rw [if_neg h1]
    by_cases h2 : x.1 = k.1 + 1
    · rw [if_pos h2, show x = adjHi k from Fin.ext h2, adjT_hi, adjLo_val]
    · rw [if_neg h2, adjT_of_ne k h1 h2]

/-- **A simple swap inverts only its own pair.** -/
theorem adjT_inverts (k : Fin (n - 1)) {p q : Fin n} (hpq : p < q)
    (hinv : adjT k q < adjT k p) : p = adjLo k ∧ q = adjHi k := by
  rw [Fin.lt_def] at hpq hinv
  rw [adjT_val, adjT_val] at hinv
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [adjLo_val, adjHi_val] <;> grind

/-- **A swap ascends across every pair but its own.** -/
theorem adjT_ascent_of_ne {k l : Fin (n - 1)} (h : (l : ℕ) ≠ (k : ℕ)) :
    adjT k (adjLo l) < adjT k (adjHi l) := by
  rw [Fin.lt_def, adjT_val, adjT_val, adjLo_val, adjHi_val]
  split_ifs <;> omega

/-! ## The group the transpositions generate -/

theorem adjT_mul_self (k : Fin (n - 1)) : adjT k * adjT k = 1 := swap_mul_self _ _

@[simp] theorem adjT_inv (k : Fin (n - 1)) : (adjT k)⁻¹ = adjT k :=
  inv_eq_of_mul_eq_one_left (adjT_mul_self k)

/-- **A transposition is not the identity** — its two endpoints differ. -/
theorem adjT_ne_one (k : Fin (n - 1)) : adjT k ≠ 1 := fun h =>
  adjLo_ne_adjHi k (by rw [← adjT_hi k, h]; rfl)

/-- **Distinct indices swap distinct pairs** — read the value at the low endpoint. -/
theorem adjT_injective : Function.Injective (adjT (n := n)) := by
  intro k l h
  have h1 : (adjT k (adjLo k)).1 = (adjT l (adjLo k)).1 := by rw [h]
  rw [adjT_val, adjT_val, adjLo_val] at h1
  refine Fin.ext ?_
  split_ifs at h1 <;> omega

theorem mul_adjT_adjT (σ : Perm (Fin n)) (k : Fin (n - 1)) : σ * adjT k * adjT k = σ := by
  rw [mul_assoc, adjT_mul_self, mul_one]

/-- Appending a simple swap swaps the two ranks it names. -/
theorem symm_mul_adjT (σ : Perm (Fin n)) (k : Fin (n - 1)) (p : Fin n) :
    (σ * adjT k).symm p = adjT k (σ.symm p) := by
  rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, adjT_adjT]
  exact (σ.apply_symm_apply p).symm

/-- Commutation of far-apart adjacent transpositions: their supports are disjoint. -/
theorem adjT_comm (i j : Fin (n - 1)) (h : i.1 + 1 < j.1) : adjT i * adjT j = adjT j * adjT i :=
  (Perm.disjoint_swap_swap (by simp [Fin.ext_iff]; omega)).commute

/-- The braid relation among consecutive adjacent transpositions: conjugating either swap by the
other gives the reversal `swap (adjLo i) (adjHi j)`. -/
theorem adjT_braid (i j : Fin (n - 1)) (h : j.1 = i.1 + 1) :
    adjT i * adjT j * adjT i = adjT j * adjT i * adjT j := by
  have conj : ∀ k l : Fin (n - 1),
      adjT k * adjT l * adjT k = swap (adjT k (adjLo l)) (adjT k (adjHi l)) := fun k l => by
    rw [swap_apply_apply, adjT_inv]; rfl
  rw [conj, conj, adjLo_eq_adjHi h, adjT_hi, ← adjLo_eq_adjHi h, adjT_lo,
    adjT_of_ne i (x := adjHi j) (by simp; omega) (by simp; omega),
    adjT_of_ne j (x := adjLo i) (by simp; omega) (by simp; omega)]

/-- Commutation between *unordered* far-apart indices. -/
theorem adjT_comm_of_apart {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) : adjT i * adjT j = adjT j * adjT i :=
  h.elim (adjT_comm i j) fun h => (adjT_comm j i h).symm

/-- …and the braid relation between unordered consecutive indices. -/
theorem adjT_braid_of_adj {i j : Fin (n - 1)}
    (h : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    adjT i * adjT j * adjT i = adjT j * adjT i * adjT j :=
  h.elim (adjT_braid i j) fun h => (adjT_braid j i h).symm

/-! ## The alternating word

`altProd` reads the word a pair spells in a monoid, letters in decreasing order; `altWord` is the
same word as a permutation, in the order peeling it off the right performs. -/

/-- The `t`-th letter of the alternating word starting at `i`. -/
def altIdx (i k : Fin (n - 1)) (t : ℕ) : Fin (n - 1) := if t % 2 = 0 then i else k

/-- The alternating word of length `t`, evaluated in a family — letters in **decreasing** order,
which is the order a climb composes them in. -/
def altProd {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (i k : Fin (n - 1)) : ℕ → M
  | 0 => 1
  | t + 1 => g (altIdx i k t) * altProd g i k t

/-- The same word as a permutation, in the order **peeling** it off the right performs. -/
def altWord (i k : Fin (n - 1)) (t : ℕ) : Perm (Fin n) := (altProd adjT i k t)⁻¹

@[simp] theorem altIdx_zero (i k : Fin (n - 1)) : altIdx i k 0 = i := rfl

/-- **The word's letters alternate**: dropping the first swaps the pair. -/
theorem altIdx_succ (i k : Fin (n - 1)) (t : ℕ) : altIdx i k (t + 1) = altIdx k i t := by
  unfold altIdx
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega)]

/-- **A letter joins on the right too**, at the cost of swapping the pair. -/
theorem altProd_succ_right {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (i k : Fin (n - 1)) :
    ∀ t : ℕ, altProd g k i t * g i = altProd g i k (t + 1)
  | 0 => (one_mul _).trans (mul_one _).symm
  | t + 1 => by
      change g (altIdx k i t) * altProd g k i t * g i
        = g (altIdx i k (t + 1)) * altProd g i k (t + 1)
      rw [mul_assoc, altProd_succ_right g i k t, altIdx_succ]

theorem altProd_two {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (i k : Fin (n - 1)) :
    altProd g i k 2 = g k * g i := congrArg (g k * ·) (mul_one _)

theorem altProd_three {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (i k : Fin (n - 1)) :
    altProd g i k 3 = g i * g k * g i :=
  (congrArg (g i * ·) (altProd_two g i k)).trans (mul_assoc _ _ _).symm

@[simp] theorem altWord_zero (i k : Fin (n - 1)) : altWord i k 0 = (1 : Perm (Fin n)) := inv_one

/-- **A letter joins on the right**, which is what a peel does. -/
theorem altWord_succ (i k : Fin (n - 1)) (t : ℕ) :
    altWord i k (t + 1) = altWord i k t * adjT (altIdx i k t) := by
  rw [altWord, altWord, altProd, mul_inv_rev, adjT_inv]

/-- **…and on the left**, swapping the pair. -/
theorem altWord_succ_left (i k : Fin (n - 1)) (t : ℕ) :
    altWord i k (t + 1) = adjT i * altWord k i t := by
  rw [altWord, altWord, ← altProd_succ_right, mul_inv_rev, adjT_inv]

@[simp] theorem altWord_one (i k : Fin (n - 1)) : altWord i k 1 = adjT i := by
  rw [altWord_succ, altWord_zero, altIdx_zero, one_mul]

/-- **Read from its far end, an alternating word is the one its last letter starts.** -/
theorem altWord_inv : ∀ (t : ℕ) (i k : Fin (n - 1)),
    (altWord k i t)⁻¹ = altWord (altIdx i k t) (altIdx k i t) t
  | 0, _, _ => by rw [altWord_zero, altWord_zero, inv_one]
  | t + 1, i, k => by
      rw [altWord_succ, mul_inv_rev, adjT_inv, altWord_inv t i k, altWord_succ_left,
        altIdx_succ, altIdx_succ]

/-- **The two alternating words differ by a power of the pair's product.** -/
theorem altWord_mul_inv : ∀ (t : ℕ) (i k : Fin (n - 1)),
    altWord i k t * (altWord k i t)⁻¹ = (adjT i * adjT k) ^ t
  | 0, _, _ => by simp only [altWord_zero, inv_one, mul_one, pow_zero]
  | t + 1, i, k => by
      rw [altWord_succ_left, altWord_succ_left k i, mul_inv_rev, adjT_inv, mul_assoc,
        ← mul_assoc (altWord k i t), altWord_mul_inv t k i, ← mul_assoc, ← mul_pow_mul, pow_succ,
        mul_assoc]

/-- **…so they agree exactly at a period of the product.** -/
theorem altWord_eq_altWord_iff {i k : Fin (n - 1)} {t : ℕ} :
    altWord i k t = altWord k i t ↔ (adjT i * adjT k) ^ t = 1 := by
  rw [← altWord_mul_inv, mul_inv_eq_one]

/-! ## The Coxeter matrix of type `A`

The order of `adjT i * adjT j` tells the two species of pair apart; this section is where it is
computed, and nothing downstream repeats the split. -/

/-- The **Coxeter exponent** of a pair of cuts: the length of the longest word they spell. -/
noncomputable def cox (i k : Fin (n - 1)) : ℕ := orderOf (adjT i * adjT k)

theorem adjT_mul_adjT_ne_one {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) :
    adjT i * adjT j ≠ 1 := fun hc =>
  hij (congrArg Fin.val (adjT_injective (by
    have h := mul_eq_one_iff_eq_inv.mp hc
    rwa [adjT_inv] at h)))

/-- **Generators that are apart have product of order two** — they commute. -/
theorem orderOf_adjT_mul_adjT_of_apart {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    (hfar : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) : orderOf (adjT i * adjT j) = 2 :=
  orderOf_eq_prime (altWord_eq_altWord_iff.mp (by
    simp only [altWord, altProd_two, mul_inv_rev, adjT_inv]
    exact adjT_comm_of_apart hfar)) (adjT_mul_adjT_ne_one hij)

/-- **Consecutive generators have product of order three** — they braid. -/
theorem orderOf_adjT_mul_adjT_of_adj {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    (hadj : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) : orderOf (adjT i * adjT j) = 3 :=
  orderOf_eq_prime (altWord_eq_altWord_iff.mp (by
    simp only [altWord, altProd_three, mul_inv_rev, adjT_inv, ← mul_assoc]
    exact adjT_braid_of_adj hadj)) (adjT_mul_adjT_ne_one hij)

/-- **Two distinct indices are apart or consecutive**, and their order says which. -/
theorem orderOf_adjT_mul_adjT_cases {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) :
    ((i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) ∧ orderOf (adjT i * adjT j) = 2
      ∨ ((j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) ∧ orderOf (adjT i * adjT j) = 3 := by
  by_cases h : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1
  · exact Or.inr ⟨h, orderOf_adjT_mul_adjT_of_adj hij h⟩
  · exact Or.inl ⟨by omega, orderOf_adjT_mul_adjT_of_apart hij (by omega)⟩

/-- **The exponent does not see the order of the pair** — the two products are inverse. -/
theorem cox_comm (i k : Fin (n - 1)) : cox i k = cox k i := by
  rw [cox, cox, ← orderOf_inv, mul_inv_rev, adjT_inv, adjT_inv]

/-- **A pair of distinct cuts spells at least two letters.** -/
theorem two_le_cox {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ)) : 2 ≤ cox i k := by
  have h0 : 0 < cox i k := orderOf_pos _
  have h1 : cox i k ≠ 1 := fun h => adjT_mul_adjT_ne_one hik (orderOf_eq_one_iff.mp h)
  omega

/-- **The two walks out of a double descent end at the same permutation.** -/
theorem altWord_cox (i k : Fin (n - 1)) : altWord i k (cox i k) = altWord k i (cox i k) :=
  altWord_eq_altWord_iff.mpr (pow_orderOf_eq_one _)

/-! ## Length-additivity for adjacent transpositions -/

/-- An adjacent transposition crosses exactly one pair. -/
theorem permLen_adjT (k : Fin (n - 1)) : permLen (adjT k) = 1 := by
  rw [permLen, Finset.card_eq_one]
  refine ⟨(adjLo k, adjHi k), ?_⟩
  ext ⟨p, q⟩
  simp only [inversions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hpq, hinv⟩
    exact adjT_inverts k hpq hinv
  · rintro ⟨rfl, rfl⟩
    exact ⟨adjLo_lt_adjHi k, by rw [adjT_hi, adjT_lo]; exact adjLo_lt_adjHi k⟩

/-- **Only the swapped pair can double-cross a simple swap** (`adjT_inverts`). -/
theorem noDoubleCross_adjT {A : Perm (Fin n)} {k : Fin (n - 1)} (h : A (adjLo k) < A (adjHi k)) :
    ∀ i j : Fin n, i < j → adjT k j < adjT k i → A (adjT k j) < A (adjT k i) := by
  intro p q hpq hinv
  obtain ⟨rfl, rfl⟩ := adjT_inverts k hpq hinv
  rw [adjT_hi, adjT_lo]
  exact h

/-- Appending a simple swap across an ascent is length-additive in the germ. -/
theorem ofPerm_mul_adjT {A : Perm (Fin n)} {k : Fin (n - 1)} (h : A (adjLo k) < A (adjHi k)) :
    ofPerm A * ofPerm (adjT k) = ofPerm (A * adjT k) :=
  ofPerm_mul_of_noDoubleCross (noDoubleCross_adjT h)

/-- Appending a simple swap across an ascent adds the one new crossing. -/
theorem permLen_mul_adjT {A : Perm (Fin n)} {k : Fin (n - 1)} (h : A (adjLo k) < A (adjHi k)) :
    permLen (A * adjT k) = permLen A + 1 := by
  rw [permLen_mul_of_noDoubleCross (σ := adjT k) (ρ := A) (noDoubleCross_adjT h), permLen_adjT,
    Nat.add_comm]

/-- …read as a length-additive product, which is the shape a germ relation asks for. -/
theorem permLen_mul_adjT_add {A : Perm (Fin n)} {k : Fin (n - 1)}
    (h : A (adjLo k) < A (adjHi k)) :
    permLen (A * adjT k) = permLen A + permLen (adjT k) := by
  rw [permLen_mul_adjT h, permLen_adjT]

/-! ## The Artin relation -/

/-- The Artin relation as a pair of **oriented** words: which word is the source is
parity-dependent (`[i,j]` against `[i,j,i]`), so unlike `IsArtinFamily` it is not one clause. -/
inductive ArtinRel (n : ℕ) : FreeMonoid (Fin (n - 1)) → FreeMonoid (Fin (n - 1)) → Prop
  | comm (i j : Fin (n - 1)) (h : (i : ℕ) + 1 < (j : ℕ)) :
      ArtinRel n (FreeMonoid.of i * FreeMonoid.of j) (FreeMonoid.of j * FreeMonoid.of i)
  | braid (i j : Fin (n - 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
      ArtinRel n (FreeMonoid.of i * FreeMonoid.of j * FreeMonoid.of i)
        (FreeMonoid.of j * FreeMonoid.of i * FreeMonoid.of j)

/-- A family satisfying **the Artin relation**: the two alternating words the pair `i, k` spells
agree, at the length the Coxeter matrix gives them. -/
structure IsArtinFamily {M : Type*} [Monoid M] (g : Fin (n - 1) → M) : Prop where
  /-- The two alternating words of length `cox` agree. -/
  altProd_cox {i k : Fin (n - 1)} (h : (i : ℕ) ≠ (k : ℕ)) :
    altProd g i k (cox i k) = altProd g k i (cox i k)

/-- **The clause is the presentation's relation**: at `cox = 2` it reads as `ArtinRel.comm`, at
`cox = 3` as `ArtinRel.braid`. -/
theorem isArtinFamily_iff {M : Type*} [Monoid M] {g : Fin (n - 1) → M} :
    IsArtinFamily g ↔ ∀ {x y}, ArtinRel n x y → FreeMonoid.lift g x = FreeMonoid.lift g y := by
  refine ⟨fun hg x y h => ?_, fun h => ⟨fun {i k} hik => ?_⟩⟩
  · cases h with
    | comm i j h =>
        simpa only [map_mul, FreeMonoid.lift_eval_of, cox, altProd_two,
          orderOf_adjT_mul_adjT_of_apart (by omega) (Or.inr h)]
          using hg.altProd_cox (i := j) (k := i) (by omega)
    | braid i j h =>
        simpa only [map_mul, FreeMonoid.lift_eval_of, cox, altProd_three,
          orderOf_adjT_mul_adjT_of_adj (by omega) (Or.inl h)]
          using hg.altProd_cox (i := i) (k := j) (by omega)
  · have lift := fun {x y} (hr : ArtinRel n x y) => by
      simpa only [map_mul, FreeMonoid.lift_eval_of] using h hr
    rcases orderOf_adjT_mul_adjT_cases hik with ⟨hfar, hc⟩ | ⟨hadj, hc⟩
    · rw [cox, hc, altProd_two, altProd_two]
      exact hfar.elim (fun h => (lift (.comm i k h)).symm) fun h => lift (.comm k i h)
    · rw [cox, hc, altProd_three, altProd_three]
      exact hadj.elim (fun h => lift (.braid i k h)) fun h => (lift (.braid k i h)).symm

/-- **The adjacent transpositions are an Artin family** — the relation they satisfy in `Sₙ`. -/
theorem isArtinFamily_adjT : IsArtinFamily (adjT (n := n)) :=
  ⟨fun {i k} _ => inv_injective (altWord_cox i k)⟩

/-! ## The Artin braid group -/

/-- A relation word, read in the free group. -/
def artinWord (n : ℕ) : FreeMonoid (Fin (n - 1)) →* FreeGroup (Fin (n - 1)) :=
  FreeMonoid.lift FreeGroup.of

/-- A group-valued hom reads an Artin word as the `FreeMonoid` lift of its values on generators. -/
theorem artinWord_lift {M : Type*} [Monoid M] {φ : FreeGroup (Fin (n - 1)) →* M}
    {f : Fin (n - 1) → M} (hf : ∀ i, φ (FreeGroup.of i) = f i) (z : FreeMonoid (Fin (n - 1))) :
    φ (artinWord n z) = FreeMonoid.lift f z :=
  DFunLike.congr_fun (FreeMonoid.hom_eq (f := φ.comp (artinWord n)) (g := FreeMonoid.lift f) hf) z

/-- The Artin relations, as free-group relators. -/
def artinRels (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  {r | ∃ x y, ArtinRel n x y ∧ r = artinWord n x * (artinWord n y)⁻¹}

/-- **The Artin braid group** on `n` strands. -/
abbrev ArtinBraid (n : ℕ) : Type := PresentedGroup (artinRels n)

/-- The `i`-th Artin generator. -/
def artinGen (i : Fin (n - 1)) : ArtinBraid n := PresentedGroup.of i

/-- **The universal property of the Artin braid group.** -/
def ArtinBraid.lift {G : Type*} [Group G] (g : Fin (n - 1) → G) (hg : IsArtinFamily g) :
    ArtinBraid n →* G :=
  PresentedGroup.toGroup (f := g) fun r ⟨x, y, h, hr⟩ => by
    have key := artinWord_lift (φ := FreeGroup.lift g) fun _ => FreeGroup.lift_apply_of
    rw [hr, map_mul, map_inv, key x, key y, isArtinFamily_iff.mp hg h, mul_inv_cancel]

@[simp] theorem ArtinBraid.lift_gen {G : Type*} [Group G] {g : Fin (n - 1) → G}
    {hg : IsArtinFamily g} (i : Fin (n - 1)) : ArtinBraid.lift g hg (artinGen i) = g i :=
  PresentedGroup.toGroup.of _

/-- **The Artin generators are an Artin family** — the presentation imposes its own relation. -/
theorem isArtinFamily_artinGen : IsArtinFamily (artinGen (n := n)) :=
  isArtinFamily_iff.mpr fun {x y} h => by
    have key := artinWord_lift (φ := PresentedGroup.mk (artinRels n))
      (f := artinGen (n := n)) fun _ => rfl
    rw [← key x, ← key y]
    exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨x, y, h, rfl⟩

end CubeChains
