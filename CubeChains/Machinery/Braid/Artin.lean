import CubeChains.Machinery.Braid.Germ
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Machinery/Braid/Artin — the adjacent transpositions, and the Artin presentation

`GarsideBraid n` is `Braid n`, the germ presentation of `Machinery/Braid/Germ`.  `ArtinBraid n` is
the classical Artin presentation on the adjacent transpositions `adjT k`, whose relation family
`ArtinRel` presents the braid *monoid* as well.

`cox i k = orderOf (adjT i * adjT k)` is the Coxeter matrix's entry, and `IsArtinFamily` is **one**
clause in it: the two alternating words of that length agree.  `comm` and `braid` are its two
readings, not two axioms.  `ArtinRel` still carries them separately because a *presentation* must
orient each relation, and which word is the source is parity-dependent — see its docstring.

The relation is a length-additive fact, so it holds in **any** germ (`isArtinFamily_of_atom`),
which gives the easy `garsideOfArtin : ArtinBraid n →* GarsideBraid n`.  Upgrading it to an
isomorphism is **Matsumoto's theorem for `Sₙ`**, in `Machinery/Braid/Matsumoto`.

Not mathlib's `GroupTheory/Coxeter`: all of it is stated for a `CoxeterSystem`, and mathlib
constructs none — `Coxeter/Basic` lists both Matsumoto and "ways to actually construct some Coxeter
groups" as TODOs, so the type-A system (the presentation of `Sₙ`, `CoxeterMatrix.A` and all) would
have to be proved here first.  It would still miss what the germ runs on: `permLen` is the
*cardinality of the inversion set*, and `permLen_mul_of_noDoubleCross` / `permLen_permSum` read
that set, whereas `CoxeterSystem.length` is a minimal word length with no inversion set attached.
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

/-- One index does not: the two endpoints of a swap are one apart. -/
theorem adjLo_lt_adjHi (k : Fin (n - 1)) : adjLo k < adjHi k :=
  Fin.lt_def.mpr (by rw [adjLo_val, adjHi_val]; omega)

theorem adjLo_ne_adjHi (k : Fin (n - 1)) : adjLo k ≠ adjHi k := (adjLo_lt_adjHi k).ne

/-- **A relation holding across every adjacent pair inside a stretch holds across the stretch.**
`P` marks the pairs the relation is given at — an index of `Fin (n-1)` being named by the coordinate
`k + 1` it separates — so a caller supplies only `P` and transitivity. -/
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

/-- `adjT_of_ne` at `adjLo l`, phrased on the index so `omega` can see the hypotheses. -/
theorem adjT_adjLo_of_ne {k l : Fin (n - 1)} (h1 : (l : ℕ) ≠ (k : ℕ))
    (h2 : (l : ℕ) ≠ (k : ℕ) + 1) : adjT k (adjLo l) = adjLo l :=
  adjT_of_ne k h1 h2

/-- …and at `adjHi l`. -/
theorem adjT_adjHi_of_ne {k l : Fin (n - 1)} (h1 : (l : ℕ) + 1 ≠ (k : ℕ))
    (h2 : (l : ℕ) + 1 ≠ (k : ℕ) + 1) : adjT k (adjHi l) = adjHi l :=
  adjT_of_ne k h1 h2

/-- The value of `adjT k x`: it swaps the values `k` and `k+1`, and fixes everything else. -/
theorem adjT_val (k : Fin (n - 1)) (x : Fin n) :
    (adjT k x).1 = if x.1 = k.1 then k.1 + 1 else if x.1 = k.1 + 1 then k.1 else x.1 := by
  by_cases h1 : x.1 = k.1
  · rw [if_pos h1]
    have hx : x = adjLo k := Fin.ext h1
    rw [hx, adjT_lo, adjHi_val]
  · rw [if_neg h1]
    by_cases h2 : x.1 = k.1 + 1
    · rw [if_pos h2]
      have hx : x = adjHi k := Fin.ext h2
      rw [hx, adjT_hi, adjLo_val]
    · rw [if_neg h2, adjT_of_ne k h1 h2]

/-- **A simple swap inverts only its own pair.**  If a refinement of the order by an adjacent
transposition reverses the pair `p < q`, then `p, q` are exactly the two swapped points. -/
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
theorem adjT_ne_one (k : Fin (n - 1)) : adjT k ≠ 1 := fun h => by
  have h1 : adjHi k = adjLo k := by rw [← adjT_lo k, h]; rfl
  have := congrArg Fin.val h1
  simp only [adjHi_val, adjLo_val] at this
  omega

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

/-- Far-apart adjacent transpositions have disjoint support. -/
theorem adjT_disjoint (i j : Fin (n - 1)) (h : i.1 + 1 < j.1) :
    Equiv.Perm.Disjoint (adjT i) (adjT j) := fun x => by
  by_cases hx : x.1 = i.1 ∨ x.1 = i.1 + 1
  · exact Or.inr (adjT_of_ne j (by omega) (by omega))
  · rw [not_or] at hx
    exact Or.inl (adjT_of_ne i hx.1 hx.2)

/-- Commutation of far-apart adjacent transpositions. -/
theorem adjT_comm (i j : Fin (n - 1)) (h : i.1 + 1 < j.1) : adjT i * adjT j = adjT j * adjT i :=
  (adjT_disjoint i j h).commute

/-- The braid relation among consecutive adjacent transpositions.  Both sides are the reversal
`swap (adjLo i) (adjHi j)`, via the swap-conjugation identity. -/
theorem adjT_braid (i j : Fin (n - 1)) (h : j.1 = i.1 + 1) :
    adjT i * adjT j * adjT i = adjT j * adjT i * adjT j := by
  have hmid : adjLo j = adjHi i := adjLo_eq_adjHi h
  have hne1 : adjHi j ≠ adjHi i := Fin.ne_of_val_ne (by rw [adjHi_val, adjHi_val]; omega)
  have hne2 : adjHi j ≠ adjLo i := Fin.ne_of_val_ne (by rw [adjHi_val, adjLo_val]; omega)
  have hne3 : adjLo i ≠ adjHi i := Fin.ne_of_val_ne (by rw [adjLo_val, adjHi_val]; omega)
  have hL : adjT i * adjT j * adjT i = swap (adjLo i) (adjHi j) := by
    unfold adjT
    rw [hmid, swap_comm (adjLo i) (adjHi i), swap_comm (adjHi i) (adjHi j),
      swap_mul_swap_mul_swap hne1 hne2]
  have hR : adjT j * adjT i * adjT j = swap (adjLo i) (adjHi j) := by
    unfold adjT
    rw [hmid, swap_mul_swap_mul_swap hne3 hne2.symm, swap_comm (adjHi j) (adjLo i)]
  rw [hL, hR]

/-- Commutation between *unordered* far-apart indices — the form the two-species dichotomy hands
down, where which of the pair is the lower is not yet known. -/
theorem adjT_comm_of_apart {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) : adjT i * adjT j = adjT j * adjT i :=
  h.elim (adjT_comm i j) fun h => (adjT_comm j i h).symm

/-- …and the braid relation between unordered consecutive indices. -/
theorem adjT_braid_of_adj {i j : Fin (n - 1)}
    (h : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    adjT i * adjT j * adjT i = adjT j * adjT i * adjT j :=
  h.elim (adjT_braid i j) fun h => (adjT_braid j i h).symm

/-- **Consecutive swaps overlap**: `j`'s swap carries the ends of `i`'s pair *two* apart, because
the two pairs share an endpoint and the window they span is three wide.  This is the whole of the
two-letter arithmetic; the two facts below are `adjT_inverts` against it. -/
theorem val_adjT_adjHi_of_adj {i j : Fin (n - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    ((adjT j (adjHi i) : Fin n) : ℕ) = ((adjT j (adjLo i) : Fin n) : ℕ) + 2 := by
  rcases hij with h | h
  · rw [← adjLo_eq_adjHi h, adjT_lo, adjT_adjLo_of_ne (k := j) (by omega) (by omega)]
    simp only [adjHi_val, adjLo_val]; omega
  · rw [adjLo_eq_adjHi h, adjT_hi, adjT_adjHi_of_ne (k := j) (by omega) (by omega)]
    simp only [adjHi_val, adjLo_val]; omega

/-- **A consecutive two-letter word ascends across the pair its first letter crosses** — it is the
three-cycle on the window the two pairs span, either way round. -/
theorem adjT_mul_adjT_ascent {i j : Fin (n - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    (adjT i * adjT j) (adjLo i) < (adjT i * adjT j) (adjHi i) := by
  rw [Perm.mul_apply, Perm.mul_apply]
  rcases lt_or_gt_of_ne (show adjT i (adjT j (adjLo i)) ≠ adjT i (adjT j (adjHi i)) from
      fun hc => (adjLo_lt_adjHi i).ne ((adjT j).injective ((adjT i).injective hc))) with h | h
  · exact h
  · obtain ⟨h1, h2⟩ := adjT_inverts i (adjT_ascent_of_ne (by omega)) h
    have hv := val_adjT_adjHi_of_adj hij
    rw [h1, h2, adjLo_val, adjHi_val] at hv
    omega

/-- **…and descends only across the pair its second letter crosses**, so a length-two word onto it
has a forced middle letter. -/
theorem eq_of_descent_adjT_mul_adjT {i j m : Fin (n - 1)}
    (hij : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1)
    (h : (adjT i * adjT j) (adjHi m) < (adjT i * adjT j) (adjLo m)) : m = j := by
  rw [Perm.mul_apply, Perm.mul_apply] at h
  rcases lt_or_gt_of_ne (show adjT j (adjLo m) ≠ adjT j (adjHi m) from
      fun hc => (adjLo_lt_adjHi m).ne ((adjT j).injective hc)) with hlt | hgt
  · -- `adjT j` would carry `m`'s pair onto `i`'s, which is two wide where `m`'s is one
    obtain ⟨h1, h2⟩ := adjT_inverts i hlt h
    have hv := val_adjT_adjHi_of_adj hij
    rw [← h1, ← h2, adjT_adjT, adjT_adjT, adjLo_val, adjHi_val] at hv
    omega
  · obtain ⟨h1, -⟩ := adjT_inverts j (adjLo_lt_adjHi m) hgt
    exact Fin.ext (by simpa only [adjLo_val] using congrArg Fin.val h1)

/-- **A transposition is read off the permutation it is**, at whichever spelling of the strand
count. -/
theorem idx_eq_of_permCongr {M N : ℕ} (h : N = M) {m : Fin (M - 1)} {j : Fin (N - 1)}
    (hmj : adjT m = (finCongr h).permCongr (adjT j)) : (m : ℕ) = (j : ℕ) := by
  subst h
  exact congrArg Fin.val (adjT_injective hmj)

/-- **…and a consecutive pair of them off their product**, the descent naming the second letter. -/
theorem idx_pair_eq_of_permCongr {M N : ℕ} (h : N = M) {a b : Fin (M - 1)}
    {i j : Fin (N - 1)} (hij : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1)
    (hab : adjT a * adjT b = (finCongr h).permCongr (adjT i * adjT j))
    (hdesc : (adjT a * adjT b) (adjHi b) < (adjT a * adjT b) (adjLo b)) :
    (a : ℕ) = (i : ℕ) ∧ (b : ℕ) = (j : ℕ) := by
  subst h
  have h0 : adjT a * adjT b = adjT i * adjT j := hab
  obtain rfl : b = j := eq_of_descent_adjT_mul_adjT hij (h0 ▸ hdesc)
  refine ⟨congrArg Fin.val (adjT_injective ?_), rfl⟩
  have h1 := congrArg (fun σ : Perm (Fin N) => σ * adjT b) h0
  simpa only [mul_assoc, adjT_mul_self, mul_one] using h1

/-! ## The Coxeter matrix of type `A`

The order of `adjT i * adjT j` tells the two species of pair apart, and is the length of the longest
word the pair spells.  Read it here; nothing downstream repeats the split.
-/

theorem adjT_mul_adjT_ne_one {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) :
    adjT i * adjT j ≠ 1 := fun hc =>
  hij (congrArg Fin.val (adjT_injective (by
    have h := mul_eq_one_iff_eq_inv.mp hc
    rwa [adjT_inv] at h)))

/-- **Generators that are apart have product of order two** — they commute, so the square splits. -/
theorem orderOf_adjT_mul_adjT_of_apart {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    (hfar : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) : orderOf (adjT i * adjT j) = 2 :=
  have hc : Commute (adjT i) (adjT j) := adjT_comm_of_apart hfar
  orderOf_eq_prime
    (by rw [hc.mul_pow, sq, sq, adjT_mul_self, adjT_mul_self, one_mul])
    (adjT_mul_adjT_ne_one hij)

/-- **Consecutive generators have product of order three** — they braid. -/
theorem orderOf_adjT_mul_adjT_of_adj {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    (hadj : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) : orderOf (adjT i * adjT j) = 3 := by
  have hb := adjT_braid_of_adj hadj
  refine orderOf_eq_prime ?_ (adjT_mul_adjT_ne_one hij)
  rw [pow_succ, pow_succ, pow_one,
    show adjT i * adjT j * (adjT i * adjT j) * (adjT i * adjT j)
      = adjT i * adjT j * adjT i * (adjT j * adjT i * adjT j) from by simp only [mul_assoc], hb]
  simp only [mul_assoc]
  rw [show adjT j * (adjT j * (adjT i * adjT j)) = adjT i * adjT j from by
      rw [← mul_assoc, adjT_mul_self, one_mul],
    show adjT i * (adjT i * adjT j) = adjT j from by rw [← mul_assoc, adjT_mul_self, one_mul]]
  exact adjT_mul_self j

/-- **Two distinct indices are apart or consecutive**, and their order says which. -/
theorem orderOf_adjT_mul_adjT_cases {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) :
    ((i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) ∧ orderOf (adjT i * adjT j) = 2
      ∨ ((j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) ∧ orderOf (adjT i * adjT j) = 3 := by
  by_cases h : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1
  · exact Or.inr ⟨h, orderOf_adjT_mul_adjT_of_adj hij h⟩
  · exact Or.inl ⟨by omega, orderOf_adjT_mul_adjT_of_apart hij (by omega)⟩

/-! ## The alternating word

The Coxeter matrix's entry, and the word of that length it indexes.  `altProd` reads the word in a
monoid; `altWord` reads it as the permutation peeling it off the right of a descent performs, the
two readings being inverse because an adjacent transposition is an involution. -/

/-- The **Coxeter exponent** of a pair of cuts: the length of the longest word they spell. -/
noncomputable def cox (i k : Fin (n - 1)) : ℕ := orderOf (adjT i * adjT k)

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
@[simp] theorem altIdx_one (i k : Fin (n - 1)) : altIdx i k 1 = k := rfl
@[simp] theorem altIdx_two (i k : Fin (n - 1)) : altIdx i k 2 = i := rfl

/-- **The word's letters alternate**: dropping the first swaps the pair. -/
theorem altIdx_succ (i k : Fin (n - 1)) (t : ℕ) : altIdx i k (t + 1) = altIdx k i t := by
  unfold altIdx
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg (by omega)]

/-- **A letter joins on the right too**, at the cost of swapping the pair — which is what lets a
climb and the cover above it be read as one word. -/
theorem altProd_succ_right {M : Type*} [Monoid M] (g : Fin (n - 1) → M) (i k : Fin (n - 1)) :
    ∀ t : ℕ, altProd g k i t * g i = altProd g i k (t + 1)
  | 0 => by
      change 1 * g i = g i * 1
      rw [one_mul, mul_one]
  | t + 1 => by
      change g (altIdx k i t) * altProd g k i t * g i
        = g (altIdx i k (t + 1)) * altProd g i k (t + 1)
      rw [mul_assoc, altProd_succ_right g i k t, altIdx_succ]

/-- **A family blind to its index spells a power.** -/
theorem altProd_const {M : Type*} [Monoid M] (x : M) (i k : Fin (n - 1)) :
    ∀ t : ℕ, altProd (fun _ : Fin (n - 1) => x) i k t = x ^ t
  | 0 => (pow_zero x).symm
  | t + 1 => by rw [altProd, altProd_const x i k t, ← pow_succ']

@[simp] theorem altWord_zero (i k : Fin (n - 1)) : altWord i k 0 = (1 : Perm (Fin n)) := inv_one

/-- **A letter joins on the right**, which is what a peel does. -/
theorem altWord_succ (i k : Fin (n - 1)) (t : ℕ) :
    altWord i k (t + 1) = altWord i k t * adjT (altIdx i k t) := by
  rw [altWord, altWord, altProd, mul_inv_rev, adjT_inv]

@[simp] theorem altWord_one (i k : Fin (n - 1)) : altWord i k 1 = adjT i := by
  rw [altWord_succ, altWord_zero, altIdx_zero, one_mul]

theorem altWord_two (i k : Fin (n - 1)) : altWord i k 2 = adjT i * adjT k := by
  rw [altWord_succ, altWord_one, altIdx_one]

/-- **The exponent does not see the order of the pair** — conjugating by `adjT i` swaps the two
products, and conjugation preserves order. -/
theorem cox_comm (i k : Fin (n - 1)) : cox i k = cox k i := by
  have hconj : (MulAut.conj (adjT i)).toMonoidHom (adjT k * adjT i) = adjT i * adjT k := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, adjT_inv]
    rw [mul_assoc, mul_assoc, adjT_mul_self, mul_one]
  rw [cox, cox, ← hconj,
    orderOf_injective (MulAut.conj (adjT i)).toMonoidHom (MulAut.conj (adjT i)).injective]

/-- **A pair of distinct cuts spells at least two letters**: their product is not the identity, and
in a finite group it has finite order.  Which of `2` and `3` it is, is not decided here — that is
`BPSet.crossCap_of_degree_eq_two`, read off the shape the two cuts span. -/
theorem two_le_cox {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ)) : 2 ≤ cox i k := by
  have h0 : 0 < cox i k := orderOf_pos _
  have h1 : cox i k ≠ 1 := fun h => adjT_mul_adjT_ne_one hik (orderOf_eq_one_iff.mp h)
  omega

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

/-- **Only the swapped pair can double-cross a simple swap** (`adjT_inverts`), so an ascent of `A`
there is the whole no-double-cross criterion for `A * adjT k`. -/
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

/-! ## The two Artin relations

The relations are a property of a *family* `g : Fin (n-1) → M`, and every germ has one. -/

/-- A family satisfying **the Artin relation**: the two alternating words the pair `i, k` spells
agree, at the length the Coxeter matrix gives them.  One clause, not two: `cox = 2` reads as
commutation and `cox = 3` as the braid relation, and `comm`/`braid` below are that reading. -/
structure IsArtinFamily {M : Type*} [Monoid M] (g : Fin (n - 1) → M) : Prop where
  /-- The two alternating words of length `cox` agree. -/
  altProd_cox {i k : Fin (n - 1)} (h : (i : ℕ) ≠ (k : ℕ)) :
    altProd g i k (cox i k) = altProd g k i (cox i k)

namespace IsArtinFamily

variable {M : Type*} [Monoid M] {g : Fin (n - 1) → M} (hg : IsArtinFamily g)
include hg

/-- **Far-apart generators commute** — the relation at `cox = 2`. -/
theorem comm (i j : Fin (n - 1)) (h : (i : ℕ) + 1 < (j : ℕ)) : g i * g j = g j * g i := by
  have hc : cox j i = 2 := orderOf_adjT_mul_adjT_of_apart (by omega) (Or.inr (by omega))
  have := hg.altProd_cox (i := j) (k := i) (by omega)
  rw [hc] at this
  change g i * (g j * 1) = g j * (g i * 1) at this
  rwa [mul_one, mul_one] at this

/-- **Consecutive generators braid** — the relation at `cox = 3`. -/
theorem braid (i j : Fin (n - 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
    g i * g j * g i = g j * g i * g j := by
  have hc : cox i j = 3 := orderOf_adjT_mul_adjT_of_adj (by omega) (Or.inl h)
  have := hg.altProd_cox (i := i) (k := j) (by omega)
  rw [hc] at this
  change g i * (g j * (g i * 1)) = g j * (g i * (g j * 1)) at this
  rwa [mul_one, mul_one, ← mul_assoc, ← mul_assoc] at this

end IsArtinFamily

/-- **…and back**: the two readings imply the relation.  `orderOf_adjT_mul_adjT_cases` is the
tree's dichotomy of the two species in permutation coordinates, and this is its only consumer. -/
theorem isArtinFamily_of_comm_braid {M : Type*} [Monoid M] {g : Fin (n - 1) → M}
    (hcomm : ∀ i j : Fin (n - 1), (i : ℕ) + 1 < (j : ℕ) → g i * g j = g j * g i)
    (hbraid : ∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
      g i * g j * g i = g j * g i * g j) : IsArtinFamily g where
  altProd_cox {i} {k} hik := by
    rcases orderOf_adjT_mul_adjT_cases hik with ⟨hfar, hc⟩ | ⟨hadj, hc⟩
    · rw [cox, hc]
      change g k * (g i * 1) = g i * (g k * 1)
      rw [mul_one, mul_one]
      exact hfar.elim (fun h => (hcomm i k h).symm) (fun h => hcomm k i h)
    · rw [cox, hc]
      change g i * (g k * (g i * 1)) = g k * (g i * (g k * 1))
      rw [mul_one, mul_one, ← mul_assoc, ← mul_assoc]
      exact hadj.elim (fun h => hbraid i k h) (fun h => (hbraid k i h).symm)

/-- **Every germ carries an Artin family.**  Multiplicativity across an ascent is the only input;
the two sides are then the same permutation (`adjT_comm`, `adjT_braid`). -/
theorem isArtinFamily_of_atom {M : Type*} [Monoid M] {g : Perm (Fin n) → M}
    (hatom : ∀ (A : Perm (Fin n)) (k : Fin (n - 1)), A (adjLo k) < A (adjHi k) →
      g A * g (adjT k) = g (A * adjT k)) :
    IsArtinFamily fun i : Fin (n - 1) => g (adjT i) :=
  isArtinFamily_of_comm_braid
    (fun i j h => by
      rw [hatom (adjT i) j (adjT_ascent_of_ne (by omega)),
        hatom (adjT j) i (adjT_ascent_of_ne (by omega)), adjT_comm i j h])
    (fun i j h => by
      rw [hatom (adjT i) j (adjT_ascent_of_ne (by omega)),
        hatom (adjT i * adjT j) i (adjT_mul_adjT_ascent (Or.inl h)),
        hatom (adjT j) i (adjT_ascent_of_ne (by omega)),
        hatom (adjT j * adjT i) j (adjT_mul_adjT_ascent (Or.inr h)), adjT_braid i j h])

/-- **The simples of the adjacent transpositions are an Artin family.** -/
theorem isArtinFamily_ofPerm_adjT :
    IsArtinFamily fun i : Fin (n - 1) => ofPerm (adjT i) :=
  isArtinFamily_of_atom fun _ _ ha => ofPerm_mul_adjT ha

/-- **The adjacent transpositions are an Artin family** — the relation they satisfy in `Sₙ`. -/
theorem isArtinFamily_adjT : IsArtinFamily (adjT (n := n)) :=
  isArtinFamily_of_comm_braid adjT_comm adjT_braid

/-- **…so the two walks out of a double descent end at the same permutation.** -/
theorem altWord_cox {i k : Fin (n - 1)} (hik : (i : ℕ) ≠ (k : ℕ)) :
    altWord i k (cox i k) = altWord k i (cox i k) :=
  congrArg Inv.inv (isArtinFamily_adjT.altProd_cox hik)

/-- **The relation is length-homogeneous** — a family blind to its index satisfies it, which is what
makes word length descend to the Artin monoid. -/
theorem isArtinFamily_const {M : Type*} [Monoid M] (x : M) :
    IsArtinFamily fun _ : Fin (n - 1) => x where
  altProd_cox {i} {k} _ := by
    rw [altProd_const, altProd_const, cox_comm i k]

/-! ## The Artin presentations

One relation family, two presented objects: `ArtinBraid` here, and the monoid `ArtinPosBraid` in
`Machinery/Braid/Matsumoto`. -/

/-- The Artin relation as a pair of **oriented** words: which of the two the presentation calls the
source is parity-dependent (`[i,j]` against `[i,j,i]`), so unlike `IsArtinFamily` this cannot be one
clause in `cox` — `Concurrency/Presentation/ArtinDegreeZero`'s `artinWords` reads the orientation,
and `paperArtinIso` is pinned to it. -/
inductive ArtinRel (n : ℕ) : FreeMonoid (Fin (n - 1)) → FreeMonoid (Fin (n - 1)) → Prop
  | comm (i j : Fin (n - 1)) (h : (i : ℕ) + 1 < (j : ℕ)) :
      ArtinRel n (FreeMonoid.of i * FreeMonoid.of j) (FreeMonoid.of j * FreeMonoid.of i)
  | braid (i j : Fin (n - 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
      ArtinRel n (FreeMonoid.of i * FreeMonoid.of j * FreeMonoid.of i)
        (FreeMonoid.of j * FreeMonoid.of i * FreeMonoid.of j)

/-- **An Artin family satisfies the relations word by word** — the shape both universal properties
ask for. -/
theorem IsArtinFamily.lift_eq {M : Type*} [Monoid M] {g : Fin (n - 1) → M} (hg : IsArtinFamily g)
    {x y : FreeMonoid (Fin (n - 1))} (h : ArtinRel n x y) :
    FreeMonoid.lift g x = FreeMonoid.lift g y := by
  cases h with
  | comm i j h => simpa only [map_mul, FreeMonoid.lift_eval_of] using hg.comm i j h
  | braid i j h => simpa only [map_mul, FreeMonoid.lift_eval_of] using hg.braid i j h

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

/-- An Artin family kills every relator, so it extends to the group. -/
theorem IsArtinFamily.lift_artinRels {G : Type*} [Group G] {g : Fin (n - 1) → G}
    (hg : IsArtinFamily g) {r : FreeGroup (Fin (n - 1))} (hr : r ∈ artinRels n) :
    FreeGroup.lift g r = 1 := by
  obtain ⟨x, y, h, rfl⟩ := hr
  have key := artinWord_lift (φ := FreeGroup.lift g) fun _ => FreeGroup.lift_apply_of
  rw [map_mul, map_inv, key x, key y, hg.lift_eq h, mul_inv_cancel]

/-- **The universal property of the Artin braid group.** -/
def ArtinBraid.lift {G : Type*} [Group G] (g : Fin (n - 1) → G) (hg : IsArtinFamily g) :
    ArtinBraid n →* G :=
  PresentedGroup.toGroup (f := g) fun _ hr => hg.lift_artinRels hr

@[simp] theorem ArtinBraid.lift_gen {G : Type*} [Group G] {g : Fin (n - 1) → G}
    {hg : IsArtinFamily g} (i : Fin (n - 1)) : ArtinBraid.lift g hg (artinGen i) = g i :=
  PresentedGroup.toGroup.of _

/-- The relations hold between the generators themselves. -/
theorem artinGen_rel {x y : FreeMonoid (Fin (n - 1))} (h : ArtinRel n x y) :
    FreeMonoid.lift artinGen x = FreeMonoid.lift artinGen y := by
  have key := artinWord_lift (φ := PresentedGroup.mk (artinRels n))
    (f := artinGen (n := n)) fun _ => rfl
  rw [← key x, ← key y]
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨x, y, h, rfl⟩

/-- **The Artin generators are an Artin family** — the presentation imposes its own relation. -/
theorem isArtinFamily_artinGen : IsArtinFamily (artinGen (n := n)) :=
  isArtinFamily_of_comm_braid
    (fun i j h => by
      simpa only [map_mul, FreeMonoid.lift_eval_of] using artinGen_rel (ArtinRel.comm i j h))
    (fun i j h => by
      simpa only [map_mul, FreeMonoid.lift_eval_of] using artinGen_rel (ArtinRel.braid i j h))

/-- **The easy direction**: the Artin group maps to the germ, sending each generator to its simple
braid.  The Artin relations hold in the germ because they are length-additive. -/
def garsideOfArtin (n : ℕ) : ArtinBraid n →* GarsideBraid n :=
  ArtinBraid.lift _ isArtinFamily_ofPerm_adjT

@[simp] theorem garsideOfArtin_gen (i : Fin (n - 1)) :
    garsideOfArtin n (artinGen i) = ofPerm (adjT i) :=
  ArtinBraid.lift_gen i

end CubeChains
