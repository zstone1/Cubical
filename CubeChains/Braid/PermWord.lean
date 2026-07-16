import CubeChains.Braid.Generated

/-!
# Braid/PermWord — the Artin word emitter

`permWord σ` bubble-sorts `σ` one adjacent descent at a time into a reduced word of adjacent
transpositions (`List (Fin (n-1))`): `wordToBraid (permWord σ) = ofPerm σ` (telescoping the germ
relation `ofPerm_mul` at each swap) and `(permWord σ).length = permLen σ` (the writhe).  No
normalization — the word is non-reduced-free but not Garside/Artin-normal (a downstream GAP job).
The emitter is independent of the braid-grading tower.
-/

namespace CubeChains

open Equiv

variable {n : ℕ}

/-! ## One adjacent descent -/

/-- Facing a descent `σ (adjHi i) < σ (adjLo i)` off the right drops the length by one. -/
theorem permLen_mul_adjT_of_descent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (hdesc : σ (adjHi i) < σ (adjLo i)) :
    permLen σ = permLen (σ * adjT i) + 1 := by
  have hinv2 : adjT i * adjT i = 1 := Equiv.swap_mul_self (adjLo i) (adjHi i)
  have hsimp : σ * adjT i * adjT i = σ := by rw [mul_assoc, hinv2, mul_one]
  have H : ∀ p q : Fin n, p < q → adjT i q < adjT i p →
      (σ * adjT i) (adjT i q) < (σ * adjT i) (adjT i p) := by
    intro p q hpq hinv
    obtain ⟨rfl, rfl⟩ := adjT_inverts i hpq hinv
    simp only [Perm.mul_apply, adjT_hi, adjT_lo]
    exact hdesc
  have key := permLen_mul_of_noDoubleCross (σ := adjT i) (ρ := σ * adjT i) H
  rw [hsimp] at key
  rw [key, permLen_adjT]; omega

/-- Peeling that descent off `ofPerm` is length-additive (the germ relation). -/
theorem ofPerm_mul_adjT_of_descent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (hdesc : σ (adjHi i) < σ (adjLo i)) :
    ofPerm (σ * adjT i) * ofPerm (adjT i) = ofPerm σ := by
  have hinv2 : adjT i * adjT i = 1 := Equiv.swap_mul_self (adjLo i) (adjHi i)
  have hsimp : σ * adjT i * adjT i = σ := by rw [mul_assoc, hinv2, mul_one]
  rw [ofPerm_mul (σ := σ * adjT i) (τ := adjT i)
    (by rw [hsimp, permLen_adjT]; exact permLen_mul_adjT_of_descent hdesc), hsimp]

/-! ## The computable first-descent search -/

/-- The first (smallest) adjacent descent of `σ`, or `none` if `σ` is sorted (the identity). -/
def firstDescent (σ : Perm (Fin n)) : Option (Fin (n - 1)) :=
  (List.finRange (n - 1)).find? (fun j => decide (σ (adjHi j) < σ (adjLo j)))

theorem firstDescent_some_descent {σ : Perm (Fin n)} {i : Fin (n - 1)}
    (h : firstDescent σ = some i) : σ (adjHi i) < σ (adjLo i) := by
  unfold firstDescent at h
  have hp := List.find?_some h
  simpa using hp

theorem firstDescent_eq_none_no_descent {σ : Perm (Fin n)} (h : firstDescent σ = none)
    (i : Fin (n - 1)) : ¬ σ (adjHi i) < σ (adjLo i) := by
  unfold firstDescent at h
  have := (List.find?_eq_none.mp h) i (List.mem_finRange i)
  simpa using this

theorem eq_one_of_firstDescent_none {σ : Perm (Fin n)} (h : firstDescent σ = none) : σ = 1 :=
  eq_one_of_no_adjacent_descent σ (firstDescent_eq_none_no_descent h)

/-! ## The word emitter -/

/-- `permWord σ`: a reduced word of adjacent transpositions for `σ`, emitted by repeatedly facing
off the first adjacent descent (bubble sort). -/
def permWord (σ : Perm (Fin n)) : List (Fin (n - 1)) :=
  match _hd : firstDescent σ with
  | none => []
  | some i => permWord (σ * adjT i) ++ [i]
  termination_by permLen σ
  decreasing_by
    exact (permLen_mul_adjT_of_descent (firstDescent_some_descent _hd)) ▸ Nat.lt_succ_self _

/-- The braid a word of adjacent transpositions realises: the product of its simple generators. -/
def wordToBraid (w : List (Fin (n - 1))) : Braid n := (w.map (fun i => ofPerm (adjT i))).prod

@[simp] theorem wordToBraid_nil : wordToBraid ([] : List (Fin (n - 1))) = 1 := rfl

@[simp] theorem wordToBraid_append (w v : List (Fin (n - 1))) :
    wordToBraid (w ++ v) = wordToBraid w * wordToBraid v := by
  simp [wordToBraid, List.map_append, List.prod_append]

@[simp] theorem wordToBraid_singleton (i : Fin (n - 1)) :
    wordToBraid [i] = ofPerm (adjT i) := by simp [wordToBraid]

/-! ## Correctness -/

/-- **The emitted word realises the germ generator.**  Strong induction on the length: each step
telescopes off one adjacent descent via `ofPerm_mul_adjT_of_descent`. -/
theorem wordToBraid_permWord (σ : Perm (Fin n)) : wordToBraid (permWord σ) = ofPerm σ := by
  have H : ∀ k, ∀ σ : Perm (Fin n), permLen σ = k →
      wordToBraid (permWord σ) = ofPerm σ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro σ hk
      rw [permWord]
      split
      · rename_i h
        rw [eq_one_of_firstDescent_none h, ofPerm_one, wordToBraid_nil]
      · rename_i i h
        have hdesc := firstDescent_some_descent h
        have hlen := permLen_mul_adjT_of_descent hdesc
        rw [wordToBraid_append, wordToBraid_singleton,
          ih (permLen (σ * adjT i)) (by omega) (σ * adjT i) rfl,
          ofPerm_mul_adjT_of_descent hdesc]
  exact H (permLen σ) σ rfl

/-- **The word length is the writhe.** -/
theorem permWord_length (σ : Perm (Fin n)) : (permWord σ).length = permLen σ := by
  have H : ∀ k, ∀ σ : Perm (Fin n), permLen σ = k → (permWord σ).length = permLen σ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro σ hk
      rw [permWord]
      split
      · rename_i h
        rw [eq_one_of_firstDescent_none h, permLen_one]; rfl
      · rename_i i h
        have hdesc := firstDescent_some_descent h
        have hlen := permLen_mul_adjT_of_descent hdesc
        rw [List.length_append, List.length_singleton,
          ih (permLen (σ * adjT i)) (by omega) (σ * adjT i) rfl, ← hlen]
  exact H (permLen σ) σ rfl

/-- The Artin word as **signed 1-based generator indices** (GAP form): `σᵢ ↦ i+1`.  A permutation's
reduced word uses no inverses, so every index is positive; the sign convention is there for the
downstream (non-permutation) braids GAP will normalise. -/
def permWordZ (σ : Perm (Fin n)) : List ℤ := (permWord σ).map (fun i => (i.1 : ℤ) + 1)

@[simp] theorem permWordZ_length (σ : Perm (Fin n)) : (permWordZ σ).length = permLen σ := by
  rw [permWordZ, List.length_map, permWord_length]

/-! ## Signed words → braids (the loop layer)

A concurrency **loop** goes out and comes back, so its word carries inverses.  `wordZToBraid`
reads a signed word (`+k ↦ σ_{k-1}`, `-k ↦ σ_{k-1}⁻¹`) back into `Braid n`; `invWordZ` reverses a
loop.  These are homomorphisms (`wordZToBraid_append`, `wordZToBraid_invWordZ`), so a zig-zag of
refinements concatenates to the braid of its loop. -/

/-- A signed 1-based index as a braid generator: `+k ↦ σ_{k-1}`, `-k ↦ σ_{k-1}⁻¹`, out-of-range
(and `0`) ↦ `1`.  The sign is carried by `Int.sign` as a `zpow`. -/
def genZ (a : ℤ) : Braid n :=
  if h : a.natAbs - 1 < n - 1 then (ofPerm (adjT ⟨a.natAbs - 1, h⟩)) ^ a.sign else 1

theorem genZ_neg (a : ℤ) : genZ (-a) = (genZ (n := n) a)⁻¹ := by
  unfold genZ
  simp only [Int.natAbs_neg, Int.sign_neg]
  by_cases h : a.natAbs - 1 < n - 1
  · simp only [dif_pos h, zpow_neg]
  · simp only [dif_neg h, inv_one]

/-- The braid a signed word realises: the product of its signed generators. -/
def wordZToBraid (w : List ℤ) : Braid n := (w.map genZ).prod

@[simp] theorem wordZToBraid_append (w v : List ℤ) :
    wordZToBraid (w ++ v) = wordZToBraid (n := n) w * wordZToBraid v := by
  simp [wordZToBraid, List.map_append, List.prod_append]

/-- Reverse-and-negate a signed word: the loop run backwards. -/
def invWordZ (w : List ℤ) : List ℤ := (w.map (- ·)).reverse

@[simp] theorem wordZToBraid_invWordZ (w : List ℤ) :
    wordZToBraid (invWordZ w) = (wordZToBraid (n := n) w)⁻¹ := by
  induction w with
  | nil => simp [wordZToBraid, invWordZ]
  | cons a t ih =>
    have hinv : invWordZ (a :: t) = invWordZ t ++ [-a] := by simp [invWordZ, List.reverse_cons]
    have h1 : wordZToBraid ([-a] : List ℤ) = genZ (n := n) (-a) := by
      rw [wordZToBraid, List.map_singleton, List.prod_singleton]
    have h2 : wordZToBraid (a :: t) = genZ (n := n) a * wordZToBraid t := by
      rw [wordZToBraid, List.map_cons, List.prod_cons]; rfl
    rw [hinv, wordZToBraid_append, ih, h1, genZ_neg, h2, mul_inv_rev]

/-- The signed generator of a positive index `i+1` is the `i`-th simple braid. -/
theorem genZ_coe (i : Fin (n - 1)) : genZ ((i.1 : ℤ) + 1) = ofPerm (adjT i) := by
  have hlt : ((i.1 : ℤ) + 1).natAbs - 1 < n - 1 := by have := i.2; omega
  have hv : ((i.1 : ℤ) + 1).natAbs - 1 = i.1 := by omega
  have hs : ((i.1 : ℤ) + 1).sign = 1 := Int.sign_eq_one_iff_pos.mpr (by omega)
  rw [genZ, dif_pos hlt, hs, zpow_one]
  exact congrArg (fun k => ofPerm (adjT k)) (Fin.ext hv)

/-- On a permutation's (positive) word, `wordZToBraid` agrees with `ofPerm`. -/
@[simp] theorem wordZToBraid_permWordZ (σ : Perm (Fin n)) :
    wordZToBraid (permWordZ σ) = ofPerm σ := by
  rw [← wordToBraid_permWord σ, wordZToBraid, permWordZ, wordToBraid, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => genZ_coe i)

/-! ## Pure-braid (Schreier) generator words

A concurrency **loop** at the single-`n`-cube — go from ordering `σ` to `σ·adjTⱼ` by an elementary
braiding, then back the reduced way — is the Schreier generator `ofPerm σ · ofPerm(adjTⱼ) ·
ofPerm(σ·adjTⱼ)⁻¹` of `Pₙ = ker(Bₙ ↠ Sₙ)`; these generate all of `Pₙ` (`pureBraid_le_of_schreier`
in `Braid/Surjectivity`).  `schreierWordZ σ j` emits its signed braid word, and `wordZToBraid` reads
it back as that pure braid. -/

/-- The signed braid word of the Schreier / pure-braid generator at `(σ, j)`. -/
def schreierWordZ (σ : Perm (Fin n)) (j : Fin (n - 1)) : List ℤ :=
  permWordZ σ ++ permWordZ (adjT j) ++ invWordZ (permWordZ (σ * adjT j))

/-- The word reads back as the Schreier generator `ofPerm σ · ofPerm(adjTⱼ) · ofPerm(σ·adjTⱼ)⁻¹`. -/
theorem wordZToBraid_schreierWordZ (σ : Perm (Fin n)) (j : Fin (n - 1)) :
    wordZToBraid (schreierWordZ σ j)
      = ofPerm σ * ofPerm (adjT j) * (ofPerm (σ * adjT j))⁻¹ := by
  rw [schreierWordZ, wordZToBraid_append, wordZToBraid_append, wordZToBraid_permWordZ,
    wordZToBraid_permWordZ, wordZToBraid_invWordZ, wordZToBraid_permWordZ]

/-- **It is a pure braid**: its underlying permutation is trivial. -/
theorem schreierWordZ_pure (σ : Perm (Fin n)) (j : Fin (n - 1)) :
    permHom n (wordZToBraid (schreierWordZ σ j)) = 1 := by
  rw [wordZToBraid_schreierWordZ, map_mul, map_mul, map_inv, permHom_ofPerm, permHom_ofPerm,
    permHom_ofPerm, mul_inv_cancel]

end CubeChains
