import CubeChains.Concurrency.Salvetti.SalBraid
import CubeChains.Concurrency.Complexification.SymReorient
import CubeChains.Concurrency.Complexification.RunClassifier

/-!
# Concurrency/Salvetti/WallCrossing — the presentation, said in arrangement language

The translation table for `hbpBraidSalEquiv : Ch (Hbp □ⁿ) ≌ (Sal (braidCOM n))ᵒᵖ`.  A chamber is a
run of the decorated cube; its `n-1` walls are its adjacent rank pairs, and each carries two
codimension-one cells — `wallStay` (crossing permutation `1`: a merge) and `wallCross` (crossing
permutation `adjT k`: an atom).  `card_wallsThrough` says codimension *counts* walls, so a
codimension-two cell lies on exactly two: consecutive (braid) or separated (commutation).

⚠ An atom is not an arrow between chambers.  A wall cell lies **below** both chambers it separates,
so in `Ch (Hbp □ⁿ)` it is the apex of a span and `σₖ` appears only after inverting one leg.
-/

open CategoryTheory Opposite CubeChain BPSet

namespace CubeChains

variable {n : ℕ}

/-! ## Beads of a refinement are intervals of the chamber's order -/

/-- **A bead of a refinement is an interval of the chamber's order.** -/
theorem beadOf_of_between {t C : Ch (□n)} (h : (chFace C).1 ⊑ (chFace t).1) {p q k : Fin n}
    (hpq : beadOf C p = beadOf C q)
    (h1 : (beadOf t p : ℕ) ≤ (beadOf t k : ℕ)) (h2 : (beadOf t k : ℕ) ≤ (beadOf t q : ℕ)) :
    beadOf C k = beadOf C p := by
  have hl := beadOf_le h h1
  have hr := beadOf_le h h2
  rw [← hpq] at hr
  exact Fin.val_injective (by omega)

/-! ## Chambers, and the ranks they impose

A chamber is a run word `w`; the coordinate of rank `r` is `w r`, and a face below it is read off
`beadOf` in that order. -/

theorem beadOf_le_word {w : Equiv.Perm (Fin n)} {C : Ch (□n)} (h : (chFace C).1 ⊑ wordTope w)
    {p q : Fin n} (hpq : (w.symm p : ℕ) ≤ (w.symm q : ℕ)) :
    (beadOf C p : ℕ) ≤ (beadOf C q : ℕ) :=
  beadOf_le h (by rw [beadOf_wordChain, beadOf_wordChain]; exact hpq)

theorem beadOf_of_between_word {w : Equiv.Perm (Fin n)} {C : Ch (□n)}
    (h : (chFace C).1 ⊑ wordTope w) {p q k : Fin n} (hpq : beadOf C p = beadOf C q)
    (h1 : (w.symm p : ℕ) ≤ (w.symm k : ℕ)) (h2 : (w.symm k : ℕ) ≤ (w.symm q : ℕ)) :
    beadOf C k = beadOf C p :=
  beadOf_of_between h hpq (by rw [beadOf_wordChain, beadOf_wordChain]; exact h1)
    (by rw [beadOf_wordChain, beadOf_wordChain]; exact h2)

/-- The ties of a chain's face are the pairs sharing a bead — the hyperplanes through it. -/
theorem chFace_eq_zero_iff (C : Ch (□n)) (e : BraidGround n) :
    (chFace C).1 e = 0 ↔ beadOf C e.1.1 = beadOf C e.1.2 := by
  rw [chFace_val, braidSign_zero_iff]
  exact ⟨fun h => Fin.val_injective (Nat.cast_injective h), fun h => by rw [h]⟩

/-! ## The walls of a chamber

The `k`-th wall of `w` merges the ranks `k` and `k+1`: the codimension-one face of `wordTope w`
on the hyperplane `x_{w k} = x_{w (k+1)}`. -/

/-- The heights of the `k`-th wall of the chamber `w`. -/
def wallHeight (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) (p : Fin n) : ℤ :=
  if (w.symm p : ℕ) = (k : ℕ) + 1 then ((k : ℕ) : ℤ) else ((w.symm p : ℕ) : ℤ)

/-- **The `k`-th wall of the chamber `w`.** -/
def wallFace (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) : SignVec (BraidGround n) :=
  braidSign (wallHeight w k)

theorem wallFace_mem (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    wallFace w k ∈ (braidCOM n).covectors := ⟨wallHeight w k, rfl⟩

/-- The wall face as an object of `Face (braidCOM n)`. -/
def wallFaceObj (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) : COM.Face (braidCOM n) :=
  ⟨wallFace w k, wallFace_mem w k⟩

theorem wallHeight_eq_iff (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) (p q : Fin n) :
    wallHeight w k p = wallHeight w k q ↔
      ((w.symm p : ℕ) = (w.symm q : ℕ) ∨
        ((w.symm p : ℕ) = (k : ℕ) ∧ (w.symm q : ℕ) = (k : ℕ) + 1) ∨
        ((w.symm p : ℕ) = (k : ℕ) + 1 ∧ (w.symm q : ℕ) = (k : ℕ))) := by
  simp only [wallHeight]
  split_ifs <;> omega

theorem wallHeight_lt_iff (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) {p q : Fin n}
    (hne : wallHeight w k p ≠ wallHeight w k q) :
    (wallHeight w k p < wallHeight w k q ↔ (w.symm p : ℕ) < (w.symm q : ℕ)) := by
  simp only [wallHeight] at hne ⊢
  split_ifs at hne ⊢ <;> omega

/-- **A wall is a face of its chamber.** -/
theorem wallFace_le (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) : wallFace w k ⊑ wordTope w := by
  rw [wallFace, wordTope_eq_braidSign, braidSign_faceLE_iff]
  intro p q hne
  rw [wallHeight_lt_iff w k hne]
  exact Iff.symm (by exact_mod_cast Iff.rfl)

/-- **A wall lies on exactly one hyperplane**: the pair of ranks it merges. -/
theorem wallFace_eq_zero_iff (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) (e : BraidGround n) :
    wallFace w k e = 0 ↔
      (((w.symm e.1.1 : ℕ) = (k : ℕ) ∧ (w.symm e.1.2 : ℕ) = (k : ℕ) + 1) ∨
        ((w.symm e.1.1 : ℕ) = (k : ℕ) + 1 ∧ (w.symm e.1.2 : ℕ) = (k : ℕ))) := by
  have hne : (w.symm e.1.1 : ℕ) ≠ (w.symm e.1.2 : ℕ) := fun hc =>
    absurd (w.symm.injective (Fin.val_injective hc)) e.2.ne
  rw [wallFace, braidSign_zero_iff, wallHeight_eq_iff]
  tauto

/-! ## The two chambers a wall separates

`w` and `w * adjT k` have the same `k`-th wall — that is what makes it a wall. -/

/-- **The chamber across the `k`-th wall has the same `k`-th wall.** -/
theorem wallFace_mul_adjT (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    wallFace (w * adjT k) k = wallFace w k := by
  refine congrArg braidSign (funext fun p => ?_)
  simp only [wallHeight, symm_mul_adjT, adjT_val]
  have hk : (k : ℕ) + 1 < n := by have := k.2; omega
  split_ifs <;> omega

/-- …so the wall is also a face of the chamber across it. -/
theorem wallFace_le_flip (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    wallFace w k ⊑ wordTope (w * adjT k) := by
  rw [← wallFace_mul_adjT w k]
  exact wallFace_le (w * adjT k) k

/-! ## The two codimension-one cells over a wall

`wallStay` keeps the chamber, `wallCross` swaps to the other side.  Their crossing permutations are
`1` and `adjT k` — the merge and the atom `σₖ`. -/

/-- **Staying on this side of the `k`-th wall of `w`** — the merge. -/
def wallStay (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) : Sal (braidCOM n) :=
  faceCell (wallFaceObj w k) ⟨wordTope w, isTope_wordTope w⟩ (wallFace_le w k)

/-- **Crossing the `k`-th wall of `w`** — the atom `σₖ`. -/
def wallCross (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) : Sal (braidCOM n) :=
  faceCell (wallFaceObj w k) ⟨wordTope (w * adjT k), isTope_wordTope _⟩ (wallFace_le_flip w k)

theorem wallCross_le (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    wallCross w k ≤ topeCell ⟨wordTope w, isTope_wordTope w⟩ :=
  faceCell_le_topeCell _ (wallFace_le w k)

/-- …and the same cell also lies below the chamber across the wall. -/
theorem wallCross_le_flip (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    wallCross w k ≤ topeCell ⟨wordTope (w * adjT k), isTope_wordTope _⟩ :=
  faceCell_le_topeCell _ (wallFace_le_flip w k)

/-! ### Crossing permutations -/

/-- **The merge crosses nothing.** -/
@[simp] theorem topeCross_wallStay (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    topeCross (topeCell ⟨wordTope w, isTope_wordTope w⟩) (wallStay w k) = 1 := by
  rw [topeCross, cellWord_of_tope _ w rfl, cellWord_of_tope _ w rfl, inv_mul_cancel]

/-- **The atom `σₖ`**: crossing the `k`-th wall of `w` is the `k`-th adjacent transposition. -/
@[simp] theorem topeCross_wallCross (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    topeCross (topeCell ⟨wordTope w, isTope_wordTope w⟩) (wallCross w k) = adjT k := by
  rw [topeCross, cellWord_of_tope _ (w * adjT k) rfl, cellWord_of_tope _ w rfl, mul_inv_rev,
    mul_assoc, inv_mul_cancel, mul_one, inv_eq_iff_mul_eq_one, adjT_mul_self]

/-- …and from the far side it crosses nothing: the atom is one leg of a span, not an arrow of
chambers. -/
@[simp] theorem topeCross_wallCross_flip (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    topeCross (topeCell ⟨wordTope (w * adjT k), isTope_wordTope _⟩) (wallCross w k) = 1 := by
  rw [topeCross, cellWord_of_tope _ (w * adjT k) rfl, cellWord_of_tope _ (w * adjT k) rfl,
    inv_mul_cancel]

/-! ## Codimension counts walls

A face below a chamber merges the chamber's ranks into consecutive blocks; the merges it performs
are exactly the walls it lies on, and there are `degree` of them. -/

/-- **A monotone surjection onto `Fin L` has unit steps** — a bigger jump would skip a value. -/
private theorem step_le_one {L : ℕ} {g : Fin n → ℕ} (hmono : Monotone g) (hlt : ∀ r, g r < L)
    (hsurj : ∀ j, j < L → ∃ r, g r = j) (k : Fin (n - 1)) : g (adjHi k) ≤ g (adjLo k) + 1 := by
  by_contra hc
  obtain ⟨r, hr⟩ := hsurj (g (adjLo k) + 1) (by have := hlt (adjHi k); omega)
  rcases Nat.lt_or_ge (r : ℕ) (adjHi k : ℕ) with h | h
  · have := hmono (show r ≤ adjLo k from Fin.le_def.mpr (by
      simp only [adjLo_val, adjHi_val] at h ⊢; omega))
    omega
  · have := hmono (show adjHi k ≤ r from Fin.le_def.mpr h)
    omega

/-- **A monotone surjection `Fin n → Fin L` merges exactly `n - L` adjacent ranks** — the unit steps
telescope, so `L - 1` of the `n - 1` adjacencies jump and the rest merge. -/
theorem card_merge_eq {L : ℕ} (g : Fin n → ℕ) (hmono : Monotone g)
    (hlt : ∀ r, g r < L) (hsurj : ∀ j, j < L → ∃ r, g r = j) :
    (Finset.univ.filter fun k : Fin (n - 1) => g (adjLo k) = g (adjHi k)).card = n - L := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hL : L = 0 := by
      by_contra hL
      obtain ⟨r, -⟩ := hsurj 0 (Nat.pos_of_ne_zero hL)
      exact absurd r.2 (Nat.not_lt_zero _)
    simp [hL]
  have hL1 : 1 ≤ L := by have := hlt ⟨0, hn⟩; omega
  have hkey : ∀ k : Fin (n - 1), g (adjLo k) ≤ g (adjHi k) := fun k =>
    hmono (Fin.le_def.mpr (by simp))
  -- `g` read on `ℕ`, frozen past the last rank, so that the steps telescope
  set f : ℕ → ℕ := fun i => g ⟨min i (n - 1), by omega⟩ with hf
  have hfmono : Monotone f := fun i j hij => hmono (Fin.le_def.mpr (by simp only; omega))
  have hf0 : f 0 = 0 := by
    obtain ⟨r, hr⟩ := hsurj 0 hL1
    have hle : f 0 ≤ g r := hmono (Fin.le_def.mpr (by simp))
    omega
  have hflast : f (n - 1) = L - 1 := by
    obtain ⟨r, hr⟩ := hsurj (L - 1) (by omega)
    have hle : g r ≤ f (n - 1) :=
      hmono (Fin.le_def.mpr (by simp only [min_self]; have := r.2; omega))
    have hub : f (n - 1) < L := hlt _
    omega
  have hjump : (Finset.univ.filter fun k : Fin (n - 1) => g (adjLo k) < g (adjHi k)).card
      = L - 1 := by
    have hterm : ∀ k : Fin (n - 1),
        (if g (adjLo k) < g (adjHi k) then 1 else 0) = f ((k : ℕ) + 1) - f (k : ℕ) := fun k => by
      have h1 : f (k : ℕ) = g (adjLo k) := by
        rw [hf]; exact congrArg g (Fin.ext (by simp only [adjLo_val]; have := k.2; omega))
      have h2 : f ((k : ℕ) + 1) = g (adjHi k) := by
        rw [hf]; exact congrArg g (Fin.ext (by simp only [adjHi_val]; have := k.2; omega))
      have := hkey k
      have := step_le_one hmono hlt hsurj k
      rw [h1, h2]
      split_ifs <;> omega
    calc (Finset.univ.filter fun k : Fin (n - 1) => g (adjLo k) < g (adjHi k)).card
        = ∑ k : Fin (n - 1), (if g (adjLo k) < g (adjHi k) then 1 else 0) := Finset.card_filter _ _
      _ = ∑ k : Fin (n - 1), (f ((k : ℕ) + 1) - f (k : ℕ)) :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = ∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) :=
          Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) (n - 1)
      _ = f (n - 1) - f 0 := Finset.sum_range_tsub hfmono _
      _ = L - 1 := by rw [hf0, hflast, Nat.sub_zero]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n - 1)))) (p := fun k => g (adjLo k) = g (adjHi k))
  have hcompl : (Finset.univ.filter fun k : Fin (n - 1) => ¬ (g (adjLo k) = g (adjHi k)))
      = Finset.univ.filter fun k : Fin (n - 1) => g (adjLo k) < g (adjHi k) :=
    Finset.filter_congr fun k _ => by have := hkey k; omega
  rw [Finset.card_univ, Fintype.card_fin, hcompl, hjump] at hsplit
  omega

/-- The walls of the chamber `w` through `C`'s face, read as the adjacent ranks `C` merges
(`mem_wallsThrough_iff`); computable, unlike the face order it encodes. -/
def wallsThrough (w : Equiv.Perm (Fin n)) (C : Ch (□n)) : Finset (Fin (n - 1)) :=
  Finset.univ.filter fun k => beadOf C (w (adjLo k)) = beadOf C (w (adjHi k))

theorem mem_wallsThrough {w : Equiv.Perm (Fin n)} {C : Ch (□n)} {k : Fin (n - 1)} :
    k ∈ wallsThrough w C ↔ beadOf C (w (adjLo k)) = beadOf C (w (adjHi k)) := by
  simp [wallsThrough]

theorem symm_apply_rank (w : Equiv.Perm (Fin n)) (r : Fin n) :
    ((w.symm (w r) : Fin n) : ℕ) = (r : ℕ) := by rw [Equiv.symm_apply_apply]

/-- **Codimension counts walls**: a face below the chamber `w` lies on exactly `degree C` of its
`n-1` walls. -/
theorem card_wallsThrough {w : Equiv.Perm (Fin n)} {C : Ch (□n)}
    (h : (chFace C).1 ⊑ wordTope w) : (wallsThrough w C).card = ChainCat.degree C := by
  have hdeg : ChainCat.degree C = n - C.dims.length := by
    rw [ChainCat.degree, BPSet.degree_eq_dimSum_sub_length, wedgeDimSum_eq C.map]
  have hval : wallsThrough w C
      = Finset.univ.filter fun k : Fin (n - 1) =>
          (beadOf C (w (adjLo k)) : ℕ) = (beadOf C (w (adjHi k)) : ℕ) :=
    Finset.filter_congr fun k _ => (Fin.val_eq_val _ _).symm
  rw [hdeg, hval]
  refine card_merge_eq (L := C.dims.length) (fun r => (beadOf C (w r) : ℕ)) (fun r r' hrr => ?_)
    (fun r => (beadOf C (w r)).2) (fun j hj => ?_)
  · exact beadOf_le_word h (by rw [symm_apply_rank, symm_apply_rank]; exact hrr)
  · obtain ⟨q, hq⟩ := beadOf_surjective C ⟨j, hj⟩
    refine ⟨w.symm q, ?_⟩
    change (beadOf C (w (w.symm q)) : ℕ) = j
    rw [Equiv.apply_symm_apply, hq]

/-- Every adjacent rank pair inside a bead is a wall. -/
theorem mem_wallsThrough_of_tie {w : Equiv.Perm (Fin n)} {C : Ch (□n)}
    (h : (chFace C).1 ⊑ wordTope w) {p q : Fin n} (hpq : beadOf C p = beadOf C q)
    {k : Fin (n - 1)} (h1 : (w.symm p : ℕ) ≤ (k : ℕ)) (h2 : (k : ℕ) + 1 ≤ (w.symm q : ℕ)) :
    k ∈ wallsThrough w C := by
  have hlo : beadOf C (w (adjLo k)) = beadOf C p :=
    beadOf_of_between_word h hpq (by rw [symm_apply_rank]; simp only [adjLo_val]; omega)
      (by rw [symm_apply_rank]; simp only [adjLo_val]; omega)
  have hhi : beadOf C (w (adjHi k)) = beadOf C p :=
    beadOf_of_between_word h hpq (by rw [symm_apply_rank]; simp only [adjHi_val]; omega)
      (by rw [symm_apply_rank]; simp only [adjHi_val]; omega)
  rw [mem_wallsThrough, hlo, hhi]

/-! ## Codimension one: stay, or cross one wall -/

theorem eq_apply_of_rank (w : Equiv.Perm (Fin n)) (p r : Fin n) (h : (w.symm p : ℕ) = (r : ℕ)) :
    p = w r := by
  conv_lhs => rw [← Equiv.apply_symm_apply w p]
  exact congrArg w (Fin.val_injective h)

/-- Adjacent ranks are distinct coordinates. -/
private theorem apply_adjLo_ne_adjHi (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    w (adjLo k) ≠ w (adjHi k) := fun hc => by
  have h := congrArg Fin.val (w.injective hc)
  simp only [adjLo_val, adjHi_val] at h
  omega

/-- **A wall's single zero, read at coordinates** rather than at ranks. -/
theorem wallFace_eq_zero_iff' (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) (e : BraidGround n) :
    wallFace w k e = 0 ↔
      ((e.1.1 = w (adjLo k) ∧ e.1.2 = w (adjHi k)) ∨
        (e.1.1 = w (adjHi k) ∧ e.1.2 = w (adjLo k))) := by
  have hlo : ∀ p : Fin n, (w.symm p : ℕ) = (k : ℕ) ↔ p = w (adjLo k) := fun p =>
    ⟨fun hp => eq_apply_of_rank w p (adjLo k) (by simpa using hp),
      fun hp => by rw [hp, symm_apply_rank]; simp⟩
  have hhi : ∀ p : Fin n, (w.symm p : ℕ) = (k : ℕ) + 1 ↔ p = w (adjHi k) := fun p =>
    ⟨fun hp => eq_apply_of_rank w p (adjHi k) (by simpa using hp),
      fun hp => by rw [hp, symm_apply_rank]; simp⟩
  rw [wallFace_eq_zero_iff, hlo, hhi, hhi, hlo]

/-- **`wallsThrough` is arrangement-native**: `C` merges the ranks `k, k+1` exactly when its face
lies on the `k`-th wall of `w`.  Both faces lie below the chamber, so `⊑` between them is reverse
inclusion of zero sets, and the wall has exactly the one zero. -/
theorem mem_wallsThrough_iff {w : Equiv.Perm (Fin n)} {C : Ch (□n)}
    (h : (chFace C).1 ⊑ wordTope w) (k : Fin (n - 1)) :
    k ∈ wallsThrough w C ↔ (chFace C).1 ⊑ wallFace w k := by
  obtain ⟨e₀, he₀⟩ := exists_ground (apply_adjLo_ne_adjHi w k)
  have hz₀ : wallFace w k e₀ = 0 := (wallFace_eq_zero_iff' w k e₀).mpr he₀
  rw [mem_wallsThrough, SignVec.faceLE_iff_zeroSet_subset h (wallFace_le w k)]
  refine ⟨fun htie e he => ?_, fun hsub => ?_⟩
  · change (chFace C).1 e = 0
    rw [chFace_eq_zero_iff]
    rcases (wallFace_eq_zero_iff' w k e).mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact htie
    · rw [h1, h2]; exact htie.symm
  · have hC := (chFace_eq_zero_iff C e₀).mp (hsub hz₀)
    rcases he₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hC; exact hC
    · rw [h1, h2] at hC; exact hC.symm

/-- **The unique tie of a codimension-one face is a pair of adjacent ranks.** -/
theorem rank_eq_of_tie_of_wallsThrough {w : Equiv.Perm (Fin n)} {C : Ch (□n)}
    (h : (chFace C).1 ⊑ wordTope w) {k₀ : Fin (n - 1)} (hs : wallsThrough w C = {k₀})
    {p q : Fin n} (hpq : beadOf C p = beadOf C q) (hlt : (w.symm p : ℕ) < (w.symm q : ℕ)) :
    (w.symm p : ℕ) = (k₀ : ℕ) ∧ (w.symm q : ℕ) = (k₀ : ℕ) + 1 := by
  have hqn : (w.symm q : ℕ) < n := (w.symm q).2
  have hk : (⟨(w.symm p : ℕ), by omega⟩ : Fin (n - 1)) ∈ wallsThrough w C :=
    mem_wallsThrough_of_tie h hpq (le_refl _) (by simpa using hlt)
  rw [hs, Finset.mem_singleton] at hk
  have hp : (w.symm p : ℕ) = (k₀ : ℕ) := congrArg Fin.val hk
  refine ⟨hp, ?_⟩
  by_contra hne
  have hk' : (⟨(w.symm p : ℕ) + 1, by omega⟩ : Fin (n - 1)) ∈ wallsThrough w C :=
    mem_wallsThrough_of_tie h hpq (by simp) (by simp; omega)
  rw [hs, Finset.mem_singleton] at hk'
  have := congrArg Fin.val hk'
  simp only at this
  omega

/-- **A codimension-one face below a chamber is one of its walls.** -/
theorem eq_wallFace_of_degree_one {w : Equiv.Perm (Fin n)} {C : Ch (□n)}
    (h : (chFace C).1 ⊑ wordTope w) (hd : ChainCat.degree C = 1) :
    ∃ k : Fin (n - 1), (chFace C).1 = wallFace w k := by
  obtain ⟨k₀, hs⟩ := Finset.card_eq_one.mp ((card_wallsThrough h).trans hd)
  have hmem : beadOf C (w (adjLo k₀)) = beadOf C (w (adjHi k₀)) :=
    mem_wallsThrough.mp (hs ▸ Finset.mem_singleton_self k₀)
  refine ⟨k₀, SignVec.eq_of_ties h (wallFace_le w k₀) fun e => ?_⟩
  rw [chFace_eq_zero_iff, wallFace_eq_zero_iff]
  constructor
  · intro htie
    rcases Nat.lt_trichotomy (w.symm e.1.1 : ℕ) (w.symm e.1.2 : ℕ) with hc | hc | hc
    · exact Or.inl (rank_eq_of_tie_of_wallsThrough h hs htie hc)
    · exact absurd (w.symm.injective (Fin.val_injective hc)) e.2.ne
    · exact Or.inr ⟨(rank_eq_of_tie_of_wallsThrough h hs htie.symm hc).2,
        (rank_eq_of_tie_of_wallsThrough h hs htie.symm hc).1⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rw [eq_apply_of_rank w e.1.1 (adjLo k₀) (by simpa using ha),
        eq_apply_of_rank w e.1.2 (adjHi k₀) (by simpa using hb)]
      exact hmem
    · rw [eq_apply_of_rank w e.1.1 (adjHi k₀) (by simpa using ha),
        eq_apply_of_rank w e.1.2 (adjLo k₀) (by simpa using hb)]
      exact hmem.symm

/-! ## The two chambers above a wall -/

theorem isTope_ne_zero {T : SignVec (BraidGround n)} (hT : (braidCOM n).IsTope T)
    (e : BraidGround n) : T e ≠ 0 := ((braidCOM_isTope_iff T).mp hT).2 e

private theorem signType_eq_neg {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    a = -b := by revert ha hb hab; cases a <;> cases b <;> decide

/-- **A wall lies on one hyperplane**, so its zero is unique. -/
theorem wallFace_zero_unique {w : Equiv.Perm (Fin n)} {k : Fin (n - 1)} {e e' : BraidGround n}
    (he : wallFace w k e = 0) (he' : wallFace w k e' = 0) : e = e' := by
  rw [wallFace_eq_zero_iff] at he he'
  have hval : ∀ {x y : Fin n}, (w.symm x : ℕ) = (w.symm y : ℕ) → x = y := fun hxy =>
    w.symm.injective (Fin.val_injective hxy)
  have h1 : e.1.1 < e.1.2 := e.2
  have h2 : e'.1.1 < e'.1.2 := e'.2
  rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases he' with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
  · exact Subtype.ext (Prod.ext (hval (ha.trans ha'.symm)) (hval (hb.trans hb'.symm)))
  · rw [hval (ha.trans hb'.symm), hval (hb.trans ha'.symm)] at h1
    exact absurd h1 (asymm h2)
  · rw [hval (ha.trans hb'.symm), hval (hb.trans ha'.symm)] at h1
    exact absurd h1 (asymm h2)
  · exact Subtype.ext (Prod.ext (hval (ha.trans ha'.symm)) (hval (hb.trans hb'.symm)))

/-- **On its own hyperplane the wall's two chambers are opposite** — that is what makes them the
two sides of the wall. -/
theorem wordTope_mul_adjT_of_eq_zero (w : Equiv.Perm (Fin n)) (k : Fin (n - 1))
    {e : BraidGround n} (hz : wallFace w k e = 0) :
    wordTope (w * adjT k) e = - wordTope w e := by
  rw [wallFace_eq_zero_iff] at hz
  have hswap1 : ((adjT k (w.symm e.1.1) : Fin n) : ℕ) = ((w.symm e.1.2 : Fin n) : ℕ) := by
    rw [adjT_val]; rcases hz with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> split_ifs <;> omega
  have hswap2 : ((adjT k (w.symm e.1.2) : Fin n) : ℕ) = ((w.symm e.1.1 : Fin n) : ℕ) := by
    rw [adjT_val]; rcases hz with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> split_ifs <;> omega
  rw [wordTope_apply, wordTope_apply, symm_mul_adjT, symm_mul_adjT, hswap1, hswap2]
  exact SignInt.sign_sub_swap _ _

/-- **A wall has exactly two chambers above it** — `w` and `w * sₖ`. -/
theorem tope_above_wallFace {w : Equiv.Perm (Fin n)} {k : Fin (n - 1)}
    {T : SignVec (BraidGround n)} (hT : (braidCOM n).IsTope T) (h : wallFace w k ⊑ T) :
    T = wordTope w ∨ T = wordTope (w * adjT k) := by
  by_cases hcase : T = wordTope w
  · exact Or.inl hcase
  refine Or.inr ?_
  obtain ⟨e₀, he₀⟩ : ∃ e, T e ≠ wordTope w e := by
    by_contra hc
    exact hcase (funext fun e => not_not.mp fun hne => hc ⟨e, hne⟩)
  have hz₀ : wallFace w k e₀ = 0 := by
    by_contra hnz₀
    exact he₀ (((h e₀).resolve_left hnz₀).symm.trans ((wallFace_le w k e₀).resolve_left hnz₀))
  have hval₀ : T e₀ = wordTope (w * adjT k) e₀ := by
    rw [wordTope_mul_adjT_of_eq_zero w k hz₀]
    exact signType_eq_neg (isTope_ne_zero hT e₀) (isTope_ne_zero (isTope_wordTope w) e₀) he₀
  funext e
  by_cases hze : wallFace w k e = 0
  · rw [wallFace_zero_unique hze hz₀]; exact hval₀
  · exact ((h e).resolve_left hze).symm.trans ((wallFace_le_flip w k e).resolve_left hze)

/-! ## The codimension of a cell, and the two species

`cellCodim` is the dimension of the cell of the Salvetti complex; across `hbpBraidSalEquiv` it is
the `degree` of the decorated chain, and `codim` of a chain map is the dimension it gains. -/

/-- The chain of `□ⁿ` that a Salvetti cell's face is. -/
def cellChain (a : Sal (braidCOM n)) : Ch (□n) := chFaceEquiv.symm ⟨a.face, a.2.1⟩

@[simp] theorem chFace_cellChain (a : Sal (braidCOM n)) : (chFace (cellChain a)).1 = a.face :=
  chFace_symm_val ⟨a.face, a.2.1⟩

/-- The **codimension** of a Salvetti cell. -/
def cellCodim (a : Sal (braidCOM n)) : ℕ := ChainCat.degree (cellChain a)

/-- A cell whose face is a chamber is the chamber's maximal cell. -/
theorem eq_topeCell_of_isTope {a : Sal (braidCOM n)} (h : (braidCOM n).IsTope a.face) :
    a = topeCell ⟨a.face, h⟩ :=
  Subtype.ext (Prod.ext rfl (h.2 a.tope a.2.2.1.1 a.2.2.2))

theorem faceLE_wordTope_cellChain {w : Equiv.Perm (Fin n)} {b : Sal (braidCOM n)}
    (hb : b ≤ topeCell ⟨wordTope w, isTope_wordTope w⟩) :
    (chFace (cellChain b)).1 ⊑ wordTope w := by
  rw [chFace_cellChain]; exact hb.1

/-- **Distinct walls of a chamber are incomparable** — each has exactly one zero, its own rank
pair. -/
theorem wallFace_faceLE_iff (w : Equiv.Perm (Fin n)) (k j : Fin (n - 1)) :
    wallFace w k ⊑ wallFace w j ↔ j = k := by
  refine ⟨fun hle => ?_, fun hj => hj ▸ SignVec.faceLE_refl _⟩
  obtain ⟨e, he⟩ := exists_ground (apply_adjLo_ne_adjHi w j)
  have hzj : wallFace w j e = 0 := (wallFace_eq_zero_iff' w j e).mpr he
  have hzk : wallFace w k e = 0 := (hle e).elim id fun hx => hx.trans hzj
  rw [wallFace_eq_zero_iff] at hzj hzk
  refine Fin.val_injective ?_
  rcases hzk with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hzj with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega

/-- **A wall lies on exactly one of its chamber's walls: itself.** -/
theorem wallsThrough_eq_singleton {w : Equiv.Perm (Fin n)} {C : Ch (□n)} {k₀ : Fin (n - 1)}
    (hC : (chFace C).1 = wallFace w k₀) : wallsThrough w C = {k₀} :=
  Finset.ext fun j => by
    rw [mem_wallsThrough_iff (by rw [hC]; exact wallFace_le w k₀) j, hC, Finset.mem_singleton]
    exact wallFace_faceLE_iff w k₀ j

/-- **A chamber cell has codimension zero** — its chain is `topeRun T`, a run. -/
@[simp] theorem cellCodim_topeCell (T : Tope n) : cellCodim (topeCell T) = 0 :=
  (isRun_iff_degree_eq_zero _).mp (topeRun T).property

/-- **A cell over a wall has codimension one.** -/
theorem cellCodim_of_face_eq_wallFace {w : Equiv.Perm (Fin n)} {k : Fin (n - 1)}
    {a : Sal (braidCOM n)} (h : a.face = wallFace w k) : cellCodim a = 1 := by
  have hC : (chFace (cellChain a)).1 = wallFace w k := (chFace_cellChain a).trans h
  rw [cellCodim, ← card_wallsThrough (by rw [hC]; exact wallFace_le w k),
    wallsThrough_eq_singleton hC, Finset.card_singleton]

@[simp] theorem cellCodim_wallStay (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    cellCodim (wallStay w k) = 1 := cellCodim_of_face_eq_wallFace rfl

@[simp] theorem cellCodim_wallCross (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    cellCodim (wallCross w k) = 1 := cellCodim_of_face_eq_wallFace rfl

/-- **Out of a chamber, codimension one is: stay, or cross one wall.** -/
theorem codim_one_cases {w : Equiv.Perm (Fin n)} {b : Sal (braidCOM n)}
    (hb : b ≤ topeCell ⟨wordTope w, isTope_wordTope w⟩) (hd : cellCodim b = 1) :
    ∃ k : Fin (n - 1), b = wallStay w k ∨ b = wallCross w k := by
  obtain ⟨k, hk⟩ := eq_wallFace_of_degree_one (faceLE_wordTope_cellChain hb) hd
  rw [chFace_cellChain] at hk
  rcases tope_above_wallFace b.2.2.1 (hk ▸ b.faceLE_face_tope) with hc | hc
  · exact ⟨k, Or.inl (Subtype.ext (Prod.ext hk hc))⟩
  · exact ⟨k, Or.inr (Subtype.ext (Prod.ext hk hc))⟩

/-- **The rank-two dichotomy.**  A codimension-two cell below the chamber `w` lies on exactly two
of its walls. -/
theorem codim_two_walls {w : Equiv.Perm (Fin n)} {b : Sal (braidCOM n)}
    (hb : b ≤ topeCell ⟨wordTope w, isTope_wordTope w⟩) (hd : cellCodim b = 2) :
    ∃ k l : Fin (n - 1), (k : ℕ) < (l : ℕ) ∧ wallsThrough w (cellChain b) = {k, l} := by
  obtain ⟨x, y, hxy, hs⟩ :=
    Finset.card_eq_two.mp ((card_wallsThrough (faceLE_wordTope_cellChain hb)).trans hd)
  rcases Nat.lt_or_ge (x : ℕ) (y : ℕ) with hc | hc
  · exact ⟨x, y, hc, hs⟩
  · exact ⟨y, x, lt_of_le_of_ne hc fun hv => hxy (Fin.val_injective hv).symm,
      by rw [hs, Finset.pair_comm]⟩

/-! ## Transport to `Ch (Hbp □ⁿ)`

The loops of chambers at the two strata are `mul_adjT_braid` and `mul_adjT_comm`: crossing the two
walls of a braid stratum alternately three times each, or of a commutation stratum twice each,
returns to the chamber it started from. -/

/-- **A decorated chain's cell has its degree** — `degree` is the dimension of the Salvetti cell. -/
theorem cellCodim_hbpBraidSalEquiv (a : Ch (Hbp.obj (□n))) :
    cellCodim ((hbpBraidSalEquiv n).functor.obj a).unop = ChainCat.degree a := by
  have hface : (⟨((hbpBraidSalEquiv n).functor.obj a).unop.face,
      ((hbpBraidSalEquiv n).functor.obj a).unop.2.1⟩ : COM.Face (braidCOM n))
      = chFaceEquiv (⟨a.dims, chainOf (□n) a.map⟩ : Ch (□n)) :=
    Subtype.ext (face_hbpBraidSalEquiv a)
  rw [cellCodim, cellChain, hface, chFaceEquiv.symm_apply_apply]
  rfl

/-- **The chambers are the runs of the decorated cube.**  A run performs the `n` directions in some
order `σ`; its cell is the maximal cell of the tope of `σ⁻¹`, the word that order spells. -/
theorem hbpBraidSalEquiv_run (r : Run (Hbp.obj (□n))) :
    ((hbpBraidSalEquiv n).functor.obj r.chain).unop
      = topeCell ⟨wordTope (runHbpCubeEquivPerm n r)⁻¹, isTope_wordTope _⟩ := by
  have hchain : (⟨r.chain.dims, chainOf (□n) r.chain.map⟩ : Ch (□n))
      = wordChain (runHbpCubeEquivPerm n r)⁻¹ := by
    rw [wordChain, wordRun, show ((runHbpCubeEquivPerm n r)⁻¹).symm = runHbpCubeEquivPerm n r from
      Equiv.symm_symm _]
    exact (congrArg Run.chain (runOfPerm_flatten (runHbpEquiv (□n) r))).symm
  have hface : ((hbpBraidSalEquiv n).functor.obj r.chain).unop.face
      = wordTope (runHbpCubeEquivPerm n r)⁻¹ := by
    rw [face_hbpBraidSalEquiv, hchain]
    rfl
  rw [eq_topeCell_of_isTope (a := ((hbpBraidSalEquiv n).functor.obj r.chain).unop)
    (by rw [hface]; exact isTope_wordTope _)]
  exact congrArg topeCell (Subtype.ext hface)

/-- **The decorated cube's chains are a poset** — `Sal` is one, so a refinement is pinned by its
endpoints. -/
instance : Quiver.IsThin (Ch (Hbp.obj (□n))) := fun a b => by
  haveI : ∀ X Y : (Sal (braidCOM n))ᵒᵖ, Subsingleton (X ⟶ Y) :=
    fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  exact ((hbpBraidSalEquiv n).fullyFaithfulFunctor.homEquiv (X := a) (Y := b)).subsingleton

/-! ### The atom is a span

`wallCross w k` lies below both chambers it separates, so in `Ch (Hbp □ⁿ)` — the *opposite* of the
Salvetti poset — it receives a leg from each.  `topeCross_wallCross` labels one `σₖ` and
`topeCross_wallCross_flip` labels the other `1`; the generator is the second inverted after the
first, which exists only in the localization. -/

/-- The decorated chain a Salvetti cell names. -/
def cellObj (a : Sal (braidCOM n)) : Ch (Hbp.obj (□n)) := (hbpBraidSalEquiv n).inverse.obj (op a)

theorem degree_cellObj (a : Sal (braidCOM n)) : ChainCat.degree (cellObj a) = cellCodim a := by
  rw [← cellCodim_hbpBraidSalEquiv, cellObj, hbpBraidSalEquiv_functor_inverse]

/-- The leg of the wall span from the chamber `w` — the **atom**, of crossing permutation `σₖ`. -/
def wallLeg (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    cellObj (topeCell ⟨wordTope w, isTope_wordTope w⟩) ⟶ cellObj (wallCross w k) :=
  (hbpBraidSalEquiv n).inverse.map (homOfLE (wallCross_le w k)).op

/-- …and from the chamber across the wall — the **merge**, of crossing permutation `1`. -/
def wallLegFlip (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)) :
    cellObj (topeCell ⟨wordTope (w * adjT k), isTope_wordTope _⟩) ⟶ cellObj (wallCross w k) :=
  (hbpBraidSalEquiv n).inverse.map (homOfLE (wallCross_le_flip w k)).op

/-- **Both legs of a wall span are codimension one** — `codim` reads only the endpoints, and a
chamber has cell-codimension `0` against the wall's `1`. -/
theorem codim_wallCross_leg {T : Tope n} {w : Equiv.Perm (Fin n)} {k : Fin (n - 1)}
    (f : cellObj (topeCell T) ⟶ cellObj (wallCross w k)) : ChainCat.codim f = 1 := by
  change ChainCat.degree (cellObj (wallCross w k)) - ChainCat.degree (cellObj (topeCell T)) = 1
  rw [degree_cellObj, degree_cellObj, cellCodim_wallCross, cellCodim_topeCell]

end CubeChains
