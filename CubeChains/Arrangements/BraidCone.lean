import CubeChains.Arrangements.BraidGeometry
import CubeChains.Arrangements.COMSum

/-!
# Arrangements/BraidCone — the bead cone realizes `⊕ᵢ A_{dᵢ−1}`

For a dimension sequence `dims : List ℕ+` an **event** is a pair `(bead i, coordinate k)`
(`beadEvent`), a **timing** is `t : beadEvent dims → ℝ`, and the **bead cone** is the set of
timings that run the beads *in series*: every event of bead `i` strictly precedes every event of
bead `i'` whenever `i < i'`.

The braid arrangement on all events would compare *every* pair of events.  On the bead cone the
cross-bead comparisons are constant (`i < i'` forces `t (i,k) < t (i',k')` for all `k`, `k'`), so
they carry no information and are deleted; only the **within-bead** pairs survive.  Those are
exactly the ground set `braidDirectSumGround dims`, and the realizable sign vectors are exactly the
covectors of the direct sum `braidDirectSum dims = ⊕ᵢ A_{dᵢ−1}` — this is why the answer is a direct
sum and not a full braid arrangement:

> `beadCovector_image : beadCovector dims '' beadCone dims = (braidDirectSum dims).covectors`.
-/

open SignType Set

namespace CubeChains

/-! ### The iterated direct sum of braid arrangements -/

/-- The ground set of the iterated direct sum `braidDirectSum dims`: the within-bead pairs. -/
def braidDirectSumGround : List ℕ+ → Type
  | [] => BraidGround 0
  | n :: rest => BraidGround (n : ℕ) ⊕ braidDirectSumGround rest

/-- **The iterated direct sum of braid arrangements** along a dimension sequence: `⊕ᵢ A_{dᵢ−1}`,
right-folded to match `serialWedge`.  The empty list gives the (empty) braid arrangement of the
point `□⁰`. -/
def braidDirectSum : (dims : List ℕ+) → COM (braidDirectSumGround dims)
  | [] => braidCOM 0
  | n :: rest => (braidCOM (n : ℕ)).directSum (braidDirectSum rest)

/-! ### Integer realisation of a real timing

`denseRank` (`Braid.lean`) turns an integer height into a bounded integer height with the same
covector; `realRank` is its `ℝ`-mirror, turning a *real* timing into an integer height with the
same covector.  Counting indices below (rather than distinct values) keeps the proofs to two
`Finset.card_lt_card`s. -/

variable {n : ℕ}

/-- The **real rank** of `t` at `i`: the number of indices strictly below `i` in the `t`-order. -/
noncomputable def realRank (t : Fin n → ℝ) (i : Fin n) : ℤ :=
  ((Finset.univ.filter fun j => t j < t i).card : ℤ)

theorem realRank_lt_realRank {t : Fin n → ℝ} {i j : Fin n} (h : t i < t j) :
    realRank t i < realRank t j := by
  have hss : (Finset.univ.filter fun k => t k < t i) ⊂ Finset.univ.filter fun k => t k < t j :=
    (Finset.ssubset_iff_of_subset (fun k hk => by
      rw [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, hk.2.trans h⟩)).mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩,
        fun hc => lt_irrefl (t i) (Finset.mem_filter.mp hc).2⟩
  have hcard := Finset.card_lt_card hss
  simp only [realRank]
  exact_mod_cast hcard

theorem realRank_eq_realRank {t : Fin n → ℝ} {i j : Fin n} (h : t i = t j) :
    realRank t i = realRank t j := by simp only [realRank, h]

/-- The real covector of a timing is the braid covector of its rank: every timing is realized by
an integer height. -/
theorem braidSign_realRank (t : Fin n → ℝ) : braidSign (realRank t) = braidCovectorR t := by
  funext e
  rw [braidSign_apply, braidCovectorR_apply]
  rcases lt_trichotomy (t e.1.1) (t e.1.2) with h | h | h
  · rw [sign_neg (show realRank t e.1.1 - realRank t e.1.2 < 0 by
        have := realRank_lt_realRank h; omega),
      sign_neg (show t e.1.1 - t e.1.2 < 0 by linarith)]
  · rw [realRank_eq_realRank h, h, sub_self, sub_self, sign_zero, sign_zero]
  · rw [sign_pos (show (0 : ℤ) < realRank t e.1.1 - realRank t e.1.2 by
        have := realRank_lt_realRank h; omega),
      sign_pos (show (0 : ℝ) < t e.1.1 - t e.1.2 by linarith)]

/-- Every real covector is a covector of the braid arrangement. -/
theorem braidCovectorR_mem (t : Fin n → ℝ) : braidCovectorR t ∈ braidCovectors n :=
  ⟨realRank t, braidSign_realRank t⟩

/-- A constant shift is invisible to the real covector (it cancels in every difference). -/
theorem braidCovectorR_add_const (t : Fin n → ℝ) (c : ℝ) :
    braidCovectorR (fun i => t i + c) = braidCovectorR t := by
  funext e; rw [braidCovectorR_apply, braidCovectorR_apply]; congr 1; ring

/-! ### Events, timings, the bead cone -/

/-- An **event**: a coordinate of a bead.  (An `abbrev` so that the `Fintype` instance and the
`Sigma` pattern matches below are available without unfolding.) -/
abbrev beadEvent (dims : List ℕ+) : Type := Σ i : Fin dims.length, Fin (dims.get i : ℕ)

/-- The **bead cone**: timings running the beads in series. -/
def beadCone (dims : List ℕ+) : Set (beadEvent dims → ℝ) :=
  {t | ∀ e e' : beadEvent dims, (e.1 : ℕ) < (e'.1 : ℕ) → t e < t e'}

variable {m : ℕ+} {rest : List ℕ+}

/-- The timings of bead `0`.  `(m :: rest).get ⟨0, _⟩` reduces to `m`, so no cast is needed. -/
def beadHead (t : beadEvent (m :: rest) → ℝ) : Fin (m : ℕ) → ℝ :=
  fun k => t ⟨⟨0, Nat.succ_pos _⟩, k⟩

/-- The timings of the later beads.  `(m :: rest).get i.succ` reduces to `rest.get i`. -/
def beadTail (t : beadEvent (m :: rest) → ℝ) : beadEvent rest → ℝ :=
  fun e => t ⟨e.1.succ, e.2⟩

/-- Assembling a timing from bead `0` and the later beads. -/
def beadCons (h : Fin (m : ℕ) → ℝ) (s : beadEvent rest → ℝ) : beadEvent (m :: rest) → ℝ
  | ⟨⟨0, _⟩, k⟩ => h k
  | ⟨⟨j + 1, hj⟩, k⟩ => s ⟨⟨j, Nat.lt_of_succ_lt_succ hj⟩, k⟩

@[simp] theorem beadHead_beadCons (h : Fin (m : ℕ) → ℝ) (s : beadEvent rest → ℝ) :
    beadHead (beadCons h s) = h := rfl

@[simp] theorem beadTail_beadCons (h : Fin (m : ℕ) → ℝ) (s : beadEvent rest → ℝ) :
    beadTail (beadCons h s) = s := rfl

theorem beadCone_add_const {dims : List ℕ+} {t : beadEvent dims → ℝ} (ht : t ∈ beadCone dims)
    (c : ℝ) : (fun e => t e + c) ∈ beadCone dims :=
  fun e e' hee' => by have := ht e e' hee'; linarith

/-- `beadCons h s` is in the cone once `s` is and bead `0` runs strictly before all of `s`. -/
theorem beadCons_mem_beadCone {h : Fin (m : ℕ) → ℝ} {s : beadEvent rest → ℝ}
    (hs : s ∈ beadCone rest) (hlt : ∀ k e, h k < s e) : beadCons h s ∈ beadCone (m :: rest) := by
  rintro ⟨⟨i, hi⟩, k⟩ ⟨⟨i', hi'⟩, k'⟩ hlt'
  cases i with
  | zero =>
      cases i' with
      | zero => exact absurd hlt' (lt_irrefl 0)
      | succ j' => exact hlt k ⟨⟨j', Nat.lt_of_succ_lt_succ hi'⟩, k'⟩
  | succ j =>
      cases i' with
      | zero => exact absurd hlt' (Nat.not_lt_zero _)
      | succ j' =>
          exact hs ⟨⟨j, Nat.lt_of_succ_lt_succ hi⟩, k⟩ ⟨⟨j', Nat.lt_of_succ_lt_succ hi'⟩, k'⟩
            (Nat.lt_of_succ_lt_succ hlt')

/-! ### The covector of a timing -/

/-- The **covector of a timing**: bead by bead, the real braid covector of that bead's times. -/
noncomputable def beadCovector : (dims : List ℕ+) → (beadEvent dims → ℝ) →
    SignVec (braidDirectSumGround dims)
  | [], _ => 0
  | _ :: rest, t => Sum.elim (braidCovectorR (beadHead t)) (beadCovector rest (beadTail t))

theorem beadCovector_add_const : ∀ (dims : List ℕ+) (t : beadEvent dims → ℝ) (c : ℝ),
    beadCovector dims (fun e => t e + c) = beadCovector dims t
  | [], _, _ => rfl
  | _ :: rest, t, c => by
      change Sum.elim (braidCovectorR fun k => beadHead t k + c)
        (beadCovector rest fun e => beadTail t e + c) = _
      rw [braidCovectorR_add_const, beadCovector_add_const rest]
      rfl

/-- **Every timing realizes a covector** — no cone hypothesis needed. -/
theorem beadCovector_mem : ∀ (dims : List ℕ+) (t : beadEvent dims → ℝ),
    beadCovector dims t ∈ (braidDirectSum dims).covectors
  | [], _ => braidCOM_isOM 0
  | _ :: rest, t => ⟨braidCovectorR_mem (beadHead t), beadCovector_mem rest (beadTail t)⟩

/-- **Every covector is realized inside the cone.**  Bead `0`'s integer height is taken as is; the
later beads are lifted by a constant `a - b + 1` above it, which leaves their covector alone. -/
theorem beadCovector_surjOn : ∀ (dims : List ℕ+), ∀ X ∈ (braidDirectSum dims).covectors,
    ∃ t ∈ beadCone dims, beadCovector dims t = X
  | [], X, _ => ⟨fun _ => 0, fun e => e.1.elim0, by funext e; exact e.1.1.elim0⟩
  | m :: rest, X, hX => by
      obtain ⟨x, hx⟩ : SignVec.restrictL X ∈ braidCovectors (m : ℕ) := hX.1
      obtain ⟨s, hsc, hsv⟩ := beadCovector_surjOn rest _ hX.2
      obtain ⟨a, ha⟩ := (Set.finite_range fun k => ((x k : ℤ) : ℝ)).bddAbove
      obtain ⟨b, hb⟩ := (Set.finite_range s).bddBelow
      refine ⟨beadCons (fun k => (x k : ℝ)) (fun e => s e + (a - b + 1)), ?_, ?_⟩
      · refine beadCons_mem_beadCone (beadCone_add_const hsc _) fun k e => ?_
        have h1 : ((x k : ℤ) : ℝ) ≤ a := ha (Set.mem_range_self k)
        have h2 : b ≤ s e := hb (Set.mem_range_self e)
        linarith
      · change Sum.elim (braidCovectorR (beadHead _)) (beadCovector rest (beadTail _)) = X
        rw [beadHead_beadCons, beadTail_beadCons, braidCovectorR_intCast, hx,
          beadCovector_add_const, hsv, SignVec.elim_restrict]

/-- **Realizability.**  The bead cone realizes exactly the covectors of `⊕ᵢ A_{dᵢ−1}`. -/
theorem beadCovector_image (dims : List ℕ+) :
    beadCovector dims '' beadCone dims = (braidDirectSum dims).covectors := by
  refine Set.Subset.antisymm ?_ fun X hX => ?_
  · rintro X ⟨t, -, rfl⟩
    exact beadCovector_mem dims t
  · obtain ⟨t, ht, htX⟩ := beadCovector_surjOn dims X hX
    exact ⟨t, ht, htX⟩

end CubeChains
