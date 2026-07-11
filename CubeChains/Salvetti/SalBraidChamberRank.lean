import CubeChains.Salvetti.Lines
import CubeChains.Arrangements.Braid

/-!
# Salvetti/SalBraidChamberRank — integer rank of a chamber

An integer height function on the directions of a `Chamber d` (a strict total order on
`Fin d`).  The **chamber rank** of a direction is its number of `lt`-predecessors; it is
injective, bounded in `[0, d)`, and its sign comparison recovers the chamber order, so
`braidSign`-style sign vectors read off the strict total order.

-/

open SignType

namespace FinalBraid

open Classical in
/-- The **chamber rank** of a direction: its number of `lt`-predecessors in the chamber order. -/
noncomputable def chamberRank {d : ℕ} (c : Chamber d) (i : Fin d) : ℤ :=
  ((Finset.univ.filter (fun k => c.lt k i)).card : ℤ)

/-- A `lt`-step strictly increases the chamber rank. -/
theorem chamberRank_strictMono {d : ℕ} (c : Chamber d) {i j : Fin d} (hij : c.lt i j) :
    chamberRank c i < chamberRank c j := by
  classical
  haveI := c.sto
  have hss : Finset.univ.filter (fun k => c.lt k i) ⊆ Finset.univ.filter (fun k => c.lt k j) := by
    intro a ha; rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, trans_of c.lt ha.2 hij⟩
  have hsub : Finset.univ.filter (fun k => c.lt k i) ⊂ Finset.univ.filter (fun k => c.lt k j) :=
    (Finset.ssubset_iff_of_subset hss).mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hij⟩,
        fun hc => (irrefl_of c.lt i) (Finset.mem_filter.mp hc).2⟩
  have hcard := Finset.card_lt_card hsub
  simp only [chamberRank]
  exact_mod_cast hcard

/-- Sign of the rank comparison recovers the chamber order. -/
theorem chamberRank_lt_iff {d : ℕ} (c : Chamber d) (i j : Fin d) :
    chamberRank c i < chamberRank c j ↔ c.lt i j := by
  classical
  haveI := c.sto
  constructor
  · intro h
    rcases trichotomous_of c.lt i j with hlt | heq | hgt
    · exact hlt
    · subst heq; exact absurd h (lt_irrefl _)
    · exact (lt_asymm h (chamberRank_strictMono c hgt)).elim
  · exact chamberRank_strictMono c

/-- The chamber rank is injective. -/
theorem chamberRank_injective {d : ℕ} (c : Chamber d) : Function.Injective (chamberRank c) := by
  haveI := c.sto
  intro i j h
  by_contra hij
  rcases trichotomous_of c.lt i j with hlt | heq | hgt
  · have hr := (chamberRank_lt_iff c i j).mpr hlt
    rw [h] at hr; exact lt_irrefl _ hr
  · exact hij heq
  · have hr := (chamberRank_lt_iff c j i).mpr hgt
    rw [h] at hr; exact lt_irrefl _ hr

/-- The chamber rank lies in `[0, d)`. -/
theorem chamberRank_bounded {d : ℕ} (c : Chamber d) (i : Fin d) :
    0 ≤ chamberRank c i ∧ chamberRank c i < d := by
  classical
  haveI := c.sto
  simp only [chamberRank]
  refine ⟨Int.natCast_nonneg _, ?_⟩
  have hsub : Finset.univ.filter (fun k => c.lt k i) ⊂ Finset.univ :=
    (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
      ⟨i, Finset.mem_univ i, fun hc => (irrefl_of c.lt i) (Finset.mem_filter.mp hc).2⟩
  have hcard := Finset.card_lt_card hsub
  have hd : (Finset.univ : Finset (Fin d)).card = d := by simp
  rw [hd] at hcard
  exact_mod_cast hcard

/-- Nonnegativity of the chamber rank. -/
theorem chamberRank_nonneg {d : ℕ} (c : Chamber d) (i : Fin d) : 0 ≤ chamberRank c i :=
  (chamberRank_bounded c i).1

open Classical in
/-- **Sign recovers the chamber order:** a `lt`-step gives a negative rank difference. -/
theorem sign_chamberRank_sub {d : ℕ} (c : Chamber d) (i j : Fin d) (hij : i ≠ j) :
    SignType.sign (chamberRank c i - chamberRank c j) = if c.lt i j then -1 else 1 := by
  haveI := c.sto
  by_cases h : c.lt i j
  · rw [if_pos h]
    have hlt : chamberRank c i < chamberRank c j := chamberRank_strictMono c h
    have hneg : chamberRank c i - chamberRank c j < 0 := by omega
    rw [sign_neg hneg]
  · rw [if_neg h]
    have hji : c.lt j i := by
      rcases trichotomous_of c.lt i j with h1 | h1 | h1
      · exact absurd h1 h
      · exact absurd h1 hij
      · exact h1
    have hlt : chamberRank c j < chamberRank c i := chamberRank_strictMono c hji
    have hpos : 0 < chamberRank c i - chamberRank c j := by omega
    rw [sign_pos hpos]

end FinalBraid
