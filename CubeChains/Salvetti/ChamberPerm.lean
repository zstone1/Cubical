import Mathlib.Order.RelClasses
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Interval.Finset.Fin
import CubeChains.Salvetti.Lines

/-!
# Salvetti/ChamberPerm — chambers are permutations

A `Chamber d` is a strict total order on `Fin d`; such an order is the same data as a
permutation of `Fin d` (its increasing enumeration).  `chamberPermEquiv` packages this
bijection.  Forward: `i ↦ #{k | k ≺ i}`, the predecessor rank; inverse: pull back the
standard order of `Fin d` along a permutation.
-/

open Finset

namespace CubeChains

variable {d : ℕ}

/-- Predecessor count of `i` in the chamber order — the rank that sends the chamber to a
permutation. -/
def Chamber.predCard (c : Chamber d) (i : Fin d) : ℕ :=
  (univ.filter (fun k => c.lt k i)).card

/-- `≺` strictly increases the predecessor count: it is the strict monotonicity that makes
the rank injective. -/
theorem Chamber.predCard_lt_predCard (c : Chamber d) {i j : Fin d} (h : c.lt i j) :
    c.predCard i < c.predCard j := by
  haveI := c.sto
  have hsub : univ.filter (fun k => c.lt k i) ⊆ univ.filter (fun k => c.lt k j) := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact trans_of c.lt hk h
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨i, ?_, ?_⟩
  · simp only [mem_filter, mem_univ, true_and]; exact h
  · simp only [mem_filter, mem_univ, true_and]; exact irrefl_of c.lt i

/-- The predecessor rank stays below `d` (its `i`-predecessors avoid `i`, so they fit in
`univ.erase i`). -/
theorem Chamber.predCard_lt (c : Chamber d) (i : Fin d) : c.predCard i < d := by
  haveI := c.sto
  have hsub : univ.filter (fun k => c.lt k i) ⊆ univ.erase i := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    simp only [mem_erase, mem_univ, and_true]
    rintro rfl
    exact absurd hk (irrefl_of c.lt _)
  calc c.predCard i ≤ (univ.erase i).card := Finset.card_le_card hsub
    _ = d - 1 := by rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
    _ < d := Nat.sub_lt (Fin.pos i) Nat.one_pos

/-- The predecessor rank of a direction in the chamber. -/
def Chamber.idx (c : Chamber d) (i : Fin d) : Fin d :=
  ⟨c.predCard i, c.predCard_lt i⟩

/-- The rank recovers the order: `i ≺ j ↔ rank i < rank j`. -/
theorem Chamber.predCard_lt_iff (c : Chamber d) (i j : Fin d) :
    c.predCard i < c.predCard j ↔ c.lt i j := by
  haveI := c.sto
  refine ⟨fun h => ?_, c.predCard_lt_predCard⟩
  rcases trichotomous_of c.lt i j with h' | h' | h'
  · exact h'
  · subst h'; exact absurd h (lt_irrefl _)
  · exact absurd (c.predCard_lt_predCard h') (Nat.lt_asymm h)

/-- The rank is injective, hence (finite endofunction) a permutation. -/
theorem Chamber.idx_injective (c : Chamber d) : Function.Injective c.idx := by
  haveI := c.sto
  intro i j hij
  by_contra hne
  have hval : c.predCard i = c.predCard j := congrArg Fin.val hij
  rcases trichotomous_of c.lt i j with h | h | h
  · exact absurd hval (Nat.ne_of_lt (c.predCard_lt_predCard h))
  · exact hne h
  · exact absurd hval.symm (Nat.ne_of_lt (c.predCard_lt_predCard h))

/-- The permutation of `Fin d` that a chamber encodes: its increasing enumeration, i.e. the
predecessor rank as a bijection. -/
noncomputable def Chamber.toPerm (c : Chamber d) : Equiv.Perm (Fin d) :=
  Equiv.ofBijective c.idx c.idx_injective.bijective_of_finite

/-- The chamber whose order pulls back the standard order of `Fin d` along `σ`. -/
def permChamber (σ : Equiv.Perm (Fin d)) : Chamber d where
  lt i j := σ i < σ j
  decLt i j := inferInstanceAs (Decidable (σ i < σ j))
  sto :=
    { trichotomous := fun _ _ h1 h2 => σ.injective (le_antisymm (not_lt.mp h2) (not_lt.mp h1))
      irrefl := fun i => lt_irrefl (σ i)
      trans := fun _ _ _ hij hjk => lt_trans hij hjk }

/-- The rank of `i` in `permChamber σ` is exactly `σ i`: `#{k | σ k < σ i} = σ i`, since `σ`
carries that predecessor set bijectively onto `Iio (σ i)`. -/
theorem permChamber_predCard (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (permChamber σ).predCard i = (σ i).val := by
  have himg : (univ.filter (fun k => σ k < σ i)).image σ = Iio (σ i) := by
    ext m
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact hk
    · intro hm
      exact ⟨σ.symm m, by rw [Equiv.apply_symm_apply]; exact hm, Equiv.apply_symm_apply σ m⟩
  calc (permChamber σ).predCard i
      = (univ.filter (fun k => σ k < σ i)).card := rfl
    _ = ((univ.filter (fun k => σ k < σ i)).image σ).card :=
        (Finset.card_image_of_injective _ σ.injective).symm
    _ = (Iio (σ i)).card := by rw [himg]
    _ = (σ i).val := by rw [Fin.card_Iio]

/-- A chamber of `□ᵈ` is the same data as a permutation of the `d` directions: the order `≺`
is recovered from its increasing enumeration. -/
noncomputable def chamberPermEquiv (d : ℕ) : Chamber d ≃ Equiv.Perm (Fin d) where
  toFun := Chamber.toPerm
  invFun := permChamber
  left_inv c := by
    apply Chamber.ext
    funext i j
    exact propext (c.predCard_lt_iff i j)
  right_inv σ := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact permChamber_predCard σ i

end CubeChains
