import CubeChains.Concurrency.Presentation.RunAtoms
import CubeChains.Concurrency.Grading.CodimTwo

/-!
# Concurrency/Presentation/PairChain — the codimension-two chain of two cuts

A shape is its junction set (`exists_boundaries_eq`), so two cuts name the chain that has lost
exactly their two junctions (`pairChain`): a square when they are apart, a hexagon when they are
adjacent.  It is the only degree-two chain both atoms reach (`eq_pairChain`), and it lies under
every chain both atoms reach, carrying any run that ascends at both cuts (`exists_pairLeg`).
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {n : ℕ}

/-! ## The chain -/

private theorem exists_pairShape (n : ℕ) (i j : Fin (n - 1)) :
    ∃ d : List ℕ+, dimSum d = n ∧
      boundaries d = Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} := by
  have := i.isLt
  have := j.isLt
  exact exists_boundaries_eq (fun t ht => by simp at ht; omega) (by simp) (by simp; omega)

/-- **The chain the cuts `i` and `j` share** — the run with the junctions `i + 1` and `j + 1`
undone. -/
noncomputable def pairChain (n : ℕ) (i j : Fin (n - 1)) : Ch Zbp :=
  zObj (exists_pairShape n i j).choose

variable (i j : Fin (n - 1))

theorem dimSum_pairChain : dimSum (pairChain n i j).dims = n :=
  (exists_pairShape n i j).choose_spec.1

/-- **The pair chain's own junctions.** -/
theorem boundaries_pairChain :
    boundaries (pairChain n i j).dims = Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} :=
  (exists_pairShape n i j).choose_spec.2

variable {i j}

theorem degree_pairChain (hij : (i : ℕ) ≠ (j : ℕ)) : degree (pairChain n i j) = 2 := by
  have := i.isLt
  have := j.isLt
  have hc := congrArg Finset.card (boundaries_pairChain i j)
  rw [card_boundaries, Finset.card_sdiff_of_subset (by intro t; simp; omega), Finset.card_range,
    Finset.card_pair_eq_two_iff.mpr (by omega)] at hc
  have h := degree_add_length (pairChain n i j)
  rw [dimSum_pairChain] at h
  omega

/-- **An atom reaches the pair chain of its own cut.** -/
private theorem nonempty_atomComp_pairChain {k : Fin (n - 1)} (hk : k = i ∨ k = j) :
    Nonempty (zObj (atomComp n k) ⟶ pairChain n i j) :=
  nonempty_hom_iff.mpr ⟨(dimSum_atomComp n k).trans (dimSum_pairChain i j).symm, fun t => by
    rw [boundaries_pairChain, zObj_dims, boundaries_atomComp]
    rcases hk with rfl | rfl <;> simp +contextual⟩

theorem nonempty_left_pairChain : Nonempty (zObj (atomComp n i) ⟶ pairChain n i j) :=
  nonempty_atomComp_pairChain (Or.inl rfl)

theorem nonempty_right_pairChain : Nonempty (zObj (atomComp n j) ⟶ pairChain n i j) :=
  nonempty_atomComp_pairChain (Or.inr rfl)

/-- **A chain of degree two below both atoms is the pair chain** — out of the run it cuts exactly
the two junctions, and a shape is its junction set. -/
theorem eq_pairChain (hij : (i : ℕ) ≠ (j : ℕ)) {w : Ch Zbp} (hdeg : degree w = 2)
    (hi : Nonempty (zObj (atomComp n i) ⟶ w)) (hj : Nonempty (zObj (atomComp n j) ⟶ w)) :
    w = pairChain n i j := by
  have hw : dimSum w.dims = n := (dimSum_eq_of_hom hi.some).symm.trans (dimSum_atomComp n i)
  have hcuts : cutsOf (runMerge w hw) = {(i : ℕ) + 1, (j : ℕ) + 1} :=
    (Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨(nonempty_hom_atomComp_iff _ i).mp hi,
        Finset.singleton_subset_iff.mpr ((nonempty_hom_atomComp_iff _ j).mp hj)⟩)
      (by rw [card_cutsOf, codim, hdeg, degree_ones, Finset.card_pair_eq_two_iff.mpr
        (by omega)])).symm
  exact Obj.eq_of_dims (boundaries_injective ((boundaries_sdiff_cutsOf (runMerge w hw)).trans
    (by rw [hcuts, zObj_dims, boundaries_ones, boundaries_pairChain])))

/-! ## Its beads, and the leg it has into every chain both atoms reach

A bead of the pair chain is crossed only at `i` or at `j`, so both the comparison the hom-set asks
for and the ascent condition `exists_crossPerm_single` asks for are statements about those two
cuts alone. -/

/-- **Two coordinates share a bead of the pair chain only across `i` or across `j`.** -/
theorem pairChain_bead {x y : Fin n}
    (h : ((dimComp (pairChain n i j).dims (dimSum_pairChain i j)).index x : ℕ)
      = ((dimComp (pairChain n i j).dims (dimSum_pairChain i j)).index y : ℕ))
    {t : ℕ} (h1 : (x : ℕ) < t) (h2 : t ≤ (y : ℕ)) : t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1 := by
  have hno : ¬ ∃ s ∈ boundaries (pairChain n i j).dims, (x : ℕ) < s ∧ s ≤ (y : ℕ) := by
    rw [← index_lt_iff_mem_boundaries (dimSum_pairChain i j)]
    omega
  have hmem : t ∉ boundaries (pairChain n i j).dims := fun hc => hno ⟨t, hc, h1, h2⟩
  rw [boundaries_pairChain, Finset.mem_sdiff] at hmem
  have hy := y.isLt
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, not_and, not_not] at hmem
  exact hmem (by omega)

/-- **A leg from the pair chain into every chain both atoms reach**, carrying the merge run to a
given run that ascends at both cuts: the atoms put `d`'s junctions among the pair chain's, and a
bead of the pair chain is crossed only at the two cuts (`exists_crossPerm_of_rise`). -/
theorem exists_pairLeg {d : Ch Zbp}
    (hi : Nonempty (zObj (atomComp n i) ⟶ d)) (hj : Nonempty (zObj (atomComp n j) ⟶ d))
    {σ : Perm (Fin n)}
    (hasc : ∀ k : Fin (n - 1), (k : ℕ) = (i : ℕ) ∨ (k : ℕ) = (j : ℕ) → σ (adjLo k) < σ (adjHi k))
    {a : zObj (𝟙^n) ⟶ d} (ha : crossPerm (dimSum_replicate n) a = σ) :
    ∃ t : pairChain n i j ⟶ d, crossPerm (dimSum_pairChain i j) t = σ :=
  exists_crossPerm_of_rise (dimSum_pairChain i j)
    (nonempty_hom_iff.mpr ⟨(dimSum_pairChain i j).trans (dimSum_eq_of_onesHom a).symm,
      fun t ht => by
        have hti := (nonempty_hom_iff.mp hi).2 ht
        have htj := (nonempty_hom_iff.mp hj).2 ht
        rw [zObj_dims, boundaries_atomComp] at hti htj
        rw [zObj_dims, boundaries_pairChain]
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hti htj ⊢
        tauto⟩)
    (fun x y h hxy => rel_of_span (P := fun t => t = (i : ℕ) + 1 ∨ t = (j : ℕ) + 1)
      (R := fun p q => σ p < σ q) (fun _ _ _ => lt_trans) (fun k hk => hasc k (by omega)) x y
      (Fin.lt_def.mp hxy) fun _ => pairChain_bead (congrArg Fin.val h)) ha

/-! ## The two species of the pair chain

`boundaries` pins a shape, and the pair chain's boundaries are the run's minus `i+1` and `j+1` — so
consecutive cuts leave one bead of three and cuts apart two of two. -/

/-- **Consecutive cuts share a hexagon** — one bead of three, and edges either side. -/
theorem dims_pairChain_of_adj (hadj : (j : ℕ) = (i : ℕ) + 1 ∨ (i : ℕ) = (j : ℕ) + 1) :
    ∃ p q : ℕ, (pairChain n i j).dims = 𝟙^p ++ (3 : ℕ+) :: 𝟙^q := by
  have hi := i.isLt
  have hj := j.isLt
  rcases hadj with h | h
  · refine ⟨(i : ℕ), n - (i : ℕ) - 3, boundaries_injective ?_⟩
    rw [boundaries_pairChain, boundaries_three_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  · refine ⟨(j : ℕ), n - (j : ℕ) - 3, boundaries_injective ?_⟩
    rw [boundaries_pairChain, boundaries_three_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega

/-- **Cuts that are apart share a square** — two beads of two, with edges between and around. -/
theorem dims_pairChain_of_apart (hfar : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) :
    ∃ p m q : ℕ,
      (pairChain n i j).dims = 𝟙^p ++ (2 : ℕ+) :: (𝟙^m ++ (2 : ℕ+) :: 𝟙^q) := by
  have hi := i.isLt
  have hj := j.isLt
  rcases hfar with h | h
  · refine ⟨(i : ℕ), (j : ℕ) - (i : ℕ) - 2, n - (j : ℕ) - 2, boundaries_injective ?_⟩
    rw [boundaries_pairChain, boundaries_two_two_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  · refine ⟨(j : ℕ), (i : ℕ) - (j : ℕ) - 2, n - (i : ℕ) - 2, boundaries_injective ?_⟩
    rw [boundaries_pairChain, boundaries_two_two_bead]
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega

end ChainCat
