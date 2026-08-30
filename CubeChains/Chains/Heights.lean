import CubeChains.Chains.ShuffleHom

/-!
# Chains/Heights — a hom-set of serial wedges is an inclusion of boundary sets

Every refinement deletes boundaries and nothing else (`heights_subset_of_hom`, `Chains/Degree`);
conversely every deletion is realised, by merging one junction at a time.  So `coarser_iff` and
`nonempty_hom_iff` reduce the whole hom-set question to an inclusion of `Finset ℕ`.
-/

open CategoryTheory Equiv BPSet CubeChain

namespace CubeChains

/-- **Merging one junction at a time.**  Induct on the boundaries still to be removed. -/
private theorem nonempty_wedgeHom_aux : ∀ (k : ℕ) (d d' : List ℕ+), dimSum d = dimSum d' →
    heights d' ⊆ heights d → (heights d).card ≤ (heights d').card + k →
    Nonempty (⋁d ⟶ ⋁d') := by
  intro k
  induction k with
  | zero =>
      intro d d' _ hsub hk
      obtain rfl := heights_injective (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      exact ⟨𝟙 _⟩
  | succ k ih =>
      intro d d' hdim hsub hk
      by_cases heq : heights d = heights d'
      · obtain rfl := heights_injective heq
        exact ⟨𝟙 _⟩
      obtain ⟨t, htd, htd'⟩ :=
        Finset.exists_of_ssubset (hsub.ssubset_of_ne fun h => heq h.symm)
      have h0 : t ≠ 0 := fun h => htd' (h ▸ zero_mem_heights d')
      have hlast : t ≠ dimSum d := fun h =>
        htd' (by rw [h, hdim]; exact dimSum_mem_heights d')
      obtain ⟨l, r, p, q, rfl, rfl⟩ := exists_split_of_mem_heights d htd h0 hlast
      have hcut := heights_cut l r p q
      have hnm := notMem_heights_cut l r p q
      have hcard : (heights (l ++ p :: q :: r)).card
          = (heights (l ++ (p + q) :: r)).card + 1 := by
        rw [hcut, Finset.card_insert_of_notMem hnm]
      refine (ih (l ++ (p + q) :: r) d' ((dimSum_cut l r p q).symm.trans hdim) ?_ (by omega)).map
        fun ψ => ChainCat.Hom.φ (ChainCat.mergeHom l r p q) ≫ ψ
      intro x hx
      rcases Finset.mem_insert.mp (hcut ▸ hsub hx) with rfl | hx'
      · exact absurd hx htd'
      · exact hx'

end CubeChains

namespace ChainCat

open CubeChains

/-- **A coarsening is an inclusion of boundary sets.** -/
theorem coarser_iff {d d' : List ℕ+} :
    Coarser d d' ↔ dimSum d = dimSum d' ∧ heights d' ⊆ heights d := by
  refine ⟨fun h => ?_, fun ⟨hdim, hsub⟩ => nonempty_wedgeHom_iff_coarser.mp
    (nonempty_wedgeHom_aux (heights d).card d d' hdim hsub (by omega))⟩
  obtain ⟨φ, -⟩ := coarser_iff_exists_pos.mp h
  exact ⟨serialWedge_dimSum_eq φ, heights_subset_of_wedgeHom φ⟩

/-- **The hom-sets of `Ch Zbp` are exactly the coarsenings**: a morphism exists precisely when the
target's boundaries are among the source's. -/
theorem nonempty_hom_iff {a b : Ch Zbp} :
    Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ heights b.dims ⊆ heights a.dims :=
  ⟨fun ⟨f⟩ => ⟨strandsEq f, heights_subset_of_hom f⟩,
   fun h => (nonempty_wedgeHom_iff_coarser.mpr (coarser_iff.mpr h)).map
     fun φ => ⟨φ, Subsingleton.elim _ _⟩⟩

end ChainCat
