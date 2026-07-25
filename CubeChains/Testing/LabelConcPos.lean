import CubeChains.Testing.ExecEquiv

/-!
# Testing/LabelConcPos — `permShadow` is the flattening of `ConcPos`'s crossing map

The graph's label is not arbitrary.  A refinement's block map sends a finer event `⟨i,k⟩` to the
coarser event `⟨refinement i, faceEmb (incl i) k⟩` — and `coordMap_eq` says that map *is* `coordMap`,
i.e. `eventEquiv`, the bijection whose flattening `permOf` (`ConcPos`'s permutation) reads.  Here we
prove `permShadow` computes exactly the canonical flattening `pos = finSigmaFinEquiv` of that block
map, so it agrees with `permOf` up to the flattening convention.

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain StdCube

/-- A bead-dimension prefix sum is the `Fin`-sum over the first `m` beads (the form
`finSigmaFinEquiv` uses). -/
theorem dimPrefix_eq_finSum {K : BPSet} (y : List (Σ n : ℕ+, K.cells (n : ℕ))) :
    ∀ (m : ℕ) (h : m ≤ y.length),
      dimPrefix y m = ∑ i : Fin m, ((y.get (Fin.castLE h i)).1 : ℕ)
  | 0, _ => by simp [dimPrefix]
  | m + 1, h => by
      have hm : m ≤ y.length := Nat.le_of_succ_le h
      have hlt : m < y.length := h
      rw [Fin.sum_univ_castSucc]
      have e1 : (∑ i : Fin m, ((y.get (Fin.castLE h i.castSucc)).1 : ℕ)) = dimPrefix y m := by
        rw [dimPrefix_eq_finSum y m hm]
        exact Finset.sum_congr rfl fun i _ => by congr 1
      rw [e1, dimPrefix, List.take_add_one, List.map_append, List.sum_append, ← dimPrefix]
      congr 1
      rw [List.getElem?_eq_getElem hlt]
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, List.get_eq_getElem, Fin.castLE, Fin.val_last]

/-- **`permShadow` flattens the block map.**  At a finer event `⟨i,k⟩` (canonically flattened by
`pos = finSigmaFinEquiv`), `permShadow` records `pos` of the coarser image `⟨refinement i,
faceEmb (incl i) k⟩` — so it is `pos ∘ (block map) ∘ pos⁻¹`, the flattening `ConcPos`'s `permOf` reads
(`coordMap_eq`). -/
theorem permShadow_flatten {K : BPSet} {a b : K.cells 0}
    {x y : List (Σ n : ℕ+, K.cells (n : ℕ))} (cr : ChainRefine a b x y)
    (i : Fin x.length) (k : Fin ((x.get i).1 : ℕ)) :
    dimPrefix y (cr.refinement i) + ((faceEmb (cr.incl i) k : Fin _) : ℕ)
      = (finSigmaFinEquiv (⟨cr.refinement i, faceEmb (cr.incl i) k⟩ :
          (j : Fin y.length) × Fin ((y.get j).1 : ℕ)) : ℕ) := by
  rw [finSigmaFinEquiv_apply, dimPrefix_eq_finSum]
