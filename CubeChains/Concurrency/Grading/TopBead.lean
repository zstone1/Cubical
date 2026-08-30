import CubeChains.Concurrency.Merge.AtomPair
import CubeChains.Concurrency.Merge.MergeGenerate

/-!
# Concurrency/Grading/TopBead — the coarsest chain on `n` events, and the arrows into it

One bead coarsens every shape and the run of edges refines every shape, so the merges
`exists_W_to_top` and `exists_W_from_ones` are the two extreme coarsenings, and two merges
with the same endpoints coincide (`eq_of_W`).  Between the two extremes nothing is constrained:
`onesTopEquiv` identifies that hom-set with `Sₙ`, which is where the braid comparison starts.
-/

open CategoryTheory CubeChains BPSet Equiv

namespace ChainCat

variable {n : ℕ}

/-! ### The merges are pinned by their endpoints -/

/-- **A merge is pinned by its endpoints.** -/
theorem eq_of_W {K : BPSet} {a b : Ch K} {f g : a ⟶ b} (hf : W K f) (hg : W K g) :
    f = g := by
  refine hom_ext' (wedgeHom_ext ?_)
  refine Equiv.ext fun e => pos.injective (Fin.ext ?_)
  change (pos (coordMap (Hom.φ f) e) : ℕ) = (pos (coordMap (Hom.φ g) e) : ℕ)
  rw [(W_iff_pos f).mp hf e, (W_iff_pos g).mp hg e]

/-! ### The coarsest chain on `n` events -/

/-- **The coarsest chain on `n` events** — one bead, or, with nothing to fire, no beads at all. -/
def topDims : ℕ → List ℕ+
  | 0 => []
  | (k + 1) => [⟨k + 1, k.succ_pos⟩]

@[simp] theorem dimSum_topDims : ∀ n : ℕ, dimSum (topDims n) = n
  | 0 => rfl
  | (_ + 1) => dimSum_single _

theorem length_topDims : ∀ n : ℕ, (topDims n).length ≤ 1
  | 0 => Nat.zero_le _
  | (_ + 1) => le_rfl

/-! ### The total merge -/

/-- **Every chain merges onto the coarsest chain on its events**: one bead separates nothing, so
the coarsening condition is vacuous. -/
theorem exists_W_to_top (d : List ℕ+) (h : dimSum d = n) :
    ∃ f : zObj d ⟶ zObj (topDims n), W Zbp f := by
  obtain ⟨φ, hφ⟩ := coarser_iff_exists_pos.mp
    ⟨h.trans (dimSum_topDims n).symm, fun x y _ => Fin.ext (by
      have := length_topDims n
      have := (flatEquiv (h.trans (dimSum_topDims n).symm) x).1.isLt
      have := (flatEquiv (h.trans (dimSum_topDims n).symm) y).1.isLt
      omega)⟩
  exact ⟨zHom φ, (W_iff_pos (zHom φ)).mpr hφ⟩

/-- **The total merge** of a chain onto the coarsest chain on its events. -/
noncomputable def totalTo (d : List ℕ+) (h : dimSum d = n) : zObj d ⟶ zObj (topDims n) :=
  (exists_W_to_top d h).choose

theorem W_totalTo (d : List ℕ+) (h : dimSum d = n) :
    W Zbp (totalTo d h) := (exists_W_to_top d h).choose_spec

/-! ### The merge from the finest chain -/

/-- **The merge from the finest chain**: the run of `N` edges merges onto every shape of strand
count `N` — dual to `exists_W_to_top`, and again vacuously, the run's beads being singletons. -/
theorem exists_W_from_ones (b : List ℕ+) {N : ℕ} (h : dimSum b = N) :
    ∃ u : zObj (𝟙^N) ⟶ zObj b, W Zbp u := by
  obtain ⟨φ, hφ⟩ := coarser_iff_exists_pos.mp
    ⟨(dimSum_replicate N).trans h.symm, fun x y hxy =>
      congrArg (fun z => (flatEquiv ((dimSum_replicate N).trans h.symm) z).1)
        (eq_of_fst_of_ones (ones_replicate N) hxy)⟩
  exact ⟨zHom φ, (W_iff_pos (zHom φ)).mpr hφ⟩

/-! ### The simples, out of the run -/

/-- **The simples are `Sₙ`**: between the two extremes nothing is constrained — the run separates
every event and one bead separates none — so an arrow from the run to the coarsest chain *is* its
crossing permutation. -/
noncomputable def onesTopEquiv (n : ℕ) :
    (zObj (𝟙^n) ⟶ zObj (topDims n)) ≃ Perm (Fin n) :=
  serialWedgeFullyFaithful.homEquiv.trans <|
    (wedgeHomEquiv (𝟙^n) (topDims n)).trans <|
      (Equiv.subtypeUnivEquiv fun e => isShuffle_of_ones e fun p q _ => Fin.le_def.mpr (by
        have := length_topDims n
        have := (e p).1.isLt
        have := (e q).1.isLt
        omega)).trans (permOfShuffle (dimSum_replicate n) (dimSum_topDims n))

@[simp] theorem onesTopEquiv_apply (n : ℕ) (f : zObj (𝟙^n) ⟶ zObj (topDims n)) :
    onesTopEquiv n f = crossPerm (dimSum_replicate n) f := rfl

end ChainCat
