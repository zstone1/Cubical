import CubeChains.Concurrency.Merge.AtomPair
import CubeChains.Concurrency.Merge.MergeGenerate

/-!
# Concurrency/Grading/TopBead — the coarsest chain on `n` events, and the arrows into it

One bead coarsens every shape and the run of edges refines every shape, so the merges
`exists_W_to_top` and `exists_W_from_ones` are the two extreme coarsenings, and two merges
with the same endpoints coincide (`eq_of_W`).  Between the two extremes nothing constrains the
bijection at all, so `arrowOnes` names an arrow per permutation, and `crossPermAt_injective` says
an arrow into the coarsest chain **is** its permutation.
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

/-- **Between the two extremes nothing is constrained**: the run separates every event and one
bead separates none, so every bijection is a shuffle. -/
theorem exists_arrowOnes (n : ℕ) (σ : Perm (Fin n)) :
    ∃ f : zObj (𝟙^n) ⟶ zObj (topDims n), crossPermAt (dimSum_replicate n) f = σ := by
  have hd : dimSum (𝟙^n) = dimSum (topDims n) :=
    (dimSum_replicate n).trans (dimSum_topDims n).symm
  set τ := ((finCongr (dimSum_replicate n)).permCongr).symm σ with hτ
  obtain ⟨f, hf⟩ := (exists_crossPerm_eq hd τ).mpr
    (isShuffle_of_ones _ fun p q _ => Fin.le_def.mpr (by
      have := length_topDims n
      have := ((permOfShuffle hd).symm τ p).1.isLt
      have := ((permOfShuffle hd).symm τ q).1.isLt
      omega))
  exact ⟨f, crossPerm_eq_iff_crossPermAt.mp hf⟩

/-- **The arrow out of the run realising a permutation** — unique, by `crossPermAt_injective`. -/
noncomputable def arrowOnes (n : ℕ) (σ : Perm (Fin n)) :
    zObj (𝟙^n) ⟶ zObj (topDims n) := (exists_arrowOnes n σ).choose

@[simp] theorem crossPermAt_arrowOnes (n : ℕ) (σ : Perm (Fin n)) :
    crossPermAt (dimSum_replicate n) (arrowOnes n σ) = σ := (exists_arrowOnes n σ).choose_spec

end ChainCat
