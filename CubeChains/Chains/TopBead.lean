import CubeChains.Chains.AtomPair
import CubeChains.Chains.MergeGenerate

/-!
# Chains/TopBead — the coarsest chain on `n` events, and the arrows into it

A merge is an arrow with trivial crossing permutation (`Winf_iff_crossPerm_eq_one`), so the merges
out of every chain (`exists_Winf_to_top`) and into every chain out of the run of edges
(`exists_Winf_from_ones`) are the identity case of the classification in `Chains/AtomPair`, and two
merges with the same endpoints coincide (`eq_of_Winf`).  Out of the run nothing constrains the
permutation, so `arrowOnes` names an arrow per permutation, and `crossPermAt_injective` says an
arrow into the coarsest chain **is** its permutation.
-/

open CategoryTheory CubeChains BPSet Equiv

namespace ChainCat

variable {n : ℕ}

/-! ### The merges are pinned by their endpoints -/

/-- **A merge is pinned by its endpoints.** -/
theorem eq_of_Winf {K : BPSet} {a b : Ch K} {f g : a ⟶ b} (hf : Winf K f) (hg : Winf K g) :
    f = g := by
  refine hom_ext' (wedgeHom_ext ?_)
  refine Equiv.ext fun e => pos.injective (Fin.ext ?_)
  change (pos (coordMap (Hom.φ f) e) : ℕ) = (pos (coordMap (Hom.φ g) e) : ℕ)
  rw [(Winf_iff_pos f).mp hf e, (Winf_iff_pos g).mp hg e]

/-! ### The coarsest chain on `n` events -/

/-- **The coarsest chain on `n` events** — one bead, or, with nothing to fire, no beads at all. -/
def topDims : ℕ → List ℕ+
  | 0 => []
  | (k + 1) => [⟨k + 1, k.succ_pos⟩]

@[simp] theorem dimSum_topDims : ∀ n : ℕ, dimSum (topDims n) = n
  | 0 => rfl
  | (_ + 1) => dimSum_single _

/-! ### The total merge -/

/-- **Every chain merges onto the coarsest chain on its events**: the arrow realising the identity
permutation. -/
theorem exists_Winf_to_top (d : List ℕ+) (h : dimSum d = n) :
    ∃ f : zObj d ⟶ zObj (topDims n), Winf Zbp f := by
  cases n with
  | zero =>
      obtain rfl := dimSum0_nil d h
      exact ⟨𝟙 _, (Winf Zbp).id_mem _⟩
  | succ k =>
      exact (exists_crossPermAt_single (m := ⟨k + 1, k.succ_pos⟩) h rfl (τ := 1)
        fun _ _ _ hlt => hlt).imp fun _ hf =>
          (Winf_iff_crossPerm_eq_one _).mpr (crossPermAt_eq_one_iff.mp hf)

/-- **The total merge** of a chain onto the coarsest chain on its events. -/
noncomputable def totalTo (d : List ℕ+) (h : dimSum d = n) : zObj d ⟶ zObj (topDims n) :=
  (exists_Winf_to_top d h).choose

theorem Winf_totalTo (d : List ℕ+) (h : dimSum d = n) :
    Winf Zbp (totalTo d h) := (exists_Winf_to_top d h).choose_spec

/-! ### The merge from the finest chain -/

/-- **The merge from the finest chain**: the run of `N` edges merges onto every shape of strand
count `N` — dual to `exists_Winf_to_top`, and again the identity permutation. -/
theorem exists_Winf_from_ones (b : List ℕ+) {N : ℕ} (h : dimSum b = N) :
    ∃ u : zObj (𝟙^N) ⟶ zObj b, Winf Zbp u :=
  (exists_crossPermAt_ones h (Subgroup.one_mem _)).imp fun _ hu =>
    (Winf_iff_crossPerm_eq_one _).mpr (crossPermAt_eq_one_iff.mp hu)

/-! ### The simples, out of the run -/

/-- Out of the run, all beads are singletons, so nothing constrains the permutation. -/
theorem exists_arrowOnes (n : ℕ) (σ : Perm (Fin n)) :
    ∃ f : zObj (𝟙^n) ⟶ zObj (topDims n), crossPermAt (dimSum_replicate n) f = σ := by
  cases n with
  | zero => exact ⟨𝟙 _, Equiv.ext fun i => i.elim0⟩
  | succ k =>
      refine exists_crossPermAt_single (m := ⟨k + 1, k.succ_pos⟩) (dimSum_replicate (k + 1))
        rfl ?_
      intro x y hxy hlt
      rw [List.map_replicate] at hxy
      simp only [PNat.one_coe, blockOfPos_replicate_one] at hxy
      rw [if_pos x.isLt, if_pos y.isLt] at hxy
      exact absurd (Fin.ext hxy) (ne_of_lt hlt)

/-- **The arrow out of the run realising a permutation** — unique, by `crossPermAt_injective`. -/
noncomputable def arrowOnes (n : ℕ) (σ : Perm (Fin n)) :
    zObj (𝟙^n) ⟶ zObj (topDims n) := (exists_arrowOnes n σ).choose

@[simp] theorem crossPermAt_arrowOnes (n : ℕ) (σ : Perm (Fin n)) :
    crossPermAt (dimSum_replicate n) (arrowOnes n σ) = σ := (exists_arrowOnes n σ).choose_spec

end ChainCat
