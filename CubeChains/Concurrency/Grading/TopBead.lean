import CubeChains.Concurrency.Grading.Coarser
import CubeChains.Concurrency.Grading.ChartHom
import CubeChains.Concurrency.Merge.AtomPair
import CubeChains.Concurrency.Merge.MergeGenerate
import Mathlib.Data.Fintype.Perm

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

/-- **A merge is pinned by its endpoints** — it crosses nothing, and a chain morphism is its
crossing permutation. -/
theorem eq_of_W {K : BPSet} {a b : Ch K} {f g : a ⟶ b} (hf : W K f) (hg : W K g) : f = g :=
  hom_ext_of_crossPerm ((crossPerm_eq_one_of_W rfl hf).trans (crossPerm_eq_one_of_W rfl hg).symm)

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

/-- **The coarsest chain is reachable from every chain on its events** — it has no boundary but
the two ends. -/
theorem nonempty_hom_top (d : List ℕ+) (h : dimSum d = n) :
    Nonempty (zObj d ⟶ zObj (topDims n)) := by
  cases n with
  | zero =>
      refine nonempty_hom_iff.mpr ⟨h, fun t ht => ?_⟩
      obtain ⟨l, r, hlr, rfl⟩ := mem_boundaries_iff.mp ht
      obtain rfl : l = [] := (List.append_eq_nil_iff.mp hlr.symm).1
      exact zero_mem_boundaries d
  | succ k => exact nonempty_hom_single (m := ⟨k + 1, k.succ_pos⟩) h

/-- **Every chain merges onto the coarsest chain on its events**: one bead separates nothing, so
the coarsening condition is vacuous. -/
theorem exists_W_to_top (d : List ℕ+) (h : dimSum d = n) :
    ∃ f : zObj d ⟶ zObj (topDims n), W Zbp f :=
  (exists_crossPerm_eq_one h (nonempty_hom_top d h)).imp fun f hf =>
    (W_iff_crossPerm_eq_one h f).mpr hf

/-! ### The merge from the finest chain -/

/-- **The merge from the finest chain**: the run of `N` edges merges onto every shape of strand
count `N` — dual to `exists_W_to_top`, and again vacuously, the run's beads being singletons. -/
theorem exists_W_from_ones {N : ℕ} (b : Ch Zbp) (h : dimSum b.dims = N) :
    ∃ u : zObj (𝟙^N) ⟶ b, W Zbp u := by
  obtain ⟨d, m⟩ := b
  obtain rfl : m = isTerminalZbp.from (⋁d) := Subsingleton.elim _ _
  exact (exists_crossPerm_eq_one (dimSum_replicate N) (nonempty_hom_ones h)).imp fun u hu =>
    (W_iff_crossPerm_eq_one _ u).mpr hu

/-- **Every chain of every `K` is entered from a run by a merge.**  No hypothesis on `K`: `W` is a
condition on the wedge map alone (`W_iff_monotone_coordMap`), so the base fact carries up the
fibration unchanged.  Hence in `Ch K[W⁻¹]` every object is *isomorphic* to a run-shaped one, for
every `K` whatever. -/
theorem exists_W_run_gen {K : BPSet} (c : Ch K) {N : ℕ} (h : dimSum c.dims = N) :
    ∃ (r : Ch K) (f : r ⟶ c), r.dims = 𝟙^N ∧ W K f := by
  obtain ⟨t, ht⟩ := exists_W_from_ones (zObj c.dims) h
  refine ⟨⟨𝟙^N, t.φ ≫ c.map⟩, ⟨t.φ, rfl⟩, rfl, ?_⟩
  rw [W_iff_monotone_coordMap]
  exact (W_iff_monotone_coordMap t).mp ht

/-! ### The simples, out of the run -/

/-- **The coarsest chain is the cube** — one bead of dimension `n`, or no bead at all. -/
def topWedgeIso : ∀ n : ℕ, ⋁(topDims n) ≅ □n
  | 0 => Iso.refl _
  | (k + 1) => serialWedge1 ⟨k + 1, k.succ_pos⟩

/-- **An arrow from the run to the coarsest chain is a run of the cube**: the coarsest chain *is*
the cube, so such an arrow is a chart of the run in it (`onesChartEquiv`). -/
noncomputable def onesTopChartEquiv (n : ℕ) :
    (zObj (𝟙^n) ⟶ zObj (topDims n)) ≃ Perm (Fin n) :=
  serialWedgeFullyFaithful.homEquiv.trans <|
    ((Iso.refl (⋁(𝟙^n))).homCongr (topWedgeIso n)).trans <|
      (onesChartEquiv n).trans (runPermEquiv n)

/-- **The simples are `Sₙ`**: the hom-set has exactly `n!` elements by `onesTopChartEquiv`, and
`crossPerm` is injective on it, so it is a bijection. -/
noncomputable def onesTopEquiv (n : ℕ) :
    (zObj (𝟙^n) ⟶ zObj (topDims n)) ≃ Perm (Fin n) :=
  haveI : Fintype (zObj (𝟙^n) ⟶ zObj (topDims n)) :=
    Fintype.ofEquiv _ (onesTopChartEquiv n).symm
  Equiv.ofBijective (fun f => crossPerm (dimSum_replicate n) f)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => hom_ext_of_crossPerm h, Fintype.card_congr (onesTopChartEquiv n)⟩)

@[simp] theorem onesTopEquiv_apply (n : ℕ) (f : zObj (𝟙^n) ⟶ zObj (topDims n)) :
    onesTopEquiv n f = crossPerm (dimSum_replicate n) f := rfl

end ChainCat
