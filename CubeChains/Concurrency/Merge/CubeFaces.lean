import CubeChains.Concurrency.Merge.Atom
import CubeChains.Concurrency.Grading.TopBead

/-!
# Concurrency/Merge/CubeFaces — a chain of a cube is an ordered partition of its axes

A shape on `n` events *is* its junction set (`boundaries_injective`, `exists_boundaries_eq`), so
there is a coarsening for every subset of a chain's junctions (`exists_coarsening`), two
coarsenings meet in the intersection of their junction sets (`exists_meet`), and two distinct
codimension-one steps close a square (`exists_join`).

Bead-sharing is stated throughout as **junction membership**: two adjacent ranks lie in one bead of
`c` exactly when `c` has dropped the junction between them, `(i : ℕ) + 1 ∉ boundaries c.dims`.
-/

open CategoryTheory Equiv BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-! ## The meet of two coarsenings

A shape on `n` events *is* its junction set, so the meet of two shapes is the intersection of their
junction sets, with nothing to construct. -/

theorem boundaries_topDims_subset (N : ℕ) : boundaries (topDims N) ⊆ {0, N} := by
  cases N with
  | zero =>
    intro x hx
    have := le_dimSum_of_mem_boundaries hx
    rw [dimSum_topDims] at this
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  | succ k =>
    rw [show topDims (k + 1) = [⟨k + 1, k.succ_pos⟩] from rfl, boundaries_singleton]
    exact fun x hx => hx

/-- **A coarsening with a prescribed shape.**  Every shape whose junctions `a` has is realised by
a coarsening of `a` — the one-bead chain is below it for free, its junctions being `0` and `n`. -/
theorem exists_coarsening {a : Ch (□n)} {m : List ℕ+} (hm : dimSum m = n)
    (hsub : boundaries m ⊆ boundaries a.dims) : ∃ (d : Ch (□n)) (_ : a ⟶ d), d.dims = m := by
  obtain ⟨d, hd, ⟨f⟩, -⟩ := exists_mid_chain (toCubeTop a) hm hsub
    (subset_trans (boundaries_topDims_subset n) fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact zero_mem_boundaries m
      · rw [Finset.mem_singleton.mp hx', ← hm]; exact dimSum_mem_boundaries m)
  exact ⟨d, f, hd⟩

/-- **Two shapes over the same events have a meet** — the shape of the intersected junction sets,
which `exists_boundaries_eq` realises. -/
theorem exists_meet_shape {N : ℕ} {d₁ d₂ : List ℕ+} (h₁ : dimSum d₁ = N) (h₂ : dimSum d₂ = N) :
    ∃ m : List ℕ+, dimSum m = N ∧ boundaries m = boundaries d₁ ∩ boundaries d₂ :=
  exists_boundaries_eq
    (fun _ ht => h₁ ▸ le_dimSum_of_mem_boundaries (Finset.mem_inter.mp ht).1)
    (Finset.mem_inter.mpr ⟨zero_mem_boundaries _, zero_mem_boundaries _⟩)
    (Finset.mem_inter.mpr ⟨h₁ ▸ dimSum_mem_boundaries _, h₂ ▸ dimSum_mem_boundaries _⟩)

/-- **Two coarsenings of a chain meet in one**, carrying the junctions of both. -/
theorem exists_meet {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂) :
    ∃ e : Ch (□n), Nonempty (d₁ ⟶ e) ∧ Nonempty (d₂ ⟶ e) ∧
      boundaries e.dims = boundaries d₁.dims ∩ boundaries d₂.dims := by
  obtain ⟨m, hm, hbm⟩ := exists_meet_shape (dimSum_dims_cube d₁) (dimSum_dims_cube d₂)
  obtain ⟨e, v₁, hed⟩ := exists_coarsening hm (by rw [hbm]; exact Finset.inter_subset_left)
  obtain ⟨e', v₂, hed'⟩ := exists_coarsening hm (by rw [hbm]; exact Finset.inter_subset_right)
  obtain rfl : e = e' := chain_ext_of_dims (u₁ ≫ v₁) (u₂ ≫ v₂) (hed.trans hed'.symm)
  exact ⟨e, ⟨v₁⟩, ⟨v₂⟩, by rw [hed, hbm]⟩

/-! ## Codimension-one faces meet one step up -/

/-- **Two codimension-one refinements of a chain meet in one face**, one further step up from each:
the meet deletes both junctions, and they are distinct. -/
theorem exists_join {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h₁ : codim u₁ = 1) (h₂ : codim u₂ = 1) (hne : d₁ ≠ d₂) :
    ∃ (e : Ch (□n)) (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e), codim v₁ = 1 ∧ codim v₂ = 1 := by
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hb⟩ := exists_meet u₁ u₂
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp ((codim_eq_card_sdiff u₁).symm.trans h₁)
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp ((codim_eq_card_sdiff u₂).symm.trans h₂)
  have hsa : s ∈ boundaries a.dims :=
    (Finset.mem_sdiff.mp (hs ▸ Finset.mem_singleton_self s)).1
  have hta : t ∈ boundaries a.dims :=
    (Finset.mem_sdiff.mp (ht ▸ Finset.mem_singleton_self t)).1
  have hB₁ : boundaries d₁.dims = boundaries a.dims \ {s} := by
    rw [← hs, Finset.sdiff_sdiff_eq_self (boundaries_subset_of_hom u₁)]
  have hB₂ : boundaries d₂.dims = boundaries a.dims \ {t} := by
    rw [← ht, Finset.sdiff_sdiff_eq_self (boundaries_subset_of_hom u₂)]
  have hst : s ≠ t := fun hc =>
    hne (chain_ext_of_dims u₁ u₂ (boundaries_injective (by rw [hB₁, hB₂, hc])))
  -- deleting `s` and deleting `t` differ in exactly the other cut
  have hcut : ∀ {x y : ℕ}, x ≠ y → y ∈ boundaries a.dims →
      (boundaries a.dims \ {x}) \ (boundaries a.dims \ {y}) = {y} := by
    intro x y hxy hy
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not]
    exact ⟨fun h => h.2 h.1.1,
      fun h => ⟨⟨h ▸ hy, fun hc => hxy (hc.symm.trans h)⟩, fun _ => h⟩⟩
  refine ⟨e, v₁, v₂, ?_, ?_⟩
  · rw [codim_eq_card_sdiff, hb, Finset.sdiff_inter_self_left, hB₁, hB₂, hcut hst hta,
      Finset.card_singleton]
  · rw [codim_eq_card_sdiff, hb, Finset.inter_comm, Finset.sdiff_inter_self_left, hB₂, hB₁,
      hcut (Ne.symm hst) hsa, Finset.card_singleton]

end ChainCat
