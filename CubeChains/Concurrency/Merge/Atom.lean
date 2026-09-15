import CubeChains.Concurrency.Grading.Coarser
import CubeChains.Concurrency.Merge.MergeBraid

/-!
# Concurrency/Merge/Atom — the atom, a single adjacent crossing

`atomComp n i` is the run of `n` edges with the junction `i+1` undone (`boundaries_atomComp`), so
`i, i+1` is the only pair of strands it lets share a bead (`eq_adj_of_index_eq`).  `atomOnes n i` is
the *other* staircase of a square (`cubeReorder 1 1`, which takes the second coordinate first)
spliced at those two beads: it crosses exactly that pair (`crossPerm_atomOnes`), which is why it is
not a merge.

Which atoms lie below a refinement of the run is then a question about its cut set
(`nonempty_hom_atomComp_iff`).
-/

open CategoryTheory Equiv BPSet CubeChain StdCube

namespace CubeChains

variable {n : ℕ}

/-! ## Bead starts of the shapes made of edges -/

/-- Every bead of the run is one coordinate, so its starts are the positions themselves. -/
theorem beadStart_replicate (N j : ℕ) : beadStart (𝟙^N) j = min j N := by
  rw [beadStart, List.take_replicate, dimSum_replicate]

/-- The run separates every position. -/
theorem index_ones {N : ℕ} (x : Fin N) :
    ((dimComp (𝟙^N) (dimSum_replicate N)).index x : ℕ) = (x : ℕ) :=
  index_eq_of_beadStart _ x (by rw [beadStart_replicate]; omega)
    (by rw [beadStart_replicate]; have := x.isLt; omega)

/-! ## The atom composition -/

theorem ones_cons₂ (r : ℕ) : (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^r = 𝟙^(r + 2) := by
  rw [show r + 2 = r + 1 + 1 from rfl, List.replicate_succ, List.replicate_succ]

theorem ones_append (a b : ℕ) : 𝟙^a ++ 𝟙^b = 𝟙^(a + b) := (List.replicate_add a b _).symm

/-- The all-ones shape, cut at one pair of beads. -/
theorem ones_eq_atomCut {n i : ℕ} (h : i + 2 ≤ n) :
    𝟙^n = 𝟙^i ++ (1 : ℕ+) :: (1 : ℕ+) :: 𝟙^(n - 2 - i) := by
  rw [ones_cons₂, ones_append]
  congr 1
  omega

/-- `1ⁱ 2 1^{n-2-i}` — the composition of `n` whose only non-trivial bead is `{i, i+1}`. -/
def atomComp (n : ℕ) (i : Fin (n - 1)) : List ℕ+ := 𝟙^(i : ℕ) ++ (2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ))

@[simp] theorem dimSum_atomComp (n : ℕ) (i : Fin (n - 1)) : dimSum (atomComp n i) = n := by
  have hi := i.isLt
  have h2 : dimSum ((2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ))) = 2 + (n - 2 - (i : ℕ)) := by
    rw [show ((2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ))) = [(2 : ℕ+)] ++ 𝟙^(n - 2 - (i : ℕ)) from rfl,
      dimSum_append, dimSum_single, dimSum_replicate]
    rfl
  rw [show atomComp n i = 𝟙^(i : ℕ) ++ (2 : ℕ+) :: 𝟙^(n - 2 - (i : ℕ)) from rfl,
    dimSum_append, dimSum_replicate, h2]
  omega

@[simp] theorem length_atomComp (N : ℕ) (k : Fin (N - 1)) : (atomComp N k).length = N - 1 := by
  have := k.isLt
  simp only [atomComp, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- **The `k`-th atom's shape drops exactly the junction `k+1`** — it is the run with one cut
undone, so `boundaries_cut` names the boundary it loses. -/
theorem boundaries_atomComp (N : ℕ) (k : Fin (N - 1)) :
    boundaries (atomComp N k) = Finset.range (N + 1) \ {(k : ℕ) + 1} := by
  have hk := k.isLt
  have hins : Finset.range (N + 1) = insert ((k : ℕ) + 1) (boundaries (atomComp N k)) := by
    rw [← ChainCat.boundaries_ones N, ones_eq_atomCut (by omega : (k : ℕ) + 2 ≤ N),
      boundaries_cut, dimSum_replicate, PNat.one_coe]
    rfl
  have hnot : ((k : ℕ) + 1) ∉ boundaries (atomComp N k) := fun hmem => by
    have hc := congrArg Finset.card hins
    rw [Finset.card_range, Finset.insert_eq_self.mpr hmem, card_boundaries, length_atomComp] at hc
    omega
  rw [hins]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun hx => ⟨Or.inr hx, fun hc => hnot (hc ▸ hx)⟩, fun hx => hx.1.resolve_left hx.2⟩

/-- **Only the swapped pair shares a bead of `atomComp n i`** — the shape loses the single junction
`i+1`, and sharing a bead is being on the same side of every junction. -/
theorem eq_adj_of_index_eq (n : ℕ) (i : Fin (n - 1)) {x y : Fin n}
    (h : (dimComp (atomComp n i) (dimSum_atomComp n i)).index x
       = (dimComp (atomComp n i) (dimSum_atomComp n i)).index y) (hlt : x < y) :
    x = adjLo i ∧ y = adjHi i := by
  have hxy : (x : ℕ) < (y : ℕ) := Fin.lt_def.mp hlt
  have hy := y.isLt
  -- nothing between `x` and `y` is a junction, and `i + 1` is the only position that is not one
  have hcut : ∀ t : ℕ, (x : ℕ) < t → t ≤ (y : ℕ) → t = (i : ℕ) + 1 := fun t h1 h2 => by
    by_contra hne
    refine absurd ((index_lt_iff_mem_boundaries (dimSum_atomComp n i) x y).mpr ⟨t, ?_, h1, h2⟩)
      (by rw [h]; exact lt_irrefl _)
    rw [boundaries_atomComp]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), by simpa using hne⟩
  exact ⟨Fin.ext (by have := hcut ((x : ℕ) + 1) (by omega) (by omega); rw [adjLo_val]; omega),
    Fin.ext ((hcut (y : ℕ) hxy le_rfl).trans (adjHi_val i).symm)⟩

end CubeChains

namespace ChainCat

open CubeChains

variable {a : List ℕ+} {N : ℕ}

/-! ## Realising a permutation

Into one bead the crossing permutations are exactly those rising inside each bead of the source:
one bead separates nothing, so the refinement condition of `exists_crossPerm_of_blocks` is
vacuous. -/

/-- **Into a single bead**: a permutation increasing on each bead of `a` is a crossing permutation
— the minimal coset representatives, as an existence statement at `Fin N`.  One bead separates
nothing, so the refinement condition is vacuous. -/
theorem exists_crossPerm_single (ha : dimSum a = N) {m : ℕ+} (hm : (m : ℕ) = N)
    {τ : Perm (Fin N)}
    (hτ : ∀ x y : Fin N, (dimComp a ha).index x = (dimComp a ha).index y → x < y → τ x < τ y) :
    ∃ g : zObj a ⟶ zObj [m], crossPerm ha g = τ := by
  refine exists_crossPerm_of_blocks ha ((dimSum_single m).trans hm) τ (fun p q heq hpq => ?_)
    (fun p q hne => absurd ?_ hne)
  · rcases lt_trichotomy ((τ⁻¹ : Perm (Fin N)) p) ((τ⁻¹ : Perm (Fin N)) q) with hc | hc | hc
    · exact hc
    · exact absurd hpq (by rw [(by simpa using congrArg (⇑τ) hc : p = q)]; exact lt_irrefl _)
    · exact absurd (by simpa using hτ _ _ heq.symm hc : q < p) (asymm hpq)
  · have hz : ∀ x : Fin N,
        ((dimComp ([m] : List ℕ+) ((dimSum_single m).trans hm)).index x : ℕ) = 0 := fun x =>
      index_eq_of_beadStart _ x (by simp [beadStart]) (by
        have := x.isLt
        rw [show (0 : ℕ) + 1 = 1 from rfl, beadStart, List.take_one,
          show ([m] : List ℕ+).head? = some m from rfl]
        simpa [dimSum] using by omega)
    rw [hz, hz]

/-! ## The atom

`cubeReorder 1 1` is the *other* wedge-to-tensor comparison of a square: it sends the beads to the
opposite coordinate blocks, so they cross.  Spliced at a cut (`atomHom`) it exchanges exactly the
two strands there and fixes the rest — an adjacent transposition, and by the same token not a
merge. -/

/-- **The reordering staircase swaps its two strands** — its first bead on the tail block, its
second on the head block. -/
theorem pos_coordMap_spliceNil_cubeReorder (r : List ℕ+) (e : beadEvent (1 :: 1 :: r)) :
    (pos (coordMap (spliceNil r 1 1 (cubeReorder 1 1)) e) : ℕ)
      = if (pos e : ℕ) = 0 then 1 else if (pos e : ℕ) = 1 then 0 else (pos e : ℕ) := by
  induction e using spliceEventCases with
  | h0 k =>
      rw [pos_coordMap_spliceNil_zero, pos_cons_zero]
      exact (faceEmb_cubeReorder_inl 1 1 k).trans (by have := k.isLt; simp at this ⊢)
  | h1 k =>
      have hk : (k : ℕ) = 0 := by
        have hlt : (k : ℕ) < 1 := k.isLt
        omega
      have hp : (pos (⟨1, k⟩ : beadEvent (1 :: 1 :: r)) : ℕ) = 1 :=
        (pos_cons_succ 1 (1 :: r) 0 k).trans (by rw [pos_cons_zero, hk]; rfl)
      rw [pos_coordMap_spliceNil_one, hp]
      exact (faceEmb_cubeReorder_inr 1 1 k).trans hk
  | ht j k =>
      rw [pos_coordMap_spliceNil_tail, pos_cons_succ, pos_cons_succ]
      simp only [PNat.add_coe, PNat.one_coe]
      split_ifs <;> omega

/-- **The atom at a cut swaps the two strands there** — a splice fixes the events in front of its
cut and moves the rest as `cubeReorder` does. -/
theorem crossPerm_atomHom {N : ℕ} (l r : List ℕ+)
    (h : dimSum (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) = N) {x y : Fin N}
    (hx : (x : ℕ) = dimSum l) (hy : (y : ℕ) = dimSum l + 1) :
    crossPerm h (atomHom l r) = Equiv.swap x y := by
  refine Equiv.ext fun z => Fin.ext ?_
  have he : (z : ℕ) = (pos ((strand _ h).symm z) : ℕ) :=
    (congrArg Fin.val ((strand _ h).apply_symm_apply z)).symm.trans (strand_val _ h _)
  rw [crossPerm_val h _ he]
  refine (pos_coordMap_splicePhi r 1 1 (cubeReorder 1 1)
    (fun x => if x = 0 then 1 else if x = 1 then 0 else x)
    (pos_coordMap_spliceNil_cubeReorder r) l _).trans ?_
  rw [← he, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> simp only [Fin.ext_iff] at * <;> omega

/-- **The atom at a cut of two edges**, at any spelling of its endpoints: `atomHom` has the cut
built into its type, so a word given in another shape is transported into it. -/
def atomAt {d e : List ℕ+} (l r : List ℕ+) (hd : d = l ++ (1 : ℕ+) :: (1 : ℕ+) :: r)
    (he : e = l ++ (2 : ℕ+) :: r) : zObj d ⟶ zObj e :=
  eqToHom (congrArg zObj hd) ≫ atomHom l r ≫ eqToHom (congrArg zObj he.symm)

/-- **A transported atom swaps the two strands at its cut** — `crossPerm_atomHom`, with the
endpoints respelled. -/
theorem crossPerm_atomAt {d e : List ℕ+} {N : ℕ} {l r : List ℕ+}
    (hd : d = l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) (he : e = l ++ (2 : ℕ+) :: r) (h : dimSum d = N)
    {x y : Fin N} (hx : (x : ℕ) = dimSum l) (hy : (y : ℕ) = dimSum l + 1) :
    crossPerm h (atomAt l r hd he) = Equiv.swap x y := by
  subst hd
  subst he
  rw [atomAt, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact crossPerm_atomHom l r h hx hy

/-- **The `i`-th atom**: the reordering staircase spliced at the beads `i, i+1` of the run. -/
def atomOnes (n : ℕ) (i : Fin (n - 1)) : zObj (𝟙^n) ⟶ zObj (atomComp n i) :=
  atomAt 𝟙^(i : ℕ) 𝟙^(n - 2 - (i : ℕ)) (ones_eq_atomCut (by have := i.isLt; omega)) rfl

@[simp] theorem crossPerm_atomOnes (n : ℕ) (i : Fin (n - 1)) :
    crossPerm (dimSum_replicate n) (atomOnes n i) = adjT i :=
  crossPerm_atomAt _ _ _ (by rw [adjLo_val, dimSum_replicate])
    (by rw [adjHi_val, dimSum_replicate])

theorem degree_ones (N : ℕ) : degree (zObj (𝟙^N)) = 0 :=
  (degree_eq_zero_iff _).mpr fun _ hd => List.eq_of_mem_replicate hd

/-- **The atom merges two beads into one**: one bead of size two among `N - 1` beads. -/
theorem degree_atomComp (N : ℕ) (k : Fin (N - 1)) : degree (zObj (atomComp N k)) = 1 := by
  have := k.isLt
  have h := ChainCat.degree_add_length (zObj (atomComp N k))
  rw [zObj_dims, dimSum_atomComp, length_atomComp] at h
  omega

/-- **The atom is one cut** — `codim` reads only the two endpoints, and the atom loses one bead. -/
theorem codim_atomOnes (N : ℕ) (k : Fin (N - 1)) : codim (atomOnes N k) = 1 := by
  rw [codim, degree_atomComp, degree_ones]

/-- Distinct adjacent transpositions — the swaps are pinned by where they move `k`. -/
theorem adjT_inj {n : ℕ} {i j : Fin (n - 1)} (h : adjT i = adjT j) : (i : ℕ) = (j : ℕ) := by
  have h1 : ((adjT i (adjLo i) : Fin n) : ℕ) = ((adjT j (adjLo i) : Fin n) : ℕ) :=
    congrArg (fun σ : Perm (Fin n) => ((σ (adjLo i) : Fin n) : ℕ)) h
  simp only [adjT_val, adjLo_val] at h1
  split_ifs at h1 <;> omega

/-! ## Counting the atoms below a cell

Which atoms sit below a shape is a question about junctions, so it is answered on `boundaries`
and read back as atom indices. -/

/-- **The atoms below a refinement of the run are exactly its cuts.**  The `k`-th atom drops the
junction `k+1` and nothing else, so it lands under `d` precisely when `d` has dropped it too. -/
theorem nonempty_hom_atomComp_iff {N : ℕ} {d : Ch Zbp} (f : zObj (𝟙^N) ⟶ d) (k : Fin (N - 1)) :
    Nonempty (zObj (atomComp N k) ⟶ d) ↔ (k : ℕ) + 1 ∈ cutsOf f := by
  have hk := k.isLt
  have hdimd : dimSum d.dims = N := by
    have := dimSum_eq_of_hom f
    rw [zObj_dims, dimSum_replicate] at this
    exact this.symm
  have hran : boundaries d.dims ⊆ Finset.range (N + 1) := by
    have := boundaries_subset_of_hom f
    rwa [zObj_dims, boundaries_ones] at this
  rw [nonempty_hom_iff, zObj_dims, dimSum_atomComp, hdimd, boundaries_atomComp, cutsOf, zObj_dims,
    boundaries_ones, Finset.mem_sdiff, Finset.subset_sdiff]
  simp only [Finset.disjoint_singleton_right, Finset.mem_range, true_and, and_iff_right hran,
    and_iff_right (show (k : ℕ) + 1 < N + 1 by omega)]

/-- **Exactly two atoms lie below a codimension-two refinement of the run** — its two cuts, read as
atom indices. -/
theorem exists_atomPair_of_codim_two {N : ℕ} {d : Ch Zbp} (f : zObj (𝟙^N) ⟶ d)
    (hcod : codim f = 2) :
    ∃ i j : Fin (N - 1), (i : ℕ) < (j : ℕ) ∧
      ∀ k : Fin (N - 1), Nonempty (zObj (atomComp N k) ⟶ d) ↔ (k = i ∨ k = j) := by
  obtain ⟨s, t, hs0, hst, htN, hcut⟩ := exists_cutsOf_eq_pair f hcod
  refine ⟨⟨s - 1, by omega⟩, ⟨t - 1, by omega⟩, show s - 1 < t - 1 by omega, fun k => ?_⟩
  have hk := k.isLt
  rw [nonempty_hom_atomComp_iff f k, hcut, Finset.mem_insert, Finset.mem_singleton]
  simp only [Fin.ext_iff]
  omega

end ChainCat
