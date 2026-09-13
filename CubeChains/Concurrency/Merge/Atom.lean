import CubeChains.Concurrency.Grading.Coarser
import CubeChains.Concurrency.Merge.MergeBraid

/-!
# Concurrency/Merge/Atom — the atom relation, realised by a composable pair of chain maps

`germ_of_atom` cuts the germ relations down to the products `β * adjT i` with
`permLen (β * adjT i) = permLen β + 1`.  Each of those is a two-step factorisation in `Ch Zbp`

  `𝟙^n ⟶ atomComp n i ⟶ [n]`,

the first step the *other* staircase of a square (`cubeReorder 1 1`, which takes the second
coordinate first) spliced at the beads `i, i+1`, the second an ascent of `β` across that one bead.
`crossPerm_comp` multiplies them, so the pair is the geometry `PosBraid.liftAtom` asks for.
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

/-- `n` as a positive natural — an inhabitant of `Fin (n - 1)` forces `2 ≤ n`. -/
def atomTop (n : ℕ) (i : Fin (n - 1)) : ℕ+ := ⟨n, by have := i.isLt; omega⟩

@[simp] theorem atomTop_coe (n : ℕ) (i : Fin (n - 1)) : ((atomTop n i : ℕ+) : ℕ) = n := rfl

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
  have hi := i.isLt
  obtain ⟨h1, h2⟩ := eq_adj_of_beadAt_eq (d := atomComp n i) (N := n) (j := (i : ℕ) + 1)
    (by omega) (by omega)
    (fun t ht hne => by
      rw [boundaries_atomComp]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), by simpa using hne⟩)
    x.isLt (Fin.lt_def.mp hlt)
    ((index_eq_iff_beadAt (dimSum_atomComp n i) x y).mp (congrArg Fin.val h))
  exact ⟨Fin.ext (by rw [adjLo_val]; omega), Fin.ext (by rw [adjHi_val]; exact h2)⟩

end CubeChains

namespace ChainCat

open CubeChains

variable {a b : List ℕ+} {N : ℕ}

/-! ## Realising a permutation

The two degenerate hom-sets are where the coordinates go: out of the run exactly the permutations
preserving each bead of the target, into one bead exactly those rising inside each bead of the
source.  Every hom-set in between is pinned by those two (`exists_crossPerm_mid`), with no
coordinates at all. -/

/-- **Out of the all-ones shape**: a permutation of the strands preserving each bead of `b` is a
crossing permutation — the parabolic subgroup, as an existence statement at `Fin N`.  Each bead of
`1ᴺ` is one coordinate, so the rising condition is vacuous. -/
theorem exists_crossPerm_ones (hb : dimSum b = N) {σ : Perm (Fin N)}
    (hσ : σ ∈ (dimComp b hb).parabolic) :
    ∃ f : zObj (𝟙^N) ⟶ zObj b, crossPerm (dimSum_replicate N) f = σ := by
  have hpar : ∀ x : Fin N, ((dimComp b hb).index (σ⁻¹ x) : ℕ) = ((dimComp b hb).index x : ℕ) := by
    intro x
    have h := (Composition.mem_parabolic (dimComp b hb)).mp hσ (σ⁻¹ x)
    rw [show σ (σ⁻¹ x) = x by simp] at h
    exact congrArg Fin.val h.symm
  -- `index_monotone` at `b`, pulled back along `σ⁻¹` by the parabolic condition
  have key : ∀ u v : Fin N, (σ⁻¹ u : Fin N) ≤ σ⁻¹ v →
      ((dimComp b hb).index u : ℕ) ≤ ((dimComp b hb).index v : ℕ) := fun u v huv => by
    have hm := (dimComp b hb).index_monotone huv
    simp only [] at hm
    rw [hpar, hpar] at hm
    exact hm
  refine exists_crossPerm_of_blocks (dimSum_replicate N) hb σ (fun p q heq hpq => ?_)
    (fun p q hne => ?_)
  · exfalso
    have hinv : (σ⁻¹ p : Fin N) = σ⁻¹ q :=
      Fin.ext (by rw [← index_ones (σ⁻¹ p), ← index_ones (σ⁻¹ q), heq])
    have : p = q := by simpa using congrArg (⇑σ) hinv
    exact absurd hpq (by rw [this]; exact lt_irrefl _)
  · rw [index_ones, index_ones]
    exact ⟨fun hlt => not_le.mp fun hc => absurd (key q p (Fin.le_def.mpr hc)) (by omega),
      fun hlt => lt_of_le_of_ne (key p q (Fin.le_def.mpr hlt.le)) hne⟩

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

/-- **A permutation realised at both extremes is realised in between** — `exists_crossPerm_mid`,
with the two degenerate hom-sets supplying its outer legs.  `hcoarse` is what makes the middle
hom-set inhabited at all. -/
theorem exists_crossPerm_blocks (ha : dimSum a = N) (hb : dimSum b = N) {σ : Perm (Fin N)}
    (hcoarse : ∀ x y : Fin N, (dimComp a ha).index x = (dimComp a ha).index y →
      (dimComp b hb).index x = (dimComp b hb).index y)
    (hpar : σ ∈ (dimComp b hb).parabolic)
    (hin : ∀ x y : Fin N, (dimComp a ha).index x = (dimComp a ha).index y → x < y → σ x < σ y) :
    ∃ f : zObj a ⟶ zObj b, crossPerm ha f = σ := by
  have hab := nonempty_hom_of_index (a := zObj a) (b := zObj b) ha hb hcoarse
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact hab.elim fun f => ⟨f, Subsingleton.elim _ _⟩
  obtain ⟨t, ht⟩ := exists_crossPerm_eq_one (dimSum_replicate N) (nonempty_hom_ones ha)
  obtain ⟨s, hs⟩ := exists_crossPerm_eq_one hb (nonempty_hom_single (a := zObj b) (m := ⟨N, hN⟩) hb)
  obtain ⟨u, hu⟩ := exists_crossPerm_ones hb hpar
  obtain ⟨g, hg⟩ := exists_crossPerm_single ha (m := ⟨N, hN⟩) rfl hin
  exact exists_crossPerm_mid ht hs hab hu hg

/-! ## The atom

`cubeReorder 1 1` is the *other* wedge-to-tensor comparison of a square: it sends the beads to the
opposite coordinate blocks, so they cross.  Spliced at a cut (`atomHom`) it exchanges exactly the
two strands there and fixes the rest — an adjacent transposition, and by the same token not a
merge. -/

/-- **The reordering staircase swaps its two strands.** -/
theorem pos_coordMap_pairMerge_cubeReorder (y : beadEvent [1, 1]) :
    (pos (coordMap (pairMerge 1 1 (cubeReorder 1 1)) y) : ℕ) = 1 - (pos y : ℕ) := by
  induction y using pairEventCases with
  | h0 k =>
      rw [coordMap_pairMerge_zero, pos_cons_zero, pos_cons_zero]
      exact (faceEmb_cubeReorder_inl 1 1 k).trans (by simp [Nat.lt_one_iff.mp k.isLt])
  | h1 k =>
      rw [coordMap_pairMerge_one, pos_cons_zero, pos_pair_one]
      exact (faceEmb_cubeReorder_inr 1 1 k).trans (by simp [Nat.lt_one_iff.mp k.isLt])

/-- **The atom at a cut swaps the two strands there** — its middle map is `cubeReorder`, which sends
the two beads to the opposite coordinate blocks; the blocks flanking the cut are untouched. -/
theorem crossPerm_atomHom {N : ℕ} (l r : List ℕ+)
    (h : dimSum (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) = N) {x y : Fin N}
    (hx : (x : ℕ) = dimSum l) (hy : (y : ℕ) = dimSum l + 1) :
    crossPerm h (atomHom l r) = Equiv.swap x y := by
  have hd : dimSum ([1, 1] : List ℕ+) = 2 := by simp [dimSum]
  -- away from the cut the swap fixes the strand
  have off : ∀ z : Fin N, (z : ℕ) ≠ dimSum l → (z : ℕ) ≠ dimSum l + 1 →
      (Equiv.swap x y z : ℕ) = (z : ℕ) := fun z h1 h2 =>
    congrArg Fin.val (Equiv.swap_apply_of_ne_of_ne
      (fun hc => h1 ((congrArg Fin.val hc).trans hx))
      (fun hc => h2 ((congrArg Fin.val hc).trans hy)))
  -- `crossPerm_val` at the splice's own spelling: `(atomHom l r).φ` is `rfl`-equal to it, but `rw`
  -- will not unfold `atomHom` to see that
  have key : ∀ e : beadEvent (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r),
      (crossPerm h (atomHom l r) (strand _ h e) : ℕ)
        = (pos (coordMap (splicePhi l r 1 1 (cubeReorder 1 1)) e) : ℕ) :=
    fun e => crossPerm_val h (atomHom l r) (strand_val _ h e)
  refine Equiv.ext fun z => ?_
  obtain ⟨e, rfl⟩ := (strand (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) h).surjective z
  refine Fin.ext ((key e).trans ?_)
  induction e using spliceEventCases with
  | head u =>
      have hs : (strand _ h (eventInl l ((1 : ℕ+) :: (1 : ℕ+) :: r) u) : ℕ) = (pos u : ℕ) :=
        (strand_val _ h _).trans (pos_eventInl l _ u)
      have hu : (pos u : ℕ) < dimSum l := (pos u).isLt
      rw [off _ (by omega) (by omega), pos_coordMap_splicePhi_head, hs]
  | mid v =>
      have hs : (strand _ h (eventInr l ((1 : ℕ+) :: (1 : ℕ+) :: r) (eventInl [1, 1] r v)) : ℕ)
          = dimSum l + (pos v : ℕ) := (strand_val _ h _).trans (pos_eventMid l r 1 1 v)
      have h2 : (pos v : ℕ) < 2 := lt_of_lt_of_eq (pos v).isLt hd
      rw [pos_coordMap_splicePhi_mid, pos_coordMap_pairMerge_cubeReorder v]
      rcases Nat.lt_or_ge (pos v : ℕ) 1 with h1 | h1
      · rw [show strand _ h (eventInr l _ (eventInl [1, 1] r v)) = x from
          Fin.ext (hs.trans (by omega)), Equiv.swap_apply_left, hy]
        omega
      · rw [show strand _ h (eventInr l _ (eventInl [1, 1] r v)) = y from
          Fin.ext (hs.trans (by omega)), Equiv.swap_apply_right, hx]
        omega
  | tail u =>
      have hs : (strand _ h (eventInr l ((1 : ℕ+) :: (1 : ℕ+) :: r) (eventInr [1, 1] r u)) : ℕ)
          = dimSum l + (dimSum ([1, 1] : List ℕ+) + (pos u : ℕ)) :=
        (strand_val _ h _).trans (pos_eventTail l r 1 1 u)
      rw [off _ (by omega) (by omega), pos_coordMap_splicePhi_tail, hs]

/-- **The atom is not a merge** — the two comparisons `cubeMerge`/`cubeReorder` differ, and the
strands at the cut are where. -/
theorem not_W_atomHom (l r : List ℕ+) : ¬ W Zbp (atomHom l r) := fun hW => by
  have hlt : dimSum l + 1 < dimSum (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r) := by
    rw [dimSum_append, dimSum_cons, dimSum_cons]
    simp only [PNat.one_coe]
    omega
  have h1 : Equiv.swap (⟨dimSum l, Nat.lt_of_succ_lt hlt⟩ :
        Fin (dimSum (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r))) ⟨dimSum l + 1, hlt⟩ = 1 :=
    (crossPerm_atomHom l r rfl rfl rfl).symm.trans (crossPerm_eq_one_of_W rfl hW)
  have h2 := congrArg
    (fun σ : Equiv.Perm (Fin (dimSum (l ++ (1 : ℕ+) :: (1 : ℕ+) :: r))) =>
      (σ ⟨dimSum l, Nat.lt_of_succ_lt hlt⟩ : ℕ)) h1
  simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at h2
  omega

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

/-- **The second step**: a `β` that is an ascent across the one double bead sorts `atomComp n i`
into a single cube. -/
theorem exists_crossPerm_of_ascent {n : ℕ} {i : Fin (n - 1)} {β : Perm (Fin n)}
    (hβ : permLen (β * adjT i) = permLen β + 1) :
    ∃ g : zObj (atomComp n i) ⟶ zObj [atomTop n i], crossPerm (dimSum_atomComp n i) g = β :=
  exists_crossPerm_single (dimSum_atomComp n i) (atomTop_coe n i) fun _ _ hxy hlt => by
    obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq n i hxy hlt
    exact ascent_of_permLen_mul_adjT hβ

/-- **The atom relation, geometrically**: every length-additive `β * adjT i` is the crossing
permutation of a composable pair through `atomComp n i` — the hypothesis of `PosBraid.liftAtom`,
realised in `Ch Zbp`. -/
theorem exists_atom_pair {n : ℕ} (i : Fin (n - 1)) {β : Perm (Fin n)}
    (hβ : permLen (β * adjT i) = permLen β + 1) :
    ∃ (f : zObj (𝟙^n) ⟶ zObj (atomComp n i)) (g : zObj (atomComp n i) ⟶ zObj [atomTop n i]),
      crossPerm (dimSum_replicate n) f = adjT i ∧
      crossPerm (dimSum_atomComp n i) g = β ∧
      crossPerm (dimSum_replicate n) (f ≫ g) = β * adjT i := by
  obtain ⟨g, hg⟩ := exists_crossPerm_of_ascent hβ
  exact ⟨atomOnes n i, g, crossPerm_atomOnes n i, hg,
    (crossPerm_comp (dimSum_replicate n) (atomOnes n i) g).trans
      (by rw [crossPerm_atomOnes]; exact congrArg (· * adjT i) hg)⟩

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
