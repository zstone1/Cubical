import CubeChains.Concurrency.Merge.CubeWeakOrder

/-!
# Concurrency/Merge/CubeFaces — a chain of a cube is an ordered partition of its axes

`cross c = (flatten c)⁻¹` (`cross_eq_flatten_inv`): a chain's crossing permutation is its own firing
order, read backwards, and a coarsening's beads are its shape's blocks read in that order
(`beadOf_of_hom`).  Hence the normal form `cross_eq_of_sort`: a coarsening re-sorts the source's
firing order inside each block, so naming the sorting permutation names the coarsening's `cross`.

Two coarsenings meet in one (`exists_meet`); the meet of two atoms out of a run deletes exactly
their two junctions (`boundaries_of_meet`), so the sorting permutation there is the product of the
two swaps — `cross_of_meet_far`, `cross_of_meet_braid`, on the nose.
-/

open CategoryTheory Equiv BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-! ## `cross` is the firing order, read backwards -/

/-- The one-bead chain fires in the cube's own order. -/
@[simp] theorem flatten_cubeTop (n : ℕ) : flatten (cubeTop n) = 1 := by
  have hlen : (cubeTop n).dims.length ≤ 1 := length_topDims n
  have hbead : ∀ x y : Fin n, beadOf (cubeTop n) x = beadOf (cubeTop n) y := fun x y =>
    Fin.ext (by
      have hx := (beadOf (cubeTop n) x).isLt
      have hy := (beadOf (cubeTop n) y).isLt
      omega)
  refine Equiv.ext fun q => ?_
  simpa using flatten_apply (cubeTop n) 1 (fun x y hxy => Or.inr ⟨hbead _ _, hxy⟩) q

/-- **The crossing permutation of a chain is its firing order, inverted.**  Its refinement of the
one-bead chain takes the chain's order to the cube's, and `crossPerm` compares the two charts. -/
theorem cross_eq_flatten_inv (c : Ch (□n)) : cross c = (flatten c)⁻¹ := by
  have hc : (⟨c.dims, Hom.φ (toCubeTop c) ≫ (cubeTop n).map⟩ : Ch (□n)) = c := by
    obtain ⟨d, x⟩ := c
    change (⟨d, (x ≫ (topWedgeIso n).inv) ≫ (topWedgeIso n).hom⟩ : Ch (□n)) = ⟨d, x⟩
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have htop : ∀ q : Fin n,
      flatten (⟨(cubeTop n).dims, (cubeTop n).map⟩ : Ch (□n)) q = q := fun q => by
    rw [show (⟨(cubeTop n).dims, (cubeTop n).map⟩ : Ch (□n)) = cubeTop n from rfl, flatten_cubeTop]
    rfl
  refine Equiv.ext fun y => ?_
  obtain ⟨q, rfl⟩ := (flatten c).surjective y
  have h := crossPerm_flatten (dimSum_dims_cube c) (toCubeTop c) (cubeTop n).map q
  rw [hc, htop q] at h
  rw [show ((flatten c)⁻¹ : Equiv.Perm (Fin n)) ((flatten c) q) = q from by simp]
  exact h

/-- …the same equation solved for `flatten`, which is the direction every consumer wants. -/
theorem flatten_eq_cross_inv (c : Ch (□n)) : flatten c = (cross c)⁻¹ := by
  rw [cross_eq_flatten_inv, inv_inv]

/-- **A run's beads are its firing order**: one coordinate per bead, so `beadOf` is `cross`
inverted. -/
theorem beadOf_run {r : Ch (□n)} (hr : ∀ d ∈ r.dims, d = 1) (q : Fin n) :
    (beadOf r q : ℕ) = ((cross r)⁻¹ q : ℕ) := by
  obtain ⟨hlo, hhi⟩ := flatten_mem_bead r q
  rw [beadStart_ones hr (beadOf r q).isLt.le] at hlo
  rw [beadStart_ones hr (by have := (beadOf r q).isLt; omega)] at hhi
  have hf : (flatten r q : ℕ) = ((cross r)⁻¹ q : ℕ) := by rw [flatten_eq_cross_inv]
  omega

/-! ## A coarsening's beads are its shape's blocks -/

private theorem beadStart_le_dimSum (d : List ℕ+) (j : ℕ) : beadStart d j ≤ dimSum d := by
  rcases le_or_gt j d.length with hj | hj
  · exact le_dimSum_of_mem_boundaries (beadStart_mem_boundaries d hj)
  · rw [beadStart, List.take_of_length_le hj.le]

private theorem card_flatten_lt (A : Ch (□n)) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter fun r : Fin n => (flatten A r : ℕ) < k).card = k := by
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [Finset.filter_true_of_mem fun r _ => (flatten A r).isLt, Finset.card_univ,
      Fintype.card_fin]
  · simpa [Fin.lt_def] using Equiv.Perm.card_filter_lt (flatten A) ⟨k, hlt⟩

/-- **A coarsening's beads are its shape's blocks, read in the source's firing order.**  Both are
down-sets for that order with the same counts, so they agree; the target's own chart never
appears. -/
theorem beadOf_of_hom {A M : Ch (□n)} (f : A ⟶ M) (q : Fin n) :
    (beadOf M q : ℕ) = ((dimComp M.dims (wedgeDimSum_eq M.map)).index (flatten A q) : ℕ) := by
  have hmono : ∀ r s : Fin n, (flatten A r : ℕ) ≤ (flatten A s : ℕ) →
      (beadOf M r : ℕ) ≤ (beadOf M s : ℕ) := by
    intro r s hrs
    refine beadOf_le_of_hom f ?_
    rcases eq_or_lt_of_le hrs with heq | hlt
    · have hrs' : r = s := (flatten A).injective (Fin.ext heq)
      rw [hrs']
    · rcases (flatten_lt_iff A).mp (Fin.lt_def.mpr hlt) with h | ⟨h, -⟩
      · exact le_of_lt h
      · rw [h]
  have hn : dimSum M.dims = n := wedgeDimSum_eq M.map
  have hset : ∀ j : ℕ, (Finset.univ.filter fun r : Fin n => (beadOf M r : ℕ) < j)
      = Finset.univ.filter fun r : Fin n => (flatten A r : ℕ) < beadStart M.dims j := by
    intro j
    have hst : beadStart M.dims j ≤ n := le_of_le_of_eq (beadStart_le_dimSum M.dims j) hn
    have hcT : (Finset.univ.filter fun r : Fin n => (beadOf M r : ℕ) < j).card
        = beadStart M.dims j := card_beadOf_lt M j
    have hcT' : (Finset.univ.filter fun r : Fin n => (flatten A r : ℕ) < beadStart M.dims j).card
        = beadStart M.dims j := card_flatten_lt A hst
    have hdown : ∀ r s : Fin n, (flatten A r : ℕ) ≤ (flatten A s : ℕ) →
        s ∈ (Finset.univ.filter fun t : Fin n => (beadOf M t : ℕ) < j) →
        r ∈ Finset.univ.filter fun t : Fin n => (beadOf M t : ℕ) < j := by
      intro r s hrs hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_lt (hmono r s hrs) (Finset.mem_filter.mp hs).2⟩
    have hdown' : ∀ r s : Fin n, (flatten A r : ℕ) ≤ (flatten A s : ℕ) →
        s ∈ (Finset.univ.filter fun t : Fin n => (flatten A t : ℕ) < beadStart M.dims j) →
        r ∈ Finset.univ.filter fun t : Fin n => (flatten A t : ℕ) < beadStart M.dims j := by
      intro r s hrs hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_lt hrs (Finset.mem_filter.mp hs).2⟩
    exact Finset.Subset.antisymm (downSet_subset hdown' hdown (by omega))
      (downSet_subset hdown hdown' (by omega))
  have hiff : ∀ j : ℕ, (beadOf M q : ℕ) < j ↔
      ((dimComp M.dims hn).index (flatten A q) : ℕ) < j := by
    intro j
    rw [index_lt_iff_beadStart hn (flatten A q) j]
    constructor
    · intro h
      have hq : q ∈ Finset.univ.filter fun r : Fin n => (beadOf M r : ℕ) < j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩
      rw [hset j] at hq
      exact (Finset.mem_filter.mp hq).2
    · intro h
      have hq : q ∈ Finset.univ.filter fun r : Fin n => (flatten A r : ℕ) < beadStart M.dims j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩
      rw [← hset j] at hq
      exact (Finset.mem_filter.mp hq).2
  have h1 := (hiff ((beadOf M q : ℕ) + 1)).mp (by omega)
  have h2 := (hiff (((dimComp M.dims hn).index (flatten A q) : ℕ) + 1)).mpr (by omega)
  omega

/-! ## Blocks and the junctions that separate them -/

/-- **Two coordinates share a block exactly when no junction separates them.** -/
theorem index_eq_iff_no_boundary {d : List ℕ+} (hd : dimSum d = n) {x y : Fin n} (hxy : x ≤ y) :
    ((dimComp d hd).index x : ℕ) = ((dimComp d hd).index y : ℕ)
      ↔ ∀ t, (x : ℕ) < t → t ≤ (y : ℕ) → t ∉ boundaries d := by
  constructor
  · intro heq t h1 h2 hmem
    have := (index_lt_index_iff hd x y).mpr ⟨t, hmem, h1, h2⟩
    omega
  · intro h
    rcases eq_or_lt_of_le ((dimComp d hd).index_monotone hxy) with heq | hlt
    · exact heq
    · obtain ⟨t, ht, h1, h2⟩ := (index_lt_index_iff hd x y).mp hlt
      exact absurd ht (h t h1 h2)

/-- **The block index jumps exactly at a junction** — `index_eq_iff_no_boundary` at consecutive
coordinates, where the only candidate junction between them is `y` itself. -/
theorem index_eq_iff_notMem_boundaries {d : List ℕ+} (hd : dimSum d = n) {z y : Fin n}
    (hzy : (y : ℕ) = (z : ℕ) + 1) :
    ((dimComp d hd).index z : ℕ) = ((dimComp d hd).index y : ℕ) ↔ (y : ℕ) ∉ boundaries d := by
  rw [index_eq_iff_no_boundary hd (Fin.le_def.mpr (by omega))]
  exact ⟨fun h => h (y : ℕ) (by omega) le_rfl,
    fun h t h1 h2 => by rw [show t = (y : ℕ) by omega]; exact h⟩

/-- **Blocks read off the missing junctions**: two coordinates of a shape whose junctions are all of
`0 … n` but `S` share a block exactly when every step between them lies in `S`. -/
theorem index_eq_iff_mem_cuts {d : List ℕ+} (hd : dimSum d = n) {S : Finset ℕ}
    (hS : boundaries d = Finset.range (n + 1) \ S) {x y : Fin n} (hxy : x ≤ y) :
    ((dimComp d hd).index x : ℕ) = ((dimComp d hd).index y : ℕ)
      ↔ ∀ t, (x : ℕ) < t → t ≤ (y : ℕ) → t ∈ S := by
  have hyn := y.isLt
  rw [index_eq_iff_no_boundary hd hxy, hS]
  refine ⟨fun h t h1 h2 => ?_, fun h t h1 h2 hc => (Finset.mem_sdiff.mp hc).2 (h t h1 h2)⟩
  have hc := h t h1 h2
  simp only [Finset.mem_sdiff, Finset.mem_range, not_and, not_not] at hc
  exact hc (by omega)

/-- **An adjacent swap across a deleted junction stays inside its block.** -/
theorem index_adjT_of_notMem {d : List ℕ+} (hd : dimSum d = n) {i : Fin (n - 1)}
    (hi : (i : ℕ) + 1 ∉ boundaries d) (x : Fin n) :
    ((dimComp d hd).index (adjT i x) : ℕ) = ((dimComp d hd).index x : ℕ) := by
  have hstep : ((dimComp d hd).index (adjLo i) : ℕ) = ((dimComp d hd).index (adjHi i) : ℕ) :=
    (index_eq_iff_notMem_boundaries hd (by simp)).mpr (by simpa using hi)
  rcases eq_or_ne (x : ℕ) (i : ℕ) with hx | hx
  · rw [show x = adjLo i from Fin.ext (by simpa using hx), adjT_lo]; exact hstep.symm
  rcases eq_or_ne (x : ℕ) ((i : ℕ) + 1) with hx' | hx'
  · rw [show x = adjHi i from Fin.ext (by simpa using hx'), adjT_hi]; exact hstep
  · rw [WeakOrder.adjT_apply_of_ne hx hx']

/-! ## The normal form: a coarsening re-sorts the firing order inside each block

`cross_eq_of_sort` is `flatten_apply` with the bead computed by `beadOf_of_hom`.  Every crossing
permutation below is read off it, by naming the permutation that sorts the blocks. -/

/-- **A coarsening re-sorts its source's firing order inside each block.**  `g` permutes each block
of `c` (`hblk`) into `σ`-increasing order (`hrise`); then `σ * g` is `c`'s crossing permutation. -/
theorem cross_eq_of_sort {r c : Ch (□n)} {σ : Equiv.Perm (Fin n)} (hr : cross r = σ) (f : r ⟶ c)
    (hn : dimSum c.dims = n) (g : Equiv.Perm (Fin n))
    (hblk : ∀ x : Fin n,
      ((dimComp c.dims hn).index (g x) : ℕ) = ((dimComp c.dims hn).index x : ℕ))
    (hrise : ∀ x y : Fin n, x < y →
      ((dimComp c.dims hn).index x : ℕ) = ((dimComp c.dims hn).index y : ℕ) →
        σ (g x) < σ (g y)) :
    cross c = σ * g := by
  have hfr : flatten r = σ⁻¹ := by rw [flatten_eq_cross_inv, hr]
  have hbo : ∀ q : Fin n, (beadOf c q : ℕ) = ((dimComp c.dims hn).index (flatten r q) : ℕ) :=
    beadOf_of_hom f
  have hbead : ∀ x : Fin n, (beadOf c ((σ * g) x) : ℕ)
      = ((dimComp c.dims hn).index x : ℕ) := fun x => by
    rw [hbo, show flatten r ((σ * g) x) = g x by rw [hfr]; simp, hblk]
  have hmono : ∀ x y : Fin n, (x : ℕ) ≤ (y : ℕ) →
      ((dimComp c.dims hn).index x : ℕ) ≤ ((dimComp c.dims hn).index y : ℕ) :=
    fun x y hxy => (dimComp c.dims hn).index_monotone (Fin.le_def.mpr hxy)
  have hsort : ∀ x y : Fin n, x < y →
      (beadOf c ((σ * g) x) : ℕ) < (beadOf c ((σ * g) y) : ℕ)
        ∨ (beadOf c ((σ * g) x) = beadOf c ((σ * g) y) ∧ (σ * g) x < (σ * g) y) := by
    intro x y hxy
    rcases lt_or_eq_of_le (hmono x y (Fin.le_def.mp hxy.le)) with h | h
    · exact Or.inl (by rw [hbead, hbead]; exact h)
    · exact Or.inr ⟨Fin.ext (by rw [hbead, hbead, h]),
        by simpa only [Equiv.Perm.mul_apply] using hrise x y hxy h⟩
  have hkey : flatten c = (σ * g)⁻¹ := Equiv.ext fun z => by
    obtain ⟨x, rfl⟩ : ∃ x, (σ * g) x = z := ⟨(σ * g)⁻¹ z, by simp⟩
    rw [flatten_apply c (σ * g) hsort x]
    simp
  rw [cross_eq_flatten_inv, hkey, inv_inv]

/-! ## Crossings are pairs of coordinates the chain takes out of order -/

/-- The crossings of a chain: the pairs of coordinates whose beads are out of order. -/
noncomputable def crossPairs (c : Ch (□n)) : Finset (Fin n × Fin n) := inversions (flatten c)

theorem mem_crossPairs {c : Ch (□n)} {p q : Fin n} :
    (p, q) ∈ crossPairs c ↔ p < q ∧ (beadOf c q : ℕ) < (beadOf c p : ℕ) := by
  simp only [crossPairs, inversions, Finset.mem_filter, Finset.mem_univ, true_and, flatten_lt_iff]
  constructor
  · rintro ⟨hpq, hlt | ⟨-, hqp⟩⟩
    · exact ⟨hpq, hlt⟩
    · exact absurd hqp (asymm hpq)
  · rintro ⟨hpq, hlt⟩
    exact ⟨hpq, Or.inl hlt⟩

@[simp] theorem crossLen_eq_card (c : Ch (□n)) : crossLen c = (crossPairs c).card := by
  rw [crossLen, cross_eq_flatten_inv, permLen_inv]
  rfl

/-- **A refinement only ever un-crosses.** -/
theorem crossPairs_subset {a b : Ch (□n)} (f : a ⟶ b) : crossPairs b ⊆ crossPairs a := by
  rintro ⟨p, q⟩ hpq
  rw [mem_crossPairs] at hpq ⊢
  refine ⟨hpq.1, ?_⟩
  by_contra hcon
  exact absurd (beadOf_le_of_hom f (not_lt.mp hcon)) (not_le.mpr hpq.2)

/-- **What a refinement crosses is what it un-crosses.** -/
theorem permLen_crossPerm_eq_card {a b : Ch (□n)} (f : a ⟶ b) :
    permLen (crossPerm (dimSum_dims_cube a) f) = (crossPairs a \ crossPairs b).card := by
  have h := crossLen_eq_add f
  rw [crossLen_eq_card, crossLen_eq_card] at h
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (crossPairs_subset f)]
  omega

/-- **…and it un-crosses only what it merges**: a pair the refinement stops crossing lies in one
bead of the target. -/
theorem beadOf_eq_of_mem_sdiff {a b : Ch (□n)} (f : a ⟶ b) {p q : Fin n}
    (h : (p, q) ∈ crossPairs a \ crossPairs b) : beadOf b p = beadOf b q := by
  rw [Finset.mem_sdiff, mem_crossPairs, mem_crossPairs] at h
  obtain ⟨⟨hpq, hba⟩, hnb⟩ := h
  have h2 : (beadOf b q : ℕ) ≤ (beadOf b p : ℕ) := beadOf_le_of_hom f (le_of_lt hba)
  have h1 : (beadOf b p : ℕ) ≤ (beadOf b q : ℕ) := not_lt.mp fun hc => hnb ⟨hpq, hc⟩
  exact Fin.ext (by omega)

/-! ## A step at one cut

A step whose crossing permutation is a single adjacent swap `adjT i` faces off a *descent* of the
source's firing order and deletes the junction between the two ranks it names.  Those are the two
inputs `cross_eq_of_sort` needs at every atom below. -/

/-- The step's crossing permutation, transported to the target. -/
private theorem cross_mul_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) : cross b = cross a * adjT i := by
  have h := cross_eq_mul f
  rw [hf] at h
  rw [h, mul_adjT_adjT]

/-- **Only a descent shortens**: a step crossing one adjacent pair faces off a descent. -/
theorem cross_descent_of_crossPerm_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) :
    cross a (adjHi i) < cross a (adjLo i) := by
  have hadd := crossLen_eq_add f
  simp only [crossLen, hf, permLen_adjT, cross_mul_adjT f hf] at hadd
  rcases lt_trichotomy (cross a (adjHi i)) (cross a (adjLo i)) with h | h | h
  · exact h
  · exact absurd (congrArg Fin.val ((cross a).injective h))
      (by simp only [adjHi_val, adjLo_val]; omega)
  · have := permLen_mul_adjT h
    omega

/-- **…and it deletes the junction between the two ranks it names**: were the junction still there,
the target would fire the two coordinates in the order the swap has just reversed. -/
theorem notMem_boundaries_of_crossPerm_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) : (i : ℕ) + 1 ∉ boundaries b.dims := by
  intro hmem
  have hfa : flatten a = (cross a)⁻¹ := flatten_eq_cross_inv a
  have hfb : flatten b = adjT i * (cross a)⁻¹ := by
    rw [flatten_eq_cross_inv, cross_mul_adjT f hf, mul_inv_rev,
      show ((adjT i)⁻¹ : Equiv.Perm (Fin n)) = adjT i from by rw [adjT, Equiv.swap_inv]]
  have hlt : (beadOf b (cross a (adjLo i)) : ℕ) < (beadOf b (cross a (adjHi i)) : ℕ) := by
    rw [beadOf_of_hom f, beadOf_of_hom f, hfa,
      show ((cross a)⁻¹ : Equiv.Perm (Fin n)) (cross a (adjLo i)) = adjLo i from by simp,
      show ((cross a)⁻¹ : Equiv.Perm (Fin n)) (cross a (adjHi i)) = adjHi i from by simp]
    exact (index_lt_index_iff _ _ _).mpr ⟨(i : ℕ) + 1, hmem, by simp, by simp⟩
  have hcon := (flatten_lt_iff b).mpr (Or.inl hlt)
  rw [hfb, show (adjT i * (cross a)⁻¹) (cross a (adjLo i)) = adjHi i from by simp [adjT_lo],
    show (adjT i * (cross a)⁻¹) (cross a (adjHi i)) = adjLo i from by simp [adjT_hi]] at hcon
  exact absurd (Fin.lt_def.mp hcon) (by simp only [adjHi_val, adjLo_val]; omega)

/-! ## The meet of two coarsenings

Two shapes over the same events have a meet — the shape whose junctions are the junctions of both
— obtained by deleting the junctions of one that the other lacks, one at a time. -/

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

/-- **A coarsening with a prescribed shape.**  Every shape whose junctions `a` has is realised by a
coarsening of `a` — the one-bead chain is below it for free, its only junctions being `0` and `n`. -/
theorem exists_coarsening {a : Ch (□n)} {m : List ℕ+} (hm : dimSum m = n)
    (hsub : boundaries m ⊆ boundaries a.dims) : ∃ (d : Ch (□n)) (_ : a ⟶ d), d.dims = m := by
  obtain ⟨d, hd, ⟨f⟩, -⟩ := exists_mid_chain (toCubeTop a) hm hsub
    (subset_trans (boundaries_topDims_subset n) fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact zero_mem_boundaries m
      · rw [Finset.mem_singleton.mp hx', ← hm]; exact dimSum_mem_boundaries m)
  exact ⟨d, f, hd⟩

/-- Merging one junction out of a shape. -/
private theorem exists_erase_shape {N : ℕ} {d : List ℕ+} (h : dimSum d = N) {t : ℕ}
    (ht : t ∈ boundaries d) (h0 : t ≠ 0) (hN : t ≠ N) :
    ∃ m : List ℕ+, dimSum m = N ∧ boundaries m = (boundaries d).erase t := by
  obtain ⟨w, -⟩ := exists_W_top (b := zObj d) h
  have htc : t ∈ cutsOf w := Finset.mem_sdiff.mpr ⟨ht, fun hc => by
    rcases Finset.mem_insert.mp (boundaries_topDims_subset N hc) with h' | h'
    · exact h0 h'
    · exact hN (Finset.mem_singleton.mp h')⟩
  obtain ⟨c, ec, -, hcut, -⟩ := exists_factor_first w htc
  exact ⟨c.dims, (strandsEq ec).symm.trans h, boundaries_eq_erase hcut⟩

private theorem exists_meet_shape_aux : ∀ (k : ℕ) {N : ℕ} (d₁ d₂ : List ℕ+), dimSum d₁ = N →
    dimSum d₂ = N → (boundaries d₁ \ boundaries d₂).card ≤ k →
    ∃ m : List ℕ+, dimSum m = N ∧ boundaries m = boundaries d₁ ∩ boundaries d₂ := by
  intro k
  induction k with
  | zero =>
    intro N d₁ d₂ h₁ _ hk
    exact ⟨d₁, h₁, (Finset.inter_eq_left.mpr (Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.card_eq_zero.mp (Nat.le_zero.mp hk)))).symm⟩
  | succ k ih =>
    intro N d₁ d₂ h₁ h₂ hk
    rcases Finset.eq_empty_or_nonempty (boundaries d₁ \ boundaries d₂) with he | ⟨t, ht⟩
    · exact ⟨d₁, h₁, (Finset.inter_eq_left.mpr
        (Finset.sdiff_eq_empty_iff_subset.mp he)).symm⟩
    obtain ⟨htd₁, htd₂⟩ := Finset.mem_sdiff.mp ht
    obtain ⟨m₁, hm₁, hbm₁⟩ := exists_erase_shape h₁ htd₁
      (fun hc => htd₂ (hc ▸ zero_mem_boundaries d₂))
      (fun hc => htd₂ (hc ▸ h₂ ▸ dimSum_mem_boundaries d₂))
    have hsd : boundaries m₁ \ boundaries d₂ = (boundaries d₁ \ boundaries d₂).erase t := by
      rw [hbm₁]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      tauto
    obtain ⟨m, hm, hbm⟩ := ih m₁ d₂ hm₁ h₂ (by
      rw [hsd, Finset.card_erase_of_mem ht]; omega)
    refine ⟨m, hm, ?_⟩
    rw [hbm, hbm₁]
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨fun hc => htd₂ (hc ▸ hx.2), hx.1⟩, hx.2⟩⟩

/-- **Two shapes over the same events have a meet.** -/
theorem exists_meet_shape {N : ℕ} {d₁ d₂ : List ℕ+} (h₁ : dimSum d₁ = N) (h₂ : dimSum d₂ = N) :
    ∃ m : List ℕ+, dimSum m = N ∧ boundaries m = boundaries d₁ ∩ boundaries d₂ :=
  exists_meet_shape_aux _ d₁ d₂ h₁ h₂ le_rfl

/-- **Two coarsenings of a chain meet in one**, carrying the junctions of both. -/
theorem exists_meet {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂) :
    ∃ e : Ch (□n), Nonempty (d₁ ⟶ e) ∧ Nonempty (d₂ ⟶ e) ∧
      boundaries e.dims = boundaries d₁.dims ∩ boundaries d₂.dims := by
  obtain ⟨m, hm, hbm⟩ := exists_meet_shape (dimSum_dims_cube d₁) (dimSum_dims_cube d₂)
  obtain ⟨e, v₁, hed⟩ := exists_coarsening hm (by rw [hbm]; exact Finset.inter_subset_left)
  obtain ⟨e', v₂, hed'⟩ := exists_coarsening hm (by rw [hbm]; exact Finset.inter_subset_right)
  obtain rfl : e = e' := chain_ext_of_dims (u₁ ≫ v₁) (u₂ ≫ v₂) (hed.trans hed'.symm)
  exact ⟨e, ⟨v₁⟩, ⟨v₂⟩, by rw [hed, hbm]⟩

/-- **A sequence that ends below where it started steps down somewhere adjacent.**  Stated over a
bare `LinearOrder` on purpose: with nothing geometric near it, a failure downstream is bookkeeping
rather than a failure of this. -/
theorem exists_step_down {α : Type*} [LinearOrder α] {f : ℕ → α} :
    ∀ {x y : ℕ}, x ≤ y → f y < f x → ∃ z, x ≤ z ∧ z < y ∧ f (z + 1) < f z := by
  intro x y
  induction y with
  | zero =>
    intro hxy h
    exact absurd h (by rw [Nat.le_zero.mp hxy]; exact lt_irrefl _)
  | succ k ih =>
    intro hxy h
    have hxk : x ≤ k := by
      rcases Nat.lt_or_ge x (k + 1) with hc | hc
      · omega
      · exact absurd h (by rw [show x = k + 1 by omega]; exact lt_irrefl _)
    rcases lt_or_ge (f (k + 1)) (f k) with hd | hd
    · exact ⟨k, hxk, by omega, hd⟩
    · obtain ⟨z, h1, h2, h3⟩ := ih hxk (lt_of_le_of_lt hd h)
      exact ⟨z, h1, by omega, h3⟩

/-! ## `W` is closed under meets

Two refinements that cross nothing have the same firing order, so a junction one of them lacks is
one across which the coordinates rise.  Chaining that along a bead of their meet keeps the whole
bead rising — which says exactly that the meet fires in that same order, so it crosses nothing
either. -/

/-- Consecutive events in one bead of a chain have rising coordinates. -/
private theorem lt_of_index_eq {d : Ch (□n)} {ψ : Equiv.Perm (Fin n)} (hd : flatten d = ψ⁻¹)
    {z y : Fin n} (hzy : (z : ℕ) < (y : ℕ))
    (hidx : ((dimComp d.dims (wedgeDimSum_eq d.map)).index z : ℕ)
      = ((dimComp d.dims (wedgeDimSum_eq d.map)).index y : ℕ)) : ψ z < ψ y := by
  have hz : flatten d (ψ z) = z := by rw [hd]; simp
  have hy : flatten d (ψ y) = y := by rw [hd]; simp
  rcases (flatten_lt_iff d).mp (show flatten d (ψ z) < flatten d (ψ y) by
    rw [hz, hy]; exact Fin.lt_def.mpr hzy) with hb | ⟨-, hgz⟩
  · rw [beadOf_eq_index d (ψ z), beadOf_eq_index d (ψ y), hz, hy] at hb
    omega
  · exact hgz

/-- **`W` is closed under meets**: two refinements of a chain that cross nothing have a common
coarsening that crosses nothing. -/
theorem exists_meet_cross_eq {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h : cross d₁ = cross d₂) :
    ∃ e : Ch (□n), Nonempty (d₁ ⟶ e) ∧ Nonempty (d₂ ⟶ e) ∧ cross e = cross d₁ := by
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hb⟩ := exists_meet u₁ u₂
  refine ⟨e, ⟨v₁⟩, ⟨v₂⟩, ?_⟩
  have hf₁ : flatten d₁ = (cross d₁)⁻¹ := flatten_eq_cross_inv d₁
  have hf₂ : flatten d₂ = (cross d₁)⁻¹ := by rw [flatten_eq_cross_inv, h]
  have hn : dimSum e.dims = n := wedgeDimSum_eq e.map
  set ψ : Equiv.Perm (Fin n) := cross d₁ with hψ
  set idx : Fin n → ℕ := fun z => ((dimComp e.dims hn).index z : ℕ) with hidxdef
  have hmono : ∀ x y : Fin n, (x : ℕ) ≤ (y : ℕ) → idx x ≤ idx y := fun x y hxy =>
    (dimComp e.dims hn).index_monotone (Fin.le_def.mpr hxy)
  -- across a junction `e` lacks, one of `d₁`, `d₂` lacks it too, and there the coordinates rise
  have hstep : ∀ z y : Fin n, (y : ℕ) = (z : ℕ) + 1 → idx z = idx y → ψ z < ψ y := by
    intro z y hzy heq
    have hnot : (y : ℕ) ∉ boundaries e.dims := (index_eq_iff_notMem_boundaries hn hzy).mp heq
    rw [hb, Finset.mem_inter] at hnot
    rcases not_and_or.mp hnot with hm | hm
    · exact lt_of_index_eq hf₁ (by omega) ((index_eq_iff_notMem_boundaries _ hzy).mpr hm)
    · exact lt_of_index_eq hf₂ (by omega) ((index_eq_iff_notMem_boundaries _ hzy).mpr hm)
  -- chain the rise along a whole bead
  have hchain : ∀ (k : ℕ) (x y : Fin n), (y : ℕ) = (x : ℕ) + k → idx x = idx y → ψ x ≤ ψ y := by
    intro k
    induction k with
    | zero => intro x y hxy _; rw [show x = y from Fin.ext (by omega)]
    | succ k ih =>
      intro x y hxy heq
      have hzlt : (x : ℕ) + k < n := by have := y.isLt; omega
      have hz1 : idx x ≤ idx ⟨(x : ℕ) + k, hzlt⟩ := hmono _ _ (by simp)
      have hz2 : idx ⟨(x : ℕ) + k, hzlt⟩ ≤ idx y := hmono _ _ (by simp; omega)
      exact le_trans (ih x ⟨(x : ℕ) + k, hzlt⟩ rfl (by omega))
        (le_of_lt (hstep ⟨(x : ℕ) + k, hzlt⟩ y (by simp; omega) (by omega)))
  rw [show ψ = ψ * 1 from (mul_one _).symm]
  refine cross_eq_of_sort hψ.symm v₁ hn 1 (fun x => by rw [Equiv.Perm.one_apply])
    (fun x y hxy hidx => ?_)
  simp only [Equiv.Perm.one_apply]
  have hidx' : idx x = idx y := hidx
  exact lt_of_le_of_ne (hchain ((y : ℕ) - (x : ℕ)) x y (by have := Fin.lt_def.mp hxy; omega) hidx')
    fun hc => absurd (ψ.injective hc) (ne_of_lt hxy)

/-- **`W` is closed under meets**, on the nose.  Every chain in a `W`-class is a coarsening of the
class's run, so this is confluence *inside* a class — no terminal object of the class is needed. -/
theorem exists_meet_W {a d₁ d₂ : Ch (□n)} {u₁ : a ⟶ d₁} {u₂ : a ⟶ d₂}
    (h₁ : W (□n) u₁) (h₂ : W (□n) u₂) :
    ∃ (e : Ch (□n)) (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e), W (□n) v₁ ∧ W (□n) v₂ := by
  have hc₁ : cross a = cross d₁ := WeakOrder.of_injective (weakClass_eq_of_W h₁)
  have hc₂ : cross a = cross d₂ := WeakOrder.of_injective (weakClass_eq_of_W h₂)
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hce⟩ := exists_meet_cross_eq u₁ u₂ (hc₁.symm.trans hc₂)
  exact ⟨e, v₁, v₂, W_of_cross_eq v₁ hce.symm,
    W_of_cross_eq v₂ (hc₂.symm.trans (hc₁.trans hce.symm))⟩

/-! ## The atom out of a run -/

/-- **The atom out of a run.**  A descent of the run's crossing permutation is realised by merging
the two events it names: the face has one two-event bead, and crosses that pair less. -/
theorem exists_atom_face {r : Ch (□n)} (hr : ∀ x ∈ r.dims, x = 1) {i : Fin (n - 1)}
    (hi : cross r (adjHi i) < cross r (adjLo i)) :
    ∃ (d : Ch (□n)) (_ : r ⟶ d), cross d = cross r * adjT i ∧ d.dims = atomComp n i := by
  have hi2 := i.isLt
  obtain ⟨d, h, hdd⟩ := exists_coarsening (dimSum_atomComp n i) (a := r) (by
    rw [boundaries_atomComp, cubeChain_dims_ones r hr, boundaries_ones]
    exact Finset.sdiff_subset)
  refine ⟨d, h, ?_, hdd⟩
  have hn : dimSum d.dims = n := wedgeDimSum_eq d.map
  have hS : boundaries d.dims = Finset.range (n + 1) \ {(i : ℕ) + 1} := by
    rw [hdd, boundaries_atomComp]
  refine cross_eq_of_sort rfl h hn (adjT i)
    (index_adjT_of_notMem hn (by rw [hS]; simp)) (fun x y hxy hidx => ?_)
  have hkey := (index_eq_iff_mem_cuts hn hS hxy.le).mp hidx
  simp only [Finset.mem_singleton] at hkey
  have hxlt : (x : ℕ) < (y : ℕ) := Fin.lt_def.mp hxy
  have hy1 : (y : ℕ) = (x : ℕ) + 1 := by
    by_contra hc
    have h1 := hkey ((x : ℕ) + 1) (by omega) (by omega)
    have h2 := hkey ((x : ℕ) + 2) (by omega) (by omega)
    omega
  have hx1 := hkey ((x : ℕ) + 1) (by omega) (by omega)
  rw [show x = adjLo i from Fin.ext (by simp only [adjLo_val]; omega),
    show y = adjHi i from Fin.ext (by simp only [adjHi_val]; omega), adjT_lo, adjT_hi]
  exact hi

/-- **A fraction that crosses something factors through an atom.**  Some pair is un-crossed, so
along the events between its two the coordinates fall; they must fall across one junction, and that
adjacent descent's atom face lands under the target. -/
theorem exists_atom_factor {σ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (runAt σ).chain ⟶ d) (hne : cross d ≠ σ) :
    ∃ (i : Fin (n - 1)) (e : Ch (□n)), σ (adjHi i) < σ (adjLo i) ∧
      Nonempty ((runAt σ).chain ⟶ e) ∧ Nonempty (e ⟶ d)
      ∧ cross e = σ * adjT i := by
  set r : Ch (□n) := (runAt σ).chain with hr
  have hcr : cross r = σ := cross_runAt σ
  have hrd : ∀ x ∈ r.dims, x = 1 := fun x hx =>
    List.eq_of_mem_replicate (by rw [← run_dims (runAt σ)]; exact hx)
  -- something is un-crossed
  have hsd : (crossPairs r \ crossPairs d).Nonempty := by
    rw [← Finset.card_pos, ← permLen_crossPerm_eq_card u]
    by_contra hc
    exact hne (((WeakOrder.of_injective (weakClass_eq_of_W
      ((W_iff_crossPerm_eq_one (dimSum_dims_cube r) u).mpr
        (eq_one_of_permLen_eq_zero _ (by omega))))).symm.trans hcr))
  obtain ⟨⟨p, q⟩, hpq⟩ := hsd
  have hbd : beadOf d p = beadOf d q := beadOf_eq_of_mem_sdiff u hpq
  obtain ⟨hlt, hbr⟩ := mem_crossPairs.mp (Finset.mem_sdiff.mp hpq).1
  -- read the two coordinates as events
  have hfr : flatten r = σ⁻¹ := by rw [flatten_eq_cross_inv, hcr]
  have hn0 : 0 < n := by have := p.isLt; omega
  have hev : ∀ c : Fin n, (beadOf r c : ℕ) = ((σ⁻¹ c : Fin n) : ℕ) := by
    intro c
    rw [beadOf_run hrd, hcr]
  have hyx : ((σ⁻¹ q : Fin n) : ℕ) < ((σ⁻¹ p : Fin n) : ℕ) := by
    rw [← hev, ← hev]; exact hbr
  -- the coordinates fall across the events between them
  set F : ℕ → ℕ := fun w => if h : w < n then ((σ ⟨w, h⟩ : Fin n) : ℕ) else 0 with hF
  have hFval : ∀ w : Fin n, F (w : ℕ) = ((σ w : Fin n) : ℕ) := by
    intro w
    rw [hF]
    simp [w.isLt]
  obtain ⟨z, hz1, hz2, hz3⟩ :=
    exists_step_down (f := F) (x := ((σ⁻¹ q : Fin n) : ℕ)) (y := ((σ⁻¹ p : Fin n) : ℕ))
      (le_of_lt hyx) (by rw [hFval, hFval]; simpa using hlt)
  have hzn : z + 1 < n := by have := (σ⁻¹ p : Fin n).isLt; omega
  have hzn' : z < n - 1 := by omega
  set i : Fin (n - 1) := ⟨z, hzn'⟩ with hi
  have hlo : adjLo i = (⟨z, by omega⟩ : Fin n) := Fin.ext rfl
  have hhi : adjHi i = (⟨z + 1, hzn⟩ : Fin n) := Fin.ext rfl
  have hdesc : cross r (adjHi i) < cross r (adjLo i) := by
    rw [hcr, hlo, hhi, Fin.lt_def]
    have h1 : F (z + 1) = ((σ (⟨z + 1, hzn⟩ : Fin n) : Fin n) : ℕ) := hFval ⟨z + 1, hzn⟩
    have h2 : F z = ((σ (⟨z, by omega⟩ : Fin n) : Fin n) : ℕ) := hFval ⟨z, by omega⟩
    omega
  obtain ⟨e, v, hce, hde⟩ := exists_atom_face hrd hdesc
  refine ⟨i, e, by rw [← hcr]; exact hdesc, ⟨v⟩, ?_, by rw [hce, hcr]⟩
  -- the atom face lands under `d`
  have hidx : ∀ w : Fin n, ((dimComp d.dims (wedgeDimSum_eq d.map)).index w : ℕ)
      = (beadOf d (σ w) : ℕ) := by
    intro w
    rw [beadOf_of_hom u, hfr]
    simp
  -- the merged pair spans the whole stretch, so `d` has no junction inside it — `z + 1` least
  have hnotmem : (z + 1) ∉ boundaries d.dims := by
    refine (index_eq_iff_no_boundary (wedgeDimSum_eq d.map)
      (Fin.le_def.mpr (le_of_lt hyx))).mp ?_ (z + 1) (by omega) (by omega)
    rw [hidx, hidx, show σ (σ⁻¹ q) = q from by simp, show σ (σ⁻¹ p) = p from by simp]
    exact congrArg Fin.val hbd.symm
  have hsub : boundaries d.dims ⊆ boundaries e.dims := by
    rw [hde, boundaries_atomComp]
    intro t ht
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · have := boundaries_subset_of_hom u ht
      rwa [cubeChain_dims_ones r hrd, boundaries_ones] at this
    · simp only [Finset.mem_singleton]
      rintro rfl
      exact hnotmem ht
  obtain ⟨M, w, hMd⟩ := exists_coarsening (dimSum_dims_cube d) hsub
  exact ⟨(chain_ext_of_dims (v ≫ w) u hMd) ▸ w⟩

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
  have hint : ∀ S T : Finset ℕ, S \ (S ∩ T) = S \ T := fun S T => by
    ext z; simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]; tauto
  refine ⟨e, v₁, v₂, ?_, ?_⟩
  · rw [codim_eq_card_sdiff, hb, hint, hB₁, hB₂, hcut hst hta, Finset.card_singleton]
  · rw [codim_eq_card_sdiff, hb, Finset.inter_comm, hint, hB₂, hB₁,
      hcut (Ne.symm hst) hsa, Finset.card_singleton]

/-- **The bare cube has diamonds** — `exists_join` supplies the two steps, thinness the square.
Adjacent cuts have distinct target shapes, which is all `exists_join` needs of `d ≠ d'`. -/
theorem hasDiamonds_cube (n : ℕ) : HasDiamonds (□n) := by
  intro a d d' u u' c c' hadj
  obtain ⟨e, v, v', hv, hv'⟩ := exists_join u u' c.codim_eq_one c'.codim_eq_one
    fun hdd => c.tgt_dims_ne_of_adjacent c' hadj (congrArg ChainCat.Obj.dims hdd)
  exact ⟨e, v, v', hv, hv', Subsingleton.elim _ _⟩

/-! ## What the face two atoms meet in crosses

The two steps delete two junctions and the meet is a codimension-two face, so its junctions are
*exactly* the run's minus those two (`boundaries_of_meet`).  That pins its blocks, hence the
permutation that sorts them, hence its `cross`. -/

/-- **Two codimension-one steps out of a run delete exactly two junctions**, which is the room the
computation below runs on. -/
theorem length_of_two_steps {r d e : Ch (□n)} (hr : ∀ x ∈ r.dims, x = 1)
    (u : r ⟶ d) (v : d ⟶ e) (hu : codim u = 1) (hv : codim v = 1) :
    e.dims.length + 2 = n := by
  have h0 : degree r = 0 := (degree_eq_zero_iff r).mpr hr
  have h1 := degree_le_of_hom u
  have h2 := degree_le_of_hom v
  rw [codim] at hu hv
  have hd := degree_add_length e
  have hn := dimSum_dims_cube e
  omega

/-- **The face two atoms meet in has exactly their two junctions deleted.**  Each leg deletes its
own, and a codimension-two face has no room for a third. -/
theorem boundaries_of_meet {r d₁ d₂ e : Ch (□n)} {i j : Fin (n - 1)} (hij : (i : ℕ) ≠ (j : ℕ))
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    boundaries e.dims = Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} := by
  have hi := i.isLt
  have hj := j.isLt
  have hsub : boundaries e.dims ⊆ Finset.range (n + 1) \ {(i : ℕ) + 1, (j : ℕ) + 1} := by
    intro t ht
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hle := le_dimSum_of_mem_boundaries ht
      rw [dimSum_dims_cube] at hle
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl)
      · exact notMem_boundaries_of_crossPerm_adjT u₁ hf₁ (boundaries_subset_of_hom v₁ ht)
      · exact notMem_boundaries_of_crossPerm_adjT u₂ hf₂ (boundaries_subset_of_hom v₂ ht)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hcut : ({(i : ℕ) + 1, (j : ℕ) + 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_range]
    omega
  have hcard2 : ({(i : ℕ) + 1, (j : ℕ) + 1} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have hce := card_boundaries e.dims
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hcut, Finset.card_range, hcard2]
  omega

/-- **Far cuts**: two atoms at distant cuts meet in the doubly sorted permutation. -/
theorem cross_of_meet_far {σ : Equiv.Perm (Fin n)} {r d₁ d₂ e : Ch (□n)} (hr : cross r = σ)
    {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 < (j : ℕ))
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    cross e = σ * adjT i * adjT j := by
  have hi : σ (adjHi i) < σ (adjLo i) := hr ▸ cross_descent_of_crossPerm_adjT u₁ hf₁
  have hj : σ (adjHi j) < σ (adjLo j) := hr ▸ cross_descent_of_crossPerm_adjT u₂ hf₂
  have hn : dimSum e.dims = n := wedgeDimSum_eq e.map
  have hS := boundaries_of_meet (by omega : (i : ℕ) ≠ (j : ℕ)) hf₁ hf₂ v₁ v₂ hlen
  rw [mul_assoc]
  refine cross_eq_of_sort hr (u₁ ≫ v₁) hn (adjT i * adjT j)
    (fun x => ?_) (fun x y hxy hidx => ?_)
  · rw [Equiv.Perm.mul_apply, index_adjT_of_notMem hn (by rw [hS]; simp),
      index_adjT_of_notMem hn (by rw [hS]; simp)]
  · have hkey := (index_eq_iff_mem_cuts hn hS hxy.le).mp hidx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkey
    have hxlt : (x : ℕ) < (y : ℕ) := Fin.lt_def.mp hxy
    have hy1 : (y : ℕ) = (x : ℕ) + 1 := by
      by_contra hc
      have h1 := hkey ((x : ℕ) + 1) (by omega) (by omega)
      have h2 := hkey ((x : ℕ) + 2) (by omega) (by omega)
      omega
    rcases hkey ((x : ℕ) + 1) (by omega) (by omega) with hx | hx
    · rw [show x = adjLo i from Fin.ext (by simp only [adjLo_val]; omega),
        show y = adjHi i from Fin.ext (by simp only [adjHi_val]; omega),
        show (adjT i * adjT j) (adjLo i) = adjHi i from by
          rw [Equiv.Perm.mul_apply, WeakOrder.adjT_apply_of_ne (i := j) (a := adjLo i)
            (by simp only [adjLo_val]; omega) (by simp only [adjLo_val]; omega), adjT_lo],
        show (adjT i * adjT j) (adjHi i) = adjLo i from by
          rw [Equiv.Perm.mul_apply, WeakOrder.adjT_apply_of_ne (i := j) (a := adjHi i)
            (by simp only [adjHi_val]; omega) (by simp only [adjHi_val]; omega), adjT_hi]]
      exact hi
    · rw [show x = adjLo j from Fin.ext (by simp only [adjLo_val]; omega),
        show y = adjHi j from Fin.ext (by simp only [adjHi_val]; omega),
        show (adjT i * adjT j) (adjLo j) = adjHi j from by
          rw [Equiv.Perm.mul_apply, adjT_lo, WeakOrder.adjT_apply_of_ne (i := i) (a := adjHi j)
            (by simp only [adjHi_val]; omega) (by simp only [adjHi_val]; omega)],
        show (adjT i * adjT j) (adjHi j) = adjLo j from by
          rw [Equiv.Perm.mul_apply, adjT_hi, WeakOrder.adjT_apply_of_ne (i := i) (a := adjLo j)
            (by simp only [adjLo_val]; omega) (by simp only [adjLo_val]; omega)]]
      exact hj

/-- **Consecutive cuts**: two atoms at adjacent cuts meet in the sorted three-window. -/
theorem cross_of_meet_braid {σ : Equiv.Perm (Fin n)} {r d₁ d₂ e : Ch (□n)} (hr : cross r = σ)
    {i j : Fin (n - 1)} (hij : (j : ℕ) = (i : ℕ) + 1)
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    cross e = σ * adjT i * adjT j * adjT i := by
  have hi : σ (adjHi i) < σ (adjLo i) := hr ▸ cross_descent_of_crossPerm_adjT u₁ hf₁
  have hj : σ (adjHi j) < σ (adjLo j) := hr ▸ cross_descent_of_crossPerm_adjT u₂ hf₂
  have hji : adjLo j = adjHi i := WeakOrder.adjLo_eq_adjHi hij
  have hn : dimSum e.dims = n := wedgeDimSum_eq e.map
  have hS := boundaries_of_meet (by omega : (i : ℕ) ≠ (j : ℕ)) hf₁ hf₂ v₁ v₂ hlen
  -- the three-window, reversed
  have gLoI : (adjT i * adjT j * adjT i) (adjLo i) = adjHi j := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_lo, ← hji, adjT_lo,
      WeakOrder.adjT_apply_of_ne (i := i) (a := adjHi j) (by simp only [adjHi_val]; omega)
        (by simp only [adjHi_val]; omega)]
  have gHiI : (adjT i * adjT j * adjT i) (adjHi i) = adjHi i := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, adjT_hi,
      WeakOrder.adjT_apply_of_ne (i := j) (a := adjLo i) (by simp only [adjLo_val]; omega)
        (by simp only [adjLo_val]; omega), adjT_lo]
  have gHiJ : (adjT i * adjT j * adjT i) (adjHi j) = adjLo i := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      WeakOrder.adjT_apply_of_ne (i := i) (a := adjHi j) (by simp only [adjHi_val]; omega)
        (by simp only [adjHi_val]; omega), adjT_hi, hji, adjT_hi]
  rw [show σ * adjT i * adjT j * adjT i = σ * (adjT i * adjT j * adjT i) from by
    simp only [mul_assoc]]
  refine cross_eq_of_sort hr (u₁ ≫ v₁) hn (adjT i * adjT j * adjT i)
    (fun x => ?_) (fun x y hxy hidx => ?_)
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, index_adjT_of_notMem hn (by rw [hS]; simp),
      index_adjT_of_notMem hn (by rw [hS]; simp), index_adjT_of_notMem hn (by rw [hS]; simp)]
  · have hkey := (index_eq_iff_mem_cuts hn hS hxy.le).mp hidx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkey
    have hxlt : (x : ℕ) < (y : ℕ) := Fin.lt_def.mp hxy
    have hcase : ((x : ℕ) = (i : ℕ) ∧ (y : ℕ) = (i : ℕ) + 1)
        ∨ ((x : ℕ) = (i : ℕ) + 1 ∧ (y : ℕ) = (i : ℕ) + 2)
        ∨ ((x : ℕ) = (i : ℕ) ∧ (y : ℕ) = (i : ℕ) + 2) := by
      have h1 := hkey ((x : ℕ) + 1) (by omega) (by omega)
      rcases Nat.lt_or_ge ((x : ℕ) + 1) (y : ℕ) with hgt | hle
      · have h2 := hkey ((x : ℕ) + 2) (by omega) (by omega)
        rcases Nat.lt_or_ge ((x : ℕ) + 2) (y : ℕ) with hgt2 | hle2
        · have h3 := hkey ((x : ℕ) + 3) (by omega) (by omega)
          omega
        · omega
      · omega
    have hxi : (x : ℕ) = (i : ℕ) → x = adjLo i := fun h => Fin.ext (by simp only [adjLo_val]; omega)
    have hxi' : (x : ℕ) = (i : ℕ) + 1 → x = adjHi i :=
      fun h => Fin.ext (by simp only [adjHi_val]; omega)
    have hyi : (y : ℕ) = (i : ℕ) + 1 → y = adjHi i :=
      fun h => Fin.ext (by simp only [adjHi_val]; omega)
    have hyj : (y : ℕ) = (i : ℕ) + 2 → y = adjHi j :=
      fun h => Fin.ext (by simp only [adjHi_val]; omega)
    rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hxi hx, hyi hy, gLoI, gHiI]
      exact hji ▸ hj
    · rw [hxi' hx, hyj hy, gHiI, gHiJ]
      exact hi
    · rw [hxi hx, hyj hy, gLoI, gHiJ]
      exact lt_trans (hji ▸ hj) hi

end ChainCat
