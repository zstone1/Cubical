import CubeChains.Concurrency.Merge.CubeWeakOrder

/-!
# Concurrency/Merge/CubeFaces — a chain of a cube is an ordered partition of its axes

`cross c = (flatten c)⁻¹` (`cross_eq_flatten_inv`): a chain's crossing permutation is its own firing
order, read backwards, and a coarsening's beads are its shape's blocks read in that order
(`beadOf_of_hom`).  So a crossing is a pair of coordinates whose beads are out of order
(`mem_crossPairs`), a refinement only ever un-crosses (`crossPairs_subset`), and what it un-crosses
is what it merges (`beadOf_eq_of_mem_sdiff`), so it crosses at most what its target merged
(`permLen_crossPerm_le`).

Two coarsenings meet in one (`exists_meet`).  The meet crosses what the weak order predicts when
both steps cross (`cross_of_meet_far`, `cross_of_meet_braid`), and nothing when neither does
(`exists_meet_W`).
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

/-- **A run's beads are its firing order**: one coordinate per bead, so `beadOf` is `cross`
inverted. -/
theorem beadOf_run {r : Ch (□n)} (hr : ∀ d ∈ r.dims, d = 1) (q : Fin n) :
    (beadOf r q : ℕ) = ((cross r)⁻¹ q : ℕ) := by
  obtain ⟨hlo, hhi⟩ := flatten_mem_bead r q
  rw [beadStart_ones hr (beadOf r q).isLt.le] at hlo
  rw [beadStart_ones hr (by have := (beadOf r q).isLt; omega)] at hhi
  have hf : (flatten r q : ℕ) = ((cross r)⁻¹ q : ℕ) := by rw [cross_eq_flatten_inv, inv_inv]
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

/-- The pairs of coordinates a chain has put in a single bead. -/
noncomputable def samePairs (c : Ch (□n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun pq => pq.1 < pq.2 ∧ beadOf c pq.1 = beadOf c pq.2

theorem mem_samePairs {c : Ch (□n)} {p q : Fin n} :
    (p, q) ∈ samePairs c ↔ p < q ∧ beadOf c p = beadOf c q := by
  simp [samePairs]

/-- **A refinement destroys only the crossings it merges.** -/
theorem sdiff_subset_samePairs {a b : Ch (□n)} (f : a ⟶ b) :
    crossPairs a \ crossPairs b ⊆ samePairs b := by
  rintro ⟨p, q⟩ h
  exact mem_samePairs.mpr ⟨(mem_crossPairs.mp (Finset.mem_sdiff.mp h).1).1,
    beadOf_eq_of_mem_sdiff f h⟩

/-- **…so a refinement crosses at most what its target has merged.**  This is the bound clause (c)
of the join runs on: it turns a crossing count into a count of pairs inside beads. -/
theorem permLen_crossPerm_le {a b : Ch (□n)} (f : a ⟶ b) :
    permLen (crossPerm (dimSum_dims_cube a) f) ≤ (samePairs b).card :=
  (permLen_crossPerm_eq_card f).le.trans (Finset.card_le_card (sdiff_subset_samePairs f))

/-! ## The pair an atom un-crosses

`crossPairs` read through `cross` rather than `flatten` is a statement about permutations, and the
one below is the whole content of an atom: `adjT i` reverses only the pair sitting at ranks `i`,
`i+1`, so that is the only pair the refinement stops crossing. -/

theorem crossPairs_eq_inversions (c : Ch (□n)) : crossPairs c = inversions ((cross c)⁻¹) := by
  rw [crossPairs, cross_eq_flatten_inv, inv_inv]

/-- **A refinement crossing one adjacent pair un-crosses exactly the coordinates firing there.** -/
theorem sdiff_eq_of_crossPerm_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) :
    crossPairs a \ crossPairs b = {(cross a (adjHi i), cross a (adjLo i))} := by
  have hinvb : ((cross b)⁻¹ : Equiv.Perm (Fin n)) = adjT i * (cross a)⁻¹ := by
    have h := cross_eq_mul f
    rw [hf] at h
    rw [show cross b = cross a * adjT i by rw [h, mul_adjT_adjT], mul_inv_rev,
      show ((adjT i)⁻¹ : Equiv.Perm (Fin n)) = adjT i by rw [adjT, Equiv.swap_inv]]
  have hfwd : ∀ p q : Fin n, (p, q) ∈ crossPairs a \ crossPairs b →
      p = cross a (adjHi i) ∧ q = cross a (adjLo i) := by
    intro p q hmem
    rw [Finset.mem_sdiff, crossPairs_eq_inversions, crossPairs_eq_inversions, hinvb,
      mem_inversions, mem_inversions] at hmem
    obtain ⟨⟨hpq, hlt⟩, hnot⟩ := hmem
    have hflip : (adjT i * (cross a)⁻¹) p < (adjT i * (cross a)⁻¹) q :=
      lt_of_le_of_ne (not_lt.mp fun hc => hnot ⟨hpq, hc⟩)
        fun hc => absurd ((adjT i * (cross a)⁻¹ : Equiv.Perm (Fin n)).injective hc)
          (ne_of_lt hpq)
    obtain ⟨h1, h2⟩ := adjT_inverts i hlt hflip
    exact ⟨by rw [← h2]; simp, by rw [← h1]; simp⟩
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
    (by rw [← permLen_crossPerm_eq_card f, hf, permLen_adjT] :
      (crossPairs a \ crossPairs b).card = 1)
  obtain ⟨h1, h2⟩ := hfwd x.1 x.2 (by rw [hx]; exact Finset.mem_singleton_self x)
  rw [hx, show x = (cross a (adjHi i), cross a (adjLo i)) from Prod.ext h1 h2]

/-- …and it is a descent of the source's crossing permutation. -/
theorem cross_descent_of_crossPerm_adjT {a b : Ch (□n)} (f : a ⟶ b) {i : Fin (n - 1)}
    (hf : crossPerm (dimSum_dims_cube a) f = adjT i) :
    cross a (adjHi i) < cross a (adjLo i) :=
  (mem_crossPairs.mp (Finset.mem_sdiff.mp (by
    rw [sdiff_eq_of_crossPerm_adjT f hf]; exact Finset.mem_singleton_self _)).1).1

/-! ## Counting the merged pairs

A bead holds `beadCard` coordinates, the beads partition them, and every bead is inhabited — so the
beads with room to merge anything are as few as the junctions the chain has deleted. -/

/-- How many coordinates a chain puts in a given bead. -/
noncomputable def beadCard (c : Ch (□n)) (k : Fin c.dims.length) : ℕ :=
  (Finset.univ.filter fun q : Fin n => beadOf c q = k).card

theorem sum_beadCard (c : Ch (□n)) : ∑ k, beadCard c k = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := beadOf c)
    (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin c.dims.length)))
    fun x _ => Finset.mem_univ _
  simpa [beadCard] using h.symm

theorem one_le_beadCard (c : Ch (□n)) (k : Fin c.dims.length) : 1 ≤ beadCard c k := by
  obtain ⟨q, hq⟩ := beadOf_surjective c k
  exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩

/-- **The deleted junctions are the room the beads have.** -/
theorem sum_beadCard_sub_one (c : Ch (□n)) :
    (∑ k, (beadCard c k - 1)) + c.dims.length = n := by
  calc (∑ k : Fin c.dims.length, (beadCard c k - 1)) + c.dims.length
      = ∑ k : Fin c.dims.length, ((beadCard c k - 1) + 1) := by
        rw [Finset.sum_add_distrib]; simp
    _ = ∑ k : Fin c.dims.length, beadCard c k :=
        Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (one_le_beadCard c k)
    _ = n := sum_beadCard c

/-- A merged pair needs a bead with room for it. -/
theorem two_le_beadCard_of_mem_samePairs {c : Ch (□n)} {p q : Fin n}
    (h : (p, q) ∈ samePairs c) : 2 ≤ beadCard c (beadOf c p) := by
  obtain ⟨hpq, hb⟩ := mem_samePairs.mp h
  have hsub : ({p, q} : Finset (Fin n))
      ⊆ Finset.univ.filter fun r : Fin n => beadOf c r = beadOf c p := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_singleton.mp hr) ▸ hb.symm⟩
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [ne_of_lt hpq]), Finset.card_singleton] at hcard

/-- **A two-coordinate bead merges exactly one pair**, so the merged pairs inject into the beads. -/
theorem card_samePairs_le (c : Ch (□n)) (h2 : ∀ k, beadCard c k ≤ 2) :
    (samePairs c).card + c.dims.length ≤ n := by
  have hbig : (samePairs c).card
      ≤ (Finset.univ.filter fun k : Fin c.dims.length => 2 ≤ beadCard c k).card := by
    refine Finset.card_le_card_of_injOn (fun pq => beadOf c pq.1)
      (fun pq hpq => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        two_le_beadCard_of_mem_samePairs (by simpa using hpq)⟩) ?_
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := mem_samePairs.mp (by simpa using hx)
    obtain ⟨hy1, hy2⟩ := mem_samePairs.mp (by simpa using hy)
    have hfib : ({x.1, x.2} : Finset (Fin n))
        = Finset.univ.filter fun r : Fin n => beadOf c r = beadOf c x.1 := by
      refine Finset.eq_of_subset_of_card_le (fun r hr => ?_) ?_
      · rcases Finset.mem_insert.mp hr with rfl | hr
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_singleton.mp hr) ▸ hx2.symm⟩
      · rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hx1]), Finset.card_singleton]
        exact h2 (beadOf c x.1)
    have hy1m : y.1 ∈ ({x.1, x.2} : Finset (Fin n)) := by
      rw [hfib]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.symm⟩
    have hy2m : y.2 ∈ ({x.1, x.2} : Finset (Fin n)) := by
      rw [hfib]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy2.symm.trans hxy.symm⟩
    have h1 : y.1 = x.1 := by
      rcases Finset.mem_insert.mp hy1m with h | h
      · exact h
      · rcases Finset.mem_insert.mp hy2m with h' | h'
        · exact absurd (h' ▸ (Finset.mem_singleton.mp h) ▸ hy1) (by simp [asymm hx1])
        · exact absurd ((Finset.mem_singleton.mp h).trans (Finset.mem_singleton.mp h').symm)
            (ne_of_lt hy1)
    have h2' : y.2 = x.2 := by
      rcases Finset.mem_insert.mp hy2m with h | h
      · exact absurd (h1 ▸ h ▸ hy1) (lt_irrefl _)
      · exact Finset.mem_singleton.mp h
    exact Prod.ext h1.symm h2'.symm
  have hle : (Finset.univ.filter fun k : Fin c.dims.length => 2 ≤ beadCard c k).card
      ≤ ∑ k, (beadCard c k - 1) := by
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : 2 ≤ beadCard c k
    · simp only [hk, if_true]; omega
    · simp [hk]
  have := sum_beadCard_sub_one c
  omega

/-- The increasing pairs of a finset are half its off-diagonal. -/
private theorem two_mul_card_lt_pairs (S : Finset (Fin n)) :
    2 * ((S ×ˢ S).filter fun pq : Fin n × Fin n => pq.1 < pq.2).card
      = S.card * S.card - S.card := by
  classical
  set T := (S ×ˢ S).filter fun pq : Fin n × Fin n => pq.1 < pq.2 with hT
  set T' := (S ×ˢ S).filter fun pq : Fin n × Fin n => pq.2 < pq.1 with hT'
  have himg : T' = T.image Prod.swap := by
    ext ⟨p, q⟩
    simp only [hT, hT', Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hp, hq⟩, hlt⟩
      exact ⟨q, p, ⟨⟨hq, hp⟩, hlt⟩, rfl, rfl⟩
    · rintro ⟨x, y, ⟨⟨hx, hy⟩, hlt⟩, rfl, rfl⟩
      exact ⟨⟨hy, hx⟩, hlt⟩
  have hcard' : T'.card = T.card := by
    rw [himg, Finset.card_image_of_injective _ Prod.swap_injective]
  have hdisj : Disjoint T T' := by
    rw [Finset.disjoint_left]
    rintro ⟨p, q⟩ h h'
    exact absurd ((Finset.mem_filter.mp h).2) (asymm (Finset.mem_filter.mp h').2)
  have hunion : T ∪ T' = S.offDiag := by
    ext ⟨p, q⟩
    simp only [hT, hT', Finset.mem_union, Finset.mem_filter, Finset.mem_product,
      Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hp, hq⟩, hlt⟩ | ⟨⟨hp, hq⟩, hlt⟩)
      · exact ⟨hp, hq, ne_of_lt hlt⟩
      · exact ⟨hp, hq, (ne_of_lt hlt).symm⟩
    · rintro ⟨hp, hq, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨⟨hp, hq⟩, h⟩
      · exact Or.inr ⟨⟨hp, hq⟩, h⟩
  have hsum := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.offDiag_card, hcard'] at hsum
  omega

/-- **At most three pairs are merged by deleting two junctions.** -/
theorem card_samePairs_le_three (c : Ch (□n)) (hlen : c.dims.length + 2 = n) :
    (samePairs c).card ≤ 3 := by
  classical
  have hsum := sum_beadCard_sub_one c
  by_cases h2 : ∀ k, beadCard c k ≤ 2
  · have := card_samePairs_le c h2
    omega
  simp only [not_forall, not_le] at h2
  obtain ⟨k₀, hk₀⟩ := h2
  have hsingle : beadCard c k₀ - 1 ≤ ∑ k, (beadCard c k - 1) :=
    Finset.single_le_sum (f := fun k => beadCard c k - 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k₀)
  have hk₀' : beadCard c k₀ = 3 := by omega
  have honly : ∀ k, k ≠ k₀ → beadCard c k = 1 := by
    intro k hk
    have hpair : (beadCard c k - 1) + (beadCard c k₀ - 1) ≤ ∑ m, (beadCard c m - 1) := by
      have hs := Finset.sum_le_sum_of_subset (f := fun m => beadCard c m - 1)
        (Finset.subset_univ ({k, k₀} : Finset (Fin c.dims.length)))
      rwa [Finset.sum_pair hk] at hs
    have := one_le_beadCard c k
    omega
  have hsub : samePairs c
      ⊆ ((Finset.univ.filter fun q : Fin n => beadOf c q = k₀) ×ˢ
          (Finset.univ.filter fun q : Fin n => beadOf c q = k₀)).filter
        fun pq : Fin n × Fin n => pq.1 < pq.2 := by
    rintro ⟨p, q⟩ hpq
    obtain ⟨hlt, hb⟩ := mem_samePairs.mp hpq
    have hk : beadOf c p = k₀ := by
      by_contra hc
      exact absurd (two_le_beadCard_of_mem_samePairs hpq) (by rw [honly _ hc]; omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb ▸ hk⟩⟩, hlt⟩
  have hb := two_mul_card_lt_pairs (Finset.univ.filter fun q : Fin n => beadOf c q = k₀)
  rw [show (Finset.univ.filter fun q : Fin n => beadOf c q = k₀).card = 3 from hk₀'] at hb
  have := Finset.card_le_card hsub
  omega

/-- **Two disjoint merged pairs use up all the room**, so no bead then holds three coordinates. -/
theorem beadCard_le_two_of_disjoint {c : Ch (□n)} (hlen : c.dims.length + 2 = n)
    {p q p' q' : Fin n} (h : (p, q) ∈ samePairs c) (h' : (p', q') ∈ samePairs c)
    (hpp : p ≠ p') (hpq : p ≠ q') (hqp : q ≠ p') (hqq : q ≠ q') (k : Fin c.dims.length) :
    beadCard c k ≤ 2 := by
  classical
  have hsum := sum_beadCard_sub_one c
  obtain ⟨hlt, hb⟩ := mem_samePairs.mp h
  obtain ⟨hlt', hb'⟩ := mem_samePairs.mp h'
  have hpair : ∀ m₁ m₂ : Fin c.dims.length, m₁ ≠ m₂ →
      (beadCard c m₁ - 1) + (beadCard c m₂ - 1) ≤ ∑ m, (beadCard c m - 1) := by
    intro m₁ m₂ hm
    have hs := Finset.sum_le_sum_of_subset (f := fun m => beadCard c m - 1)
      (Finset.subset_univ ({m₁, m₂} : Finset (Fin c.dims.length)))
    rwa [Finset.sum_pair hm] at hs
  have hne : beadOf c p ≠ beadOf c p' := by
    intro hc
    have hsub : ({p, q, p', q'} : Finset (Fin n))
        ⊆ Finset.univ.filter fun r : Fin n => beadOf c r = beadOf c p := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hr with rfl | rfl | rfl | rfl
      · rfl
      · exact hb.symm
      · exact hc.symm
      · exact hb'.symm.trans hc.symm
    have hcard : ({p, q, p', q'} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hlt, hpp, hpq]),
        Finset.card_insert_of_notMem (by simp [hqp, hqq]),
        Finset.card_insert_of_notMem (by simp [ne_of_lt hlt']), Finset.card_singleton]
    have h4 : 4 ≤ beadCard c (beadOf c p) := hcard ▸ Finset.card_le_card hsub
    have hs : beadCard c (beadOf c p) - 1 ≤ ∑ m, (beadCard c m - 1) :=
      Finset.single_le_sum (f := fun m => beadCard c m - 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (beadOf c p))
    omega
  have h2p : 2 ≤ beadCard c (beadOf c p) := two_le_beadCard_of_mem_samePairs h
  have h2p' : 2 ≤ beadCard c (beadOf c p') := two_le_beadCard_of_mem_samePairs h'
  by_contra hk
  rw [not_le] at hk
  by_cases hk1 : k = beadOf c p
  · rw [hk1] at hk
    have := hpair (beadOf c p) (beadOf c p') hne
    omega
  by_cases hk2 : k = beadOf c p'
  · rw [hk2] at hk
    have := hpair (beadOf c p) (beadOf c p') hne
    omega
  have hkmem : k ∉ ({beadOf c p, beadOf c p'} : Finset (Fin c.dims.length)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hk1, hk2⟩
  have htri : (beadCard c k - 1) + ((beadCard c (beadOf c p) - 1)
      + (beadCard c (beadOf c p') - 1)) ≤ ∑ m, (beadCard c m - 1) := by
    have hs : ∑ m ∈ ({k, beadOf c p, beadOf c p'} : Finset (Fin c.dims.length)),
        (beadCard c m - 1) ≤ ∑ m, (beadCard c m - 1) :=
      Finset.sum_le_sum_of_subset (f := fun m => beadCard c m - 1) (Finset.subset_univ _)
    rwa [Finset.sum_insert hkmem, Finset.sum_pair hne] at hs
  omega

/-! ## What a face the two atoms meet in crosses

`cross` of the meet is what the weak order predicts: below by the two lower covers, above because a
refinement crosses at most what it merges, and only so much can be merged by deleting two
junctions. -/

/-- The two coordinates an atom stops crossing, as a merged pair of the face below it. -/
private theorem atomPair_mem_samePairs {r d e : Ch (□n)} {i : Fin (n - 1)} (u : r ⟶ d)
    (hf : crossPerm (dimSum_dims_cube r) u = adjT i) (v : d ⟶ e) :
    (cross r (adjHi i), cross r (adjLo i)) ∈ samePairs e := by
  refine sdiff_subset_samePairs (u ≫ v) ?_
  have h1 : (cross r (adjHi i), cross r (adjLo i)) ∈ crossPairs r \ crossPairs d := by
    rw [sdiff_eq_of_crossPerm_adjT u hf]; exact Finset.mem_singleton_self _
  rw [Finset.mem_sdiff] at h1 ⊢
  exact ⟨h1.1, fun hc => h1.2 (crossPairs_subset v hc)⟩

/-- The crossing permutation of the meet, from a bound on how much it can un-cross. -/
private theorem cross_meet {σ ρ : Equiv.Perm (Fin n)} {r e : Ch (□n)} (hr : cross r = σ)
    (f : r ⟶ e) {k : ℕ} (hk : permLen ρ + k = permLen σ) (hcard : (samePairs e).card ≤ k)
    (hle : weakClass e ≤ WeakOrder.of ρ) : cross e = ρ := by
  have hadd := crossLen_eq_add f
  have hbound := permLen_crossPerm_le f
  rw [crossLen, crossLen, hr] at hadd
  rw [WeakOrder.le_def] at hle
  simp only [perm_weakClass, WeakOrder.perm_of] at hle
  have hz : permLen ((cross e)⁻¹ * ρ) = 0 := by omega
  have h1 := eq_one_of_permLen_eq_zero _ hz
  have h2 : cross e * ((cross e)⁻¹ * ρ) = cross e * 1 := by rw [h1]
  rwa [mul_inv_cancel_left, mul_one, eq_comm] at h2

/-- **Two codimension-one steps out of a run delete exactly two junctions**, which is the room the
bounds above run on. -/
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

/-- **Far cuts**: two atoms at distant cuts meet in the doubly sorted permutation. -/
theorem cross_of_meet_far {σ : Equiv.Perm (Fin n)} {r d₁ d₂ e : Ch (□n)} (hr : cross r = σ)
    {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 < (j : ℕ))
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    cross e = σ * adjT i * adjT j := by
  have hi : σ (adjHi i) < σ (adjLo i) := hr ▸ cross_descent_of_crossPerm_adjT u₁ hf₁
  have hj : σ (adjHi j) < σ (adjLo j) := hr ▸ cross_descent_of_crossPerm_adjT u₂ hf₂
  have hd₁ : cross d₁ = σ * adjT i := by
    have h := cross_eq_mul u₁; rw [hf₁, hr] at h; rw [h, mul_adjT_adjT]
  have hd₂ : cross d₂ = σ * adjT j := by
    have h := cross_eq_mul u₂; rw [hf₂, hr] at h; rw [h, mul_adjT_adjT]
  have hle₁ : weakClass e ≤ WeakOrder.of (σ * adjT i) := hd₁ ▸ weakClass_le v₁
  have hle₂ : weakClass e ≤ WeakOrder.of (σ * adjT j) := hd₂ ▸ weakClass_le v₂
  have hne : ∀ x y : Fin n, (x : ℕ) ≠ (y : ℕ) → cross r x ≠ cross r y := fun x y hxy hc =>
    hxy (congrArg Fin.val ((cross r).injective hc))
  have hcard : (samePairs e).card ≤ 2 := by
    have := card_samePairs_le e (beadCard_le_two_of_disjoint hlen
      (atomPair_mem_samePairs u₁ hf₁ v₁) (atomPair_mem_samePairs u₂ hf₂ v₂)
      (hne _ _ (by simp only [adjHi_val]; omega))
      (hne _ _ (by simp only [adjHi_val, adjLo_val]; omega))
      (hne _ _ (by simp only [adjHi_val, adjLo_val]; omega))
      (hne _ _ (by simp only [adjLo_val]; omega)))
    omega
  refine cross_meet hr (u₁ ≫ v₁) ?_ hcard
    (WeakOrder.le_mul_adjT_mul_adjT hij hi hj hle₁ hle₂)
  have h1 := permLen_mul_adjT_of_descent hi
  have h2 := permLen_mul_adjT_of_descent (WeakOrder.descent_mul_adjT_far hij hj)
  omega

/-- **Consecutive cuts**: two atoms at adjacent cuts meet in the sorted three-window. -/
theorem cross_of_meet_braid {σ : Equiv.Perm (Fin n)} {r d₁ d₂ e : Ch (□n)} (hr : cross r = σ)
    {i j : Fin (n - 1)} (hij : (j : ℕ) = (i : ℕ) + 1)
    {u₁ : r ⟶ d₁} (hf₁ : crossPerm (dimSum_dims_cube r) u₁ = adjT i)
    {u₂ : r ⟶ d₂} (hf₂ : crossPerm (dimSum_dims_cube r) u₂ = adjT j)
    (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e) (hlen : e.dims.length + 2 = n) :
    cross e = σ * adjT i * adjT j * adjT i := by
  have hi : σ (adjHi i) < σ (adjLo i) := hr ▸ cross_descent_of_crossPerm_adjT u₁ hf₁
  have hj : σ (adjHi j) < σ (adjLo j) := hr ▸ cross_descent_of_crossPerm_adjT u₂ hf₂
  have hd₁ : cross d₁ = σ * adjT i := by
    have h := cross_eq_mul u₁; rw [hf₁, hr] at h; rw [h, mul_adjT_adjT]
  have hd₂ : cross d₂ = σ * adjT j := by
    have h := cross_eq_mul u₂; rw [hf₂, hr] at h; rw [h, mul_adjT_adjT]
  refine cross_meet hr (u₁ ≫ v₁) ?_ (card_samePairs_le_three e hlen)
    (WeakOrder.le_mul_adjT_braid hij hi hj (hd₁ ▸ weakClass_le v₁) (hd₂ ▸ weakClass_le v₂))
  have h1 := permLen_mul_adjT_of_descent hi
  have h2 := permLen_mul_adjT_of_descent (WeakOrder.descent_mul_adjT_braid₁ hij hi hj)
  have h3 := permLen_mul_adjT_of_descent (WeakOrder.descent_mul_adjT_braid₂ hij hj)
  omega

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
  have hs₁ : boundaries m ⊆ boundaries d₁.dims := by rw [hbm]; exact Finset.inter_subset_left
  have hs₂ : boundaries m ⊆ boundaries d₂.dims := by rw [hbm]; exact Finset.inter_subset_right
  have hmC : boundaries (cubeTop n).dims ⊆ boundaries m := by
    rw [hbm]
    exact Finset.subset_inter (boundaries_subset_of_hom (toCubeTop d₁))
      (boundaries_subset_of_hom (toCubeTop d₂))
  obtain ⟨e, hed, ⟨v₁⟩, -⟩ := exists_mid_chain (toCubeTop d₁) hm hs₁ hmC
  obtain ⟨e', hed', ⟨v₂⟩, -⟩ := exists_mid_chain (toCubeTop d₂) hm hs₂ hmC
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

/-- A block index that does not jump means no junction in between. -/
theorem notMem_boundaries_of_index_eq {d : List ℕ+} (hd : dimSum d = n) {z y : Fin n}
    (hzy : (y : ℕ) = (z : ℕ) + 1)
    (heq : ((dimComp d hd).index z : ℕ) = ((dimComp d hd).index y : ℕ)) :
    (y : ℕ) ∉ boundaries d := by
  intro hmem
  have hlt : ((dimComp d hd).index z : ℕ) < ((dimComp d hd).index y : ℕ) :=
    (index_lt_index_iff hd z y).mpr ⟨(y : ℕ), hmem, by omega, le_rfl⟩
  omega

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

/-- A shape's block index does not jump except at a junction. -/
private theorem index_eq_of_notMem {d : List ℕ+} (hd : dimSum d = n) {z y : Fin n}
    (hzy : (y : ℕ) = (z : ℕ) + 1) (hmem : (y : ℕ) ∉ boundaries d) :
    ((dimComp d hd).index z : ℕ) = ((dimComp d hd).index y : ℕ) := by
  have hle : ((dimComp d hd).index z : ℕ) ≤ ((dimComp d hd).index y : ℕ) :=
    (dimComp d hd).index_monotone (show z ≤ y from Fin.le_def.mpr (by omega))
  rcases eq_or_lt_of_le hle with hq | hq
  · exact hq
  · obtain ⟨t, ht, h1, h2⟩ := (index_lt_index_iff hd z y).mp hq
    exact absurd ((show t = (y : ℕ) by omega) ▸ ht) hmem

/-- **`W` is closed under meets**: two refinements of a chain that cross nothing have a common
coarsening that crosses nothing. -/
theorem exists_meet_cross_eq {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h : cross d₁ = cross d₂) :
    ∃ e : Ch (□n), Nonempty (d₁ ⟶ e) ∧ Nonempty (d₂ ⟶ e) ∧ cross e = cross d₁ := by
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hb⟩ := exists_meet u₁ u₂
  refine ⟨e, ⟨v₁⟩, ⟨v₂⟩, ?_⟩
  have hf₁ : flatten d₁ = (cross d₁)⁻¹ := by rw [cross_eq_flatten_inv, inv_inv]
  have hf₂ : flatten d₂ = (cross d₁)⁻¹ := by rw [h, cross_eq_flatten_inv, inv_inv]
  have hn : dimSum e.dims = n := wedgeDimSum_eq e.map
  set ψ : Equiv.Perm (Fin n) := cross d₁ with hψ
  set idx : Fin n → ℕ := fun z => ((dimComp e.dims hn).index z : ℕ) with hidxdef
  have hmono : ∀ x y : Fin n, (x : ℕ) ≤ (y : ℕ) → idx x ≤ idx y := fun x y hxy =>
    (dimComp e.dims hn).index_monotone (show x ≤ y from Fin.le_def.mpr hxy)
  have hbead : ∀ x : Fin n, (beadOf e (ψ x) : ℕ) = idx x := by
    intro x
    rw [beadOf_of_hom v₁, hf₁, hidxdef]
    simp
  have hstep : ∀ z y : Fin n, (y : ℕ) = (z : ℕ) + 1 → idx z = idx y → ψ z < ψ y := by
    intro z y hzy heq
    have hnot : (y : ℕ) ∉ boundaries e.dims := notMem_boundaries_of_index_eq hn hzy heq
    rw [hb, Finset.mem_inter] at hnot
    rcases not_and_or.mp hnot with hm | hm
    · exact lt_of_index_eq hf₁ (by omega) (index_eq_of_notMem _ hzy hm)
    · exact lt_of_index_eq hf₂ (by omega) (index_eq_of_notMem _ hzy hm)
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
  have hsort : ∀ x y : Fin n, x < y → (beadOf e (ψ x) : ℕ) < (beadOf e (ψ y) : ℕ)
      ∨ (beadOf e (ψ x) = beadOf e (ψ y) ∧ ψ x < ψ y) := by
    intro x y hxy
    rcases eq_or_lt_of_le (hmono x y (le_of_lt (Fin.lt_def.mp hxy))) with heq | hlt
    · refine Or.inr ⟨Fin.ext (by rw [hbead, hbead]; exact heq), ?_⟩
      refine lt_of_le_of_ne (hchain ((y : ℕ) - (x : ℕ)) x y (by
        have := Fin.lt_def.mp hxy; omega) heq) fun hc => ?_
      exact absurd (ψ.injective hc) (ne_of_lt hxy)
    · exact Or.inl (by rw [hbead, hbead]; exact hlt)
  have hkey : flatten e = flatten d₁ := by
    refine Equiv.ext fun c => ?_
    obtain ⟨x, rfl⟩ : ∃ x, ψ x = c := ⟨ψ.symm c, by simp⟩
    rw [flatten_apply e ψ hsort x, hf₁]
    simp
  rw [cross_eq_flatten_inv, hkey, ← cross_eq_flatten_inv]

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

/-- An adjacent swap does not move a coordinate out of the bead the atom's shape puts it in. -/
private theorem index_atomComp_adjT (n : ℕ) (i : Fin (n - 1)) (z : Fin n) :
    ((dimComp (atomComp n i) (dimSum_atomComp n i)).index (adjT i z) : ℕ)
      = ((dimComp (atomComp n i) (dimSum_atomComp n i)).index z : ℕ) := by
  rw [index_atomComp, index_atomComp]
  rcases eq_or_ne (z : ℕ) (i : ℕ) with hz | hz
  · rw [show adjT i z = adjHi i from by
      rw [show z = adjLo i from Fin.ext (by rw [adjLo_val]; exact hz)]; exact adjT_lo i]
    simp only [adjHi_val]
    split_ifs <;> omega
  rcases eq_or_ne (z : ℕ) ((i : ℕ) + 1) with hz' | hz'
  · rw [show adjT i z = adjLo i from by
      rw [show z = adjHi i from Fin.ext (by rw [adjHi_val]; exact hz')]; exact adjT_hi i]
    simp only [adjLo_val]
    split_ifs <;> omega
  · rw [WeakOrder.adjT_apply_of_ne hz hz']

/-- **The atom out of a run.**  A descent of the run's crossing permutation is realised by merging
the two events it names: the face has one two-event bead, and crosses that pair less. -/
theorem exists_atom_face {r : Ch (□n)} (hr : ∀ x ∈ r.dims, x = 1) {i : Fin (n - 1)}
    (hi : cross r (adjHi i) < cross r (adjLo i)) :
    ∃ (d : Ch (□n)) (_ : r ⟶ d), cross d = cross r * adjT i ∧ d.dims = atomComp n i := by
  have hi2 := i.isLt
  have hm : dimSum (atomComp n i) = n := dimSum_atomComp n i
  have hsub : boundaries (atomComp n i) ⊆ boundaries r.dims := by
    rw [boundaries_atomComp, cubeChain_dims_ones r hr, boundaries_ones]
    exact Finset.sdiff_subset
  have hmC : boundaries (cubeTop n).dims ⊆ boundaries (atomComp n i) := by
    refine subset_trans (boundaries_topDims_subset n) ?_
    rw [boundaries_atomComp]
    intro x hx
    have hx' : x = 0 ∨ x = n := by
      rcases Finset.mem_insert.mp hx with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega),
      by simp only [Finset.mem_singleton]; omega⟩
  obtain ⟨d, hdd, ⟨h⟩, -⟩ := exists_mid_chain (toCubeTop r) hm hsub hmC
  obtain ⟨dd, χ⟩ := d
  change dd = atomComp n i at hdd
  subst hdd
  refine ⟨⟨atomComp n i, χ⟩, h, ?_, rfl⟩
  have hfr : flatten r = (cross r)⁻¹ := by rw [cross_eq_flatten_inv, inv_inv]
  set g : Equiv.Perm (Fin n) := cross r * adjT i with hg
  have hbead : ∀ x : Fin n, (beadOf (⟨atomComp n i, χ⟩ : Ch (□n)) (g x) : ℕ)
      = ((dimComp (atomComp n i) (dimSum_atomComp n i)).index x : ℕ) := by
    intro x
    rw [beadOf_of_hom h]
    have hfx : flatten r (g x) = adjT i x := by rw [hfr, hg]; simp
    rw [hfx]
    exact index_atomComp_adjT n i x
  have hsort : ∀ x y : Fin n, x < y →
      (beadOf (⟨atomComp n i, χ⟩ : Ch (□n)) (g x) : ℕ)
        < (beadOf (⟨atomComp n i, χ⟩ : Ch (□n)) (g y) : ℕ)
      ∨ (beadOf (⟨atomComp n i, χ⟩ : Ch (□n)) (g x)
          = beadOf (⟨atomComp n i, χ⟩ : Ch (□n)) (g y) ∧ g x < g y) := by
    intro x y hxy
    have hmono : ((dimComp (atomComp n i) (dimSum_atomComp n i)).index x : ℕ)
        ≤ ((dimComp (atomComp n i) (dimSum_atomComp n i)).index y : ℕ) :=
      (dimComp (atomComp n i) (dimSum_atomComp n i)).index_monotone (le_of_lt hxy)
    rcases eq_or_lt_of_le hmono with heq | hlt
    · obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq n i (Fin.ext heq) hxy
      refine Or.inr ⟨Fin.ext (by rw [hbead, hbead]; exact heq), ?_⟩
      rw [hg]
      simp only [Equiv.Perm.mul_apply, adjT_lo, adjT_hi]
      exact hi
    · exact Or.inl (by rw [hbead, hbead]; exact hlt)
  have hkey : flatten (⟨atomComp n i, χ⟩ : Ch (□n)) = g⁻¹ := by
    refine Equiv.ext fun c => ?_
    obtain ⟨x, rfl⟩ : ∃ x, g x = c := ⟨g.symm c, by simp⟩
    rw [flatten_apply (⟨atomComp n i, χ⟩ : Ch (□n)) g hsort x]
    simp
  rw [cross_eq_flatten_inv, hkey, inv_inv]

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
  have hfr : flatten r = σ⁻¹ := by rw [← hcr, cross_eq_flatten_inv, inv_inv]
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
  have hsq : ∀ w : Fin n, ((σ⁻¹ q : Fin n) : ℕ) ≤ (w : ℕ) → (w : ℕ) ≤ ((σ⁻¹ p : Fin n) : ℕ) →
      ((dimComp d.dims (wedgeDimSum_eq d.map)).index w : ℕ)
        = ((dimComp d.dims (wedgeDimSum_eq d.map)).index (σ⁻¹ q) : ℕ) := by
    intro w h1 h2
    have m1 : ((dimComp d.dims (wedgeDimSum_eq d.map)).index (σ⁻¹ q) : ℕ)
        ≤ ((dimComp d.dims (wedgeDimSum_eq d.map)).index w : ℕ) :=
      (dimComp d.dims (wedgeDimSum_eq d.map)).index_monotone (Fin.le_def.mpr h1)
    have m2 : ((dimComp d.dims (wedgeDimSum_eq d.map)).index w : ℕ)
        ≤ ((dimComp d.dims (wedgeDimSum_eq d.map)).index (σ⁻¹ p) : ℕ) :=
      (dimComp d.dims (wedgeDimSum_eq d.map)).index_monotone (Fin.le_def.mpr h2)
    have m3 : ((dimComp d.dims (wedgeDimSum_eq d.map)).index (σ⁻¹ p) : ℕ)
        = ((dimComp d.dims (wedgeDimSum_eq d.map)).index (σ⁻¹ q) : ℕ) := by
      rw [hidx, hidx]
      rw [show σ (σ⁻¹ p) = p from by simp, show σ (σ⁻¹ q) = q from by simp]
      exact congrArg Fin.val hbd
    omega
  have hnotmem : (z + 1) ∉ boundaries d.dims := by
    have e1 := hsq (⟨z, by omega⟩ : Fin n) hz1 (le_of_lt hz2)
    have e2 := hsq (⟨z + 1, hzn⟩ : Fin n)
      (show ((σ⁻¹ q : Fin n) : ℕ) ≤ z + 1 by omega)
      (show z + 1 ≤ ((σ⁻¹ p : Fin n) : ℕ) by omega)
    exact notMem_boundaries_of_index_eq (d := d.dims) (wedgeDimSum_eq d.map)
      (z := (⟨z, by omega⟩ : Fin n)) (y := (⟨z + 1, hzn⟩ : Fin n)) rfl (e1.trans e2.symm)
  have hsub : boundaries d.dims ⊆ boundaries e.dims := by
    rw [hde, boundaries_atomComp]
    intro t ht
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · have := boundaries_subset_of_hom u ht
      rwa [cubeChain_dims_ones r hrd, boundaries_ones] at this
    · simp only [Finset.mem_singleton]
      rintro rfl
      exact hnotmem ht
  obtain ⟨M, hMd, ⟨w⟩, -⟩ := exists_mid_chain (toCubeTop e) (dimSum_dims_cube d) hsub
    (boundaries_subset_of_hom (toCubeTop d))
  exact ⟨(chain_ext_of_dims (v ≫ w) u hMd) ▸ w⟩


/-! ## Codimension-one faces meet one step up -/

/-- **Two codimension-one refinements of a chain meet in one face**, one further step up from each:
the meet deletes both junctions, and they are distinct. -/
theorem exists_join {a d₁ d₂ : Ch (□n)} (u₁ : a ⟶ d₁) (u₂ : a ⟶ d₂)
    (h₁ : codim u₁ = 1) (h₂ : codim u₂ = 1) (hne : d₁ ≠ d₂) :
    ∃ (e : Ch (□n)) (v₁ : d₁ ⟶ e) (v₂ : d₂ ⟶ e), codim v₁ = 1 ∧ codim v₂ = 1 := by
  obtain ⟨e, ⟨v₁⟩, ⟨v₂⟩, hb⟩ := exists_meet u₁ u₂
  have hga := degree_add_length a
  have hgd₁ := degree_add_length d₁
  have hgd₂ := degree_add_length d₂
  have hge := degree_add_length e
  have hna := dimSum_dims_cube a
  have hnd₁ := dimSum_dims_cube d₁
  have hnd₂ := dimSum_dims_cube d₂
  have hnee := dimSum_dims_cube e
  have hle₁ := degree_le_of_hom u₁
  have hle₂ := degree_le_of_hom u₂
  have hlev₁ := degree_le_of_hom v₁
  have hlev₂ := degree_le_of_hom v₂
  rw [codim] at h₁ h₂
  have hca := card_boundaries a.dims
  have hcd₁ := card_boundaries d₁.dims
  have hcd₂ := card_boundaries d₂.dims
  have hce := card_boundaries e.dims
  have hbe : (boundaries e.dims).card
      = (boundaries d₁.dims ∩ boundaries d₂.dims).card := by rw [hb]
  have hunion : (boundaries d₁.dims ∪ boundaries d₂.dims).card ≤ (boundaries a.dims).card :=
    Finset.card_le_card (Finset.union_subset (boundaries_subset_of_hom u₁)
      (boundaries_subset_of_hom u₂))
  have hui := Finset.card_union_add_card_inter (boundaries d₁.dims) (boundaries d₂.dims)
  have hnsub : ¬ (boundaries d₁.dims ⊆ boundaries d₂.dims) := fun hc =>
    hne (chain_ext_of_dims u₁ u₂ (boundaries_injective
      (Finset.eq_of_subset_of_card_le hc (by omega))))
  obtain ⟨x, hx1, hx2⟩ := Finset.not_subset.mp hnsub
  have hstrict : (boundaries d₁.dims ∩ boundaries d₂.dims).card < (boundaries d₁.dims).card :=
    Finset.card_lt_card ((Finset.ssubset_iff_of_subset Finset.inter_subset_left).mpr
      ⟨x, hx1, fun hc => hx2 (Finset.mem_inter.mp hc).2⟩)
  exact ⟨e, v₁, v₂, by rw [codim]; omega, by rw [codim]; omega⟩

/-- **The bare cube has diamonds** — `exists_join` supplies the two steps, thinness the square.
Adjacent cuts have distinct target shapes, which is all `exists_join` needs of `d ≠ d'`. -/
theorem hasDiamonds_cube (n : ℕ) : HasDiamonds (□n) := by
  intro a d d' u u' c c' hadj
  obtain ⟨e, v, v', hv, hv'⟩ := exists_join u u' c.codim_eq_one c'.codim_eq_one
    fun hdd => c.tgt_dims_ne_of_adjacent c' hadj (congrArg ChainCat.Obj.dims hdd)
  exact ⟨e, v, v', hv, hv', Subsingleton.elim _ _⟩

end ChainCat
