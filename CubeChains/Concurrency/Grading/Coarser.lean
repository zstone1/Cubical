import CubeChains.Concurrency.Grading.ChartHom

/-!
# Concurrency/Grading/Coarser — factoring through an intermediate shape

Between a chart and a coarsening of it, a shape is realised by exactly one chain.  Uniqueness: the
initial runs of the coarsening's beads are down-sets for the source's bead order, and down-sets of
a total order are linearly ordered by inclusion, so `card_beadOf_lt` pins them.  Existence: send a
coordinate to the block of the shape in which its own bead starts.

Read in a chart of the target, that is `compEquiv` — composition through an intermediate shape is a
bijection, `factor_ext` its injectivity and `exists_factor` its surjectivity.

This file is where the shape model stops: `boundaries` is used to prove `exists_first` and
`exists_diamond`, whose statements mention only `codim` and composition, and the presentation
above sees nothing else.
-/

open CategoryTheory Equiv CubeChains CubeChain BPSet StdCube ChainCat

namespace CubeChains

@[simp] theorem dimSum_single (n : ℕ+) : dimSum [n] = (n : ℕ) := by simp [dimSum]

/-! ## A coarsening of an ordered partition is pinned by its shape -/

/-- Under a refinement the target's bead order is coarser than the source's. -/
theorem beadOf_le_of_hom {N : ℕ} {A M : Ch (□N)} (f : A ⟶ M) {r s : Fin N}
    (h : (beadOf A r : ℕ) ≤ (beadOf A s : ℕ)) : (beadOf M r : ℕ) ≤ (beadOf M s : ℕ) := by
  by_contra hc
  exact absurd ((chFace_faceLE_iff.mp (chFace_faceLE f) s r (by omega)).mp (by omega)) (by omega)

/-- Down-sets of a total order are linearly ordered by inclusion, so the larger contains the
smaller. -/
theorem downSet_subset {N : ℕ} {L : Type*} [LinearOrder L] {g : Fin N → L}
    {T T' : Finset (Fin N)}
    (hT : ∀ r s, g r ≤ g s → s ∈ T → r ∈ T) (hT' : ∀ r s, g r ≤ g s → s ∈ T' → r ∈ T')
    (hcard : T'.card ≤ T.card) : T' ⊆ T := by
  by_contra hsub
  obtain ⟨r, hrT', hrT⟩ := Finset.not_subset.mp hsub
  have hsub' : T ⊆ T' := fun s hs => by
    rcases le_total (g s) (g r) with hle | hle
    · exact hT' s r hle hrT'
    · exact absurd (hT r s hle hs) hrT
  exact absurd (Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub').mpr ⟨r, hrT', hrT⟩))
    (by omega)

/-- **A coarsening is pinned by its shape**: two refinements of one chain of a cube with the same
bead dimensions are the same chain. -/
theorem chain_ext_of_dims {N : ℕ} {A M M' : Ch (□N)} (f : A ⟶ M) (f' : A ⟶ M')
    (h : M.dims = M'.dims) : M = M' := by
  have hd : ∀ (P : Ch (□N)), (A ⟶ P) → ∀ (j : ℕ) (r s : Fin N),
      (beadOf A r : ℕ) ≤ (beadOf A s : ℕ) →
      s ∈ Finset.univ.filter (fun t : Fin N => (beadOf P t : ℕ) < j) →
      r ∈ Finset.univ.filter (fun t : Fin N => (beadOf P t : ℕ) < j) := by
    intro P u j r s hrs hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact lt_of_le_of_lt (beadOf_le_of_hom u hrs) hs
  have hset : ∀ j : ℕ, (Finset.univ.filter fun r : Fin N => (beadOf M r : ℕ) < j)
      = Finset.univ.filter fun r : Fin N => (beadOf M' r : ℕ) < j := fun j => by
    have hcard : (Finset.univ.filter fun r : Fin N => (beadOf M r : ℕ) < j).card
        = (Finset.univ.filter fun r : Fin N => (beadOf M' r : ℕ) < j).card := by
      rw [card_beadOf_lt, card_beadOf_lt, h]
    exact Finset.Subset.antisymm
      (downSet_subset (g := fun r => (beadOf A r : ℕ)) (hd M' f' j) (hd M f j) hcard.le)
      (downSet_subset (g := fun r => (beadOf A r : ℕ)) (hd M f j) (hd M' f' j) hcard.ge)
  refine eq_of_beadOf fun q => ?_
  have key : ∀ j : ℕ, (beadOf M q : ℕ) < j ↔ (beadOf M' q : ℕ) < j := fun j => by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using Finset.ext_iff.mp (hset j) q
  have h1 := (key ((beadOf M q : ℕ) + 1)).mp (Nat.lt_succ_self _)
  have h2 := (key ((beadOf M' q : ℕ) + 1)).mpr (Nat.lt_succ_self _)
  omega

/-! ## Realising an intermediate shape

Send a coordinate to the block of the shape in which the *start of its own bead* falls.
`card_beadOf_lt` turns the shape's prefix sums back into coordinate counts, which pins the
result. -/

/-- Where a coordinate's bead starts. -/
private def beadPos {N : ℕ} (A : Ch (□N)) (r : Fin N) : ℕ := beadStart A.dims (beadOf A r)

private theorem beadPos_lt {N : ℕ} (A : Ch (□N)) (r : Fin N) : beadPos A r < N := by
  have h := wedgeDimSum_eq A.map
  have hlt := beadStart_lt_beadStart (d := A.dims) (j := A.dims.length) le_rfl (beadOf A r).isLt
  rw [beadStart_length] at hlt
  change beadStart A.dims (beadOf A r) < N
  omega

private theorem beadPos_lt_iff {N : ℕ} (A : Ch (□N)) {r : Fin N} {i : ℕ} (hi : i ≤ A.dims.length) :
    beadPos A r < beadStart A.dims i ↔ (beadOf A r : ℕ) < i := by
  refine ⟨fun h => ?_, fun h => beadStart_lt_beadStart hi h⟩
  by_contra hc
  exact absurd (beadStart_mono A.dims (not_lt.mp hc)) (by simpa only [beadPos] using not_le.mpr h)

private theorem card_beadPos_lt {N : ℕ} (A : Ch (□N)) {i : ℕ} (hi : i ≤ A.dims.length) :
    (Finset.univ.filter fun r : Fin N => beadPos A r < beadStart A.dims i).card
      = beadStart A.dims i := by
  have h : (Finset.univ.filter fun r : Fin N => beadPos A r < beadStart A.dims i)
      = Finset.univ.filter fun r : Fin N => (beadOf A r : ℕ) < i :=
    Finset.filter_congr fun r _ => beadPos_lt_iff A hi
  rw [h, card_beadOf_lt]

/-- **Junctions compare by counting coordinates**: a down-set inclusion is a `beadStart`
inequality, `card_beadOf_lt` read at both ends. -/
private theorem beadStart_le_of_subset {N : ℕ} {A C : Ch (□N)} {i j : ℕ}
    (h : ∀ s : Fin N, (beadOf A s : ℕ) < i → (beadOf C s : ℕ) < j) :
    beadStart A.dims i ≤ beadStart C.dims j := by
  rw [← card_beadOf_lt A i, ← card_beadOf_lt C j]
  exact Finset.card_le_card fun s hs =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h s (Finset.mem_filter.mp hs).2⟩

/-- **The intermediate chain's bead map**: a coordinate goes to the block of `m` in which its own
bead starts. -/
private def midBead {N : ℕ} (A : Ch (□N)) {m : List ℕ+} (hm : dimSum m = N) (r : Fin N) :
    Fin (dimComp m hm).length :=
  (dimComp m hm).index ⟨beadPos A r, beadPos_lt A r⟩

private theorem midBead_lt_iff {N : ℕ} (A : Ch (□N)) {m : List ℕ+} (hm : dimSum m = N)
    (r : Fin N) (j : ℕ) :
    (midBead A hm r : ℕ) < j ↔ beadPos A r < beadStart m j :=
  index_lt_iff_beadStart hm _ j

private theorem beadPos_lt_of_midBead_lt {N : ℕ} (A : Ch (□N)) {m : List ℕ+} (hm : dimSum m = N)
    {r s : Fin N} (h : (midBead A hm r : ℕ) < (midBead A hm s : ℕ)) :
    beadPos A r < beadPos A s :=
  lt_of_lt_of_le ((midBead_lt_iff A hm r _).mp h)
    (not_lt.mp fun hc => absurd ((midBead_lt_iff A hm s _).mpr hc) (lt_irrefl _))

private theorem midBead_le_of_beadPos_le {N : ℕ} (A : Ch (□N)) {m : List ℕ+} (hm : dimSum m = N)
    {r s : Fin N} (h : beadPos A r ≤ beadPos A s) :
    (midBead A hm r : ℕ) ≤ (midBead A hm s : ℕ) :=
  not_lt.mp fun hc => absurd (beadPos_lt_of_midBead_lt A hm hc) (by omega)

/-- **A shape between two comparable chains of a cube is realised between them.** -/
theorem exists_mid_chain {N : ℕ} {A C : Ch (□N)} (u : A ⟶ C) {m : List ℕ+} (hm : dimSum m = N)
    (hAm : boundaries m ⊆ boundaries A.dims) (hmC : boundaries C.dims ⊆ boundaries m) :
    ∃ M : Ch (□N), M.dims = m ∧ Nonempty (A ⟶ M) ∧ Nonempty (M ⟶ C) := by
  have hNA : dimSum A.dims = N := wedgeDimSum_eq A.map
  have hpull : ∀ j ≤ m.length, ∃ i ≤ A.dims.length, beadStart A.dims i = beadStart m j :=
    fun j hj => mem_boundaries_iff_beadStart.mp (hAm (beadStart_mem_boundaries m hj))
  have hcard : ∀ j ≤ m.length,
      (Finset.univ.filter fun r : Fin N => (midBead A hm r : ℕ) < j).card = beadStart m j := by
    intro j hj
    obtain ⟨i, hi, hib⟩ := hpull j hj
    have hfil : (Finset.univ.filter fun r : Fin N => (midBead A hm r : ℕ) < j)
        = Finset.univ.filter fun r : Fin N => beadPos A r < beadStart A.dims i :=
      Finset.filter_congr fun r _ => by rw [hib]; exact midBead_lt_iff A hm r j
    rw [hfil, card_beadPos_lt A hi, hib]
  have hsurj : Function.Surjective (midBead A hm) := by
    intro j
    have hjm : (j : ℕ) < m.length := by rw [← dimComp_length m hm]; exact j.isLt
    obtain ⟨i, hi, hib⟩ := hpull j hjm.le
    have hilt : i < A.dims.length := by
      rcases lt_or_eq_of_le hi with hlt | rfl
      · exact hlt
      · exfalso
        have h1 : beadStart m (j : ℕ) < beadStart m m.length :=
          beadStart_lt_beadStart le_rfl hjm
        rw [beadStart_length, hm] at h1
        rw [beadStart_length, hNA] at hib
        omega
    obtain ⟨r, hr⟩ := beadOf_surjective A ⟨i, hilt⟩
    have hpos : beadPos A r = beadStart m (j : ℕ) := by rw [beadPos, hr]; exact hib
    refine ⟨r, Fin.ext (Nat.le_antisymm ?_ ?_)⟩
    · exact Nat.lt_succ_iff.mp ((midBead_lt_iff A hm r _).mpr
        (by rw [hpos]; exact beadStart_lt_beadStart hjm (Nat.lt_succ_self _)))
    · by_contra hc
      exact absurd ((midBead_lt_iff A hm r _).mp (not_le.mp hc))
        (by rw [hpos]; exact lt_irrefl _)
  refine ⟨blockChain (midBead A hm) hsurj, dims_blockChain hm hsurj hcard, ?_, ?_⟩
  · refine ⟨reflectHom (chFace_faceLE_iff.mpr fun p q hne => ?_)⟩
    rw [beadOf_blockChain, beadOf_blockChain] at hne ⊢
    exact ⟨fun h => (beadPos_lt_iff A (beadOf A q).isLt.le).mp
        (beadPos_lt_of_midBead_lt A hm h),
      fun h => lt_of_le_of_ne (midBead_le_of_beadPos_le A hm
        (beadStart_lt_beadStart (beadOf A q).isLt.le h).le) hne⟩
  · refine ⟨reflectHom (chFace_faceLE_iff.mpr fun p q hne => ?_)⟩
    rw [beadOf_blockChain, beadOf_blockChain]
    have hAC : ∀ r s : Fin N, (beadOf C r : ℕ) < (beadOf C s : ℕ) →
        (beadOf A r : ℕ) < (beadOf A s : ℕ) := fun r s h =>
      (chFace_faceLE_iff.mp (chFace_faceLE u) r s (by omega)).mp h
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hle : beadStart C.dims (beadOf C q) ≤ beadPos A q :=
        beadStart_le_of_subset fun s hs => hAC s q hs
      have hgt : beadPos A p < beadStart C.dims (beadOf C q) :=
        lt_of_lt_of_le
          (beadStart_lt_beadStart (beadOf A p).isLt (Nat.lt_succ_self (beadOf A p : ℕ)))
          (beadStart_le_of_subset fun s hs =>
            lt_of_le_of_lt (beadOf_le_of_hom u (Nat.lt_succ_iff.mp hs)) h)
      obtain ⟨j', hj', hjb⟩ := mem_boundaries_iff_beadStart.mp
        (hmC (beadStart_mem_boundaries C.dims (beadOf C q).isLt.le))
      have hlt1 : (midBead A hm p : ℕ) < j' :=
        (midBead_lt_iff A hm p j').mpr (by rw [hjb]; exact hgt)
      have hlt2 : ¬ ((midBead A hm q : ℕ) < j') := fun hc =>
        absurd ((midBead_lt_iff A hm q j').mp hc) (by rw [hjb]; omega)
      omega
    · refine lt_of_le_of_ne (beadOf_le_of_hom u ((beadPos_lt_iff A (beadOf A q).isLt.le).mp
        (beadPos_lt_of_midBead_lt A hm h)).le) hne

end CubeChains

namespace ChainCat

open CubeChains

variable {a m b : Ch Zbp}

/-! ## The cut of a refinement

The shape model, used from here down and hidden above it: a refinement drops a set of the source's
junctions, and the codimension counts them. -/

/-- The boundaries a refinement of serial wedges removes. -/
def cutsOf {a b : Ch Zbp} (_f : a ⟶ b) : Finset ℕ := boundaries a.dims \ boundaries b.dims

theorem card_cutsOf {a b : Ch Zbp} (f : a ⟶ b) : (cutsOf f).card = codim f :=
  (codim_eq_card_sdiff f).symm

theorem cutsOf_comp {a b c : Ch Zbp} (f : a ⟶ b) (g : b ⟶ c) :
    cutsOf (f ≫ g) = cutsOf f ∪ cutsOf g := by
  rw [cutsOf, cutsOf, cutsOf, ← Finset.sup_eq_union]
  exact (sdiff_sup_sdiff_cancel (boundaries_subset_of_hom f) (boundaries_subset_of_hom g)).symm

/-- **The target keeps exactly the boundaries the refinement does not cut.** -/
theorem boundaries_sdiff_cutsOf {a b : Ch Zbp} (f : a ⟶ b) :
    boundaries b.dims = boundaries a.dims \ cutsOf f :=
  (Finset.sdiff_sdiff_eq_self (boundaries_subset_of_hom f)).symm

/-- Where a one-cut refinement's cut sits. -/
theorem mem_cutsOf {f : a ⟶ b} {t : ℕ} (h : cutsOf f = {t}) :
    t ∈ boundaries a.dims ∧ t ∉ boundaries b.dims := by
  have ht : t ∈ cutsOf f := h ▸ Finset.mem_singleton_self t
  exact Finset.mem_sdiff.mp ht

theorem exists_cutsOf_eq_singleton {f : a ⟶ b} (h : codim f = 1) : ∃ t, cutsOf f = {t} :=
  Finset.card_eq_one.mp ((card_cutsOf f).trans h)

theorem codim_eq_one_of_cutsOf {f : a ⟶ b} {t : ℕ} (h : cutsOf f = {t}) : codim f = 1 := by
  rw [← card_cutsOf, h, Finset.card_singleton]

/-- **A one-cut refinement erases exactly its cut from the boundary set.** -/
theorem boundaries_eq_erase {f : a ⟶ b} {t : ℕ} (h : cutsOf f = {t}) :
    boundaries b.dims = (boundaries a.dims).erase t := by
  rw [Finset.erase_eq, ← h, boundaries_sdiff_cutsOf f]

theorem cutsOf_eq_singleton {f : a ⟶ b} {t : ℕ} (ht : t ∈ boundaries a.dims)
    (h : boundaries b.dims = (boundaries a.dims).erase t) : cutsOf f = {t} := by
  rw [cutsOf, h, Finset.sdiff_erase_self ht]

/-- **A step is pinned by the boundary it removes** — an equation of shapes, not an iso, since a
shape is its boundary set. -/
theorem mid_eq_of_cuts_eq {c c' : Ch Zbp} {e : a ⟶ c} {e' : a ⟶ c'} {t : ℕ}
    (h : cutsOf e = {t}) (h' : cutsOf e' = {t}) : c = c' :=
  Obj.eq_of_dims
    (boundaries_injective ((boundaries_eq_erase h).trans (boundaries_eq_erase h').symm))

/-! ## The two extremes

The run `1ᴺ` refines every shape on `N` events and one bead coarsens every one — the boundary
inclusions are `⊆ range (N+1)` and `{0, N} ⊆ ·`. -/

/-- **The run has every boundary.** -/
@[simp] theorem boundaries_ones (N : ℕ) : boundaries (𝟙^N) = Finset.range (N + 1) := by
  ext t
  rw [mem_boundaries_iff, Finset.mem_range]
  constructor
  · rintro ⟨l, r, hlr, rfl⟩
    have hl : ∀ d ∈ l, d = (1 : ℕ+) := fun d hd =>
      List.eq_of_mem_replicate (hlr ▸ List.mem_append_left r hd)
    have hlen := congrArg List.length hlr
    simp only [List.length_replicate, List.length_append] at hlen
    rw [dimSum_eq_length_of_ones hl]
    omega
  · exact fun ht => ⟨𝟙^t, 𝟙^(N - t),
      by rw [← List.replicate_add, show t + (N - t) = N by omega], dimSum_replicate t⟩

/-- **The run refines every shape on its event count.** -/
theorem nonempty_hom_ones {d : List ℕ+} {N : ℕ} (h : dimSum d = N) :
    Nonempty (zObj (𝟙^N) ⟶ zObj d) :=
  nonempty_hom_iff.mpr ⟨(dimSum_replicate N).trans h.symm, fun _ ht =>
    boundaries_ones N ▸ Finset.mem_range.mpr
      (Nat.lt_succ_of_le (h ▸ le_dimSum_of_mem_boundaries ht))⟩

/-! ### The cuts out of the run

A shape *is* its boundary set, so out of the run a refinement is exactly the set of the run's `N-1`
junctions it drops — and the codimension counts them. -/

/-- Out of the run every position is a boundary, so a cut is an interior one. -/
theorem cutsOf_ones_subset {N : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b) :
    cutsOf f ⊆ Finset.Ioo 0 N := by
  have hdim : dimSum b.dims = N := (strandsEq f).symm.trans (dimSum_replicate N)
  intro s hs
  rw [cutsOf, zObj_dims, boundaries_ones, Finset.mem_sdiff] at hs
  exact Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero fun h => hs.2 (h ▸ zero_mem_boundaries _),
    lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs.1)) fun h =>
      hs.2 (h ▸ hdim ▸ dimSum_mem_boundaries _)⟩

/-- **Out of the run a refinement is the set of junctions it drops.** -/
theorem codim_ones_iff {N k : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b) :
    codim f = k ↔ ∃ S ⊆ Finset.Ioo 0 N, S.card = k ∧
      boundaries b.dims = Finset.range (N + 1) \ S := by
  have hb : boundaries b.dims = Finset.range (N + 1) \ cutsOf f := by
    rw [boundaries_sdiff_cutsOf f, zObj_dims, boundaries_ones]
  refine ⟨fun h => ⟨cutsOf f, cutsOf_ones_subset f, (card_cutsOf f).trans h, hb⟩, ?_⟩
  rintro ⟨S, hS, rfl, hbS⟩
  have hSr : S ⊆ Finset.range (N + 1) := hS.trans fun s hs =>
    Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_Ioo.mp hs).2)
  have hcut : cutsOf f = S := by
    rw [cutsOf, zObj_dims, boundaries_ones, hbS, Finset.sdiff_sdiff_eq_self hSr]
  rw [← card_cutsOf f, hcut]

/-- **Out of the run, codimension one drops one junction.** -/
theorem codim_eq_one_ones_iff {N : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b) :
    codim f = 1 ↔ ∃ s, 0 < s ∧ s < N ∧ boundaries b.dims = Finset.range (N + 1) \ {s} := by
  rw [codim_ones_iff f]
  constructor
  · rintro ⟨S, hS, hcard, hb⟩
    obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨h0, hN⟩ := Finset.mem_Ioo.mp (hS (Finset.mem_singleton_self s))
    exact ⟨s, h0, hN, hb⟩
  · rintro ⟨s, h0, hN, hb⟩
    exact ⟨{s}, Finset.singleton_subset_iff.mpr (Finset.mem_Ioo.mpr ⟨h0, hN⟩),
      Finset.card_singleton s, hb⟩

/-- **The two codimension-two species out of the run**: the two junctions dropped are adjacent —
one bead cut in three, the braid relation — or apart — two disjoint edge pairs, commutation. -/
theorem codim_eq_two_ones_iff {N : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b) :
    codim f = 2 ↔ ∃ s t, 0 < s ∧ s < t ∧ t < N ∧
      boundaries b.dims = Finset.range (N + 1) \ {s, t} := by
  rw [codim_ones_iff f]
  constructor
  · rintro ⟨S, hS, hcard, hb⟩
    obtain ⟨s, t, hst, rfl⟩ := Finset.card_eq_two.mp hcard
    have hs := Finset.mem_Ioo.mp (hS (Finset.mem_insert_self s {t}))
    have ht := Finset.mem_Ioo.mp (hS (Finset.mem_insert_of_mem (Finset.mem_singleton_self t)))
    rcases lt_or_gt_of_ne hst with h | h
    · exact ⟨s, t, hs.1, h, ht.2, hb⟩
    · exact ⟨t, s, ht.1, h, hs.2, by rwa [Finset.pair_comm t s]⟩
  · rintro ⟨s, t, h0, hst, hN, hb⟩
    exact ⟨{s, t}, Finset.insert_subset (Finset.mem_Ioo.mpr ⟨h0, hst.trans hN⟩)
      (Finset.singleton_subset_iff.mpr (Finset.mem_Ioo.mpr ⟨h0.trans hst, hN⟩)),
      Finset.card_pair hst.ne, hb⟩

/-- **One bead coarsens every shape on its event count.** -/
theorem nonempty_hom_single {d : List ℕ+} {m : ℕ+} (h : dimSum d = (m : ℕ)) :
    Nonempty (zObj d ⟶ zObj [m]) := by
  refine nonempty_hom_iff.mpr ⟨h.trans (dimSum_single m).symm, fun t ht => ?_⟩
  rw [show (zObj [m]).dims = [m] from rfl, boundaries_singleton] at ht
  rcases Finset.mem_insert.mp ht with rfl | ht'
  · exact zero_mem_boundaries d
  · rw [show (zObj d).dims = d from rfl, Finset.mem_singleton.mp ht', ← h]
    exact dimSum_mem_boundaries d

/-! ## Unique factorisation through an intermediate shape

Read in a chart of `b`, a factorisation of `f : a ⟶ b` through `m` *is* a chain of `□N` of shape
`m.dims` between the two — and `exists_mid_chain` and `chain_ext_of_dims` say there is exactly
one. -/

/-- **The two factors are determined**: the intermediate chart is a coarsening of `a`'s of shape
`m.dims`, hence unique, and a chart is a monomorphism. -/
theorem factor_ext {f : a ⟶ b} {g g' : a ⟶ m} {e e' : m ⟶ b}
    (h : g ≫ e = f) (h' : g' ≫ e' = f) : g = g' ∧ e = e' := by
  obtain ⟨χ⟩ := nonempty_toCube b.dims
  have hφ : ∀ {u : a ⟶ m} {v : m ⟶ b}, u ≫ v = f →
      Hom.φ u ≫ (Hom.φ v ≫ χ) = Hom.φ f ≫ χ := fun {u v} huv => by
    rw [← Category.assoc, ← comp_φ, huv]
  obtain ⟨φg, hg⟩ : ∃ w : ⋁a.dims ⟶ ⋁m.dims, w ≫ (Hom.φ e ≫ χ) = Hom.φ f ≫ χ :=
    ⟨_, hφ h⟩
  obtain ⟨φg', hg'⟩ : ∃ w : ⋁a.dims ⟶ ⋁m.dims, w ≫ (Hom.φ e' ≫ χ) = Hom.φ f ≫ χ :=
    ⟨_, hφ h'⟩
  have hMM' : (⟨m.dims, Hom.φ e ≫ χ⟩ : Ch (□(dimSum b.dims)))
      = ⟨m.dims, Hom.φ e' ≫ χ⟩ :=
    chain_ext_of_dims (A := ⟨a.dims, Hom.φ f ≫ χ⟩) ⟨φg, hg⟩ ⟨φg', hg'⟩ rfl
  obtain ⟨hd, hmap⟩ := ChainCat.Obj.eq_mk_of_eq hMM'
  rw [Subsingleton.elim hd rfl] at hmap
  have hee : Hom.φ e = Hom.φ e' := wedgeHom_ext_chart (by simpa using hmap)
  have hcomp : Hom.φ g ≫ (Hom.φ e ≫ χ) = Hom.φ g' ≫ (Hom.φ e ≫ χ) := by
    rw [hφ h, hee, hφ h']
  haveI := chart_mono (⟨m.dims, Hom.φ e ≫ χ⟩ : Ch (□(dimSum b.dims)))
  refine ⟨hom_ext' (BPSet.hom_ext ((cancel_mono (Hom.φ e ≫ χ).hom).mp ?_)), hom_ext' hee⟩
  rw [← comp_hom, ← comp_hom, hcomp]

/-- **Factorisation through an intermediate shape.**  Read in a chart of `b`, the factorisation is
an intermediate chain of the cube — which `exists_mid_chain` supplies. -/
theorem exists_factor (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b)) (f : a ⟶ b) :
    ∃ (g : a ⟶ m) (e : m ⟶ b), g ≫ e = f := by
  obtain ⟨χ⟩ := nonempty_toCube b.dims
  obtain ⟨w⟩ := ham
  obtain ⟨v⟩ := hmb
  obtain ⟨φf, hφf⟩ : ∃ z : ⋁a.dims ⟶ ⋁b.dims, z ≫ χ = Hom.φ f ≫ χ := ⟨Hom.φ f, rfl⟩
  obtain ⟨M, hMd, ⟨g₀⟩, ⟨e₀⟩⟩ := exists_mid_chain
    (A := (⟨a.dims, Hom.φ f ≫ χ⟩ : Ch (□(dimSum b.dims))))
    (C := (⟨b.dims, χ⟩ : Ch (□(dimSum b.dims)))) ⟨φf, hφf⟩
    ((strandsEq w).symm.trans (strandsEq f)) (boundaries_subset_of_hom w)
    (boundaries_subset_of_hom v)
  obtain ⟨Md, Mmap⟩ := M
  subst hMd
  obtain ⟨φg, hφg⟩ : ∃ z : ⋁a.dims ⟶ ⋁m.dims, z ≫ Mmap = Hom.φ f ≫ χ := ⟨_, g₀.w⟩
  obtain ⟨φe, hφe⟩ : ∃ z : ⋁m.dims ⟶ ⋁b.dims, z ≫ χ = Mmap := ⟨_, e₀.w⟩
  have hcomp : (φg ≫ φe) ≫ χ = Hom.φ f ≫ χ := by rw [Category.assoc, hφe]; exact hφg
  exact ⟨⟨φg, Subsingleton.elim _ _⟩, ⟨φe, Subsingleton.elim _ _⟩,
    hom_ext' (by rw [comp_φ]; exact wedgeHom_ext_chart hcomp)⟩

/-- **Composition through an intermediate shape is a bijection** whenever both legs are possible —
the Garside-interval form of `exists_factor` (surjectivity) and `factor_ext` (injectivity). -/
noncomputable def compEquiv (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b)) :
    ((a ⟶ m) × (m ⟶ b)) ≃ (a ⟶ b) :=
  Equiv.ofBijective (fun ge => ge.1 ≫ ge.2)
    ⟨fun _ _ h => Prod.ext (factor_ext h rfl).1 (factor_ext h rfl).2,
      fun f => (exists_factor ham hmb f).elim fun g hg => hg.elim fun e he => ⟨⟨g, e⟩, he⟩⟩

/-! ## Splitting off one junction

`exists_first` and `exists_diamond` are the boundary-free consequences of the cut calculus — the
only ones `Concurrency/Presentation/CutPresentation` is allowed to see. -/

/-- The fine end, with the two beads meeting at a removed boundary merged. -/
private theorem exists_mid_merge (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ c : Ch Zbp, boundaries c.dims = (boundaries a.dims).erase t
      ∧ dimSum c.dims = dimSum a.dims := by
  rw [cutsOf, Finset.mem_sdiff] at ht
  have h0 : t ≠ 0 := fun h => ht.2 (h ▸ zero_mem_boundaries _)
  have hlast : t ≠ dimSum a.dims := fun h =>
    ht.2 (by rw [h, strandsEq f]; exact dimSum_mem_boundaries b.dims)
  obtain ⟨l, r, p, q, ha, hl⟩ := exists_split_of_mem_boundaries a.dims ht.1 h0 hlast
  refine ⟨zObj (l ++ (p + q) :: r), ?_, by rw [zObj_dims, ha]; exact (dimSum_cut l r p q).symm⟩
  rw [zObj_dims, ha, boundaries_cut, hl,
    Finset.erase_insert (hl ▸ notMem_boundaries_cut l r p q)]

/-- **A refinement splits off its first cut at any boundary it removes.**  Uniqueness is
`mid_eq_of_cuts_eq` and `factor_ext`. -/
theorem exists_factor_first (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ (c : Ch Zbp) (e : a ⟶ c) (g : c ⟶ b), cutsOf e = {t} ∧ e ≫ g = f := by
  obtain ⟨c, hc, hcd⟩ := exists_mid_merge f ht
  have ht' := Finset.mem_sdiff.mp ht
  have hd := strandsEq f
  obtain ⟨e, g, heg⟩ := exists_factor
    (nonempty_hom_iff.mpr ⟨hcd.symm, hc ▸ Finset.erase_subset _ _⟩)
    (nonempty_hom_iff.mpr ⟨by omega,
      hc ▸ Finset.subset_erase.mpr ⟨boundaries_subset_of_hom f, ht'.2⟩⟩) f
  exact ⟨c, e, g, cutsOf_eq_singleton ht'.1 hc, heg⟩

/-- **A refinement of positive codimension splits off a generator at the front.** -/
theorem exists_first (f : a ⟶ b) (hf : codim f ≠ 0) :
    ∃ (c : Ch Zbp) (e : a ⟶ c) (g : c ⟶ b), codim e = 1 ∧ e ≫ g = f := by
  obtain ⟨t, ht⟩ : ∃ t, t ∈ cutsOf f := Finset.card_pos.mp (by rw [card_cutsOf]; omega)
  obtain ⟨c, e, g, hcut, heg⟩ := exists_factor_first f ht
  exact ⟨c, e, g, codim_eq_one_of_cutsOf hcut, heg⟩

/-- **The diamond**: two codimension-one steps out of one shape, both below `b`, are completed by
one more step each.  The apex is the shape whose boundaries are the two targets' in common, and it
still lies above `b`, so the square closes over `b` — no order on the cuts is involved. -/
theorem exists_diamond {c c' : Ch Zbp} {e : a ⟶ c} {g : c ⟶ b} {e' : a ⟶ c'} {g' : c' ⟶ b}
    (he : codim e = 1) (he' : codim e' = 1) (h : e ≫ g = e' ≫ g') (hne : c ≠ c') :
    ∃ (w : Ch Zbp) (u : c ⟶ w) (u' : c' ⟶ w) (k : w ⟶ b),
      codim u = 1 ∧ codim u' = 1 ∧ e ≫ u = e' ≫ u' ∧ u ≫ k = g ∧ u' ≫ k = g' := by
  obtain ⟨t, ht⟩ := exists_cutsOf_eq_singleton he
  obtain ⟨t', ht'⟩ := exists_cutsOf_eq_singleton he'
  have hts : t ≠ t' := fun hc => hne (mid_eq_of_cuts_eq ht (hc ▸ ht'))
  have hmem : t' ∈ cutsOf g := Finset.mem_sdiff.mpr
    ⟨boundaries_eq_erase ht ▸ Finset.mem_erase.mpr ⟨hts.symm, (mem_cutsOf ht').1⟩,
      fun hb => (mem_cutsOf ht').2 (boundaries_subset_of_hom g' hb)⟩
  have hmem' : t ∈ cutsOf g' := Finset.mem_sdiff.mpr
    ⟨boundaries_eq_erase ht' ▸ Finset.mem_erase.mpr ⟨hts, (mem_cutsOf ht).1⟩,
      fun hb => (mem_cutsOf ht).2 (boundaries_subset_of_hom g hb)⟩
  obtain ⟨w, u, k, hu, huk⟩ := exists_factor_first g hmem
  obtain ⟨w', u', k', hu', hu'k⟩ := exists_factor_first g' hmem'
  obtain rfl : w = w' := Obj.eq_of_dims (boundaries_injective (by
    rw [boundaries_eq_erase hu, boundaries_eq_erase hu', boundaries_eq_erase ht,
      boundaries_eq_erase ht', Finset.erase_right_comm]))
  obtain ⟨hsq, rfl⟩ := factor_ext (f := e ≫ g) (by rw [Category.assoc, huk])
    (by rw [Category.assoc, hu'k, h])
  exact ⟨w, u, u', k, codim_eq_one_of_cutsOf hu, codim_eq_one_of_cutsOf hu', hsq, huk, hu'k⟩

/-! ## The middle hom-set, from the two extremes

`o ⟶ a ⟶ b ⟶ z` with the outer legs crossing nothing.  Uniqueness of the factorisation of
`o ⟶ z` through `b` forces the leg out of `b` to be the merge, so the crossing permutation of
`a ⟶ b` is the one the outer legs already carry. -/

/-- **Interpolation**: a permutation realised at both extremes is realised in the middle. -/
theorem exists_crossPerm_mid {o z : Ch Zbp} {N : ℕ} {ho : dimSum o.dims = N}
    {ha : dimSum a.dims = N} {hb : dimSum b.dims = N} {σ : Equiv.Perm (Fin N)}
    {t : o ⟶ a} (ht : crossPerm ho t = 1) {s : b ⟶ z} (hs : crossPerm hb s = 1)
    (hab : Nonempty (a ⟶ b)) {u : o ⟶ b} (hu : crossPerm ho u = σ)
    {g : a ⟶ z} (hg : crossPerm ha g = σ) :
    ∃ f : a ⟶ b, crossPerm ha f = σ := by
  obtain ⟨f, v, hfv⟩ := exists_factor hab ⟨s⟩ g
  have hv : v = s :=
    (factor_ext (g := t ≫ f) (e := v) (f := u ≫ s)
      (hom_ext_of_crossPerm (h := ho) (by
        rw [Category.assoc, hfv, crossPerm_comp ho t g, crossPerm_comp ho u s, ht, hs, hu, hg,
          mul_one, one_mul])) rfl).2
  refine ⟨f, ?_⟩
  have h := crossPerm_comp ha f v
  rw [hfv, hg, hv, hs, one_mul] at h
  exact h.symm

end ChainCat
