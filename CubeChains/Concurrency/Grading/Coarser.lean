import CubeChains.Concurrency.Grading.ChainHom

/-!
# Concurrency/Grading/Coarser — factoring through an intermediate shape

Between a chain and a coarsening of it, a shape is realised by exactly one chain.  Both halves read
the coarsening off the source's firing order: a coarsening's beads are down-sets for it, pinned by
their sizes (`beadOf_of_hom`), and conversely a shape whose junctions the source has is realised by
sending a coordinate to the block its own rank falls in (`exists_mid_chain`).

Read through the target's wedge map, that is `compEquiv` — composition through an intermediate
shape is a bijection, `factor_ext` its injectivity and `exists_factor` its surjectivity.

This file is where the shape model stops: `boundaries` is used to prove `exists_first` and
`exists_diamond`, whose statements mention only `codim` and composition, and the presentation
above sees nothing else.
-/

open CategoryTheory Equiv CubeChains CubeChain BPSet StdCube ChainCat

namespace CubeChains

@[simp] theorem dimSum_single (n : ℕ+) : dimSum [n] = (n : ℕ) := by simp [dimSum]

/-! ## A coarsening is read off the source's firing order

`flatten A` enumerates the coordinates, so a set closed downwards under it is pinned by its size
(`eq_filter_flatten_of_downSet`).  Every bead of a coarsening is such a set, of size the shape's own
prefix sum — which says a coarsening's beads are its shape's blocks read in that order
(`beadOf_of_hom`), and hence that the coarsening is pinned by its shape. -/

/-- Under a refinement the target's bead order is coarser than the source's — `beadOf_le` at the
face order a chain morphism induces. -/
theorem beadOf_le_of_hom {N : ℕ} {A M : Ch (□N)} (f : A ⟶ M) {r s : Fin N}
    (h : (beadOf A r : ℕ) ≤ (beadOf A s : ℕ)) : (beadOf M r : ℕ) ≤ (beadOf M s : ℕ) :=
  beadOf_le (chFace_faceLE f) h

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

/-- **A down-set for the firing order is pinned by its size** — it is the initial segment of that
many ranks. -/
theorem eq_filter_flatten_of_downSet {N : ℕ} (A : Ch (□N)) {S : Finset (Fin N)} {k : ℕ}
    (hcard : S.card = k)
    (hdown : ∀ r s : Fin N, (flatten A r : ℕ) ≤ (flatten A s : ℕ) → s ∈ S → r ∈ S) :
    S = Finset.univ.filter fun r : Fin N => (flatten A r : ℕ) < k := by
  have hk : k ≤ N := hcard ▸ (Finset.card_le_univ S).trans_eq (by simp)
  have hT : ∀ r s : Fin N, (flatten A r : ℕ) ≤ (flatten A s : ℕ) →
      s ∈ Finset.univ.filter (fun t : Fin N => (flatten A t : ℕ) < k) →
      r ∈ Finset.univ.filter (fun t : Fin N => (flatten A t : ℕ) < k) := fun r s hrs hs =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt hrs (Finset.mem_filter.mp hs).2⟩
  have hcards := (card_flatten_lt A hk).trans hcard.symm
  exact Finset.Subset.antisymm
    (downSet_subset (g := fun r => (flatten A r : ℕ)) hT hdown hcards.ge)
    (downSet_subset (g := fun r => (flatten A r : ℕ)) hdown hT hcards.le)

/-- **A coarsening's beads are its shape's blocks, read in the source's firing order** — each is a
down-set for that order, of size the shape's own prefix sum.  The target's own map never
appears. -/
theorem beadOf_of_hom {N : ℕ} {A M : Ch (□N)} (f : A ⟶ M) (q : Fin N) :
    (beadOf M q : ℕ) = ((dimComp M.dims (wedgeDimSum_eq M.map)).index (flatten A q) : ℕ) := by
  have hn : dimSum M.dims = N := wedgeDimSum_eq M.map
  have hiff : ∀ j : ℕ, (beadOf M q : ℕ) < j
      ↔ ((dimComp M.dims hn).index (flatten A q) : ℕ) < j := fun j => by
    have hset := eq_filter_flatten_of_downSet A (card_beadOf_lt M j) fun r s hrs hs =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_le_of_lt (beadOf_le_of_hom f (beadOf_le_of_flatten_le A hrs))
          (Finset.mem_filter.mp hs).2⟩
    rw [index_lt_iff_beadStart hn (flatten A q) j]
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using Finset.ext_iff.mp hset q
  have h1 := (hiff ((beadOf M q : ℕ) + 1)).mp (Nat.lt_succ_self _)
  have h2 := (hiff (((dimComp M.dims hn).index (flatten A q) : ℕ) + 1)).mpr (Nat.lt_succ_self _)
  omega

/-- **A coarsening is pinned by its shape**: two refinements of one chain of a cube with the same
bead dimensions are the same chain. -/
theorem chain_ext_of_dims {N : ℕ} {A M M' : Ch (□N)} (f : A ⟶ M) (f' : A ⟶ M')
    (h : M.dims = M'.dims) : M = M' := by
  obtain ⟨d, χ⟩ := M
  obtain ⟨d', χ'⟩ := M'
  cases h
  exact eq_of_beadOf fun q => (beadOf_of_hom f q).trans (beadOf_of_hom f' q).symm

/-! ## Realising an intermediate shape

A coordinate goes to the block of the shape its own rank falls in.  Its whole bead of `A` lies in
one block of `m` (every junction of `m` is one of `A`), which is what makes the assignment a
coarsening of `A`. -/

/-- **A shape between two comparable chains of a cube is realised between them.** -/
theorem exists_mid_chain {N : ℕ} {A C : Ch (□N)} (u : A ⟶ C) {m : List ℕ+} (hm : dimSum m = N)
    (hAm : boundaries m ⊆ boundaries A.dims) (hmC : boundaries C.dims ⊆ boundaries m) :
    ∃ M : Ch (□N), M.dims = m ∧ Nonempty (A ⟶ M) ∧ Nonempty (M ⟶ C) := by
  set β : Fin N → Fin (dimComp m hm).length := fun r => (dimComp m hm).index (flatten A r) with hβ
  have hsurj : Function.Surjective β := fun j =>
    ⟨(flatten A).symm ((dimComp m hm).embedding j ⟨0, (dimComp m hm).one_le_blocksFun j⟩), by
      simp only [hβ, Equiv.apply_symm_apply, Composition.index_embedding]⟩
  have hcard : ∀ j ≤ m.length,
      (Finset.univ.filter fun r : Fin N => (β r : ℕ) < j).card = beadStart m j := fun j _ => by
    rw [show (Finset.univ.filter fun r : Fin N => (β r : ℕ) < j)
          = Finset.univ.filter fun r : Fin N => (flatten A r : ℕ) < beadStart m j from
        Finset.filter_congr fun r _ => index_lt_iff_beadStart hm _ j,
      card_flatten_lt A ((beadStart_le_dimSum m j).trans_eq hm)]
  refine ⟨blockChain β hsurj, dims_blockChain hm hsurj hcard, ⟨reflectHom ?_⟩, ⟨reflectHom ?_⟩⟩
  · refine chFace_faceLE_iff.mpr fun p q hne => ?_
    rw [beadOf_blockChain, beadOf_blockChain] at hne ⊢
    rw [beadOf_eq_index A p, beadOf_eq_index A q, index_lt_iff_beadAt, index_lt_iff_beadAt]
    exact beadAt_lt_iff_of_subset hAm fun hc => hne ((index_eq_iff_beadAt hm _ _).mpr hc)
  · refine chFace_faceLE_iff.mpr fun p q hne => ?_
    rw [beadOf_blockChain, beadOf_blockChain]
    rw [beadOf_of_hom u p, beadOf_of_hom u q] at hne ⊢
    rw [index_lt_iff_beadAt, index_lt_iff_beadAt]
    exact beadAt_lt_iff_of_subset hmC fun hc =>
      hne ((index_eq_iff_beadAt (wedgeDimSum_eq C.map) _ _).mpr hc)

end CubeChains

namespace ChainCat

open CubeChains

variable {K : BPSet} {a m b : Ch K}

/-! ## The cut of a refinement

The shape model, used from here down and hidden above it: a refinement drops a set of the source's
junctions, and the codimension counts them. -/

/-- The boundaries a refinement of serial wedges removes. -/
def cutsOf {K : BPSet} {a b : Ch K} (_f : a ⟶ b) : Finset ℕ :=
  boundaries a.dims \ boundaries b.dims

theorem card_cutsOf (f : a ⟶ b) : (cutsOf f).card = codim f :=
  (codim_eq_card_sdiff f).symm

/-- **The target keeps exactly the boundaries the refinement does not cut.** -/
theorem boundaries_sdiff_cutsOf (f : a ⟶ b) :
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

/-- **A step is pinned by the boundary it removes** — an equation of shapes, a shape being its
boundary set.  Which *chain* of that shape is reached needs a coarsening the two steps share
(`eq_of_join_of_dims_eq`). -/
theorem dims_eq_of_cuts_eq {c c' : Ch K} {e : a ⟶ c} {e' : a ⟶ c'} {t : ℕ}
    (h : cutsOf e = {t}) (h' : cutsOf e' = {t}) : c.dims = c'.dims :=
  boundaries_injective ((boundaries_eq_erase h).trans (boundaries_eq_erase h').symm)

/-! ## The two extremes

The run `1ᴺ` refines every shape on `N` events and one bead coarsens every one — the boundary
inclusions are `⊆ range (N+1)` and `{0, N} ⊆ ·`. -/

/-- **The run has every boundary** — it has `N + 1` of them and they all lie in `{0,…,N}`. -/
@[simp] theorem boundaries_ones (N : ℕ) : boundaries (𝟙^N) = Finset.range (N + 1) :=
  Finset.eq_of_subset_of_card_le
    (fun t ht => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (dimSum_replicate N ▸ le_dimSum_of_mem_boundaries ht)))
    (by simp [card_boundaries])

/-- **The run refines every shape on its event count.** -/
theorem nonempty_hom_ones {d : List ℕ+} {N : ℕ} (h : dimSum d = N) :
    Nonempty (zObj (𝟙^N) ⟶ zObj d) :=
  nonempty_hom_iff.mpr ⟨(dimSum_replicate N).trans h.symm, fun _ ht =>
    boundaries_ones N ▸ Finset.mem_range.mpr
      (Nat.lt_succ_of_le (h ▸ le_dimSum_of_mem_boundaries ht))⟩

/-! ### The cuts out of the run

A shape *is* its boundary set, so out of the run a refinement is exactly the set of the run's `N-1`
interior junctions it drops (`cutsOf`), and `card_cutsOf` counts them. -/

/-- Out of the run every position is a boundary, so a cut is an interior one. -/
theorem cutsOf_ones_subset {N : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b) :
    cutsOf f ⊆ Finset.Ioo 0 N := by
  have hdim : dimSum b.dims = N := (dimSum_eq_of_hom f).symm.trans (dimSum_replicate N)
  intro s hs
  rw [cutsOf, zObj_dims, boundaries_ones, Finset.mem_sdiff] at hs
  exact Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero fun h => hs.2 (h ▸ zero_mem_boundaries _),
    lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs.1)) fun h =>
      hs.2 (h ▸ hdim ▸ dimSum_mem_boundaries _)⟩

/-- **A cut set of size two is a pair of interior junctions in order** — the codimension-two data,
with no species read into it. -/
theorem exists_cutsOf_eq_pair {N : ℕ} {b : Ch Zbp} (f : zObj (𝟙^N) ⟶ b) (hf : codim f = 2) :
    ∃ s t, 0 < s ∧ s < t ∧ t < N ∧ cutsOf f = {s, t} := by
  obtain ⟨s, t, hst, hset⟩ := Finset.card_eq_two.mp ((card_cutsOf f).trans hf)
  have hmem : ∀ u ∈ ({s, t} : Finset ℕ), 0 < u ∧ u < N := fun u hu =>
    Finset.mem_Ioo.mp (cutsOf_ones_subset f (hset ▸ hu))
  have hs := hmem s (Finset.mem_insert_self s {t})
  have ht := hmem t (Finset.mem_insert_of_mem (Finset.mem_singleton_self t))
  rcases lt_or_gt_of_ne hst with h | h
  · exact ⟨s, t, hs.1, h, ht.2, hset⟩
  · exact ⟨t, s, ht.1, h, hs.2, hset.trans (Finset.pair_comm s t)⟩

/-- **One bead coarsens every chain on its event count.**  Stated at the chain and not at `zObj` of
its shape: those are equal only propositionally (`Obj.eq_of_dims`), and a caller with a chain in
hand would have to transport. -/
theorem nonempty_hom_single {a : Ch Zbp} {m : ℕ+} (h : dimSum a.dims = (m : ℕ)) :
    Nonempty (a ⟶ zObj [m]) := by
  refine nonempty_hom_iff.mpr ⟨h.trans (dimSum_single m).symm, fun t ht => ?_⟩
  rw [show (zObj [m]).dims = [m] from rfl, boundaries_singleton] at ht
  rcases Finset.mem_insert.mp ht with rfl | ht'
  · exact zero_mem_boundaries a.dims
  · rw [Finset.mem_singleton.mp ht', ← h]
    exact dimSum_mem_boundaries a.dims

/-! ## Unique factorisation through an intermediate shape

Read through `b`'s wedge map, a factorisation of `f : a ⟶ b` through `m` *is* a chain of `□N`
of shape `m.dims` between the two — and `exists_mid_chain` and `chain_ext_of_dims` say there
is exactly one. -/

/-- **The two factors are determined**: the intermediate chain is a coarsening of `a`'s of shape
`m.dims`, hence unique, and a wedge map is a monomorphism. -/
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
  have hee : Hom.φ e = Hom.φ e' := wedgeHom_ext_chain (by simpa using hmap)
  have hcomp : Hom.φ g ≫ (Hom.φ e ≫ χ) = Hom.φ g' ≫ (Hom.φ e ≫ χ) := by
    rw [hφ h, hee, hφ h']
  haveI := chain_mono (⟨m.dims, Hom.φ e ≫ χ⟩ : Ch (□(dimSum b.dims)))
  refine ⟨hom_ext' (BPSet.hom_ext ((cancel_mono (Hom.φ e ≫ χ).hom).mp ?_)), hom_ext' hee⟩
  rw [← comp_hom, ← comp_hom, hcomp]

/-- **Factorisation through an intermediate shape.**  Read through `b`'s wedge map, the
factorisation is an intermediate chain of the cube — which `exists_mid_chain` supplies. -/
theorem exists_factor {a m b : Ch Zbp} (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b))
    (f : a ⟶ b) : ∃ (g : a ⟶ m) (e : m ⟶ b), g ≫ e = f := by
  obtain ⟨χ⟩ := nonempty_toCube b.dims
  obtain ⟨w⟩ := ham
  obtain ⟨v⟩ := hmb
  obtain ⟨φf, hφf⟩ : ∃ z : ⋁a.dims ⟶ ⋁b.dims, z ≫ χ = Hom.φ f ≫ χ := ⟨Hom.φ f, rfl⟩
  obtain ⟨M, hMd, ⟨g₀⟩, ⟨e₀⟩⟩ := exists_mid_chain
    (A := (⟨a.dims, Hom.φ f ≫ χ⟩ : Ch (□(dimSum b.dims))))
    (C := (⟨b.dims, χ⟩ : Ch (□(dimSum b.dims)))) ⟨φf, hφf⟩
    ((dimSum_eq_of_hom w).symm.trans (dimSum_eq_of_hom f)) (boundaries_subset_of_hom w)
    (boundaries_subset_of_hom v)
  obtain ⟨Md, Mmap⟩ := M
  subst hMd
  obtain ⟨φg, hφg⟩ : ∃ z : ⋁a.dims ⟶ ⋁m.dims, z ≫ Mmap = Hom.φ f ≫ χ := ⟨_, g₀.w⟩
  obtain ⟨φe, hφe⟩ : ∃ z : ⋁m.dims ⟶ ⋁b.dims, z ≫ χ = Mmap := ⟨_, e₀.w⟩
  have hcomp : (φg ≫ φe) ≫ χ = Hom.φ f ≫ χ := by rw [Category.assoc, hφe]; exact hφg
  exact ⟨⟨φg, Subsingleton.elim _ _⟩, ⟨φe, Subsingleton.elim _ _⟩,
    hom_ext' (by rw [comp_φ]; exact wedgeHom_ext_chain hcomp)⟩

/-- **Composition through an intermediate shape is a bijection** whenever both legs are possible —
the Garside-interval form of `exists_factor` (surjectivity) and `factor_ext` (injectivity). -/
noncomputable def compEquiv {a m b : Ch Zbp} (ham : Nonempty (a ⟶ m)) (hmb : Nonempty (m ⟶ b)) :
    ((a ⟶ m) × (m ⟶ b)) ≃ (a ⟶ b) :=
  Equiv.ofBijective (fun ge => ge.1 ≫ ge.2)
    ⟨fun _ _ h => Prod.ext (factor_ext h rfl).1 (factor_ext h rfl).2,
      fun f => (exists_factor ham hmb f).elim fun g hg => hg.elim fun e he => ⟨⟨g, e⟩, he⟩⟩

/-! ## Lifting a factorisation of the shape

`toChZ K` is a discrete fibration, so a factorisation of the shape a refinement performs lifts: the
middle chain is that shape carrying `b`'s classifying map along the second leg.  This is what makes
the cut calculus — stated on shapes — available at every `K`.

    a ────▸ liftChain b g ────▸ b            lies over      zObj a.dims ──▸ c ──▸ zObj b.dims -/

/-- The shape a refinement performs. -/
def baseMap (f : a ⟶ b) : zObj a.dims ⟶ zObj b.dims := zHom f.φ

/-- The chain a shape over `b` names — the cartesian lift along the fibration. -/
def liftChain (b : Ch K) {m : Ch Zbp} (g : m ⟶ zObj b.dims) : Ch K := ⟨m.dims, g.φ ≫ b.map⟩

/-- …refining `b` by the shape it lies over. -/
def liftSnd (b : Ch K) {m : Ch Zbp} (g : m ⟶ zObj b.dims) : liftChain b g ⟶ b := ⟨g.φ, rfl⟩

/-- …and the first leg a factorisation of the shape supplies. -/
def liftFst {f : a ⟶ b} {m : Ch Zbp} {e : zObj a.dims ⟶ m} {g : m ⟶ zObj b.dims}
    (h : e ≫ g = baseMap f) : a ⟶ liftChain b g :=
  ⟨e.φ, ((Category.assoc (Hom.φ e) (Hom.φ g) b.map).symm.trans
    (congrArg (fun t => t ≫ b.map)
      (congrArg (fun t : zObj a.dims ⟶ zObj b.dims => Hom.φ t) h))).trans f.w⟩

@[simp] theorem liftFst_comp_liftSnd {f : a ⟶ b} {m : Ch Zbp} {e : zObj a.dims ⟶ m}
    {g : m ⟶ zObj b.dims} (h : e ≫ g = baseMap f) : liftFst h ≫ liftSnd b g = f :=
  hom_ext' (congrArg (fun t : zObj a.dims ⟶ zObj b.dims => Hom.φ t) h)

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
    ht.2 (by rw [h, dimSum_eq_of_hom f]; exact dimSum_mem_boundaries b.dims)
  obtain ⟨l, r, p, q, ha, hl⟩ := exists_split_of_mem_boundaries a.dims ht.1 h0 hlast
  refine ⟨zObj (l ++ (p + q) :: r), ?_, by rw [zObj_dims, ha]; exact (dimSum_cut l r p q).symm⟩
  rw [zObj_dims, ha, boundaries_cut, hl,
    Finset.erase_insert (hl ▸ notMem_boundaries_cut l r p q)]

/-- **A refinement splits off its first cut at any boundary it removes.**  Uniqueness is
`dims_eq_of_cuts_eq` and `factor_ext`. -/
theorem exists_factor_first (f : a ⟶ b) {t : ℕ} (ht : t ∈ cutsOf f) :
    ∃ (c : Ch K) (e : a ⟶ c) (g : c ⟶ b), cutsOf e = {t} ∧ e ≫ g = f := by
  obtain ⟨c, hc, hcd⟩ := exists_mid_merge f ht
  have ht' := Finset.mem_sdiff.mp ht
  have hd := dimSum_eq_of_hom f
  obtain ⟨e, g, heg⟩ := exists_factor
    (nonempty_hom_iff.mpr ⟨hcd.symm, hc ▸ Finset.erase_subset _ _⟩)
    (nonempty_hom_iff.mpr ⟨by simp only [zObj_dims]; omega,
      hc ▸ Finset.subset_erase.mpr ⟨boundaries_subset_of_hom f, ht'.2⟩⟩) (baseMap f)
  exact ⟨liftChain b g, liftFst heg, liftSnd b g, cutsOf_eq_singleton ht'.1 hc,
    liftFst_comp_liftSnd heg⟩

/-- **A refinement of positive codimension splits off a generator at the front.** -/
theorem exists_first (f : a ⟶ b) (hf : codim f ≠ 0) :
    ∃ (c : Ch K) (e : a ⟶ c) (g : c ⟶ b), codim e = 1 ∧ e ≫ g = f := by
  obtain ⟨t, ht⟩ : ∃ t, t ∈ cutsOf f := Finset.card_pos.mp (by rw [card_cutsOf]; omega)
  obtain ⟨c, e, g, hcut, heg⟩ := exists_factor_first f ht
  exact ⟨c, e, g, codim_eq_one_of_cutsOf hcut, heg⟩

/-- **The diamond**: two codimension-one steps out of one shape, both below `b`, are completed by
one more step each.  The apex is the shape whose boundaries are the two targets' in common, and it
still lies above `b`, so the square closes over `b` — no order on the cuts is involved. -/
theorem exists_diamond {a b : Ch Zbp} {c c' : Ch Zbp} {e : a ⟶ c} {g : c ⟶ b} {e' : a ⟶ c'}
    {g' : c' ⟶ b} (he : codim e = 1) (he' : codim e' = 1) (h : e ≫ g = e' ≫ g') (hne : c ≠ c') :
    ∃ (w : Ch Zbp) (u : c ⟶ w) (u' : c' ⟶ w) (k : w ⟶ b),
      codim u = 1 ∧ codim u' = 1 ∧ e ≫ u = e' ≫ u' ∧ u ≫ k = g ∧ u' ≫ k = g' := by
  obtain ⟨t, ht⟩ := exists_cutsOf_eq_singleton he
  obtain ⟨t', ht'⟩ := exists_cutsOf_eq_singleton he'
  have hts : t ≠ t' := fun hc => hne (Obj.eq_of_dims (dims_eq_of_cuts_eq ht (hc ▸ ht')))
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
theorem exists_crossPerm_mid {a b : Ch Zbp} {o z : Ch Zbp} {N : ℕ} {ho : dimSum o.dims = N}
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

namespace ChainCat

/-! ## The same-shape species of a diamond is empty

A factorisation is its middle *shape* (`factor_ext`), and over `Zbp` a wedge map needs no
condition, so two codimension-one refinements of a chain that meet again over a common coarsening
have the same second leg as soon as their targets have the same shape — and the second leg carries
the map.  That is why `exists_join_of_dims_ne` asks for distinct shapes: the species it excludes
could never have been filled, for any `K`. -/

/-- **At equal shapes there is no diamond**: a commuting square of codimension-one refinements
whose two middle objects have the same dimension sequence has them equal. -/
theorem eq_of_join_of_dims_eq {K : BPSet} {a d d' j : Ch K} {u : a ⟶ d} {u' : a ⟶ d'}
    {v : d ⟶ j} {v' : d' ⟶ j} (hdims : d.dims = d'.dims) (hsq : u ≫ v = u' ≫ v') : d = d' := by
  have hφ : Hom.φ u ≫ Hom.φ v = Hom.φ u' ≫ Hom.φ v' := congrArg Hom.φ hsq
  obtain ⟨D, dm⟩ := d
  obtain ⟨D', dm'⟩ := d'
  dsimp only at hdims
  subst hdims
  obtain ⟨φu, _hu⟩ := u
  obtain ⟨φu', _hu'⟩ := u'
  obtain ⟨φv, hv0⟩ := v
  obtain ⟨φv', hv0'⟩ := v'
  dsimp only at hφ hv0 hv0'
  have hv : φv = φv' :=
    congrArg Hom.φ (factor_ext (f := zHom (φu ≫ φv)) (g := zHom φu) (e := zHom φv)
      (g' := zHom φu') (e' := zHom φv') (hom_ext' rfl) (hom_ext' hφ.symm)).2
  exact Obj.mk_eq_mk rfl
    (by simpa using hv0.symm.trans ((congrArg (· ≫ j.map) hv).trans hv0'))

end ChainCat
