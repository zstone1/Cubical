import CubeChains.Concurrency.Grading.ChartHom

/-!
# Concurrency/Grading/Coarser — factoring through an intermediate shape

Between a chart and a coarsening of it, a shape is realised by exactly one chain.  Uniqueness: the
initial runs of the coarsening's beads are down-sets for the source's bead order, and down-sets of
a total order are linearly ordered by inclusion, so `card_beadOf_lt` pins them.  Existence: send a
coordinate to the block of the shape in which its own bead starts.

Read in a chart of the target, that is `compEquiv` — composition through an intermediate shape is a
bijection, `factor_ext` its injectivity and `exists_factor` its surjectivity.
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
private theorem downSet_subset {N : ℕ} {L : Type*} [LinearOrder L] {g : Fin N → L}
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
  show beadStart A.dims (beadOf A r) < N
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
  refine ⟨blockChain (midBead A hm) hsurj, ?_, ?_, ?_⟩
  · have hlen : (blockChain (midBead A hm) hsurj).dims.length = m.length := by
      rw [length_blockChain, dimComp_length]
    refine eq_of_beadStart_eq hlen fun j hj => ?_
    rw [← card_beadOf_lt, ← hcard j (hlen ▸ hj)]
    exact congrArg Finset.card
      (Finset.filter_congr fun r _ => by rw [beadOf_blockChain (midBead A hm) hsurj r])
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
    · have hle : beadStart C.dims (beadOf C q) ≤ beadPos A q := by
        have h1 : beadStart C.dims (beadOf C q) = (Finset.univ.filter fun s : Fin N =>
            (beadOf C s : ℕ) < (beadOf C q : ℕ)).card := (card_beadOf_lt C _).symm
        have h2 : beadPos A q = (Finset.univ.filter fun s : Fin N =>
            (beadOf A s : ℕ) < (beadOf A q : ℕ)).card := (card_beadOf_lt A _).symm
        rw [h1, h2]
        exact Finset.card_le_card fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hAC s q (Finset.mem_filter.mp hs).2⟩
      have hgt : beadPos A p < beadStart C.dims (beadOf C q) := by
        have hsub : (Finset.univ.filter fun s : Fin N => (beadOf A s : ℕ) < (beadOf A p : ℕ) + 1)
            ⊆ Finset.univ.filter fun s : Fin N => (beadOf C s : ℕ) < (beadOf C q : ℕ) :=
          fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            lt_of_le_of_lt (beadOf_le_of_hom u
              (Nat.lt_succ_iff.mp (Finset.mem_filter.mp hs).2)) h⟩
        have h1 := Finset.card_le_card hsub
        rw [card_beadOf_lt A, card_beadOf_lt C] at h1
        exact lt_of_lt_of_le
          (beadStart_lt_beadStart (beadOf A p).isLt (Nat.lt_succ_self (beadOf A p : ℕ))) h1
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

/-! ## The two extremes

The run `1ᴺ` refines every shape on `N` events and one bead coarsens every one — the boundary
inclusions are `⊆ range (N+1)` and `{0, N} ⊆ ·`. -/

/-- **The run refines every shape on its event count.** -/
theorem nonempty_hom_ones {d : List ℕ+} {N : ℕ} (h : dimSum d = N) :
    Nonempty (zObj (𝟙^N) ⟶ zObj d) := by
  refine nonempty_hom_iff.mpr ⟨(dimSum_replicate N).trans h.symm, fun t ht => ?_⟩
  have hle : t ≤ N := h ▸ le_dimSum_of_mem_boundaries ht
  refine mem_boundaries_iff.mpr ⟨𝟙^t, 𝟙^(N - t), ?_, dimSum_replicate t⟩
  rw [show (zObj (𝟙^N)).dims = 𝟙^N from rfl, ← List.replicate_add,
    show t + (N - t) = N by omega]

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

variable {a m b : Ch Zbp}

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
