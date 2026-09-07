import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.WedgeBraid
import CubeChains.Concurrency.Grading.Degree
import CubeChains.Concurrency.Executions.RunPerm
import CubeChains.Concurrency.Salvetti.ChainBraidFace
import CubeChains.Machinery.Composition
import CubeChains.Precubical.Chains.Correspondence

/-!
# Concurrency/Grading/ChartHom — a wedge map is a chart refining a chart

A serial wedge maps into the cube of its own total dimension (`nonempty_toCube`) and a chart is a
monomorphism (`descent_mono`), so `φ ↦ φ ≫ χ` identifies `⋁a ⟶ ⋁b` with the charts of `⋁a` lying
over a fixed chart of `⋁b` — the fibre description of the discrete fibration `Ch (□N) ⥤ Ch Zbp`,
with `Ch (□N)` thin.

A chart's shape is then read as a mathlib `Composition` (`dimComp`), whose `index` is `beadOf`
under the firing order (`beadOf_eq_index`); the hom-sets come off `boundaries` alone.
-/

open CategoryTheory BPSet CubeChain ChainCat

namespace CubeChains

variable {a b d d' : List ℕ+}

/-! ## Charts -/

/-- A chart is a monomorphism — the descent map of a chain of the cube. -/
theorem chart_mono {N : ℕ} (A : Ch (□N)) : Mono A.map.hom :=
  descent_mono (cube_nonSelfLinked N) (BPSet.cube_admitsAltitude N) A

/-- **A wedge map is pinned by its chart.** -/
theorem wedgeHom_ext_chart {N : ℕ} {χ : ⋁b ⟶ □N} {φ ψ : ⋁a ⟶ ⋁b} (h : φ ≫ χ = ψ ≫ χ) :
    φ = ψ := by
  haveI := chart_mono (⟨b, χ⟩ : Ch (□N))
  exact BPSet.hom_ext ((cancel_mono χ.hom).mp (congrArg BPSet.Hom.hom h))

/-- **A serial-wedge map is a chart of the source lying over a fixed chart of the target.**

```
    ⋁a ---φ---> ⋁b
      \          |
       x         χ
        \        v
         ------> □N
```
`Ch (□N) ⥤ Ch Zbp` is a discrete fibration, so the pair `(x, φ)` is the datum of the chart alone;
`Ch (□N)` is thin, so `φ` is recovered from it. -/
noncomputable def chartHomEquiv {N : ℕ} (χ : ⋁b ⟶ □N) :
    (⋁a ⟶ ⋁b) ≃ {x : ⋁a ⟶ □N // Nonempty ((⟨a, x⟩ : Ch (□N)) ⟶ ⟨b, χ⟩)} where
  toFun φ := ⟨φ ≫ χ, ⟨⟨φ, rfl⟩⟩⟩
  invFun x := ChainCat.Hom.φ x.2.some
  left_inv φ :=
    congrArg ChainCat.Hom.φ
      ((chCube_isThin N (⟨a, φ ≫ χ⟩ : Ch (□N)) ⟨b, χ⟩).elim _ ⟨φ, rfl⟩)
  right_inv x := Subtype.ext x.2.some.w

/-- An all-edges chain has one bead per event. -/
theorem ones_dims_eq {X : BPSet} {n : ℕ} {A : Ch X} (h : ∀ c ∈ A.dims, c = 1)
    (hn : dimSum A.dims = n) : A.dims = 𝟙^n :=
  (eq_replicate_of_ones h).trans
    (congrArg (List.replicate · (1 : ℕ+)) ((dimSum_eq_length_of_ones h).symm.trans hn))

/-- **A chain map out of the all-edges chain is a run of the target**, whenever the target has
`n` events along every chain. -/
def onesHomEquivRun {X : BPSet} {n : ℕ} (hn : ∀ {d : List ℕ+} (_ : ⋁d ⟶ X), dimSum d = n) :
    (⋁(𝟙^n) ⟶ X) ≃ Run X where
  toFun φ := ⟨⟨𝟙^n, φ⟩, fun _ hx => List.eq_of_mem_replicate hx⟩
  invFun r := ⋁≡ (ones_dims_eq r.ones (hn r.map)).symm ≫ r.map
  left_inv φ := Category.id_comp φ
  right_inv r := Run.ext (Obj.mk_eq_mk (ones_dims_eq r.ones (hn r.map)).symm rfl)

/-- **A chart of the run in a cube is a run of that cube** — the cube has `N` events along every
chain, so `onesHomEquivRun` applies. -/
def onesChartEquiv (N : ℕ) : (⋁(𝟙^N) ⟶ □N) ≃ Run (□N) :=
  onesHomEquivRun fun φ => wedgeDimSum_eq φ

/-! ## Realising a firing order

A chart of shape `d` fires its coordinates in an order that rises inside each block of `d` — and
every such order occurs, the beads being the blocks of `d` read through it.  The order itself
(`flatten`) and its comparison with the partition (`beadOf`) live in
`Concurrency/Salvetti/ChainBraidFace`; here only `dimComp` enters. -/

/-- A shape's block index against its own bead starts — `dimComp`'s `sizeUpTo` *is* `beadStart`. -/
theorem index_lt_iff_beadStart {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (p : Fin N) (j : ℕ) :
    ((dimComp d hd).index p : ℕ) < j ↔ (p : ℕ) < beadStart d j := by
  rw [Composition.index_lt_iff, dimComp_sizeUpTo]
  rfl

/-- **A coordinate's block, from the two bead starts bracketing it.** -/
theorem index_eq_of_beadStart {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) {j : ℕ} (p : Fin N)
    (h1 : beadStart d j ≤ (p : ℕ)) (h2 : (p : ℕ) < beadStart d (j + 1)) :
    ((dimComp d hd).index p : ℕ) = j :=
  Composition.index_eq_of_bracket _ p (by rw [dimComp_sizeUpTo]; exact h1)
    (by rw [dimComp_sizeUpTo]; exact h2)

/-- **The block index is the bead count** — the one bridge from `Composition.index` down to the
junction set, and hence the only place a total has to be threaded. -/
theorem index_lt_iff_beadAt {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (p q : Fin N) :
    ((dimComp d hd).index p : ℕ) < ((dimComp d hd).index q : ℕ) ↔ beadAt d p < beadAt d q := by
  rw [beadAt_lt_iff]
  constructor
  · exact fun h => ⟨beadStart d ((dimComp d hd).index q : ℕ),
      beadStart_mem_boundaries d
        (by rw [← dimComp_length d hd]; exact ((dimComp d hd).index q).isLt.le),
      (index_lt_iff_beadStart hd p _).mp h,
      not_lt.mp fun hc => absurd ((index_lt_iff_beadStart hd q _).mpr hc) (lt_irrefl _)⟩
  · rintro ⟨t, ht, hpt, htq⟩
    obtain ⟨j, -, rfl⟩ := mem_boundaries_iff_beadStart.mp ht
    have h1 : ((dimComp d hd).index p : ℕ) < j := (index_lt_iff_beadStart hd p j).mpr hpt
    have h2 : ¬ (((dimComp d hd).index q : ℕ) < j) := fun hc =>
      absurd ((index_lt_iff_beadStart hd q j).mp hc) (by omega)
    omega

theorem index_eq_iff_beadAt {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (p q : Fin N) :
    ((dimComp d hd).index p : ℕ) = ((dimComp d hd).index q : ℕ) ↔ beadAt d p = beadAt d q := by
  have h1 := index_lt_iff_beadAt hd p q
  have h2 := index_lt_iff_beadAt hd q p
  omega

/-- **A block map realises the shape its down-sets count out**: the chain assembled from `β` has
shape `d` exactly when the coordinates below each block have the shape's prefix sums for counts. -/
theorem dims_blockChain {N : ℕ} {d : List ℕ+} (hd : dimSum d = N)
    {β : Fin N → Fin (dimComp d hd).length} (hsurj : Function.Surjective β)
    (hcard : ∀ j ≤ d.length,
      (Finset.univ.filter fun r : Fin N => (β r : ℕ) < j).card = beadStart d j) :
    (blockChain β hsurj).dims = d := by
  have hlen : (blockChain β hsurj).dims.length = d.length := by
    rw [length_blockChain, dimComp_length]
  refine eq_of_beadStart_eq hlen fun j hj => ?_
  rw [← card_beadOf_lt, ← hcard j (hlen ▸ hj)]
  exact congrArg Finset.card (Finset.filter_congr fun r _ => by rw [beadOf_blockChain])

/-- **Every order that rises inside each block of `d` is the firing order of a chart of shape
`d`** — its beads are the blocks of `d`, read through the order. -/
theorem exists_chart_flatten {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (ρ : Equiv.Perm (Fin N))
    (hrise : ∀ q q' : Fin N, (dimComp d hd).index (ρ q) = (dimComp d hd).index (ρ q') →
      q < q' → ρ q < ρ q') :
    ∃ χ : ⋁d ⟶ □N, flatten (⟨d, χ⟩ : Ch (□N)) = ρ := by
  suffices hex : ∃ A : Ch (□N), A.dims = d ∧ flatten A = ρ by
    obtain ⟨A, hAdims, hAflat⟩ := hex
    obtain ⟨Ad, Amap⟩ := A
    subst hAdims
    exact ⟨Amap, hAflat⟩
  have hsurj : Function.Surjective (fun q : Fin N => (dimComp d hd).index (ρ q)) := fun j =>
    ⟨ρ.symm ((dimComp d hd).embedding j ⟨0, (dimComp d hd).one_le_blocksFun j⟩), by
      simp only [Equiv.apply_symm_apply, Composition.index_embedding]⟩
  set β : Fin N → Fin (dimComp d hd).length := fun q => (dimComp d hd).index (ρ q) with hβ
  refine ⟨blockChain β hsurj, ?_, ?_⟩
  · refine dims_blockChain hd hsurj fun j _ => ?_
    rw [show beadStart d j = (dimComp d hd).sizeUpTo j from (dimComp_sizeUpTo d hd j).symm,
      ← Composition.sizeUpTo_eq_card]
    exact Finset.card_equiv ρ fun r => by simp [hβ]
  · refine Equiv.ext fun q => ?_
    have key := flatten_apply (blockChain β hsurj) ρ.symm (fun x y hlt => ?_) (ρ q)
    · rwa [Equiv.symm_apply_apply] at key
    have hρ : ρ (ρ.symm x) < ρ (ρ.symm y) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hlt
    rw [beadOf_blockChain, beadOf_blockChain]
    rcases eq_or_lt_of_le ((dimComp d hd).index_monotone (Fin.le_def.mp hρ.le)) with heq | hblt
    · refine Or.inr ⟨Fin.ext (by rw [beadOf_blockChain, beadOf_blockChain]; exact heq), ?_⟩
      by_contra hc
      rcases eq_or_lt_of_le (not_lt.mp hc) with heq2 | hgt
      · exact absurd hρ (by rw [heq2]; exact lt_irrefl _)
      · exact absurd (hrise _ _ (Fin.ext heq.symm) hgt) (asymm hρ)
    · exact Or.inl hblt

/-- **A coordinate's bead is the block its rank falls in** — the dictionary between a chart's
partition and its shape's blocks. -/
theorem beadOf_eq_index {N : ℕ} (A : Ch (□N)) (q : Fin N) :
    (beadOf A q : ℕ) = ((dimComp A.dims (wedgeDimSum_eq A.map)).index (flatten A q) : ℕ) :=
  (index_eq_of_beadStart _ (flatten A q) (flatten_mem_bead A q).1 (flatten_mem_bead A q).2).symm

/-- **A chart is pinned by its shape and its firing order** — `beadOf` reads back off `flatten`
through the shape's own blocks. -/
theorem chain_ext_of_flatten {N : ℕ} {A A' : Ch (□N)} (hd : A.dims = A'.dims)
    (h : flatten A = flatten A') : A = A' := by
  obtain ⟨d, χ⟩ := A
  obtain ⟨d', χ'⟩ := A'
  cases hd
  exact eq_of_beadOf fun q => by rw [beadOf_eq_index, beadOf_eq_index, h]

/-- The **standard chart** of a shape — beads in order, coordinates in order: the chart whose
firing order is the identity. -/
noncomputable def stdChart {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) : ⋁d ⟶ □N :=
  (exists_chart_flatten hd 1 fun _ _ _ h => h).choose

@[simp] theorem flatten_stdChart {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) :
    flatten (⟨d, stdChart hd⟩ : Ch (□N)) = 1 :=
  (exists_chart_flatten hd 1 fun _ _ _ h => h).choose_spec

theorem beadOf_stdChart {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (q : Fin N) :
    (beadOf (⟨d, stdChart hd⟩ : Ch (□N)) q : ℕ) = ((dimComp d hd).index q : ℕ) := by
  rw [beadOf_eq_index, flatten_stdChart]
  rfl

/-- **A serial wedge maps into the cube of its own total dimension** — its own standard chart. -/
theorem nonempty_toCube (b : List ℕ+) : Nonempty (⋁b ⟶ □(dimSum b)) := ⟨stdChart rfl⟩

/-! ## Coarsening -/

/-- `d'` **coarsens** `d`: the same events, and every junction of `d'` is one of `d`. -/
def Coarser (d d' : List ℕ+) : Prop :=
  dimSum d = dimSum d' ∧ boundaries d' ⊆ boundaries d

end CubeChains

namespace ChainCat

open CubeChains

variable {d d' : List ℕ+}

/-! ### `crossPerm` on charts -/

/-- **A chain morphism is the comparison of the two charts' firing orders.**  Read `f` in any chart
`χ` of its target; the source chart is `f ≫ χ`, and `crossPerm` takes one `flatten` to the other —
the cocycle law `conjPerm_mul_pullback` at the source chart `coordFlip_comp` pulls back. -/
theorem crossPerm_mul_flatten {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (χ : ⋁b.dims ⟶ □N) :
    crossPerm h f * flatten (⟨a.dims, Hom.φ f ≫ χ⟩ : Ch (□N))
      = flatten (⟨b.dims, χ⟩ : Ch (□N)) :=
  (congrArg (crossPerm h f * conjPerm · (strand a.dims h) (Equiv.refl _))
      (coordFlip_comp (Hom.φ f) χ)).trans
    (conjPerm_mul_pullback (strand a.dims h) (strand b.dims (tgtStrands f h)) (coordFlip χ)
      (coordMapEquiv (Hom.φ f)))

theorem crossPerm_flatten {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (χ : ⋁b.dims ⟶ □N) (q : Fin N) :
    crossPerm h f (flatten (⟨a.dims, Hom.φ f ≫ χ⟩ : Ch (□N)) q)
      = flatten (⟨b.dims, χ⟩ : Ch (□N)) q :=
  Equiv.ext_iff.mp (crossPerm_mul_flatten h f χ) q

/-- **A chain morphism is its crossing permutation.**  `crossPerm` pins the source chart's firing
order, and a chart is pinned by its shape and firing order (`chain_ext_of_flatten`). -/
theorem hom_ext_of_crossPerm {K : BPSet} {x y : Ch K} {N : ℕ} {h : dimSum x.dims = N} {f g : x ⟶ y}
    (hfg : crossPerm h f = crossPerm h g) : f = g := by
  obtain ⟨χ⟩ := nonempty_toCube y.dims
  have hM : dimSum x.dims = dimSum y.dims := strandsEq f
  have hfg' : crossPerm hM f = crossPerm hM g := by
    rw [crossPerm_recount h hM f, crossPerm_recount h hM g, hfg]
  have hA : (⟨x.dims, Hom.φ f ≫ χ⟩ : Ch (□(dimSum y.dims))) = ⟨x.dims, Hom.φ g ≫ χ⟩ := by
    refine chain_ext_of_flatten rfl (Equiv.ext fun q => ?_)
    have h1 := crossPerm_flatten hM f χ q
    have h2 := crossPerm_flatten hM g χ q
    rw [hfg'] at h1
    exact (crossPerm hM g).injective (h1.trans h2.symm)
  obtain ⟨hd, hmap⟩ := Obj.eq_mk_of_eq hA
  rw [Subsingleton.elim hd rfl] at hmap
  exact hom_ext' (wedgeHom_ext_chart (χ := χ) (by simpa using hmap))

/-- **Realising a crossing permutation.**  Read the target in its standard chart: `σ` is realised
by an arrow `a ⟶ b` when `σ⁻¹` rises inside each bead of `a` and the beads it induces on the
coordinates sit inside `b`'s (`chFace_faceLE_iff`). -/
theorem exists_crossPerm_of_blocks {a b : List ℕ+} {N : ℕ} (ha : dimSum a = N) (hb : dimSum b = N)
    (σ : Equiv.Perm (Fin N))
    (hrise : ∀ p q : Fin N,
        (dimComp a ha).index (σ⁻¹ p) = (dimComp a ha).index (σ⁻¹ q) →
        p < q → (σ⁻¹ p : Fin N) < (σ⁻¹ q : Fin N))
    (hface : ∀ p q : Fin N,
        ((dimComp b hb).index p : ℕ) ≠ ((dimComp b hb).index q : ℕ) →
        (((dimComp b hb).index p : ℕ) < ((dimComp b hb).index q : ℕ)
            ↔ ((dimComp a ha).index (σ⁻¹ p) : ℕ) < ((dimComp a ha).index (σ⁻¹ q) : ℕ))) :
    ∃ f : zObj a ⟶ zObj b, crossPerm ha f = σ := by
  obtain ⟨x, hx⟩ := exists_chart_flatten ha σ⁻¹ hrise
  set A : Ch (□N) := ⟨a, x⟩ with hA
  have hbeadA : ∀ q, (beadOf A q : ℕ) = ((dimComp a ha).index (σ⁻¹ q) : ℕ) := fun q => by
    rw [beadOf_eq_index, hx]
  have hle : (chFace (⟨b, stdChart hb⟩ : Ch (□N))).1 ⊑ (chFace A).1 :=
    chFace_faceLE_iff.mpr fun p q hne => by
      rw [beadOf_stdChart, beadOf_stdChart] at hne ⊢
      rw [hbeadA, hbeadA]
      exact hface p q hne
  obtain ⟨φ, hφ⟩ : ∃ z : ⋁a ⟶ ⋁b, z ≫ stdChart hb = x := ⟨_, (reflectHom hle).w⟩
  obtain ⟨f, hfφ⟩ : ∃ f : zObj a ⟶ zObj b, Hom.φ f = φ := ⟨⟨φ, Subsingleton.elim _ _⟩, rfl⟩
  refine ⟨f, Equiv.ext fun q => ?_⟩
  have h0 : (⟨(zObj a).dims, Hom.φ f ≫ stdChart hb⟩ : Ch (□N)) = A := by
    rw [hA, hfφ]; exact congrArg _ hφ
  have h2 : flatten (⟨(zObj b).dims, stdChart hb⟩ : Ch (□N)) = 1 := flatten_stdChart hb
  have h1 := crossPerm_flatten ha f (stdChart hb) (σ q)
  rw [h0, hx, h2] at h1
  simpa using h1

/-- **Merging one junction at a time.**  Induct on the boundaries still to be removed; each step is
a bead merge, so the composite crosses nothing. -/
private theorem exists_W_aux : ∀ (k : ℕ) (d d' : List ℕ+), dimSum d = dimSum d' →
    boundaries d' ⊆ boundaries d → (boundaries d).card ≤ (boundaries d').card + k →
    ∃ f : zObj d ⟶ zObj d', W Zbp f := by
  intro k
  induction k with
  | zero =>
      intro d d' _ hsub hk
      obtain rfl := boundaries_injective (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      exact ⟨𝟙 _, MorphismProperty.id_mem _ _⟩
  | succ k ih =>
      intro d d' hdim hsub hk
      by_cases heq : boundaries d = boundaries d'
      · obtain rfl := boundaries_injective heq
        exact ⟨𝟙 _, MorphismProperty.id_mem _ _⟩
      obtain ⟨t, htd, htd'⟩ :=
        Finset.exists_of_ssubset (hsub.ssubset_of_ne fun h => heq h.symm)
      have h0 : t ≠ 0 := fun h => htd' (h ▸ zero_mem_boundaries d')
      have hlast : t ≠ dimSum d := fun h =>
        htd' (by rw [h, hdim]; exact dimSum_mem_boundaries d')
      obtain ⟨l, r, p, q, rfl, rfl⟩ := exists_split_of_mem_boundaries d htd h0 hlast
      have hcard : (boundaries (l ++ p :: q :: r)).card
          = (boundaries (l ++ (p + q) :: r)).card + 1 := by
        rw [boundaries_cut l r p q,
          Finset.card_insert_of_notMem (notMem_boundaries_cut l r p q)]
      have hcut := boundaries_cut l r p q
      obtain ⟨ψ, hψ⟩ := ih (l ++ (p + q) :: r) d' ((dimSum_cut l r p q).symm.trans hdim)
        (by
          intro x hx
          rcases Finset.mem_insert.mp (hcut ▸ hsub hx) with rfl | hx'
          · exact absurd hx htd'
          · exact hx')
        (by omega)
      exact ⟨mergeHom l r p q ≫ ψ,
        (W Zbp).comp_mem _ _ (merge_le_W Zbp _ (merge_mergeHom l r p q)) hψ⟩

/-- **A coarsening is realised without crossings**: the merges that delete the extra junctions. -/
theorem exists_W_of_coarser (h : Coarser d d') : ∃ f : zObj d ⟶ zObj d', W Zbp f :=
  exists_W_aux (boundaries d).card d d' h.1 h.2 (by omega)

/-- **A hom exists exactly at a coarsening** — every wedge map only deletes junctions
(`boundaries_subset_of_wedgeHom`), and every deletion is a composite of merges. -/
theorem nonempty_wedgeHom_iff_coarser : Nonempty (⋁d ⟶ ⋁d') ↔ Coarser d d' :=
  ⟨fun ⟨φ⟩ => ⟨serialWedge_dimSum_eq φ, boundaries_subset_of_wedgeHom φ⟩,
   fun h => ⟨Hom.φ (exists_W_of_coarser h).choose⟩⟩

/-- **The hom-sets of `Ch Zbp` are exactly the coarsenings.** -/
theorem nonempty_hom_iff {a b : Ch Zbp} :
    Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ boundaries b.dims ⊆ boundaries a.dims :=
  ⟨fun ⟨f⟩ => ⟨strandsEq f, boundaries_subset_of_hom f⟩,
   fun h => (nonempty_wedgeHom_iff_coarser.mpr h).map fun φ => ⟨φ, Subsingleton.elim _ _⟩⟩

/-- **A hom-set is inhabited exactly at a refinement of beads** — a junction is where the bead
changes (`boundaries_subset_of_beadAt`), so refining beads is inclusion of junctions. -/
theorem nonempty_hom_of_index {d d' : List ℕ+} {N : ℕ} (h : dimSum d = N) (h' : dimSum d' = N)
    (hb : ∀ x y : Fin N, (dimComp d h).index x = (dimComp d h).index y →
      (dimComp d' h').index x = (dimComp d' h').index y) :
    Nonempty (zObj d ⟶ zObj d') := by
  refine nonempty_hom_iff.mpr ⟨h.trans h'.symm,
    boundaries_subset_of_beadAt (h.trans h'.symm) fun p q hp hq hpq => ?_⟩
  exact (index_eq_iff_beadAt h' ⟨p, h ▸ hp⟩ ⟨q, h ▸ hq⟩).mp
    (congrArg Fin.val (hb _ _ (Fin.ext ((index_eq_iff_beadAt h _ _).mpr hpq))))

/-- **Comparable at all is comparable without braiding**: `exists_crossPerm_of_blocks` at the
identity, the bead condition being `beadAt_lt_iff_of_subset`. -/
theorem exists_crossPerm_eq_one {a b : Ch Zbp} {N : ℕ} (h : dimSum a.dims = N)
    (hab : Nonempty (a ⟶ b)) : ∃ f : a ⟶ b, crossPerm h f = 1 := by
  obtain ⟨hdim, hsub⟩ := nonempty_hom_iff.mp hab
  have hb : dimSum b.dims = N := hdim ▸ h
  obtain ⟨f, hf⟩ := exists_crossPerm_of_blocks h hb 1 (fun _ _ _ hpq => by simpa using hpq)
    (fun p q hne => by
      simpa only [inv_one, Equiv.Perm.one_apply, index_lt_iff_beadAt] using
        beadAt_lt_iff_of_subset hsub fun hc => hne ((index_eq_iff_beadAt hb p q).mpr hc))
  exact ⟨⟨Hom.φ f, Subsingleton.elim _ _⟩, hf⟩

end ChainCat
