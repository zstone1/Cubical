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

A chart's coordinate bijection `coordFlip` has two components: the ordered partition of `Fin N`
(`beadOf`) and the firing order (`flatten`, the event order `pos` transported).  Everything
downstream is read off those — the hom-sets off `boundaries` alone.
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

/-! ## The firing order

A chart identifies the events of its shape with the coordinates of the cube (`coordFlip`), so it
transports the canonical event order `pos`: `flatten` is the order in which the chain fires the
coordinates.  Every statement below is a `pos` statement read through that identification, `beadOf`
being the other component of the same inverse. -/

/-- **Inside one bead a chart is the order embedding `faceEmb`**, so it carries the event order. -/
theorem coordFlip_lt_iff_pos_lt {N : ℕ} (χ : ⋁d ⟶ □N) {u v : beadEvent d} (h : u.1 = v.1) :
    coordFlip χ u < coordFlip χ v ↔ pos u < pos v := by
  obtain ⟨j, l⟩ := u
  obtain ⟨j', l'⟩ := v
  obtain rfl : j = j' := h
  rw [coordFlip_eq, coordFlip_eq, pos_lt_iff_of_fst_eq]
  exact (faceEmb (beadFace χ.hom j)).lt_iff_lt

/-- **The firing order of a chart**: the rank of the event that flips a coordinate — the event
order `pos`, transported along the chart's coordinate bijection. -/
def flatten {N : ℕ} (A : Ch (□N)) : Equiv.Perm (Fin N) :=
  (coordFlip A.map).symm.trans (ChainCat.strand A (wedgeDimSum_eq A.map))

theorem flatten_val {N : ℕ} (A : Ch (□N)) (q : Fin N) :
    (flatten A q : ℕ) = (pos ((coordFlip A.map).symm q) : ℕ) := rfl

/-- **A chart carries the event order to its own**: the chart's `flatten` *is* `pos`. -/
theorem flatten_coordFlip {N : ℕ} (χ : ⋁d ⟶ □N) (e : beadEvent d) :
    flatten (⟨d, χ⟩ : Ch (□N)) (coordFlip χ e)
      = ChainCat.strand (⟨d, χ⟩ : Ch (□N)) (wedgeDimSum_eq χ) e := by
  simp only [flatten, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- **The flattening orders by bead, then by the cube's own order** — the two clauses of the
lexicographic event order, transported. -/
theorem flatten_lt_iff {N : ℕ} (A : Ch (□N)) {q q' : Fin N} :
    flatten A q < flatten A q' ↔
      (beadOf A q : ℕ) < (beadOf A q' : ℕ) ∨ (beadOf A q = beadOf A q' ∧ q < q') := by
  have hlt : flatten A q < flatten A q'
      ↔ pos ((coordFlip A.map).symm q) < pos ((coordFlip A.map).symm q') := by
    rw [Fin.lt_def, Fin.lt_def, flatten_val, flatten_val]
  rw [hlt, beadOf_eq, beadOf_eq]
  refine ⟨fun h => ?_, ?_⟩
  · rcases eq_or_lt_of_le (fst_le_of_pos_lt h) with heq | hfst
    · refine Or.inr ⟨Fin.ext heq, ?_⟩
      have hq := (coordFlip_lt_iff_pos_lt A.map (Fin.ext heq)).mpr h
      rwa [(coordFlip A.map).apply_symm_apply, (coordFlip A.map).apply_symm_apply] at hq
    · exact Or.inl hfst
  · rintro (h | ⟨h, h2⟩)
    · exact pos_lt_of_fst_lt h
    · refine (coordFlip_lt_iff_pos_lt A.map h).mp ?_
      rwa [(coordFlip A.map).apply_symm_apply, (coordFlip A.map).apply_symm_apply]

/-- **The flattening lands in the bead's own block of ranks** — `pos` is `beadStart` plus the
within-bead offset. -/
theorem flatten_mem_bead {N : ℕ} (A : Ch (□N)) (q : Fin N) :
    beadStart A.dims (beadOf A q) ≤ (flatten A q : ℕ) ∧
      (flatten A q : ℕ) < beadStart A.dims ((beadOf A q : ℕ) + 1) := by
  have hp : (flatten A q : ℕ)
      = beadStart A.dims (beadOf A q) + (((coordFlip A.map).symm q).2 : ℕ) := pos_val _
  have hk : ((((coordFlip A.map).symm q).2 : ℕ)) < (A.dims.get (beadOf A q) : ℕ) :=
    ((coordFlip A.map).symm q).2.isLt
  have hs := beadStart_succ A.dims (beadOf A q)
  omega

/-- **A coordinate sits in an earlier bead exactly when its rank sits before that bead starts.** -/
theorem beadOf_lt_iff {N : ℕ} (A : Ch (□N)) (q : Fin N) (j : ℕ) :
    (beadOf A q : ℕ) < j ↔ (flatten A q : ℕ) < beadStart A.dims j := by
  obtain ⟨hlo, hhi⟩ := flatten_mem_bead A q
  refine ⟨fun h => lt_of_lt_of_le hhi (beadStart_mono A.dims h), fun h => ?_⟩
  by_contra hc
  exact absurd (le_trans (beadStart_mono A.dims (not_lt.mp hc)) hlo) (not_le.mpr h)

/-- **A run's step order *is* its chart's firing order** — the two names for one construction
(`localStep` is `Concurrency/Executions/RunSegal`'s, at a run of the cube). -/
theorem localStep_eq_flatten {N : ℕ} (r : Run (□N)) : localStep r = flatten r.chain := rfl

/-- **On an all-edges chain the firing order is the partition**: one event per bead, so the rank of
a coordinate is its bead. -/
theorem flatten_eq_beadOf_of_ones {N : ℕ} {A : Ch (□N)} (h : ∀ c ∈ A.dims, c = 1) (q : Fin N) :
    (flatten A q : ℕ) = (beadOf A q : ℕ) :=
  localStep_val ⟨A, h⟩ q

/-- **The firing order refines the bead order.** -/
theorem beadOf_le_of_flatten_le {N : ℕ} (A : Ch (□N)) {r s : Fin N}
    (h : (flatten A r : ℕ) ≤ (flatten A s : ℕ)) : (beadOf A r : ℕ) ≤ (beadOf A s : ℕ) :=
  Nat.lt_succ_iff.mp ((beadOf_lt_iff A r _).mpr (lt_of_le_of_lt h (flatten_mem_bead A s).2))

/-- A permutation of `Fin N` has exactly `k` values below `k`. -/
theorem card_flatten_lt {N : ℕ} (A : Ch (□N)) {k : ℕ} (hk : k ≤ N) :
    (Finset.univ.filter fun r : Fin N => (flatten A r : ℕ) < k).card = k := by
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [Finset.filter_true_of_mem fun r _ => (flatten A r).isLt, Finset.card_univ,
      Fintype.card_fin]
  · simpa [Fin.lt_def] using Equiv.Perm.card_filter_lt (flatten A) ⟨k, hlt⟩

/-- **The coordinates before a junction are the first `beadStart` many.**  The bridge from a
chart's partition to its shape's `boundaries`. -/
theorem card_beadOf_lt {N : ℕ} (A : Ch (□N)) (j : ℕ) :
    (Finset.univ.filter fun r : Fin N => (beadOf A r : ℕ) < j).card = beadStart A.dims j := by
  rw [← card_flatten_lt A ((beadStart_le_dimSum A.dims j).trans_eq (wedgeDimSum_eq A.map))]
  exact congrArg Finset.card (Finset.filter_congr fun r _ => beadOf_lt_iff A r j)

/-- **`flatten` is the only order on the coordinates that sorts by `(bead, then rank)`**: a
bijection `g` respecting that key is `flatten`'s inverse, since `flatten ∘ g` is then a monotone
permutation. -/
theorem flatten_apply {N : ℕ} (A : Ch (□N)) (g : Equiv.Perm (Fin N))
    (hg : ∀ x y : Fin N, x < y → (beadOf A (g x) : ℕ) < (beadOf A (g y) : ℕ) ∨
      (beadOf A (g x) = beadOf A (g y) ∧ g x < g y)) (x : Fin N) :
    flatten A (g x) = x := by
  have hmono : Monotone (g.trans (flatten A)) := fun u v huv => by
    simp only [Equiv.trans_apply]
    rcases eq_or_lt_of_le huv with rfl | hlt
    · exact le_rfl
    · exact le_of_lt ((flatten_lt_iff A).mpr (hg u v hlt))
  exact Equiv.ext_iff.mp ((Equiv.Perm.monotone_iff _).mp hmono) x

/-! ## Realising a firing order

A chart of shape `d` fires its coordinates in an order that rises inside each block of `d` — and
every such order occurs, the beads being the blocks of `d` read through it. -/

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
`χ` of its target; the source chart is `f ≫ χ`, and `crossPerm` takes one `flatten` to the other. -/
theorem crossPerm_flatten {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (χ : ⋁b.dims ⟶ □N) (q : Fin N) :
    crossPerm h f (flatten (⟨a.dims, Hom.φ f ≫ χ⟩ : Ch (□N)) q)
      = flatten (⟨b.dims, χ⟩ : Ch (□N)) q := by
  obtain ⟨e, rfl⟩ := (coordFlip (Hom.φ f ≫ χ)).surjective q
  rw [flatten_coordFlip, coordFlip_comp, flatten_coordFlip]
  exact crossPerm_strand h f e

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

/-- **The block index jumps exactly across a junction** — the dictionary between
`Composition.index` and `boundaries`, and the only thing the two comparisons below need. -/
theorem index_lt_index_iff {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (p q : Fin N) :
    ((dimComp d hd).index p : ℕ) < ((dimComp d hd).index q : ℕ) ↔
      ∃ t ∈ boundaries d, (p : ℕ) < t ∧ t ≤ (q : ℕ) := by
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

/-- **A junction is where the block index jumps**: if `a`'s blocks refine `b`'s, then every
junction of `b` is one of `a`. -/
theorem boundaries_subset_of_index {a b : List ℕ+} {N : ℕ} (ha : dimSum a = N)
    (hb : dimSum b = N)
    (h : ∀ x y : Fin N, (dimComp a ha).index x = (dimComp a ha).index y →
      (dimComp b hb).index x = (dimComp b hb).index y) :
    boundaries b ⊆ boundaries a := by
  intro t ht
  have htN : t ≤ N := hb ▸ le_dimSum_of_mem_boundaries ht
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · exact zero_mem_boundaries a
  rcases eq_or_lt_of_le htN with rfl | hlt
  · rw [← ha]; exact dimSum_mem_boundaries a
  -- `0 < t < N`: `b`'s index jumps between `t-1` and `t`, hence so does `a`'s, hence `t` is one of
  -- `a`'s junctions — it is the only candidate the jump can sit at.
  obtain ⟨x, hx⟩ : ∃ x : Fin N, (x : ℕ) = t - 1 := ⟨⟨t - 1, by omega⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin N, (y : ℕ) = t := ⟨⟨t, by omega⟩, rfl⟩
  have hbj : ((dimComp b hb).index x : ℕ) < ((dimComp b hb).index y : ℕ) :=
    (index_lt_index_iff hb x y).mpr ⟨t, ht, by omega, by omega⟩
  have haj : ((dimComp a ha).index x : ℕ) < ((dimComp a ha).index y : ℕ) :=
    lt_of_le_of_ne ((dimComp a ha).index_monotone (Fin.le_def.mpr (by omega)))
      fun hcon => absurd (congrArg Fin.val (h x y (Fin.ext hcon))) (by omega)
  obtain ⟨s, hs, hxs, hsy⟩ := (index_lt_index_iff ha x y).mp haj
  exact (show s = t by omega) ▸ hs

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

/-- **Junctions order the blocks**: if every junction of `b` is one of `a`, then `a`'s blocks
refine `b`'s, order and all. -/
theorem index_lt_of_index_lt {a b : List ℕ+} {N : ℕ} (ha : dimSum a = N) (hb : dimSum b = N)
    (hsub : boundaries b ⊆ boundaries a) {p q : Fin N}
    (h : ((dimComp b hb).index p : ℕ) < ((dimComp b hb).index q : ℕ)) :
    ((dimComp a ha).index p : ℕ) < ((dimComp a ha).index q : ℕ) :=
  let ⟨t, ht, hpt, htq⟩ := (index_lt_index_iff hb p q).mp h
  (index_lt_index_iff ha p q).mpr ⟨t, hsub ht, hpt, htq⟩

/-- **…and the finer blocks order them the same way**, once the coarser already separates them:
the two block orders agree wherever the coarse one is defined. -/
theorem index_lt_iff_index_lt {c f : List ℕ+} {N : ℕ} (hc : dimSum c = N) (hf : dimSum f = N)
    (hsub : boundaries c ⊆ boundaries f) {p q : Fin N}
    (hne : ((dimComp c hc).index p : ℕ) ≠ ((dimComp c hc).index q : ℕ)) :
    ((dimComp c hc).index p : ℕ) < ((dimComp c hc).index q : ℕ)
      ↔ ((dimComp f hf).index p : ℕ) < ((dimComp f hf).index q : ℕ) :=
  ⟨index_lt_of_index_lt hf hc hsub,
   fun h => lt_of_le_of_ne
     (not_lt.mp fun hcon => absurd (index_lt_of_index_lt hf hc hsub hcon) (asymm h)) hne⟩

/-- **A hom-set is inhabited exactly at a refinement of blocks** — a junction is where the block
index jumps, so refining blocks is inclusion of junctions. -/
theorem nonempty_hom_of_index {d d' : List ℕ+} {N : ℕ} (h : dimSum d = N) (h' : dimSum d' = N)
    (hb : ∀ x y : Fin N, (dimComp d h).index x = (dimComp d h).index y →
      (dimComp d' h').index x = (dimComp d' h').index y) :
    Nonempty (zObj d ⟶ zObj d') :=
  nonempty_hom_iff.mpr ⟨h.trans h'.symm, boundaries_subset_of_index h h' hb⟩

/-- **Comparable at all is comparable without braiding**: `exists_crossPerm_of_blocks` at the
identity, the block condition being `index_lt_of_index_lt` both ways. -/
theorem exists_crossPerm_eq_one {a b : Ch Zbp} {N : ℕ} (h : dimSum a.dims = N)
    (hab : Nonempty (a ⟶ b)) : ∃ f : a ⟶ b, crossPerm h f = 1 := by
  obtain ⟨hdim, hsub⟩ := nonempty_hom_iff.mp hab
  have hb : dimSum b.dims = N := hdim ▸ h
  obtain ⟨f, hf⟩ := exists_crossPerm_of_blocks h hb 1 (fun _ _ _ hpq => by simpa using hpq)
    (fun p q hne => by
      simpa only [inv_one, Equiv.Perm.one_apply] using index_lt_iff_index_lt hb h hsub hne)
  exact ⟨⟨Hom.φ f, Subsingleton.elim _ _⟩, hf⟩

end ChainCat
