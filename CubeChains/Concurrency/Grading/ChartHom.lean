import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.WedgeBraid
import CubeChains.Concurrency.Grading.Degree
import CubeChains.Concurrency.Executions.RunPerm
import CubeChains.Concurrency.Salvetti.ChainBraidFace
import CubeChains.Machinery.SortPerm
import CubeChains.Machinery.Composition
import CubeChains.Precubical.Chains.Correspondence
import Mathlib.Data.Prod.Lex

/-!
# Concurrency/Grading/ChartHom — a wedge map is a chart refining a chart

A serial wedge maps into the cube of its own total dimension (`nonempty_toCube`) and a chart is a
monomorphism (`descent_mono`), so `φ ↦ φ ≫ χ` identifies `⋁a ⟶ ⋁b` with the charts of `⋁a` lying
over a fixed chart of `⋁b` — the fibre description of the discrete fibration `Ch (□N) ⥤ Ch Zbp`,
with `Ch (□N)` thin.

A chart *is* an ordered partition of `Fin N` (`beadOf`), so everything downstream is read off that:
the hom-sets off `boundaries` alone, and the firing order off `flatten` — sort the coordinates by
bead, ties broken by the cube's own order.
-/

open CategoryTheory BPSet CubeChain ChainCat

namespace CubeChains

variable {a b d d' : List ℕ+}

/-! ## Charts -/

/-- **Total merge**: a serial wedge maps into the cube of its own total dimension — absorb the
leading bead with `cubeMerge`, recurse on the tail. -/
theorem nonempty_toCube : ∀ b : List ℕ+, Nonempty (⋁b ⟶ □(dimSum b))
  | [] => ⟨𝟙 _⟩
  | p :: rest => (nonempty_toCube rest).map fun χ =>
      ChainCat.wedge2Map (𝟙 (□(p : ℕ))) χ ≫ ChainCat.cubeMerge (p : ℕ) (dimSum rest)

/-- A chart is a monomorphism — the descent map of a chain of the cube. -/
theorem chart_mono {N : ℕ} (A : Ch (□N)) : Mono A.map.hom :=
  descent_mono (cube_nonSelfLinked N) (BPSet.cube_admitsAltitude N) A

/-- **Chains of a cube are a poset** — a chart pins the map it came from. -/
instance chCube_isThin (N : ℕ) : Quiver.IsThin (Ch (□N)) :=
  chainCat_hom_subsingleton (cube_nonSelfLinked N) (BPSet.cube_admitsAltitude N)

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

/-- **A chart of a fixed shape is a chain of that shape** — the fibre of `Ch K ⥤ Ch Zbp`. -/
def chartFibreEquiv {K : BPSet} (d : List ℕ+) : (⋁d ⟶ K) ≃ {A : Ch K // A.dims = d} where
  toFun x := ⟨⟨d, x⟩, rfl⟩
  invFun A := ⋁≡A.2.symm ≫ A.1.map
  left_inv x := by simp
  right_inv A := Subtype.ext (ChainCat.Obj.mk_eq_mk A.2.symm rfl)

/-- An all-edges chain of a cube is the run shape: its bead count is its total dimension. -/
theorem cubeChain_dims_ones_iff {N : ℕ} (A : Ch (□N)) : A.dims = 𝟙^N ↔ ∀ c ∈ A.dims, c = 1 := by
  refine ⟨fun h c hc => List.eq_of_mem_replicate (h ▸ hc), fun h => ?_⟩
  have hlen : A.dims.length = N := (dimSum_eq_length_of_ones h).symm.trans (wedgeDimSum_eq A.map)
  conv_lhs => rw [eq_replicate_of_ones h]
  rw [hlen]

/-- The runs are the all-edges chains, as a subtype. -/
def runSubtypeEquiv (K : BPSet) : {A : Ch K // ∀ c ∈ A.dims, c = 1} ≃ Run K where
  toFun A := ⟨A.1, A.2⟩
  invFun r := ⟨r.1, r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A chart of the run in a cube is a run of that cube.** -/
def onesChartEquiv (N : ℕ) : (⋁(𝟙^N) ⟶ □N) ≃ Run (□N) :=
  (chartFibreEquiv (𝟙^N)).trans
    ((Equiv.subtypeEquivRight fun A => cubeChain_dims_ones_iff A).trans (runSubtypeEquiv (□N)))

/-! ## Ordered partitions: counting, and the firing order

A chart enumerates each bead's block of coordinates, so the fibres of `beadOf` have the bead's
dimension — and summing over a prefix recovers the shape's own prefix sums (`card_beadOf_lt`).
Sorting the coordinates by that data is `flatten`, the order in which the chain fires them. -/

/-- **The bead fibre of a chart has the bead's dimension.**  `faceEmb` enumerates exactly the
coordinates whose bead is `i` (`mem_range_iff_beadOf`). -/
theorem card_beadFibre {N : ℕ} (A : Ch (□N)) (i : Fin A.dims.length) :
    (Finset.univ.filter fun q => beadOf A q = i).card = (A.dims.get i : ℕ) := by
  refine ((Finset.card_bij (s := (Finset.univ : Finset (Fin (A.dims.get i : ℕ))))
    (t := Finset.univ.filter fun q => beadOf A q = i)
    (fun k _ => coordFlip A.map ⟨i, k⟩) ?_ ?_ ?_).symm.trans (Finset.card_fin _))
  · intro k _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [beadOf_eq, Equiv.symm_apply_apply]
  · intro k _ k' _ h
    simpa using (coordFlip A.map).injective h
  · intro q hq
    obtain ⟨k, hk⟩ := (mem_range_iff_beadOf A i q).mpr (Finset.mem_filter.mp hq).2
    exact ⟨k, Finset.mem_univ _, by simp only [coordFlip_eq]; exact hk⟩

/-- **The coordinates before a junction are the first `beadStart` many** — `card_beadFibre` summed
over the earlier beads.  The bridge from a chain's partition to its shape's `boundaries`. -/
theorem card_beadOf_lt {N : ℕ} (A : Ch (□N)) (j : ℕ) :
    (Finset.univ.filter fun r : Fin N => (beadOf A r : ℕ) < j).card = beadStart A.dims j := by
  induction j with
  | zero => simp [beadStart]
  | succ j ih =>
      rcases lt_or_ge j A.dims.length with hj | hj
      · have hsplit : (Finset.univ.filter fun r : Fin N => (beadOf A r : ℕ) < j + 1)
            = (Finset.univ.filter fun r : Fin N => (beadOf A r : ℕ) < j)
              ∪ Finset.univ.filter fun r : Fin N => beadOf A r = ⟨j, hj⟩ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.ext_iff]
          omega
        have hdisj : Disjoint (Finset.univ.filter fun r : Fin N => (beadOf A r : ℕ) < j)
            (Finset.univ.filter fun r : Fin N => beadOf A r = ⟨j, hj⟩) := by
          simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.ext_iff]
          omega
        rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, card_beadFibre A ⟨j, hj⟩,
          beadStart_succ A.dims ⟨j, hj⟩]
      · have hstart : beadStart A.dims (j + 1) = beadStart A.dims j := by
          rw [beadStart, beadStart, List.take_of_length_le (by omega),
            List.take_of_length_le (by omega)]
        rw [hstart, ← ih]
        refine congrArg Finset.card (Finset.filter_congr fun r _ => ?_)
        have hr := (beadOf A r).isLt
        exact ⟨fun _ => by omega, fun _ => by omega⟩

/-- The key a chart sorts its coordinates by: bead first, then the cube's own order. -/
private def flatKey {N : ℕ} (A : Ch (□N)) (q : Fin N) : Fin A.dims.length ×ₗ Fin N :=
  toLex (beadOf A q, q)

private theorem flatKey_injective {N : ℕ} (A : Ch (□N)) : Function.Injective (flatKey A) :=
  fun _ _ h => congrArg (fun p => (ofLex p).2) h

/-- **The firing order of a chart**: a coordinate's rank when the coordinates are sorted by bead,
ties broken by the cube's own order.  A function of `beadOf` alone — of the geometry. -/
noncomputable def flatten {N : ℕ} (A : Ch (□N)) : Equiv.Perm (Fin N) :=
  (Tuple.sort (flatKey A))⁻¹

/-- The flattening is the rank for the key it sorts by. -/
private theorem flatten_lt_iff_key {N : ℕ} (A : Ch (□N)) {q q' : Fin N} :
    flatten A q < flatten A q' ↔ flatKey A q < flatKey A q' := by
  have hsm : StrictMono (flatKey A ∘ ⇑(Tuple.sort (flatKey A))) :=
    (Tuple.monotone_sort (flatKey A)).strictMono_of_injective
      ((flatKey_injective A).comp (Tuple.sort (flatKey A)).injective)
  have key : ∀ r : Fin N, flatKey A r = (flatKey A ∘ ⇑(Tuple.sort (flatKey A))) (flatten A r) :=
    fun r => by simp [flatten]
  rw [key q, key q']
  exact (hsm.lt_iff_lt).symm

/-- **The flattening orders by bead, then by the cube's own order.** -/
theorem flatten_lt_iff {N : ℕ} (A : Ch (□N)) {q q' : Fin N} :
    flatten A q < flatten A q' ↔
      (beadOf A q : ℕ) < (beadOf A q' : ℕ) ∨ (beadOf A q = beadOf A q' ∧ q < q') := by
  rw [flatten_lt_iff_key]
  exact Prod.Lex.toLex_lt_toLex

/-- **The flattening lands in the bead's own block of ranks** — the sandwich that lets a shape read
`beadOf` back off `flatten`. -/
theorem flatten_mem_bead {N : ℕ} (A : Ch (□N)) (q : Fin N) :
    beadStart A.dims (beadOf A q) ≤ (flatten A q : ℕ) ∧
      (flatten A q : ℕ) < beadStart A.dims ((beadOf A q : ℕ) + 1) := by
  have hsplit : (Finset.univ.filter fun j : Fin N => flatten A j < flatten A q)
      = (Finset.univ.filter fun j : Fin N => (beadOf A j : ℕ) < (beadOf A q : ℕ))
        ∪ Finset.univ.filter fun j : Fin N => beadOf A j = beadOf A q ∧ j < q := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, flatten_lt_iff]
  have hdisj : Disjoint
      (Finset.univ.filter fun j : Fin N => (beadOf A j : ℕ) < (beadOf A q : ℕ))
      (Finset.univ.filter fun j : Fin N => beadOf A j = beadOf A q ∧ j < q) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro j hj ⟨hj', -⟩
    rw [hj'] at hj
    exact absurd hj (lt_irrefl _)
  have hcount := Equiv.Perm.card_filter_lt (flatten A) (flatten A q)
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_beadOf_lt A] at hcount
  have hlt : (Finset.univ.filter fun j : Fin N => beadOf A j = beadOf A q ∧ j < q).card
      < (A.dims.get (beadOf A q) : ℕ) := by
    rw [← card_beadFibre A (beadOf A q)]
    refine Finset.card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
    · exact absurd (Finset.mem_filter.mp
        (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ q, rfl⟩))).2.2 (lt_irrefl q)
  have hsucc := beadStart_succ A.dims (beadOf A q)
  omega

/-- **A chart is pinned by its shape and its firing order** — the sandwich reads `beadOf` back. -/
theorem chain_ext_of_flatten {N : ℕ} {A A' : Ch (□N)} (hd : A.dims = A'.dims)
    (h : flatten A = flatten A') : A = A' := by
  refine eq_of_beadOf fun q => ?_
  obtain ⟨h1, h2⟩ := flatten_mem_bead A q
  obtain ⟨h1', h2'⟩ := flatten_mem_bead A' q
  have e1 : beadStart A'.dims (beadOf A' q : ℕ) = beadStart A.dims (beadOf A' q : ℕ) := by rw [hd]
  have e2 : beadStart A'.dims ((beadOf A' q : ℕ) + 1)
      = beadStart A.dims ((beadOf A' q : ℕ) + 1) := by rw [hd]
  rw [e1] at h1'
  rw [e2] at h2'
  rw [h] at h1 h2
  by_contra hne
  rcases Nat.lt_or_ge (beadOf A q : ℕ) (beadOf A' q : ℕ) with hc | hc
  · have hm := beadStart_mono A.dims (show (beadOf A q : ℕ) + 1 ≤ (beadOf A' q : ℕ) from hc)
    omega
  · have hm := beadStart_mono A.dims
      (show (beadOf A' q : ℕ) + 1 ≤ (beadOf A q : ℕ) by omega)
    omega

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

/-- A bead start is the start of its own block. -/
theorem index_beadStart {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) {j : ℕ} (hj : j < d.length)
    (p : Fin N) (hp : (p : ℕ) = beadStart d j) : ((dimComp d hd).index p : ℕ) = j :=
  index_eq_of_beadStart hd p hp.ge (by rw [hp]; exact beadStart_lt_beadStart hj (Nat.lt_succ_self j))

/-- The coordinates below a bound are the first that many. -/
private theorem card_val_lt (N : ℕ) {t : ℕ} (ht : t ≤ N) :
    (Finset.univ.filter fun p : Fin N => (p : ℕ) < t).card = t := by
  refine ((Finset.card_bij (s := (Finset.univ : Finset (Fin t)))
    (t := Finset.univ.filter fun p : Fin N => (p : ℕ) < t)
    (fun k _ => ⟨(k : ℕ), lt_of_lt_of_le k.isLt ht⟩) ?_ ?_ ?_).symm.trans (Finset.card_fin t))
  · exact fun k _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩
  · intro k _ k' _ h
    exact Fin.ext (by simpa using h)
  · exact fun p hp => ⟨⟨(p : ℕ), (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩

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
  have hsurj : Function.Surjective (fun q : Fin N => (dimComp d hd).index (ρ q)) := by
    intro j
    have hjd : (j : ℕ) < d.length := by rw [← dimComp_length d hd]; exact j.isLt
    have hjN : beadStart d (j : ℕ) < N := by
      have h1 : beadStart d (j : ℕ) < beadStart d d.length := beadStart_lt_beadStart le_rfl hjd
      rw [beadStart_length] at h1
      omega
    refine ⟨ρ.symm ⟨beadStart d (j : ℕ), hjN⟩, Fin.ext ?_⟩
    show ((dimComp d hd).index (ρ (ρ.symm ⟨beadStart d (j : ℕ), hjN⟩)) : ℕ) = (j : ℕ)
    rw [Equiv.apply_symm_apply]
    exact index_beadStart hd hjd _ rfl
  set β : Fin N → Fin (dimComp d hd).length := fun q => (dimComp d hd).index (ρ q) with hβ
  refine ⟨blockChain β hsurj, ?_, ?_⟩
  · refine eq_of_beadStart_eq (by rw [length_blockChain, dimComp_length]) fun j hj => ?_
    have hjd : j ≤ d.length := by rwa [length_blockChain, dimComp_length] at hj
    have hfil : (Finset.univ.filter fun r : Fin N => (beadOf (blockChain β hsurj) r : ℕ) < j)
        = Finset.univ.filter fun r : Fin N => (ρ r : ℕ) < beadStart d j :=
      Finset.filter_congr fun r _ => by
        rw [beadOf_blockChain]; exact index_lt_iff_beadStart hd (ρ r) j
    have hle : beadStart d j ≤ N := by
      have := beadStart_mono d hjd
      rw [beadStart_length] at this
      omega
    rw [← card_beadOf_lt, hfil]
    exact (Finset.card_equiv ρ fun r => by simp).trans (card_val_lt N hle)
  · have hmono : Monotone (ρ.symm.trans (flatten (blockChain β hsurj))) := by
      intro x y hxy
      simp only [Equiv.trans_apply]
      rcases eq_or_lt_of_le hxy with rfl | hlt
      · exact le_rfl
      set q := ρ.symm x with hq
      set q' := ρ.symm y with hq'
      have hρ : ρ q < ρ q' := by rw [hq, hq', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
                                 exact hlt
      refine le_of_lt ((flatten_lt_iff _).mpr ?_)
      rw [beadOf_blockChain, beadOf_blockChain]
      rcases eq_or_lt_of_le ((dimComp d hd).index_monotone (Fin.le_def.mp hρ.le)) with heq | hblt
      · refine Or.inr ⟨Fin.ext (by rw [beadOf_blockChain, beadOf_blockChain]; exact heq), ?_⟩
        by_contra hc
        rcases eq_or_lt_of_le (not_lt.mp hc) with heq2 | hgt
        · exact absurd hρ (by rw [heq2]; exact lt_irrefl _)
        · exact absurd (hrise q' q (Fin.ext heq.symm) hgt) (asymm hρ)
      · exact Or.inl hblt
    have hone := Equiv.Perm.eq_one_of_monotone hmono
    refine Equiv.ext fun q => ?_
    have := Equiv.ext_iff.mp hone (ρ q)
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] using this

/-- **A coordinate's bead is the block its rank falls in** — the dictionary between a chart's
partition and its shape's blocks. -/
theorem beadOf_eq_index {N : ℕ} (A : Ch (□N)) (q : Fin N) :
    (beadOf A q : ℕ) = ((dimComp A.dims (wedgeDimSum_eq A.map)).index (flatten A q) : ℕ) := by
  obtain ⟨h1, h2⟩ := flatten_mem_bead A q
  have hb : (beadOf A q : ℕ) < A.dims.length := (beadOf A q).isLt
  have k1 : ¬ (((dimComp A.dims (wedgeDimSum_eq A.map)).index (flatten A q) : ℕ)
      < (beadOf A q : ℕ)) :=
    fun hc => absurd ((index_lt_iff_beadStart _ _ _).mp hc) (by omega)
  have k2 : ((dimComp A.dims (wedgeDimSum_eq A.map)).index (flatten A q) : ℕ)
      < (beadOf A q : ℕ) + 1 :=
    (index_lt_iff_beadStart _ _ _).mpr h2
  omega

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

/-! ## The bridge to `crossPerm`

`crossPerm` is defined from the lexicographic flattening `pos` of the *events* of a shape
(`Grading/WedgeBraid`).  These two lemmas are the only place where that spelling meets the chart's
own order; everything downstream reads `crossPerm` off `flatten` instead. -/

/-- Inside one bead a chart is the order embedding `faceEmb`, so it carries the event order. -/
theorem coordFlip_lt_of_pos_lt {N : ℕ} (χ : ⋁d ⟶ □N) {u v : beadEvent d} (h : u.1 = v.1)
    (hlt : pos u < pos v) : coordFlip χ u < coordFlip χ v := by
  obtain ⟨j, l⟩ := u
  obtain ⟨j', l'⟩ := v
  obtain rfl : j = j' := h
  rw [coordFlip_eq, coordFlip_eq]
  exact (faceEmb (beadFace χ.hom j)).strictMono (pos_lt_iff_of_fst_eq.mp hlt)

/-- **A chart carries the event order to its own**: the chart's `flatten` *is* `pos`. -/
theorem flatten_coordFlip {N : ℕ} (χ : ⋁d ⟶ □N) (e : beadEvent d) :
    flatten (⟨d, χ⟩ : Ch (□N)) (coordFlip χ e)
      = ChainCat.strand (⟨d, χ⟩ : Ch (□N)) (wedgeDimSum_eq χ) e := by
  set A : Ch (□N) := ⟨d, χ⟩ with hA
  set hN : dimSum A.dims = N := wedgeDimSum_eq χ with hNdef
  have hbead : ∀ x : beadEvent d, beadOf A (coordFlip χ x) = x.1 := fun x => by
    rw [beadOf_eq]; exact congrArg Sigma.fst ((coordFlip χ).symm_apply_apply x)
  have hmono : Monotone
      ((ChainCat.strand A hN).symm.trans ((coordFlip χ).trans (flatten A))) := by
    intro x y hxy
    simp only [Equiv.trans_apply]
    set u := (ChainCat.strand A hN).symm x with hu
    set v := (ChainCat.strand A hN).symm y with hv
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    have hposlt : pos u < pos v := by
      have : ChainCat.strand A hN u < ChainCat.strand A hN v := by
        rw [hu, hv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hlt
      exact this
    refine le_of_lt ((flatten_lt_iff A).mpr ?_)
    rcases eq_or_lt_of_le (fst_le_of_pos_lt hposlt) with heq | hfst
    · exact Or.inr ⟨by rw [hbead, hbead]; exact Fin.ext heq,
        coordFlip_lt_of_pos_lt χ (Fin.ext heq) hposlt⟩
    · exact Or.inl (by rw [hbead, hbead]; exact hfst)
  have hone := Equiv.Perm.eq_one_of_monotone hmono
  have := Equiv.ext_iff.mp hone (ChainCat.strand A hN e)
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] using this

/-! ## Coarsening -/

/-- `d'` **coarsens** `d`: the same events, and every junction of `d'` is one of `d`. -/
def Coarser (d d' : List ℕ+) : Prop :=
  dimSum d = dimSum d' ∧ boundaries d' ⊆ boundaries d

end CubeChains

namespace ChainCat

open CubeChains

variable {d d' : List ℕ+}

/-- A chain of `Zbp` is its dimension list — the terminal target carries no data. -/
theorem eq_zObj (a : Ch Zbp) : a = zObj a.dims := Obj.eq_of_dims rfl

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

theorem crossPerm_injective {K : BPSet} {x y : Ch K} {N : ℕ} (h : dimSum x.dims = N) :
    Function.Injective fun f : x ⟶ y => crossPerm h f := fun _ _ hfg => hom_ext_of_crossPerm hfg

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
  -- `0 < t < N`: `b`'s block index jumps at `t`, hence so does `a`'s.
  set x : Fin N := ⟨t - 1, by omega⟩ with hxdef
  set y : Fin N := ⟨t, by omega⟩ with hydef
  have hbjump : (dimComp b hb).index x ≠ (dimComp b hb).index y := by
    obtain ⟨j, hj, hjt⟩ := mem_boundaries_iff_beadStart.mp ht
    have hjlt : j < b.length := by
      rcases eq_or_lt_of_le hj with rfl | hh
      · rw [beadStart_length, hb] at hjt; omega
      · exact hh
    have h1 : ((dimComp b hb).index y : ℕ) = j := index_beadStart hb hjlt y hjt.symm
    have h2 : ((dimComp b hb).index x : ℕ) < j :=
      (index_lt_iff_beadStart hb x j).mpr (show (t : ℕ) - 1 < beadStart b j by omega)
    exact fun hcon => absurd (congrArg Fin.val hcon) (by omega)
  have hajump : ((dimComp a ha).index x : ℕ) ≠ ((dimComp a ha).index y : ℕ) := fun hcon =>
    hbjump (h x y (Fin.ext hcon))
  have halen : ((dimComp a ha).index y : ℕ) < a.length := by
    rw [← dimComp_length a ha]; exact ((dimComp a ha).index y).isLt
  have hle : ((dimComp a ha).index x : ℕ) ≤ ((dimComp a ha).index y : ℕ) :=
    (dimComp a ha).index_monotone (Fin.le_def.mpr (show (t : ℕ) - 1 ≤ t by omega))
  have hup : ¬ (t < beadStart a ((dimComp a ha).index y : ℕ)) := fun hc =>
    absurd ((index_lt_iff_beadStart ha y _).mpr hc) (lt_irrefl _)
  have hdn : (t : ℕ) - 1 < beadStart a ((dimComp a ha).index y : ℕ) :=
    (index_lt_iff_beadStart ha x ((dimComp a ha).index y : ℕ)).mp (by omega)
  have heq : beadStart a ((dimComp a ha).index y : ℕ) = t := by omega
  exact heq ▸ beadStart_mem_boundaries a halen.le

/-- **A hom exists exactly at a coarsening** — every wedge map only deletes junctions
(`boundaries_subset_of_wedgeHom`), and every deletion is a composite of merges. -/
theorem nonempty_wedgeHom_iff_coarser : Nonempty (⋁d ⟶ ⋁d') ↔ Coarser d d' :=
  ⟨fun ⟨φ⟩ => ⟨serialWedge_dimSum_eq φ, boundaries_subset_of_wedgeHom φ⟩,
   fun h => ⟨Hom.φ (exists_W_of_coarser h).choose⟩⟩

/-- **A coarsening is an inclusion of boundary sets.** -/
theorem coarser_iff : Coarser d d' ↔ dimSum d = dimSum d' ∧ boundaries d' ⊆ boundaries d := Iff.rfl

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
    ((dimComp a ha).index p : ℕ) < ((dimComp a ha).index q : ℕ) := by
  set j := ((dimComp b hb).index q : ℕ) with hj
  have hjb : j ≤ b.length := by rw [hj, ← dimComp_length b hb]; exact ((dimComp b hb).index q).isLt.le
  have hpt : (p : ℕ) < beadStart b j := (index_lt_iff_beadStart hb p j).mp h
  have hqt : ¬ ((q : ℕ) < beadStart b j) := fun hc =>
    absurd ((index_lt_iff_beadStart hb q j).mpr hc) (by omega)
  obtain ⟨i, hi, hib⟩ := mem_boundaries_iff_beadStart.mp (hsub (beadStart_mem_boundaries b hjb))
  have h1 : ((dimComp a ha).index p : ℕ) < i :=
    (index_lt_iff_beadStart ha p i).mpr (by rw [hib]; exact hpt)
  have h2 : ¬ (((dimComp a ha).index q : ℕ) < i) := fun hc =>
    hqt (by rw [← hib]; exact (index_lt_iff_beadStart ha q i).mp hc)
  omega

/-- **A hom-set is inhabited exactly at a refinement of blocks** — a junction is where the block
index jumps, so refining blocks is inclusion of junctions. -/
theorem nonempty_hom_of_index {d d' : List ℕ+} {N : ℕ} (h : dimSum d = N) (h' : dimSum d' = N)
    (hb : ∀ x y : Fin N, (dimComp d h).index x = (dimComp d h).index y →
      (dimComp d' h').index x = (dimComp d' h').index y) :
    Nonempty (zObj d ⟶ zObj d') :=
  nonempty_hom_iff.mpr ⟨h.trans h'.symm, boundaries_subset_of_index h h' hb⟩

/-- **Comparable at all is comparable without braiding**: the two standard charts are comparable,
and an arrow between charts that both flatten to the identity crosses nothing. -/
theorem exists_crossPerm_eq_one {a b : Ch Zbp} {N : ℕ} (h : dimSum a.dims = N)
    (hab : Nonempty (a ⟶ b)) : ∃ f : a ⟶ b, crossPerm h f = 1 := by
  obtain ⟨hdim, hsub⟩ := nonempty_hom_iff.mp hab
  have hb : dimSum b.dims = N := hdim ▸ h
  have hle : (chFace (⟨b.dims, stdChart hb⟩ : Ch (□N))).1
      ⊑ (chFace (⟨a.dims, stdChart h⟩ : Ch (□N))).1 :=
    chFace_faceLE_iff.mpr fun p q hne => by
      rw [beadOf_stdChart, beadOf_stdChart] at hne ⊢
      rw [beadOf_stdChart, beadOf_stdChart]
      refine ⟨index_lt_of_index_lt h hb hsub, fun hlt => ?_⟩
      refine lt_of_le_of_ne ?_ hne
      by_contra hc
      exact absurd (index_lt_of_index_lt h hb hsub (not_le.mp hc)) (asymm hlt)
  obtain ⟨φ, hφ⟩ : ∃ z : ⋁a.dims ⟶ ⋁b.dims, z ≫ stdChart hb = stdChart h :=
    ⟨_, (reflectHom hle).w⟩
  refine ⟨⟨φ, Subsingleton.elim _ _⟩, Equiv.ext fun x => ?_⟩
  have h0 : (⟨(zObj a.dims).dims, φ ≫ stdChart hb⟩ : Ch (□N))
      = ⟨a.dims, stdChart h⟩ := congrArg _ hφ
  have h1 := crossPerm_flatten h (⟨φ, Subsingleton.elim _ _⟩ : a ⟶ b) (stdChart hb) x
  rw [show (⟨a.dims, Hom.φ (⟨φ, Subsingleton.elim _ _⟩ : a ⟶ b) ≫ stdChart hb⟩ : Ch (□N))
      = ⟨a.dims, stdChart h⟩ from h0,
    flatten_stdChart, show flatten (⟨b.dims, stdChart hb⟩ : Ch (□N)) = 1 from flatten_stdChart hb]
    at h1
  simpa using h1

end ChainCat
