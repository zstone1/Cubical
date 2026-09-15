import CubeChains.Concurrency.Grading.CoordFunctor
import CubeChains.Precubical.Chains.Embedding

/-!
# Concurrency/Grading/OrderedPartition — a chain of `□n` is an ordered partition of `Fin n`

```
Ch (□n)  ≃  {ordered partition of Fin n}        beadOf ↓   ↑ blockChain
```
`beadOf` is the bead component of `coordFlip`'s inverse and `flatten` its rank component.  Bead
`i`'s face is `blockSign` of the partition (`ev_beadFace_eq_blockSign`), so a chain is pinned by its
partition (`eq_of_beadOf`) and every partition is realised (`blockChain`); a refinement coarsens the
partition (`beadRefines_of_hom`), and a coarsening is realised by a refinement (`reflectHom`).
-/

open CategoryTheory Opposite CubeChains CubeChain PrecubicalSet

namespace CubeChains

variable {n : ℕ}

/-- **On an all-edges chain the firing order is the partition** — one event per bead. -/
theorem flatten_eq_beadOf_of_ones {A : Ch (□n)} (h : ∀ c ∈ A.dims, c = 1) (q : Fin n) :
    (flatten A q : ℕ) = (beadOf A q : ℕ) :=
  (flatten_val A q).trans (pos_ones h _)

/-- **`b`'s beads are `a`'s, unioned in order** — what a refinement `a ⟶ b` does to partitions. -/
def BeadRefines (a b : Ch (□n)) : Prop :=
  ∀ p q : Fin n, (beadOf a p : ℕ) ≤ (beadOf a q : ℕ) → (beadOf b p : ℕ) ≤ (beadOf b q : ℕ)

/-- `a` ties `p, q` ⟹ so does `b` — a coarser partition cannot separate. -/
theorem BeadRefines.tie {a b : Ch (□n)} (h : BeadRefines a b) {p q : Fin n}
    (hpq : beadOf a p = beadOf a q) : beadOf b p = beadOf b q :=
  have hv : (beadOf a p : ℕ) = (beadOf a q : ℕ) := congrArg Fin.val hpq
  Fin.val_injective (Nat.le_antisymm (h p q hv.le) (h q p hv.ge))

/-! ### The firing order against the partition

`beadOf` and `flatten` are the two components of one inverse, so every statement below is a `pos`
statement read through the chain's coordinate bijection. -/

/-- **The flattening orders by bead, then by the cube's own order.** -/
theorem flatten_lt_iff (A : Ch (□n)) {q q' : Fin n} :
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

/-- **The flattening lands in the bead's own block of ranks.** -/
theorem flatten_mem_bead (A : Ch (□n)) (q : Fin n) :
    beadStart A.dims (beadOf A q) ≤ (flatten A q : ℕ) ∧
      (flatten A q : ℕ) < beadStart A.dims ((beadOf A q : ℕ) + 1) := by
  have hp : (flatten A q : ℕ)
      = beadStart A.dims (beadOf A q) + (((coordFlip A.map).symm q).2 : ℕ) := pos_val _
  have hk : ((((coordFlip A.map).symm q).2 : ℕ)) < (A.dims.get (beadOf A q) : ℕ) :=
    ((coordFlip A.map).symm q).2.isLt
  have hs := beadStart_succ A.dims (beadOf A q)
  omega

/-- **A coordinate sits in an earlier bead exactly when its rank sits before that bead starts.** -/
theorem beadOf_lt_iff (A : Ch (□n)) (q : Fin n) (j : ℕ) :
    (beadOf A q : ℕ) < j ↔ (flatten A q : ℕ) < beadStart A.dims j := by
  obtain ⟨hlo, hhi⟩ := flatten_mem_bead A q
  refine ⟨fun h => lt_of_lt_of_le hhi (beadStart_mono A.dims h), fun h => ?_⟩
  by_contra hc
  exact absurd (le_trans (beadStart_mono A.dims (not_lt.mp hc)) hlo) (not_le.mpr h)

/-- **The firing order refines the bead order.** -/
theorem beadOf_le_of_flatten_le (A : Ch (□n)) {r s : Fin n}
    (h : (flatten A r : ℕ) ≤ (flatten A s : ℕ)) : (beadOf A r : ℕ) ≤ (beadOf A s : ℕ) :=
  Nat.lt_succ_iff.mp ((beadOf_lt_iff A r _).mpr (lt_of_le_of_lt h (flatten_mem_bead A s).2))

/-- A permutation of `Fin n` has exactly `k` values below `k`. -/
theorem card_flatten_lt (A : Ch (□n)) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter fun r : Fin n => (flatten A r : ℕ) < k).card = k := by
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [Finset.filter_true_of_mem fun r _ => (flatten A r).isLt, Finset.card_univ,
      Fintype.card_fin]
  · simpa [Fin.lt_def] using Equiv.Perm.card_filter_lt (flatten A) ⟨k, hlt⟩

/-- **`flatten` is the only order on the coordinates that sorts by `(bead, then rank)`.** -/
theorem flatten_apply (A : Ch (□n)) (g : Equiv.Perm (Fin n))
    (hg : ∀ x y : Fin n, x < y → (beadOf A (g x) : ℕ) < (beadOf A (g y) : ℕ) ∨
      (beadOf A (g x) = beadOf A (g y) ∧ g x < g y)) (x : Fin n) :
    flatten A (g x) = x := by
  have hmono : Monotone (g.trans (flatten A)) := fun u v huv => by
    simp only [Equiv.trans_apply]
    rcases eq_or_lt_of_le huv with rfl | hlt
    · exact le_rfl
    · exact le_of_lt ((flatten_lt_iff A).mpr (hg u v hlt))
  exact Equiv.ext_iff.mp ((Equiv.Perm.monotone_iff _).mp hmono) x

/-- **A chain of at most one bead fires in the cube's own order.** -/
theorem flatten_eq_one_of_length_le_one {A : Ch (□n)} (h : A.dims.length ≤ 1) : flatten A = 1 := by
  have hbead : ∀ x y : Fin n, beadOf A x = beadOf A y := fun x y =>
    Fin.ext (by have := (beadOf A x).isLt; have := (beadOf A y).isLt; omega)
  exact Equiv.ext fun q => by
    simpa using flatten_apply A 1 (fun x y hxy => Or.inr ⟨hbead _ _, hxy⟩) q

/-! ## A refinement coarsens the partition -/

/-- **`f` sends `a`'s bead of `q` to `b`'s bead of `q`** — coend functoriality (`coordFlip_comp`)
carries one coordinate bijection to the other by `coordMap fᵂ`, whose bead is `blockIdx`. -/
theorem beadOf_blockIdx {a b : Ch (□n)} (f : a ⟶ b) (q : Fin n) :
    beadOf b q = blockIdx fᵂ (beadOf a q) := by
  have hq : (coordFlip b.map).symm q = coordMap f.φ ((coordFlip a.map).symm q) := by
    rw [Equiv.symm_apply_eq, ← coordFlip_comp_apply, f.w, Equiv.apply_symm_apply]
  rw [beadOf_eq, hq, ← Sigma.eta ((coordFlip a.map).symm q), coordMap_eq]
  exact congrArg (blockIdx fᵂ) (beadOf_eq a q).symm

/-- **A refinement coarsens the partition** — `blockIdx fᵂ` is monotone. -/
theorem beadRefines_of_hom {a b : Ch (□n)} (f : a ⟶ b) : BeadRefines a b := fun p q hpq => by
  rw [beadOf_blockIdx f p, beadOf_blockIdx f q]
  exact Fin.le_def.mp (serialWedge_blockIdx_monotone f.φ (Fin.le_def.mpr hpq))

/-! ## The chain of a partition

Given `β : Fin n → Fin L` surjective, bead `j` flips exactly `β⁻¹{j}`, is `1` on earlier blocks and
`0` on later ones, and consecutive beads glue on the prefix vertex at threshold `j+1`. -/

variable {L : ℕ}

theorem noneSet_blockSign (β : Fin n → Fin L) (j : Fin L) :
    StdCube.noneSet (blockSign β j) = Finset.univ.filter (fun q => β q = j) := by
  ext q
  simp only [StdCube.mem_noneSet, Finset.mem_filter, Finset.mem_univ, true_and, blockSign]
  by_cases h : β q = j <;> simp [h]

/-- Every block is non-empty (surjectivity). -/
theorem blockSize_pos (β : Fin n → Fin L) (hβ : Function.Surjective β) (j : Fin L) :
    0 < (StdCube.noneSet (blockSign β j)).card := by
  rw [noneSet_blockSign, Finset.card_pos]
  obtain ⟨q, hq⟩ := hβ j
  exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩⟩

/-- `blockSign` packaged as a cell of `□n`; its free coordinates are block `j`. -/
def blockCell (β : Fin n → Fin L) (j : Fin L) :
    StdCube.Cell n (StdCube.noneSet (blockSign β j)).card :=
  ⟨blockSign β j, rfl⟩

/-- **The gluing computation**: bead `j`'s `ε`-vertex holds block `j` at `ε`, the rest fixed. -/
theorem substFun_blockCell (β : Fin n → Fin L) (j : Fin L) (ε : Bool) (q : Fin n) :
    StdCube.substFun (blockCell β j) (StdCube.constVertex _ ε) q
      = some (if β q = j then ε else decide ((β q : ℕ) < (j : ℕ))) := by
  by_cases hqj : β q = j
  · have h : (blockCell β j).val q = none := by simp [blockCell, blockSign, hqj]
    rw [StdCube.substFun_of_none _ _ h]; simp [StdCube.constVertex, hqj]
  · have h : (blockCell β j).val q ≠ none := by simp [blockCell, blockSign, hqj]
    rw [StdCube.substFun_of_some _ _ h]; simp [blockCell, blockSign, hqj]

/-- Junction vertex at threshold `t`: coordinate `q` is `1` iff its block is `< t`. -/
def prefixVtx (β : Fin n → Fin L) (t : ℕ) : (□n).cells 0 :=
  Box.ofSign ⟨fun q => some (decide ((β q : ℕ) < t)), by simp [StdCube.noneSet]⟩

/-- Bead `j`'s cube face of `□n`. -/
def blockCube (β : Fin n → Fin L) (j : Fin L) :
    (□n).cells (StdCube.noneSet (blockSign β j)).card :=
  Box.ofSign (blockCell β j)

/-- **Bead `j` runs from the prefix vertex at threshold `j` to the one at `j+1`.** -/
theorem vertexEnd_blockCube (β : Fin n → Fin L) (j : Fin L) (ε : Bool) :
    (□n).toPsh.vertexEnd ε (blockCube β j) = prefixVtx β ((j : ℕ) + ε.toNat) := by
  apply Box.hom_ext
  rw [sign_vertexEnd, blockCube, Box.sign_ofSign, prefixVtx, Box.sign_ofSign]
  apply Subtype.ext; funext q
  rw [StdCube.subst_val, substFun_blockCell]
  have hne : β q = j ∨ (β q : ℕ) ≠ (j : ℕ) := (em (β q = j)).imp id fun h he => h (Fin.ext he)
  rcases hne with h | h
  · have hq : (β q : ℕ) = (j : ℕ) := congrArg Fin.val h
    rw [if_pos h]; cases ε <;> simp [hq]
  · rw [if_neg fun he => h (congrArg Fin.val he)]
    congr 1
    rw [decide_eq_decide]
    cases ε <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Below threshold `0` the prefix vertex is the initial vertex. -/
theorem prefixVtx_zero (β : Fin n → Fin L) : prefixVtx β 0 = (□n).init := by
  apply Box.hom_ext
  rw [prefixVtx, Box.sign_ofSign,
    show Box.sign ((□n).init) = StdCube.constVertex n false from Box.sign_ofSign _]
  apply Subtype.ext; funext q
  change some (decide ((β q : ℕ) < 0)) = some false
  simp

/-- Above threshold `L` the prefix vertex is the final vertex. -/
theorem prefixVtx_last (β : Fin n → Fin L) : prefixVtx β L = (□n).final := by
  apply Box.hom_ext
  rw [prefixVtx, Box.sign_ofSign,
    show Box.sign ((□n).final) = StdCube.constVertex n true from Box.sign_ofSign _]
  apply Subtype.ext; funext q
  change some (decide ((β q : ℕ) < L)) = some true
  rw [decide_eq_true_iff.mpr (β q).isLt]

/-- The cube list of the reconstructed chain: one bead per block, in order. -/
def blockCubes (β : Fin n → Fin L) (hβ : Function.Surjective β) :
    List (Σ d : ℕ+, (□n).cells (d : ℕ)) :=
  List.ofFn fun j : Fin L => ⟨⟨_, blockSize_pos β hβ j⟩, blockCube β j⟩

theorem length_blockCubes (β : Fin n → Fin L) (hβ : Function.Surjective β) :
    (blockCubes β hβ).length = L := List.length_ofFn

/-- **The cube chain realising an ordered partition** `β`. -/
def ofBlockMap (β : Fin n → Fin L) (hβ : Function.Surjective β) : CubeChain (□n) :=
  ofIsCubeChain (blockCubes β hβ) <| by
    have key := isCubeChain_aux (blockCubes β hβ) (fun t => prefixVtx β (t : ℕ))
      (fun i => by
        unfold blockCubes; rw [List.get_ofFn]; exact (vertexEnd_blockCube β _ false).symm ▸ rfl)
      (fun i => by
        unfold blockCubes; rw [List.get_ofFn]; exact (vertexEnd_blockCube β _ true).symm ▸ rfl)
    have hz : (fun t : Fin ((blockCubes β hβ).length + 1) => prefixVtx β (t : ℕ)) 0
        = (□n).init := by simpa using prefixVtx_zero β
    have hl : (fun t : Fin ((blockCubes β hβ).length + 1) => prefixVtx β (t : ℕ))
        (Fin.last (blockCubes β hβ).length) = (□n).final := by
      simp only [Fin.val_last]; rw [length_blockCubes]; exact prefixVtx_last β
    rw [hz, hl] at key; exact key

/-- **The chain of `□n` whose beads are the blocks of `β`, in order**, read in `Ch`. -/
def blockChain (β : Fin n → Fin L) (hβ : Function.Surjective β) : Ch (□n) :=
  (ChainCat.chCubes (□n)).symm (ofBlockMap β hβ)

theorem length_blockChain (β : Fin n → Fin L) (hβ : Function.Surjective β) :
    (blockChain β hβ).dims.length = L := by
  simp only [blockChain]
  rw [ChainCat.chCubes_symm_dims]
  change ((ofBlockMap β hβ).cubes.map (fun c => c.1)).length = L
  rw [List.length_map]
  exact length_blockCubes β hβ

/-! ## The round trips -/

/-- Bead `j`'s cube face reads its `blockSign`. -/
theorem ev_blockCube_val (β : Fin n → Fin L) (j : Fin L) :
    (Box.sign (blockCube β j)).val = blockSign β j :=
  congrArg Subtype.val (Box.sign_ofSign (blockCell β j))

/-- `blockSign` depends only on the block values. -/
theorem blockSign_congr {L' : ℕ} {β : Fin n → Fin L} {β' : Fin n → Fin L'} {j : Fin L}
    {j' : Fin L'} (hβ : ∀ q, (β q : ℕ) = (β' q : ℕ)) (hj : (j : ℕ) = (j' : ℕ)) :
    blockSign β j = blockSign β' j' := by
  funext q; simp only [blockSign, ← Fin.val_eq_val, hβ q, hj]

/-- Two cube-list entries agree once their sign vectors do (the dimension is the free-count). -/
theorem cube_sigma_ext {d₁ d₂ : ℕ+} (c₁ : (□n).cells (d₁ : ℕ)) (c₂ : (□n).cells (d₂ : ℕ))
    (h : (Box.sign c₁).val = (Box.sign c₂).val) :
    (⟨d₁, c₁⟩ : Σ d : ℕ+, (□n).cells (d : ℕ)) = ⟨d₂, c₂⟩ := by
  have e1 : (StdCube.noneSet (Box.sign c₁).val).card = (d₁ : ℕ) := (Box.sign c₁).prop
  have e2 : (StdCube.noneSet (Box.sign c₂).val).card = (d₂ : ℕ) := (Box.sign c₂).prop
  have hd : (d₁ : ℕ) = (d₂ : ℕ) := by rw [← e1, ← e2, h]
  obtain rfl : d₁ = d₂ := PNat.coe_injective hd
  rw [Box.hom_ext (Subtype.ext h)]

/-- **Right round-trip on beads**: the chain of `β` recovers `β` (up to the length cast). -/
theorem beadOf_blockChain (β : Fin n → Fin L) (hβ : Function.Surjective β) (q : Fin n) :
    (beadOf (blockChain β hβ) q : ℕ) = (β q : ℕ) := by
  set b := blockChain β hβ with hb
  have hcubes : (beadCell b.map.hom).toList = blockCubes β hβ := by
    calc (beadCell b.map.hom).toList
        = (ChainCat.chCubes (□n) b).cubes := (ChainCat.chCubes_val b).symm
      _ = (ofBlockMap β hβ).cubes := by rw [hb, blockChain, Equiv.apply_symm_apply]
      _ = blockCubes β hβ := rfl
  rw [Beads.toList_eq_ofFn] at hcubes
  simp only [blockCubes] at hcubes
  obtain ⟨hlen, hFG⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp (List.ofFn_inj'.mp hcubes)
  have hentry : ∀ i : Fin b.dims.length,
      (Box.sign (beadFace b.map.hom i)).val = blockSign β (Fin.cast hlen i) := fun i => by
    have hi := congrArg
      (fun x : (Σ d : ℕ+, (□n).cells (d : ℕ)) => (Box.sign x.2).val) (congrFun hFG i)
    simp only [Function.comp_apply] at hi
    change (Box.sign (beadCell b.map.hom i)).val = blockSign β (Fin.cast hlen i)
    rw [hi]
    exact ev_blockCube_val β (Fin.cast hlen i)
  have hflip : blockSign β (Fin.cast hlen (beadOf b q)) q = none := by
    rw [← hentry (beadOf b q)]
    exact (ev_beadFace_eq_none_iff b (beadOf b q) q).mpr rfl
  have hβq : β q = Fin.cast hlen (beadOf b q) := by
    by_contra hcon
    simp only [blockSign] at hflip
    rw [if_neg hcon] at hflip
    exact Option.some_ne_none _ hflip
  rw [hβq, Fin.val_cast]

/-- **Left round-trip on cubes**: a chain's cube list is the block list of its partition. -/
theorem ofBlockMap_cubes_eq (b : Ch (□n)) (β : Fin n → Fin L) (hβ : Function.Surjective β)
    (hlen : L = b.dims.length) (hβval : ∀ q, (β q : ℕ) = (beadOf b q : ℕ)) :
    blockCubes β hβ = (beadCell b.map.hom).toList := by
  rw [Beads.toList_eq_ofFn]
  simp only [blockCubes]
  rw [List.ofFn_congr hlen]
  refine congrArg List.ofFn (funext fun i => ?_)
  dsimp only
  refine cube_sigma_ext _ _ ?_
  calc (Box.sign (blockCube β (Fin.cast hlen.symm i))).val
      = blockSign β (Fin.cast hlen.symm i) := ev_blockCube_val β (Fin.cast hlen.symm i)
    _ = blockSign (beadOf b) i := blockSign_congr hβval (Fin.val_cast _ _)
    _ = (Box.sign (beadFace b.map.hom i)).val :=
        (funext fun q => ev_beadFace_eq_blockSign b i q).symm

/-- Chains with the same partition have the same number of beads — the partitions' images. -/
private theorem length_le_of_beadOf {t t' : Ch (□n)}
    (h : ∀ q, (beadOf t q : ℕ) = (beadOf t' q : ℕ)) : t.dims.length ≤ t'.dims.length := by
  rcases Nat.eq_zero_or_pos t.dims.length with h0 | hpos
  · omega
  · obtain ⟨q, hq⟩ := beadOf_surjective t ⟨t.dims.length - 1, by omega⟩
    have := (beadOf t' q).isLt
    have h' := h q
    rw [hq] at h'
    simp only at h'
    omega

/-- **A chain of `□n` is pinned by its ordered partition** — both cube lists are its block list. -/
theorem eq_of_beadOf {t t' : Ch (□n)} (h : ∀ q, (beadOf t q : ℕ) = (beadOf t' q : ℕ)) : t = t' :=
  ChainCat.Obj.eq_of_toList
    ((ofBlockMap_cubes_eq t (beadOf t) (beadOf_surjective t) rfl fun _ => rfl).symm.trans
      (ofBlockMap_cubes_eq t' (beadOf t) (beadOf_surjective t)
        (Nat.le_antisymm (length_le_of_beadOf h) (length_le_of_beadOf fun q => (h q).symm)) h))

/-- A chain is the block chain of its own ordered partition. -/
theorem blockChain_beadOf (C : Ch (□n)) : blockChain (beadOf C) (beadOf_surjective C) = C :=
  eq_of_beadOf fun q => beadOf_blockChain _ _ q

/-! ## A coarsening is realised by a refinement

`blockReindex` sends each `a`-bead to the `b`-bead of its least coordinate (`Finset.min'`, no
`choice`), `blockIncl` restricts its sign vector to that bead's free coordinates, and `homOfBeads`
assembles the two into a chain map, `b.map` being injective on vertices
(`chain_vertex_injective`). -/

private theorem blockReindex_nonempty {a : Ch (□n)} (i : Fin a.dims.length) :
    (Finset.univ.filter (fun q => beadOf a q = i)).Nonempty :=
  (beadOf_surjective a i).elim fun q hq => ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩⟩

/-- **The block reindexing**: each `a`-bead to the `b`-bead of its least coordinate. -/
def blockReindex {a b : Ch (□n)} (i : Fin a.dims.length) : Fin b.dims.length :=
  beadOf b ((Finset.univ.filter (fun q => beadOf a q = i)).min' (blockReindex_nonempty i))

private theorem blockReindex_rep {a : Ch (□n)} (i : Fin a.dims.length) :
    beadOf a ((Finset.univ.filter (fun q => beadOf a q = i)).min' (blockReindex_nonempty i)) = i :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (blockReindex_nonempty i))).2

/-- `blockReindex` factors `beadOf b` through `beadOf a`. -/
theorem blockReindex_spec {a b : Ch (□n)} (h : BeadRefines a b) (q : Fin n) :
    beadOf b q = blockReindex (beadOf a q) :=
  (h.tie (blockReindex_rep (beadOf a q))).symm

/-- `blockReindex` is monotone. -/
theorem blockReindex_mono {a b : Ch (□n)} (h : BeadRefines a b) :
    Monotone (blockReindex (a := a) (b := b)) := fun i j hij => by
  rw [Fin.le_def]
  refine h _ _ ?_
  rw [blockReindex_rep, blockReindex_rep]; exact hij

open StdCube in
/-- The free coordinates of `a`-bead `i` inject into `b`-bead `blockReindex i`. -/
private theorem blockIncl_card {a b : Ch (□n)} (h : BeadRefines a b)
    (i : Fin a.dims.length) :
    (noneSet (fun k => (Box.sign (beadFace a.map.hom i)).val
      (faceEmb (beadFace b.map.hom (blockReindex i)) k))).card = (a.dims.get i : ℕ) := by
  have hprop : (noneSet (Box.sign (beadFace a.map.hom i)).val).card = (a.dims.get i : ℕ) :=
    (Box.sign (beadFace a.map.hom i)).prop
  have hcontain : ∀ q, beadOf a q = i →
      q ∈ Set.range (faceEmb (beadFace b.map.hom (blockReindex i))) := fun q hq => by
    rw [mem_range_iff_beadOf, blockReindex_spec h q, hq]
  refine (Finset.card_bij (fun k _ => faceEmb (beadFace b.map.hom (blockReindex i)) k)
    (fun k hk => ?_) (fun k _ k' _ he => (faceEmb _).injective he) (fun q hq => ?_)).trans hprop
  · rw [mem_noneSet] at hk ⊢; exact hk
  · rw [mem_noneSet] at hq
    obtain ⟨k, rfl⟩ := hcontain q ((ev_beadFace_eq_none_iff a i q).mp hq)
    exact ⟨k, mem_noneSet.mpr hq, rfl⟩

/-- **The block-face inclusion**: `a`-bead `i`'s sign vector restricted to `b`-bead
`blockReindex i`'s free coordinates. -/
def blockIncl {a b : Ch (□n)} (h : BeadRefines a b) (i : Fin a.dims.length) :
    ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (blockReindex i) : ℕ) :=
  Box.ofSign ⟨fun k => (Box.sign (beadFace a.map.hom i)).val
    (faceEmb (beadFace b.map.hom (blockReindex i)) k), blockIncl_card h i⟩

open StdCube in
/-- `a`-bead `i`'s face is `b`-bead `blockReindex i`'s pulled back along `blockIncl`. -/
theorem blockIncl_spec {a b : Ch (□n)} (h : BeadRefines a b) (i : Fin a.dims.length) :
    beadFace a.map.hom i
      = (□n).toPsh.map (blockIncl h i).op (beadFace b.map.hom (blockReindex i)) := by
  change beadFace a.map.hom i = Box.ofSign ⟨fun k => (Box.sign (beadFace a.map.hom i)).val
    (faceEmb (beadFace b.map.hom (blockReindex i)) k), blockIncl_card h i⟩
      ≫ beadFace b.map.hom (blockReindex i)
  apply Box.hom_ext
  rw [Box.sign_comp, Box.sign_ofSign]
  refine Subtype.ext (funext fun q => ?_)
  rw [subst_val]
  by_cases hqn : (Box.sign (beadFace b.map.hom (blockReindex i))).val q = none
  · rw [substFun_of_none _ _ hqn]
    exact congrArg (Box.sign (beadFace a.map.hom i)).val
      (nones_nonesIdx (Box.sign (beadFace b.map.hom (blockReindex i))) q _).symm
  · rw [substFun_of_some _ _ hqn, ev_beadFace_eq_blockSign, ev_beadFace_eq_blockSign]
    have hbne : beadOf b q ≠ blockReindex i :=
      fun he => hqn ((ev_beadFace_eq_none_iff b (blockReindex i) q).mpr he)
    have hane : beadOf a q ≠ i := fun he => hbne (by rw [blockReindex_spec h q, he])
    have hbne' : (blockReindex (b := b) (beadOf a q) : ℕ) ≠ (blockReindex (b := b) i : ℕ) := by
      rw [← blockReindex_spec h q]; exact fun he => hbne (Fin.val_injective he)
    simp only [blockSign, if_neg hane, if_neg hbne]
    rw [blockReindex_spec h q, Option.some.injEq, decide_eq_decide]
    exact ⟨fun hlt => lt_of_le_of_ne (blockReindex_mono h hlt.le) hbne',
      fun hlt => (blockReindex_mono h).reflect_lt hlt⟩

/-- **The reflected refinement**: a coarsening of partitions is a chain map `a ⟶ b`. -/
def reflectHom {a b : Ch (□n)} (h : BeadRefines a b) : a ⟶ b :=
  homOfBeads (chain_vertex_injective b) blockReindex (blockIncl h) (blockIncl_spec h)

end CubeChains
