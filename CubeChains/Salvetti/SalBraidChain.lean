import CubeChains.Salvetti.SalBraidPartition

/-!
# Salvetti/SalBraidChain — build a cube chain of `□ⁿ` from an ordered set partition

The object-level inverse of `SalBraidPartition`: that file extracts an ordered set
partition of `Fin n` (`blockOf`/`blockIndex`) from a cube chain of `□ⁿ`; here we build
the chain **from** the partition and prove the two round trips.

Input: a surjection `β : Fin n → Fin k` (an ordered set partition: block `i` is the fibre
`β⁻¹ i`, ordered by `i`).

- `blockStar β i : Cell n dᵢ` — the star vector of bead `i` (`dᵢ = |β⁻¹ i|`): the
  block-`i` coordinates are free (`none`); a coordinate in an **earlier** block (`β p < i`)
  has already flipped, so it is `some true`; a **later** block (`i < β p`) has not, so it is
  `some false`.
- `chainOf β hβ : RefineObj (cube n).init (cube n).final` — the cube chain, `bead i` classified
  by `blockStar β i`.
- Round trips: `blockOf_chainOf`/`blockIndex_chainOf` (partition ⟶ chain ⟶ partition) and
  `chainOf_blockIndex` (chain ⟶ partition ⟶ chain).

-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

variable {n k : ℕ}

/-! ## Part 1 — the star vector of a bead -/

/-- **The star vector of bead `i`.** Block-`i` coordinates are free (`none`); a coordinate in
an earlier block (`β p < i`) has already flipped (`some true`); a later block (`i < β p`) has
not yet flipped (`some false`). The free coordinates are exactly the fibre `β⁻¹ i`. -/
def blockStar (β : Fin n → Fin k) (i : Fin k) :
    Cell n (Finset.univ.filter (fun p => β p = i)).card :=
  ⟨fun p => if β p = i then none else some (decide (β p < i)), by
    have hns : noneSet
        (fun p => if β p = i then (none : Option Bool) else some (decide (β p < i)))
        = Finset.univ.filter (fun p => β p = i) := by
      ext p
      rw [mem_noneSet, Finset.mem_filter]
      by_cases h : β p = i <;> simp [h]
    rw [hns]⟩

@[simp] theorem blockStar_val (β : Fin n → Fin k) (i : Fin k) (p : Fin n) :
    (blockStar β i).val p = if β p = i then none else some (decide (β p < i)) := rfl

/-- The free (`none`) coordinates of bead `i` are exactly the fibre `β⁻¹ i`. -/
theorem noneSet_blockStar (β : Fin n → Fin k) (i : Fin k) :
    noneSet (blockStar β i).val = Finset.univ.filter (fun p => β p = i) := by
  ext p
  rw [mem_noneSet, blockStar_val, Finset.mem_filter]
  by_cases h : β p = i <;> simp [h]

theorem mem_noneSet_blockStar (β : Fin n → Fin k) (i : Fin k) (p : Fin n) :
    p ∈ noneSet (blockStar β i).val ↔ β p = i := by
  rw [noneSet_blockStar, Finset.mem_filter]; simp

/-! ## Part 2 — lift the beads to cells of `(cube n).toPsh` -/

/-- Bead `i` as a cell of `(cube n).toPsh`, classified by its star vector. -/
noncomputable def blockCell (β : Fin n → Fin k) (i : Fin k) :
    (□n).cells (Finset.univ.filter (fun p => β p = i)).card :=
  canonicalMap (blockStar β i)

theorem toStar_blockCell (β : Fin n → Fin k) (i : Fin k) :
    toStar (blockCell β i) = blockStar β i :=
  toStar_canonicalMap (blockStar β i)

/-- Positivity of the block size (the fibre of a surjection is nonempty). -/
theorem blockCard_pos (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    0 < (Finset.univ.filter (fun p => β p = i)).card := by
  obtain ⟨p, hp⟩ := hβ i
  exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩

/-- The `i`-th bead of the chain, as a dimension-tagged cell. -/
noncomputable def bead (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    Σ m : ℕ+, (□n).cells (m : ℕ) :=
  ⟨⟨(Finset.univ.filter (fun p => β p = i)).card, blockCard_pos β hβ i⟩, blockCell β i⟩

theorem toStar_bead (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    toStar (bead β hβ i).2 = blockStar β i :=
  toStar_blockCell β i

/-! ## Part 3 — the junction vertices -/

/-- The junction vertex before bead `m` (all coordinates flipped iff their block is `< m`). -/
def juncStar (β : Fin n → Fin k) (m : ℕ) : Cell n 0 :=
  ⟨fun p => some (decide ((β p : ℕ) < m)), by
    rw [Finset.card_eq_zero]
    ext p
    simp [mem_noneSet]⟩

@[simp] theorem juncStar_val (β : Fin n → Fin k) (m : ℕ) (p : Fin n) :
    (juncStar β m).val p = some (decide ((β p : ℕ) < m)) := rfl

/-- The junction vertex before bead `m` as a cell of `(cube n).toPsh`. -/
noncomputable def juncVertex (β : Fin n → Fin k) (m : ℕ) : (□n).cells 0 :=
  canonicalMap (juncStar β m)

theorem toStar_juncVertex (β : Fin n → Fin k) (m : ℕ) :
    toStar (juncVertex β m) = juncStar β m :=
  toStar_canonicalMap (juncStar β m)

/-- The `0`-th junction is the initial vertex (nothing has flipped yet). -/
theorem juncVertex_zero (β : Fin n → Fin k) : juncVertex β 0 = (□n).init :=
  congrArg canonicalMap
    (show juncStar β 0 = constVertex n false by
      apply Subtype.ext; funext p; simp [juncStar, constVertex])

/-- The junction before a bead `m` past every block is the final vertex (all flipped). -/
theorem juncVertex_top (β : Fin n → Fin k) {m : ℕ} (h : ∀ p, (β p : ℕ) < m) :
    juncVertex β m = (□n).final :=
  congrArg canonicalMap
    (show juncStar β m = constVertex n true by
      apply Subtype.ext; funext p; simp [juncStar, constVertex, h p])

/-! ## Part 4 — the vertices of a bead -/

/-- The source vertex of bead `i` is the junction before it. -/
theorem vertex₀_blockCell (β : Fin n → Fin k) (i : Fin k) :
    (□n).toPsh.vertex₀ (blockCell β i) = juncVertex β (i : ℕ) := by
  apply toStar_injective
  rw [toStar_vertex₀, toStar_juncVertex, toStar_blockCell]
  apply Subtype.ext
  funext p
  rw [app_constVertex_val]
  by_cases hp : p ∈ noneSet (blockStar β i).val
  · rw [if_pos hp]
    have hbi : β p = i := (mem_noneSet_blockStar β i p).mp hp
    have : (β p : ℕ) = (i : ℕ) := by rw [hbi]
    change some false = (juncStar β (i : ℕ)).val p
    rw [juncStar_val, this]; simp
  · rw [if_neg hp]
    have hbi : β p ≠ i := fun h => hp ((mem_noneSet_blockStar β i p).mpr h)
    change (blockStar β i).val p = (juncStar β (i : ℕ)).val p
    rw [blockStar_val, if_neg hbi, juncStar_val]
    exact congrArg some (decide_eq_decide.mpr Fin.lt_def)

/-- The target vertex of bead `i` is the junction after it. -/
theorem vertex₁_blockCell (β : Fin n → Fin k) (i : Fin k) :
    (□n).toPsh.vertex₁ (blockCell β i) = juncVertex β ((i : ℕ) + 1) := by
  apply toStar_injective
  rw [toStar_vertex₁, toStar_juncVertex, toStar_blockCell]
  apply Subtype.ext
  funext p
  rw [app_constVertex_val]
  by_cases hp : p ∈ noneSet (blockStar β i).val
  · rw [if_pos hp]
    have hbi : β p = i := (mem_noneSet_blockStar β i p).mp hp
    have : (β p : ℕ) = (i : ℕ) := by rw [hbi]
    change some true = (juncStar β ((i : ℕ) + 1)).val p
    rw [juncStar_val, this]; simp
  · rw [if_neg hp]
    have hbi : β p ≠ i := fun h => hp ((mem_noneSet_blockStar β i p).mpr h)
    have hne : (β p : ℕ) ≠ (i : ℕ) := fun h => hbi (Fin.ext h)
    change (blockStar β i).val p = (juncStar β ((i : ℕ) + 1)).val p
    rw [blockStar_val, if_neg hbi, juncStar_val]
    exact congrArg some (decide_eq_decide.mpr (by rw [Fin.lt_def]; omega))

theorem vertex₀_bead (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    (□n).toPsh.vertex₀ (bead β hβ i).2 = juncVertex β (i : ℕ) :=
  vertex₀_blockCell β i

theorem vertex₁_bead (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    (□n).toPsh.vertex₁ (bead β hβ i).2 = juncVertex β ((i : ℕ) + 1) :=
  vertex₁_blockCell β i

/-! ## Part 5 — the cube chain -/

theorem chainOf_isChain (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    IsCubeChain (□n).init (List.ofFn (bead β hβ)) (□n).final := by
  have key := isCubeChain_aux (K := □n) (List.ofFn (bead β hβ))
    (fun j => juncVertex β (j : ℕ))
    (fun i => by rw [List.get_ofFn]; exact vertex₀_bead β hβ _)
    (fun i => by rw [List.get_ofFn]; exact vertex₁_bead β hβ _)
  rw [← juncVertex_zero β,
    ← juncVertex_top β (m := (List.ofFn (bead β hβ)).length)
      (fun p => by rw [List.length_ofFn]; exact (β p).isLt)]
  exact key

/-- **The cube chain of `β`.** Bead `i` is classified by `blockStar β i`; the chain runs from
`(cube n).init` to `(cube n).final`. For `k = 0` (forcing `n = 0`) this is the empty chain. -/
noncomputable def chainOf (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    RefineObj (□n).init (□n).final where
  cubes := List.ofFn (bead β hβ)
  isChain := chainOf_isChain β hβ

@[simp] theorem chainOf_cubes (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    (chainOf β hβ).cubes = List.ofFn (bead β hβ) := rfl

theorem chainOf_cubes_length (β : Fin n → Fin k) (hβ : Function.Surjective β) :
    (chainOf β hβ).cubes.length = k := List.length_ofFn

theorem chainOf_cubes_get (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    (chainOf β hβ).cubes.get (Fin.cast (chainOf_cubes_length β hβ).symm i) = bead β hβ i :=
  List.get_ofFn (bead β hβ) (Fin.cast (chainOf_cubes_length β hβ).symm i)

/-! ## Part 6 — round trip: partition ⟶ chain ⟶ partition -/

/-- **`blockOf` of `chainOf` recovers the fibre.** The block of bead `i` in `chainOf β hβ` is
exactly the fibre `β⁻¹ i`. -/
theorem blockOf_chainOf (β : Fin n → Fin k) (hβ : Function.Surjective β) (i : Fin k) :
    blockOf (chainOf β hβ) (Fin.cast (chainOf_cubes_length β hβ).symm i)
      = Finset.univ.filter (fun p => β p = i) := by
  change noneSet (toStar
    ((chainOf β hβ).cubes.get (Fin.cast (chainOf_cubes_length β hβ).symm i)).2).val = _
  rw [chainOf_cubes_get, toStar_bead, noneSet_blockStar]

/-- **`blockIndex` of `chainOf` recovers `β`.** Stated at `ℕ`-values to avoid `Fin`-cast pain. -/
theorem blockIndex_chainOf (β : Fin n → Fin k) (hβ : Function.Surjective β) (p : Fin n) :
    ((blockIndex (chainOf β hβ) p : ℕ)) = (β p : ℕ) := by
  have hmem : p ∈ blockOf (chainOf β hβ)
      (Fin.cast (chainOf_cubes_length β hβ).symm (β p)) := by
    rw [blockOf_chainOf]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, rfl⟩
  rw [blockIndex_unique (chainOf β hβ) hmem]
  simp

/-! ## Part 7 — round trip: chain ⟶ partition ⟶ chain -/

/-- Every bead's block is nonempty, so `blockIndex x` is surjective. -/
theorem blockIndex_surjective (x : RefineObj (□n).init (□n).final) :
    Function.Surjective (blockIndex x) := by
  intro j
  have hcard : (blockOf x j).card = ((x.cubes.get j).1 : ℕ) := (toStar (x.cubes.get j).2).prop
  have hpos : 0 < (blockOf x j).card := by rw [hcard]; exact (x.cubes.get j).1.pos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, blockIndex_unique x hp⟩

/-- **The bead's sign vector is forced by the partition.** At bead `j`, a coordinate `p` in
block `j` is free; otherwise its value records whether `p`'s block precedes `j`. -/
theorem toStar_get_val (x : RefineObj (□n).init (□n).final)
    (j : Fin x.cubes.length) (p : Fin n) :
    (toStar (x.cubes.get j).2).val p
      = if blockIndex x p = j then none else some (decide (blockIndex x p < j)) := by
  by_cases hj : blockIndex x p = j
  · rw [if_pos hj]
    have hmem : p ∈ blockOf x j := (mem_block_iff x).mpr hj
    exact mem_noneSet.mp hmem
  · rw [if_neg hj]
    have hnotj : p ∉ blockOf x j := fun h => hj ((mem_block_iff x).mp h)
    -- the value at bead `j` equals the value at junction `j.castSucc`
    have h1 : (toStar (vtxCanon x.cubes (□n).final j.castSucc)).val p
        = (toStar (x.cubes.get j).2).val p := by
      rw [toStar_junc_castSucc, if_neg hnotj]
    -- that value is not `none` (p is fixed at bead j)
    have hVne : (toStar (x.cubes.get j).2).val p ≠ none := fun h =>
      hnotj (mem_noneSet.mpr h)
    obtain ⟨c, hc⟩ : ∃ c, (toStar (x.cubes.get j).2).val p = some c := by
      cases h : (toStar (x.cubes.get j).2).val p with
      | none => exact absurd h hVne
      | some c => exact ⟨c, rfl⟩
    -- read off the flip-boolean at junction j.castSucc
    have hb : Fval x p j.castSucc = c := by
      change decide ((toStar (vtxCanon x.cubes (□n).final j.castSucc)).val p
        = some true) = c
      rw [h1, hc]
      cases c <;> rfl
    have hval_eq : (toStar (x.cubes.get j).2).val p = some (Fval x p j.castSucc) := by
      rw [hc, hb]
    -- the flip-boolean is monotone, pinned by p's own block j₀ = blockIndex x p
    have hj0 : p ∈ blockOf x (blockIndex x p) := blockIndex_mem x p
    have hf0c : Fval x p (blockIndex x p).castSucc = false := by
      change decide ((toStar (vtxCanon x.cubes (□n).final
        (blockIndex x p).castSucc)).val p = some true) = false
      rw [toStar_junc_castSucc, if_pos hj0]; rfl
    have hf0s : Fval x p (blockIndex x p).succ = true := by
      change decide ((toStar (vtxCanon x.cubes (□n).final
        (blockIndex x p).succ)).val p = some true) = true
      rw [toStar_junc_succ, if_pos hj0]; rfl
    have hFval_j : Fval x p j.castSucc = decide (blockIndex x p < j) := by
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · -- blockIndex x p < j : already flipped by junction j
        have hle : (blockIndex x p).succ ≤ j.castSucc := by
          have : (blockIndex x p : ℕ) < (j : ℕ) := hlt
          rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
        have hmono := Fval_mono x p hle
        rw [hf0s] at hmono
        have hfj : Fval x p j.castSucc = true := le_antisymm (Bool.le_true _) hmono
        rw [hfj]; symm; simp only [decide_eq_true_eq]; exact hlt
      · -- j < blockIndex x p : not yet flipped by junction j
        have hle : j.castSucc ≤ (blockIndex x p).castSucc := by
          have : (j : ℕ) < (blockIndex x p : ℕ) := hgt
          rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc]; omega
        have hmono := Fval_mono x p hle
        rw [hf0c] at hmono
        have hfj : Fval x p j.castSucc = false := le_antisymm hmono (Bool.false_le _)
        rw [hfj]; symm; simp only [decide_eq_false_iff_not]; exact lt_asymm hgt
    rw [hval_eq, hFval_j]

/-- Sigma-equality of two cube beads with equal dimension and equal sign vectors. -/
theorem bead_ext {d₁ : ℕ+} {c₁ : (□n).cells (d₁ : ℕ)}
    {d₂ : ℕ+} {c₂ : (□n).cells (d₂ : ℕ)}
    (hd : (d₁ : ℕ) = (d₂ : ℕ)) (hv : (toStar c₁).val = (toStar c₂).val) :
    (⟨d₁, c₁⟩ : Σ m : ℕ+, (□n).cells (m : ℕ)) = ⟨d₂, c₂⟩ := by
  obtain rfl : d₁ = d₂ := PNat.coe_injective hd
  have : c₁ = c₂ := toStar_injective (Subtype.ext hv)
  rw [this]

/-- The fibre of `blockIndex x` at `j` is exactly block `j`. -/
theorem filter_blockIndex_eq (x : RefineObj (□n).init (□n).final)
    (j : Fin x.cubes.length) :
    Finset.univ.filter (fun p => blockIndex x p = j) = blockOf x j := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_block_iff]

/-- **`chainOf` of `blockIndex` recovers the chain.** The beads are forced: bead `j`'s block is
`blockOf x j` and its fixed coordinates are pinned by the junction values. -/
theorem chainOf_blockIndex (x : RefineObj (□n).init (□n).final) :
    chainOf (blockIndex x) (blockIndex_surjective x) = x := by
  apply RefineObj.ext'
  change List.ofFn (bead (blockIndex x) (blockIndex_surjective x)) = x.cubes
  have key : ∀ j : Fin x.cubes.length,
      bead (blockIndex x) (blockIndex_surjective x) j = x.cubes.get j := by
    intro j
    have hcard : (Finset.univ.filter (fun p => blockIndex x p = j)).card
        = ((x.cubes.get j).1 : ℕ) := by
      rw [filter_blockIndex_eq]
      exact (toStar (x.cubes.get j).2).prop
    have hv : (toStar (blockCell (blockIndex x) j)).val = (toStar (x.cubes.get j).2).val := by
      rw [toStar_blockCell]
      funext p
      rw [toStar_get_val]
      rfl
    exact bead_ext (d₁ := ⟨(Finset.univ.filter (fun p => blockIndex x p = j)).card,
        blockCard_pos (blockIndex x) (blockIndex_surjective x) j⟩)
      (c₁ := blockCell (blockIndex x) j)
      (d₂ := (x.cubes.get j).1) (c₂ := (x.cubes.get j).2) hcard hv
  rw [funext key]
  exact List.ofFn_get x.cubes

end CubeChains
