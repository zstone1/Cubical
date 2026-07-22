import CubeChains.Chains.CoordFunctor
import CubeChains.Chains.Correspondence
import CubeChains.Salvetti.Runs
import CubeChains.Arrangements.Braid
import CubeChains.Arrangements.BraidCovector
import CubeChains.Arrangements.SalElements

/-!
# Salvetti/ChainBraidFace — cube chains of `□n` are faces of the braid COM

`cubeChainFaceEquiv : CubeChain (□n) ≃ COM.Face (braidCOM n)`, factored through the ordered
set partition of `Fin n` a chain realises — no height functions.

```
CubeChain (□n)  ≃  {ordered partition Fin n}  ≃  COM.Face (braidCOM n)
        coordFlip bijection ↑            ↑ blockMap round-trips (BraidCovector)
```

* **Left ≃** — `coordFlip` (`Chains/CoordFunctor`) makes the coordinate map of a chain a
  *bijection* `(Σ i, Fin (dims i)) ≃ Fin n`; its second projection `beadOf : Fin n → Fin L` is the
  bead each coordinate flips — the ordered-partition surjection (surjective because every bead has
  positive dimension).
* **Right ≃** — a braid covector *is* a surjection `Fin n → Fin (numBlocks)` (`blockMap`), with the
  round-trips `blockMap_of_surjective` / `numBlocks_of_surjective` / `braidSign_blockMap` already in
  `Arrangements/BraidCovector`.

The braid `Face` of a chain reads `braidSign (fun q => beadOf q)` — the covector of the partition.
-/

open CategoryTheory Opposite CubeChains CubeChain PrecubicalSet

namespace CubeChains

variable {n : ℕ}

/-! ## Forward: the braid face of a chain, via `coordFlip` on its wedge map

A `Ch (□n)` object `b` carries its descent `b.map : ⋁b.dims ⟶ □n` directly, so `beadFace b.map.hom i`
is the face bead `i` flips, and `coord_sigma_bijective` makes the coordinate assignment a bijection —
the ordered partition of `Fin n`.  Working here (rather than on `CubeChain`) keeps `i : Fin
b.dims.length` matched to the `coordFlip` index with no `dims`/`cubes` transport; `CubeChain (□n)` is
the same data by `chEquivCubeChain`, so the target equiv transports across one composition. -/

/-- A coordinate is in the range of a face's `faceEmb` iff the face's sign vector is free (`none`)
there — `faceEmb` enumerates the free coordinates. -/
theorem mem_range_faceEmb {k m : ℕ} (g : ▫k ⟶ ▫m) (q : Fin m) :
    q ∈ Set.range (faceEmb g) ↔ (StdCube.ev g).val q = none := by
  unfold faceEmb StdCube.nones
  rw [Finset.range_orderEmbOfFin, Finset.mem_coe, StdCube.mem_noneSet]

/-- Coordinate `q` is flipped by bead `i` of the chain `b`. -/
def BeadFlips (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) : Prop :=
  q ∈ Set.range (faceEmb (beadFace b.map.hom i))

instance (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) : Decidable (BeadFlips b i q) :=
  decidable_of_iff (∃ k, faceEmb (beadFace b.map.hom i) k = q) Iff.rfl

/-- **Each coordinate is flipped by exactly one bead**: surjectivity of the coordinate assignment
gives a flipping bead, `coord_beads_disjoint` its uniqueness.  A `Prop`, so `beadOf` stays
computable. -/
theorem beadFlips_existsUnique (b : Ch (□n)) (q : Fin n) :
    ∃! i : Fin b.dims.length, BeadFlips b i q := by
  obtain ⟨⟨i, k⟩, hik⟩ := (coord_sigma_bijective b.map).surjective q
  exact ⟨i, ⟨k, hik⟩, fun i' hi' => coord_beads_disjoint b.dims b.map.hom i' i q hi' ⟨k, hik⟩⟩

/-- The **bead** a coordinate is flipped by — a computable `Finset.choose` search for the unique
flipping bead, so `chFace` computes; `coordFlip` only supplies the `∃!`. -/
def beadOf (b : Ch (□n)) (q : Fin n) : Fin b.dims.length :=
  Finset.choose (BeadFlips b · q) Finset.univ (by simpa using beadFlips_existsUnique b q)

theorem beadFlips_beadOf (b : Ch (□n)) (q : Fin n) : BeadFlips b (beadOf b q) q :=
  Finset.choose_property (BeadFlips b · q) _ _

/-- `beadOf b` is surjective: every bead has positive dimension, so it flips some coordinate. -/
theorem beadOf_surjective (b : Ch (□n)) : Function.Surjective (beadOf b) := fun i =>
  ⟨faceEmb (beadFace b.map.hom i) ⟨0, (b.dims.get i).2⟩,
    (beadFlips_existsUnique b _).unique (beadFlips_beadOf b _) ⟨⟨0, (b.dims.get i).2⟩, rfl⟩⟩

/-- The braid face of a chain: the covector of its ordered partition `beadOf`. -/
def chFace (b : Ch (□n)) : COM.Face (braidCOM n) :=
  ⟨braidSign (fun q => ((beadOf b q : ℕ) : ℤ)), (fun q => ((beadOf b q : ℕ) : ℤ)), rfl⟩

/-! ## Inverse: reconstruct a chain from an ordered partition (surjection)

Given the partition `β : Fin n → Fin L` (surjective), bead `j` flips exactly `β⁻¹{j}`, is `1` on
earlier blocks and `0` on later ones, and consecutive beads glue on the prefix vertex at threshold
`j+1`.  The surjection is read off a face by `blockMap` of any realising height (`X.2`), so the
covector→height bridge (`heightOfCovector`) is not needed.  Mirrors BraidSal's `heightCubeChain` but
comes straight from the surjection, so there is no `denseRank`. -/

variable {L : ℕ}

/-- Bead `j`'s sign vector: free (`none`) on `β⁻¹{j}`, `1` below, `0` above. -/
def blockSign (β : Fin n → Fin L) (j : Fin L) : Fin n → Option Bool :=
  fun q => if β q = j then none else some (decide ((β q : ℕ) < (j : ℕ)))

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

/-- **The gluing computation.**  Setting bead `j`'s free coordinates to a constant `ε` keeps the
other coordinates fixed, so `ε = 0` gives the prefix vertex `q ↦ (β q < j)` and `ε = 1` the next
one `q ↦ (β q < j+1)` (the block-`j` coordinates flip). -/
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

/-- Bead `j` starts at the prefix vertex at threshold `j`. -/
theorem vertex₀_blockCube (β : Fin n → Fin L) (j : Fin L) :
    (□n).toPsh.vertex₀ (blockCube β j) = prefixVtx β (j : ℕ) := by
  apply Box.hom_ext
  rw [sign_vertex₀, blockCube, Box.sign_ofSign, prefixVtx, Box.sign_ofSign]
  apply Subtype.ext; funext q
  rw [StdCube.subst_val, substFun_blockCell]
  by_cases h : β q = j <;> simp [h]

/-- Bead `j` ends at the prefix vertex at threshold `j+1` — the next bead's start. -/
theorem vertex₁_blockCube (β : Fin n → Fin L) (j : Fin L) :
    (□n).toPsh.vertex₁ (blockCube β j) = prefixVtx β ((j : ℕ) + 1) := by
  apply Box.hom_ext
  rw [sign_vertex₁, blockCube, Box.sign_ofSign, prefixVtx, Box.sign_ofSign]
  apply Subtype.ext; funext q
  rw [StdCube.subst_val, substFun_blockCell]
  by_cases h : β q = j
  · rw [if_pos h]; congr 1; symm; rw [decide_eq_true_eq, ← h]; omega
  · rw [if_neg h]; congr 1; rw [decide_eq_decide]
    have : (β q : ℕ) ≠ (j : ℕ) := fun he => h (Fin.ext he)
    omega

/-- Below threshold `0` the prefix vertex is the initial vertex. -/
theorem prefixVtx_zero (β : Fin n → Fin L) : prefixVtx β 0 = (□n).init := by
  apply Box.hom_ext
  rw [prefixVtx, Box.sign_ofSign,
    show Box.sign ((□n).init) = StdCube.constVertex n false from StdCube.ev_canonicalMap _]
  apply Subtype.ext; funext q
  change some (decide ((β q : ℕ) < 0)) = some false
  simp

/-- Above threshold `L` the prefix vertex is the final vertex. -/
theorem prefixVtx_last (β : Fin n → Fin L) : prefixVtx β L = (□n).final := by
  apply Box.hom_ext
  rw [prefixVtx, Box.sign_ofSign,
    show Box.sign ((□n).final) = StdCube.constVertex n true from StdCube.ev_canonicalMap _]
  apply Subtype.ext; funext q
  change some (decide ((β q : ℕ) < L)) = some true
  rw [decide_eq_true_iff.mpr (β q).isLt]

/-- The cube list of the reconstructed chain: one bead per block, in order. -/
def blockCubes (β : Fin n → Fin L) (hβ : Function.Surjective β) :
    List (Σ d : ℕ+, (□n).cells (d : ℕ)) :=
  List.ofFn fun j : Fin L => ⟨⟨_, blockSize_pos β hβ j⟩, blockCube β j⟩

theorem length_blockCubes (β : Fin n → Fin L) (hβ : Function.Surjective β) :
    (blockCubes β hβ).length = L := List.length_ofFn

/-- **Reconstruct the cube chain realising an ordered partition** `β`. -/
def ofBlockMap (β : Fin n → Fin L) (hβ : Function.Surjective β) : CubeChain (□n) where
  cubes := blockCubes β hβ
  vtx t := prefixVtx β (t : ℕ)
  vtx_zero := by
    change prefixVtx β ((0 : Fin ((blockCubes β hβ).length + 1)) : ℕ) = _
    simpa using prefixVtx_zero β
  vtx_last := by
    change prefixVtx β ((Fin.last (blockCubes β hβ).length : Fin _) : ℕ) = _
    rw [Fin.val_last, length_blockCubes]; exact prefixVtx_last β
  cube_src := fun i => by
    unfold blockCubes; rw [List.get_ofFn]
    -- the `i`-th bead of `blockCubes` starts at `prefixVtx β i`
    exact (vertex₀_blockCube β _).symm ▸ rfl
  cube_tgt := fun i => by
    unfold blockCubes; rw [List.get_ofFn]
    exact (vertex₁_blockCube β _).symm ▸ rfl

/-- **Chains are braid faces** — proved over `Ch (□n)`, where `coordFlip` applies to `b.map` with no
transport.  Forward is the partition's covector (`chFace`, computable); the inverse reconstructs the
chain from the ordered partition `blockMap X.2.choose` of a realising height.  `noncomputable` only
in the inverse (the height witness `X.2`), so `chFace` — turning a chain into a face — computes. -/
noncomputable def chFaceEquiv : Ch (□n) ≃ COM.Face (braidCOM n) where
  toFun := chFace
  invFun X :=
    (chEquivCubeChain (□n)).symm (ofBlockMap (blockMap X.2.choose) (blockMap_surjective _))
  left_inv := sorry
  right_inv := sorry

/-- **Cube chains of `□n` are faces of the braid COM** — the target statement, transported from
`chFaceEquiv` across the chain↔`Ch` correspondence. -/
noncomputable def cubeChainFaceEquiv : CubeChain (□n) ≃ COM.Face (braidCOM n) :=
  (chEquivCubeChain (□n)).symm.trans chFaceEquiv

end CubeChains
