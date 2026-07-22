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

A `Ch (□n)` `b` carries its descent `b.map : ⋁b.dims ⟶ □n`, so `beadFace b.map.hom i` is the face
bead `i` flips, and `coord_sigma_bijective` makes the coordinate map a bijection — the ordered
partition of `Fin n`.  Working here (not on `CubeChain`) keeps `i : Fin b.dims.length`
matched to the `coordFlip` index with no `dims`/`cubes` transport; `CubeChain (□n)` is the same data
by `chEquivCubeChain`, so the target equiv transports across one composition. -/

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

/-! ## Monotonicity of `chFace` under refinement

A morphism `f : a ⟶ b` in `Ch` refines `a` over `b` (`f.w : f.φ ≫ b.map = a.map`), so `a`'s
partition is finer than `b`'s and `chFace b ⊑ chFace a`.  Each of `a`'s beads factors through one of
`b`'s (`blockIdx fᵂ`), and `blockIdx` is monotone. -/

/-- **`a`'s bead face factors through `b`'s.**  Bead `i` of `a` lands in block `blockIdx fᵂ i` of
`b` via the face `blockFace fᵂ i`. -/
theorem beadFace_comp {a b : Ch (□n)} (f : a ⟶ b) (i : Fin a.dims.length) :
    beadFace a.map.hom i = blockFace fᵂ i ≫ beadFace b.map.hom (blockIdx fᵂ i) := by
  have key : ιᵂ a.dims i ≫ a.map.hom
      = yoneda.map (blockFace fᵂ i) ≫ (ιᵂ b.dims (blockIdx fᵂ i) ≫ b.map.hom) := by
    rw [show a.map.hom = fᵂ ≫ b.map.hom from by rw [← f.w, BPSet.comp_hom], ← Category.assoc,
      blockFace_spec fᵂ i]
    exact Category.assoc _ _ _
  exact (congrArg yonedaEquiv key).trans (yonedaEquiv_naturality _ _).symm

/-- **`f` sends `a`'s bead of `q` to `b`'s bead of `q`.**  The coordinate `q` flips in `a`'s bead
`beadOf a q`, whose face factors through `b`'s block `blockIdx fᵂ (beadOf a q)` — so that block is
the unique one `q` flips in `b`. -/
theorem beadOf_blockIdx {a b : Ch (□n)} (f : a ⟶ b) (q : Fin n) :
    beadOf b q = blockIdx fᵂ (beadOf a q) := by
  have hrange : Set.range (faceEmb (beadFace a.map.hom (beadOf a q)))
      ⊆ Set.range (faceEmb (beadFace b.map.hom (blockIdx fᵂ (beadOf a q)))) := by
    rw [beadFace_comp f]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, (faceEmb_comp _ _ x).symm⟩
  exact (beadFlips_existsUnique b q).unique (beadFlips_beadOf b q)
    (hrange (beadFlips_beadOf a q))

/-- **`chFace` is monotone under refinement:** `chFace b ⊑ chFace a` for a chain map `f : a ⟶ b`. -/
theorem chFace_faceLE {a b : Ch (□n)} (f : a ⟶ b) : (chFace b).1 ⊑ (chFace a).1 := by
  have hmono : Monotone (blockIdx fᵂ) := serialWedge_blockIdx_monotone fᵂ f.φ.app_init
  intro e
  simp only [chFace, braidSign_apply, beadOf_blockIdx f e.1.1, beadOf_blockIdx f e.1.2]
  set iA := beadOf a e.1.1
  set jA := beadOf a e.1.2
  rcases lt_trichotomy (blockIdx fᵂ iA) (blockIdx fᵂ jA) with h | h | h
  · have hij : (iA : ℕ) < (jA : ℕ) := hmono.reflect_lt h
    have hb : (blockIdx fᵂ iA : ℕ) < (blockIdx fᵂ jA : ℕ) := h
    exact Or.inr (by rw [sign_neg (by omega), sign_neg (by omega)])
  · exact Or.inl (by rw [h, sub_self]; exact sign_zero)
  · have hij : (jA : ℕ) < (iA : ℕ) := hmono.reflect_lt h
    have hb : (blockIdx fᵂ jA : ℕ) < (blockIdx fᵂ iA : ℕ) := h
    exact Or.inr (by rw [sign_pos (by omega), sign_pos (by omega)])

/-! ## Inverse: reconstruct a chain from an ordered partition (surjection)

Given the partition `β : Fin n → Fin L` (surjective), bead `j` flips exactly `β⁻¹{j}`, is `1` on
earlier blocks and `0` on later ones, and consecutive beads glue on the prefix vertex at threshold
`j+1`.  The surjection is read off a face by `blockMap` of the canonical height `covectorHeight X.1`
(`Arrangements/BraidCovector`), computed from the covector directly — no choice, no `denseRank`. -/

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

/-! ## The master lemma: a chain's bead faces are `blockSign` of its partition

The bead endpoints and spine reachability (`beadBot`, `beadTop`, `beadBot_reaches_beadBot`,
`beadTop_reaches_beadBot`) live in `Chains/CoordFunctor`. -/

/-- Reading the `⊥`-vertex of a cube face `g` at `q` is the fixed value of `g` there. -/
theorem cubeVtx_bot_getD {k m : ℕ} (g : ▫k ⟶ ▫m) (q : Fin m) :
    cubeVtx g (fun _ => false) q = ((StdCube.ev g).val q).getD false := by
  have h := cubeVtxOfCell_bot (toStar (g : (□m).cells k)) q
  rw [cubeVtx_eq]
  exact h

/-- **The master lemma.**  Bead `i`'s face reads, at coordinate `q`, the sign vector of the ordered
partition `beadOf b`: `none` iff `q` is in bead `i`, else `1`/`0` by whether `q`'s bead precedes
`i`.  The `1`/`0` is the `readVec` of bead `i`'s bottom vertex, pinned by spine monotonicity. -/
theorem ev_beadFace_eq_blockSign (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) :
    (StdCube.ev (beadFace b.map.hom i)).val q = blockSign (beadOf b) i q := by
  simp only [blockSign]
  by_cases h : beadOf b q = i
  · rw [if_pos h]
    exact (mem_range_faceEmb (beadFace b.map.hom i) q).mp (h ▸ beadFlips_beadOf b q)
  · rw [if_neg h]
    have hne : (StdCube.ev (beadFace b.map.hom i)).val q ≠ none := fun hnone =>
      h ((beadFlips_existsUnique b q).unique (beadFlips_beadOf b q)
        (show BeadFlips b i q from (mem_range_faceEmb (beadFace b.map.hom i) q).mpr hnone))
    obtain ⟨ε, hε⟩ := Option.ne_none_iff_exists'.mp hne
    rw [hε]
    have hqflip₀ : q ∈ Set.range (faceEmb (beadFace b.map.hom (beadOf b q))) :=
      beadFlips_beadOf b q
    have hεval : readVec (b.map.hom⟪0⟫ (beadBot b.dims i)) q = ε := by
      rw [show readVec (b.map.hom⟪0⟫ (beadBot b.dims i))
            = cubeVtx (beadFace b.map.hom i) (readVec ((□(b.dims.get i : ℕ)).init))
          from readVec_bead b.map.hom i ((□(b.dims.get i : ℕ)).init)]
      rw [show readVec ((□(b.dims.get i : ℕ)).init) = (fun _ => false)
          from funext fun r => readVec_init _ r]
      rw [cubeVtx_bot_getD, hε]
      rfl
    congr 1
    rcases lt_trichotomy (beadOf b q : ℕ) (i : ℕ) with hlt | heq | hgt
    · have htop : readVec (b.map.hom⟪0⟫ (beadTop b.dims (beadOf b q))) q = true :=
        readVec_beadTop_flip b.map.hom (beadOf b q) hqflip₀
      have hmono := readVec_mono b.map.hom
        (beadTop_reaches_beadBot b.dims (beadOf b q) i hlt) q
      rw [htop] at hmono
      rw [hεval] at hmono
      rw [le_antisymm (Bool.le_true ε) hmono]
      exact (decide_eq_true hlt).symm
    · exact absurd (Fin.val_injective heq) h
    · have hbot : readVec (b.map.hom⟪0⟫ (beadBot b.dims (beadOf b q))) q = false :=
        readVec_beadBot_flip b.map.hom (beadOf b q) hqflip₀
      have hmono := readVec_mono b.map.hom
        (beadBot_reaches_beadBot b.dims i (beadOf b q) (le_of_lt hgt)) q
      rw [hbot] at hmono
      rw [hεval] at hmono
      rw [le_antisymm hmono (Bool.false_le ε)]
      exact (decide_eq_false (by omega)).symm

/-! ## The round-trip bridges

`blockCube`'s sign is `blockSign`; a `Σ`-entry of the cube list is pinned by its sign vector. -/

/-- Bead `j`'s cube face reads its `blockSign`. -/
theorem ev_blockCube_val (β : Fin n → Fin L) (j : Fin L) :
    (StdCube.ev (blockCube β j)).val = blockSign β j :=
  congrArg Subtype.val (Box.sign_ofSign (blockCell β j))

/-- `blockSign` depends only on the block values: equal block indices and thresholds (by value)
give equal sign vectors. -/
theorem blockSign_congr {L' : ℕ} {β : Fin n → Fin L} {β' : Fin n → Fin L'} {j : Fin L}
    {j' : Fin L'} (hβ : ∀ q, (β q : ℕ) = (β' q : ℕ)) (hj : (j : ℕ) = (j' : ℕ)) :
    blockSign β j = blockSign β' j' := by
  funext q; simp only [blockSign, ← Fin.val_eq_val, hβ q, hj]

/-- Two cube-list entries agree once their sign vectors do (the dimension is the free-count). -/
theorem cube_sigma_ext {d₁ d₂ : ℕ+} (c₁ : (□n).cells (d₁ : ℕ)) (c₂ : (□n).cells (d₂ : ℕ))
    (h : (StdCube.ev c₁).val = (StdCube.ev c₂).val) :
    (⟨d₁, c₁⟩ : Σ d : ℕ+, (□n).cells (d : ℕ)) = ⟨d₂, c₂⟩ := by
  have e1 : (StdCube.noneSet (StdCube.ev c₁).val).card = (d₁ : ℕ) := (StdCube.ev c₁).prop
  have e2 : (StdCube.noneSet (StdCube.ev c₂).val).card = (d₂ : ℕ) := (StdCube.ev c₂).prop
  have hd : (d₁ : ℕ) = (d₂ : ℕ) := by rw [← e1, ← e2, h]
  obtain rfl : d₁ = d₂ := PNat.coe_injective hd
  rw [Box.hom_ext (Subtype.ext h)]

/-- **Right round-trip on beads.**  The chain reconstructed from a surjection `β` flips, at each
coordinate, the block `β` names — its `beadOf` recovers `β` (up to the length cast). -/
theorem beadOf_ofBlockMap (β : Fin n → Fin L) (hβ : Function.Surjective β) (q : Fin n) :
    (beadOf ((chEquivCubeChain (□n)).symm (ofBlockMap β hβ)) q : ℕ) = (β q : ℕ) := by
  set b := (chEquivCubeChain (□n)).symm (ofBlockMap β hβ) with hb
  have hcubes : wedgeToCubes ⟨b.dims, b.map.hom⟩ = blockCubes β hβ := by
    calc wedgeToCubes ⟨b.dims, b.map.hom⟩
        = (chEquivCubeChain (□n) b).cubes := (chEquivCubeChain_cubes (□n) b).symm
      _ = (ofBlockMap β hβ).cubes := by rw [hb, Equiv.apply_symm_apply]
      _ = blockCubes β hβ := rfl
  rw [wedgeToCubes_eq_ofFn] at hcubes
  simp only [blockCubes] at hcubes
  obtain ⟨hlen, hFG⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp (List.ofFn_inj'.mp hcubes)
  have hentry : ∀ i : Fin b.dims.length,
      (StdCube.ev (beadFace b.map.hom i)).val = blockSign β (Fin.cast hlen i) := fun i => by
    have hi := congrArg
      (fun x : (Σ d : ℕ+, (□n).cells (d : ℕ)) => (StdCube.ev x.2).val) (congrFun hFG i)
    simp only [Function.comp_apply] at hi
    change (StdCube.ev (yonedaEquiv (ιᵂ b.dims i ≫ b.map.hom))).val = blockSign β (Fin.cast hlen i)
    rw [hi]
    exact ev_blockCube_val β (Fin.cast hlen i)
  have hflip : blockSign β (Fin.cast hlen (beadOf b q)) q = none := by
    rw [← hentry (beadOf b q)]
    exact (mem_range_faceEmb (beadFace b.map.hom (beadOf b q)) q).mp (beadFlips_beadOf b q)
  have hβq : β q = Fin.cast hlen (beadOf b q) := by
    by_contra hcon
    simp only [blockSign] at hflip
    rw [if_neg hcon] at hflip
    exact Option.some_ne_none _ hflip
  rw [hβq, Fin.val_cast]

/-- **Left round-trip on cubes.**  A chain's cube list is the block list of its partition. -/
theorem ofBlockMap_cubes_eq (b : Ch (□n)) (β : Fin n → Fin L) (hβ : Function.Surjective β)
    (hlen : L = b.dims.length) (hβval : ∀ q, (β q : ℕ) = (beadOf b q : ℕ)) :
    blockCubes β hβ = wedgeToCubes ⟨b.dims, b.map.hom⟩ := by
  rw [wedgeToCubes_eq_ofFn]
  simp only [blockCubes]
  rw [List.ofFn_congr hlen]
  refine congrArg List.ofFn (funext fun i => ?_)
  dsimp only
  refine cube_sigma_ext _ _ ?_
  calc (StdCube.ev (blockCube β (Fin.cast hlen.symm i))).val
      = blockSign β (Fin.cast hlen.symm i) := ev_blockCube_val β (Fin.cast hlen.symm i)
    _ = blockSign (beadOf b) i := blockSign_congr hβval (Fin.val_cast _ _)
    _ = (StdCube.ev (beadFace b.map.hom i)).val :=
        (funext fun q => ev_beadFace_eq_blockSign b i q).symm

/-- **Chains are braid faces** — proved over `Ch (□n)`, where `coordFlip` applies to `b.map` with no
transport.  Forward is the partition's covector (`chFace`); the inverse reconstructs the chain from
the ordered partition `blockMap (covectorHeight X.1)` of the canonical height, so the equiv is
computable both ways. -/
def chFaceEquiv : Ch (□n) ≃ COM.Face (braidCOM n) where
  toFun := chFace
  invFun X :=
    (chEquivCubeChain (□n)).symm
      (ofBlockMap (blockMap (covectorHeight X.1)) (blockMap_surjective _))
  left_inv := fun b => by
    rw [Equiv.symm_apply_eq]
    apply eq_of_cubes
    rw [chEquivCubeChain_cubes]
    have hsign : braidSign (covectorHeight (chFace b).1)
        = braidSign (fun q => ((beadOf b q : ℕ) : ℤ)) := braidSign_covectorHeight_mem (chFace b).2
    have hlen : numBlocks (covectorHeight (chFace b).1) = b.dims.length :=
      (numBlocks_congr hsign).trans (numBlocks_of_surjective (beadOf b) (beadOf_surjective b))
    have hβval : ∀ q, (blockMap (covectorHeight (chFace b).1) q : ℕ) = (beadOf b q : ℕ) := fun q =>
      (blockMap_congr hsign q).trans (blockMap_of_surjective (beadOf b) (beadOf_surjective b) q)
    exact ofBlockMap_cubes_eq b (blockMap (covectorHeight (chFace b).1))
      (blockMap_surjective _) hlen hβval
  right_inv := fun X => by
    apply Subtype.ext
    have hfun : (fun q => ((beadOf ((chEquivCubeChain (□n)).symm
          (ofBlockMap (blockMap (covectorHeight X.1)) (blockMap_surjective _))) q : ℕ) : ℤ))
        = (fun q => ((blockMap (covectorHeight X.1) q : ℕ) : ℤ)) :=
      funext fun q => congrArg Nat.cast
        (beadOf_ofBlockMap (blockMap (covectorHeight X.1)) (blockMap_surjective _) q)
    change braidSign (fun q => ((beadOf ((chEquivCubeChain (□n)).symm
        (ofBlockMap (blockMap (covectorHeight X.1)) (blockMap_surjective _))) q : ℕ) : ℤ)) = X.1
    rw [hfun, braidSign_blockMap]
    exact braidSign_covectorHeight_mem X.2

/-- **Cube chains of `□n` are faces of the braid COM** — the target statement, transported from
`chFaceEquiv` across the chain↔`Ch` correspondence. -/
def cubeChainFaceEquiv : CubeChain (□n) ≃ COM.Face (braidCOM n) :=
  (chEquivCubeChain (□n)).symm.trans chFaceEquiv

/-! ## Order-reflection: `chFace b ⊑ chFace a` gives a refinement `a ⟶ b`

The converse of `chFace_faceLE`.  Phase 1 below extracts the monotone block reindexing `π` with
`beadOf b = π ∘ beadOf a` — `a`'s partition refines `b`'s. -/

open SignType in
/-- **The block reindexing of a face refinement.**  If `chFace b ⊑ chFace a` then every `a`-bead
maps to a `b`-bead monotonically, factoring `beadOf b` through `beadOf a`. -/
theorem exists_blockReindex {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) :
    ∃ π : Fin a.dims.length → Fin b.dims.length,
      Monotone π ∧ ∀ q, beadOf b q = π (beadOf a q) := by
  classical
  -- Per-ordered-pair content of `⊑`.
  have hsigns : ∀ i j : Fin n, i < j →
      sign (((beadOf b i : ℕ) : ℤ) - ((beadOf b j : ℕ) : ℤ)) = 0 ∨
        sign (((beadOf b i : ℕ) : ℤ) - ((beadOf b j : ℕ) : ℤ))
          = sign (((beadOf a i : ℕ) : ℤ) - ((beadOf a j : ℕ) : ℤ)) := by
    intro i j hij
    simpa only [chFace, braidSign_apply] using h ⟨(i, j), hij⟩
  have hbzero : ∀ p q : Fin n,
      sign (((beadOf b p : ℕ) : ℤ) - ((beadOf b q : ℕ) : ℤ)) = 0 → beadOf b p = beadOf b q := by
    intro p q h0
    have := sign_eq_zero_iff.mp h0
    exact Fin.val_injective (Nat.cast_injective (R := ℤ) (by linarith))
  -- (i) `a` ties `p, q` ⟹ so does `b`.
  have hwd : ∀ p q : Fin n, beadOf a p = beadOf a q → beadOf b p = beadOf b q := by
    intro p q hpq
    have hza : ∀ r s : Fin n, beadOf a r = beadOf a s →
        sign (((beadOf a r : ℕ) : ℤ) - ((beadOf a s : ℕ) : ℤ)) = 0 :=
      fun r s hrs => by rw [hrs, sub_self]; exact sign_zero
    rcases lt_trichotomy p q with hlt | rfl | hlt
    · exact hbzero p q ((hsigns p q hlt).elim id (fun heq => heq.trans (hza p q hpq)))
    · rfl
    · exact (hbzero q p ((hsigns q p hlt).elim id (fun heq => heq.trans (hza q p hpq.symm)))).symm
  -- (ii) `a`-order ⟹ `b`-order (`≤`).
  have hle : ∀ p q : Fin n, (beadOf a p : ℕ) < (beadOf a q : ℕ) →
      (beadOf b p : ℕ) ≤ (beadOf b q : ℕ) := by
    intro p q hpq
    rcases lt_trichotomy p q with hlt | rfl | hlt
    · rcases hsigns p q hlt with h0 | heq
      · exact le_of_eq (congrArg Fin.val (hbzero p q h0))
      · rw [(by rw [sign_eq_neg_one_iff]; omega : sign (((beadOf a p:ℕ):ℤ) - ((beadOf a q:ℕ):ℤ))
            = -1)] at heq
        have := sign_eq_neg_one_iff.mp heq; omega
    · omega
    · rcases hsigns q p hlt with h0 | heq
      · exact le_of_eq (congrArg Fin.val (hbzero q p h0).symm)
      · rw [(by rw [sign_eq_one_iff]; omega : sign (((beadOf a q:ℕ):ℤ) - ((beadOf a p:ℕ):ℤ))
            = 1)] at heq
        have := sign_eq_one_iff.mp heq; omega
  have hle' : ∀ p q : Fin n, (beadOf a p : ℕ) ≤ (beadOf a q : ℕ) →
      (beadOf b p : ℕ) ≤ (beadOf b q : ℕ) := by
    intro p q hpq
    rcases eq_or_lt_of_le hpq with heq | hlt
    · exact le_of_eq (congrArg Fin.val (hwd p q (Fin.val_injective heq)))
    · exact hle p q hlt
  -- Choose a coordinate representative per `a`-bead; reindex through it.
  have hrep : ∀ i, beadOf a (Function.surjInv (beadOf_surjective a) i) = i :=
    Function.surjInv_eq (beadOf_surjective a)
  refine ⟨fun i => beadOf b (Function.surjInv (beadOf_surjective a) i), fun i j hij => ?_,
    fun q => (hwd _ q (hrep (beadOf a q))).symm⟩
  exact hle' _ _ (by rw [hrep, hrep]; exact hij)

open StdCube in
/-- **Phase 2: the block-face inclusion.**  Given the reindexing `π` of `exists_blockReindex`,
`a`-bead `i`'s face factors through `b`-bead `π i`'s face by an explicit cube inclusion (the
restriction of `a`'s block-`i` sign vector to `b`'s block-`π i` free coordinates). -/
theorem beadFace_factor {a b : Ch (□n)} {π : Fin a.dims.length → Fin b.dims.length}
    (hmono : Monotone π) (hπ : ∀ q, beadOf b q = π (beadOf a q)) (i : Fin a.dims.length) :
    ∃ g : ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (π i) : ℕ),
      beadFace a.map.hom i = (□n).toPsh.map g.op (beadFace b.map.hom (π i)) := by
  have hαval : ∀ q, (StdCube.ev (beadFace a.map.hom i)).val q = blockSign (beadOf a) i q :=
    ev_beadFace_eq_blockSign a i
  have hβval : ∀ q, (StdCube.ev (beadFace b.map.hom (π i))).val q = blockSign (beadOf b) (π i) q :=
    ev_beadFace_eq_blockSign b (π i)
  have hprop : (noneSet (StdCube.ev (beadFace a.map.hom i)).val).card = (a.dims.get i : ℕ) :=
    (StdCube.ev (beadFace a.map.hom i)).prop
  have hcontain : ∀ q, beadOf a q = i → q ∈ Set.range (faceEmb (beadFace b.map.hom (π i))) := by
    intro q hq
    rw [mem_range_faceEmb, hβval]
    simp only [blockSign, hπ q, hq, ↓reduceIte]
  -- the inclusion cell: `a`'s block-`i` sign restricted to `b`'s block-`π i` free coordinates.
  have hcard : (noneSet (fun k => (StdCube.ev (beadFace a.map.hom i)).val
      (faceEmb (beadFace b.map.hom (π i)) k))).card = (a.dims.get i : ℕ) := by
    refine (Finset.card_bij (fun k _ => faceEmb (beadFace b.map.hom (π i)) k) (fun k hk => ?_)
      (fun k _ k' _ he => (faceEmb _).injective he) (fun q hq => ?_)).trans hprop
    · rw [mem_noneSet] at hk ⊢; exact hk
    · rw [mem_noneSet] at hq
      have hai : beadOf a q = i := by
        by_contra hne
        have h2 := hq; rw [hαval] at h2
        simp only [blockSign, if_neg hne] at h2
        exact Option.some_ne_none _ h2
      obtain ⟨k, rfl⟩ := hcontain q hai
      exact ⟨k, mem_noneSet.mpr hq, rfl⟩
  refine ⟨Box.ofSign ⟨_, hcard⟩, ?_⟩
  show beadFace a.map.hom i = Box.ofSign ⟨_, hcard⟩ ≫ beadFace b.map.hom (π i)
  apply Box.hom_ext
  rw [Box.sign_comp, Box.sign_ofSign]
  refine Subtype.ext (funext fun q => ?_)
  rw [subst_val]
  simp only [Box.sign]
  by_cases hqn : (StdCube.ev (beadFace b.map.hom (π i))).val q = none
  · rw [substFun_of_none _ _ hqn]
    exact congrArg (StdCube.ev (beadFace a.map.hom i)).val
      (nones_nonesIdx (StdCube.ev (beadFace b.map.hom (π i))) q _).symm
  · rw [substFun_of_some _ _ hqn, hαval, hβval]
    have hbne : beadOf b q ≠ π i := fun he => hqn (by rw [hβval]; simp [blockSign, he])
    have hane : beadOf a q ≠ i := fun he => hbne (by rw [hπ, he])
    have hπne : (π (beadOf a q) : ℕ) ≠ (π i : ℕ) := by
      rw [← hπ q]; exact fun he => hbne (Fin.val_injective he)
    simp only [blockSign, if_neg hane, if_neg hbne]
    rw [hπ q, Option.some.injEq, decide_eq_decide]
    exact ⟨fun hlt => lt_of_le_of_ne (hmono hlt.le) hπne, fun hlt => hmono.reflect_lt hlt⟩

/-- **Order-reflection / fullness.**  `chFace b ⊑ chFace a` gives a refinement `a ⟶ b`.  The
converse of `chFace_faceLE`, assembled from the monotone reindexing (`exists_blockReindex`) and the
block-face inclusions (`beadFace_factor`) through the wedge↔refine equivalence. -/
theorem chFace_faceLE_reflect {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) :
    Nonempty (a ⟶ b) := by
  obtain ⟨π, hmono, hπ⟩ := exists_blockReindex h
  choose g0 gspec using fun i' => beadFace_factor hmono hπ i'
  have hla := wedgeToCubes_length a.dims a.map.hom
  have hlb := wedgeToCubes_length b.dims b.map.hom
  have wac := wedgeToCubes_get a.dims a.map.hom
  have wbc := wedgeToCubes_get b.dims b.map.hom
  have hAget : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).1 = a.dims.get (i.cast hla) :=
    fun i => congrArg Sigma.fst (wac i)
  have hBget : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ((π (i.cast hla)).cast hlb.symm)).1
        = b.dims.get (π (i.cast hla)) := by
    intro i
    have hcast : ((π (i.cast hla)).cast hlb.symm).cast hlb = π (i.cast hla) :=
      Fin.ext (by simp only [Fin.val_cast])
    rw [congrArg Sigma.fst (wbc ((π (i.cast hla)).cast hlb.symm)), hcast]
  have hP : ∀ i' : Fin a.dims.length, yonedaEquiv (ιᵂ a.dims i' ≫ a.map.hom)
      = (□n).toPsh.map (g0 i').op (yonedaEquiv (ιᵂ b.dims (π i') ≫ b.map.hom)) := gspec
  have hX : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      (□n).toPsh.map (eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hAget i))).op
          (yonedaEquiv (ιᵂ a.dims (i.cast hla) ≫ a.map.hom))
        = ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).2 :=
    fun i => map_eqToHom_op_cell _ (by rw [wac i])
  have hY : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      (□n).toPsh.map (eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hBget i).symm)).op
          ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ((π (i.cast hla)).cast hlb.symm)).2
        = yonedaEquiv (ιᵂ b.dims (π (i.cast hla)) ≫ b.map.hom) := by
    intro i
    have hcast : ((π (i.cast hla)).cast hlb.symm).cast hlb = π (i.cast hla) := Fin.ext (by simp)
    exact map_eqToHom_op_cell _ (by rw [wbc ((π (i.cast hla)).cast hlb.symm), hcast])
  have m : wedgeToRefineObj a ⟶ wedgeToRefineObj b := by
    change ChainRefine (□n).init (□n).final (wedgeToCubes ⟨a.dims, a.map.hom⟩)
      (wedgeToCubes ⟨b.dims, b.map.hom⟩)
    refine
      { chainx := (wedgeToRefineObj a).isChain
        chainy := (wedgeToRefineObj b).isChain
        refinement := fun i => (π (i.cast hla)).cast hlb.symm
        incl := fun i => eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hAget i))
          ≫ g0 (i.cast hla) ≫ eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hBget i).symm)
        refinementMono := ?mono
        inclSpec := ?spec }
    case spec =>
      intro i
      rw [op_comp, op_comp, (□n).toPsh.map_comp, (□n).toPsh.map_comp, types_comp_apply,
        types_comp_apply, hY i, ← hP (i.cast hla), hX i]
    case mono =>
      intro i j hij
      have hh : π (i.cast hla) ≤ π (j.cast hla) :=
        hmono (by simpa only [Fin.le_def, Fin.coe_cast] using hij)
      simpa only [Fin.le_def, Fin.coe_cast] using hh
  exact ⟨eqToHom (refineToWedgeObj_wedgeToRefineObj a).symm
    ≫ (refineToWedge (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)).map m
    ≫ eqToHom (refineToWedgeObj_wedgeToRefineObj b)⟩

end CubeChains
