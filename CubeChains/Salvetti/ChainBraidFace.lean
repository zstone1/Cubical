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

/-- The **bead** a coordinate is flipped by — the first component of the coordinate bijection's
inverse (`coordFlip`).  Computable, so `chFace` computes. -/
def beadOf (b : Ch (□n)) (q : Fin n) : Fin b.dims.length :=
  ((coordFlip b.map).symm q).1

@[simp]
def beadOf_eq (b : Ch (□n)) (q : Fin n) : beadOf b q = ((coordFlip b.map).symm q).1 :=
  by rfl

/-- **Geometric view of `beadOf`**: `q`'s bead is `i` iff `i`'s face is free at `q` — the two sides
of the coordinate bijection, bridged by `coordFlip_eq`. -/
theorem mem_range_iff_beadOf (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) :
    q ∈ Set.range (faceEmb (beadFace b.map.hom i)) ↔ beadOf b q = i := by
  rw [beadOf_eq]
  constructor
  · rintro ⟨k, hk⟩
    rw [← coordFlip_eq b.map ⟨i, k⟩] at hk
    rw [← hk, Equiv.symm_apply_apply]
  · rintro rfl
    exact ⟨((coordFlip b.map).symm q).2,
      (coordFlip_eq b.map ((coordFlip b.map).symm q)).symm.trans (Equiv.apply_symm_apply _ q)⟩

/-- **Sign-vector view of `beadOf`**: `i`'s face is free (`none`) at `q` iff `q`'s bead is `i`
(`mem_range_faceEmb` composed with `mem_range_iff_beadOf`). -/
theorem ev_beadFace_eq_none_iff (b : Ch (□n)) (i : Fin b.dims.length) (q : Fin n) :
    (StdCube.ev (beadFace b.map.hom i)).val q = none ↔ beadOf b q = i :=
  (mem_range_faceEmb (beadFace b.map.hom i) q).symm.trans (mem_range_iff_beadOf b i q)

/-- `beadOf b` is surjective: bead `i` flips its own `0`-th coordinate. -/
theorem beadOf_surjective (b : Ch (□n)) : Function.Surjective (beadOf b) := fun i =>
  ⟨coordFlip b.map ⟨i, ⟨0, (b.dims.get i).2⟩⟩, by rw [beadOf_eq, Equiv.symm_apply_apply]⟩

/-- The braid face of a chain: the covector of its ordered partition `beadOf`. -/
def chFace (b : Ch (□n)) : COM.Face (braidCOM n) :=
  ⟨braidSign (fun q => ((beadOf b q : ℕ) : ℤ)), (fun q => ((beadOf b q : ℕ) : ℤ)), rfl⟩

/-! ## Monotonicity of `chFace` under refinement

A morphism `f : a ⟶ b` in `Ch` refines `a` over `b` (`f.w : f.φ ≫ b.map = a.map`), so `a`'s
partition is finer than `b`'s and `chFace b ⊑ chFace a`.  Each of `a`'s beads factors through one of
`b`'s (`blockIdx fᵂ`), and `blockIdx` is monotone. -/

/-- **`f` sends `a`'s bead of `q` to `b`'s bead of `q`** — `coordFlip_comp` (coend functoriality)
carries `(coordFlip a.map).symm q` to `(coordFlip b.map).symm q` by `coordMap fᵂ`, whose bead is
`blockIdx fᵂ` (`coordMap_eq`). -/
theorem beadOf_blockIdx {a b : Ch (□n)} (f : a ⟶ b) (q : Fin n) :
    beadOf b q = blockIdx fᵂ (beadOf a q) := by
  have hq : (coordFlip b.map).symm q = coordMap f.φ ((coordFlip a.map).symm q) := by
    rw [Equiv.symm_apply_eq, ← coordFlip_comp, f.w, Equiv.apply_symm_apply]
  rw [beadOf_eq, hq, ← Sigma.eta ((coordFlip a.map).symm q), coordMap_eq]
  exact congrArg (blockIdx fᵂ) (beadOf_eq a q).symm

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
def ofBlockMap (β : Fin n → Fin L) (hβ : Function.Surjective β) : CubeChain (□n) :=
  ofIsCubeChain (blockCubes β hβ) <| by
    have key := isCubeChain_aux (blockCubes β hβ) (fun t => prefixVtx β (t : ℕ))
      (fun i => by unfold blockCubes; rw [List.get_ofFn]; exact (vertex₀_blockCube β _).symm ▸ rfl)
      (fun i => by unfold blockCubes; rw [List.get_ofFn]; exact (vertex₁_blockCube β _).symm ▸ rfl)
    have hz : (fun t : Fin ((blockCubes β hβ).length + 1) => prefixVtx β (t : ℕ)) 0
        = (□n).init := by simpa using prefixVtx_zero β
    have hl : (fun t : Fin ((blockCubes β hβ).length + 1) => prefixVtx β (t : ℕ))
        (Fin.last (blockCubes β hβ).length) = (□n).final := by
      simp only [Fin.val_last]; rw [length_blockCubes]; exact prefixVtx_last β
    rw [hz, hl] at key; exact key

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
    exact (ev_beadFace_eq_none_iff b i q).mpr h
  · rw [if_neg h]
    have hne : (StdCube.ev (beadFace b.map.hom i)).val q ≠ none := fun hnone =>
      h ((ev_beadFace_eq_none_iff b i q).mp hnone)
    obtain ⟨ε, hε⟩ := Option.ne_none_iff_exists'.mp hne
    rw [hε]
    have hqflip₀ : q ∈ Set.range (faceEmb (beadFace b.map.hom (beadOf b q))) :=
      (mem_range_iff_beadOf b (beadOf b q) q).mpr rfl
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
    exact (ev_beadFace_eq_none_iff b (beadOf b q) q).mpr rfl
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

/-! ## Order-reflection: `chFace b ⊑ chFace a` gives a **computable** refinement `a ⟶ b`

The converse of `chFace_faceLE`.  `blockReindex` is the computable monotone block reindexing (a
coordinate representative per `a`-bead, chosen by `Finset.min'` — no `choice`); `reflectHom`
reconstructs an actual chain map. -/

open SignType in
/-- Per-ordered-pair content of `chFace b ⊑ chFace a`: `b` ties `p, q`, or their `b`/`a`-order
signs agree. -/
private theorem chFace_le_disj {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) (p q : Fin n) :
    beadOf b p = beadOf b q ∨
      sign (((beadOf b p : ℕ) : ℤ) - ((beadOf b q : ℕ) : ℤ))
        = sign (((beadOf a p : ℕ) : ℤ) - ((beadOf a q : ℕ) : ℤ)) := by
  have hbz : ∀ r s : Fin n,
      sign (((beadOf b r : ℕ) : ℤ) - ((beadOf b s : ℕ) : ℤ)) = 0 → beadOf b r = beadOf b s :=
    fun r s h0 => Fin.val_injective
      (Nat.cast_injective (R := ℤ) (by have := sign_eq_zero_iff.mp h0; linarith))
  have hsig : ∀ r s : Fin n, r < s →
      sign (((beadOf b r : ℕ) : ℤ) - ((beadOf b s : ℕ) : ℤ)) = 0 ∨
        sign (((beadOf b r : ℕ) : ℤ) - ((beadOf b s : ℕ) : ℤ))
          = sign (((beadOf a r : ℕ) : ℤ) - ((beadOf a s : ℕ) : ℤ)) :=
    fun r s hrs => by simpa only [chFace, braidSign_apply] using h ⟨(r, s), hrs⟩
  rcases lt_trichotomy p q with hlt | rfl | hlt
  · exact (hsig p q hlt).imp (hbz p q) id
  · exact Or.inl rfl
  · refine (hsig q p hlt).imp (fun h0 => (hbz q p h0).symm) (fun heq => ?_)
    rw [show ((beadOf b p : ℕ) : ℤ) - ((beadOf b q : ℕ) : ℤ)
          = -(((beadOf b q : ℕ) : ℤ) - ((beadOf b p : ℕ) : ℤ)) from by ring,
      show ((beadOf a p : ℕ) : ℤ) - ((beadOf a q : ℕ) : ℤ)
          = -(((beadOf a q : ℕ) : ℤ) - ((beadOf a p : ℕ) : ℤ)) from by ring,
      Left.sign_neg, Left.sign_neg, heq]

open SignType in
/-- `a` ties `p, q` ⟹ so does `b`. -/
private theorem beadOf_tie {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) {p q : Fin n}
    (hpq : beadOf a p = beadOf a q) : beadOf b p = beadOf b q := by
  rcases chFace_le_disj h p q with heq | hsg
  · exact heq
  · have h0 : sign (((beadOf b p : ℕ) : ℤ) - ((beadOf b q : ℕ) : ℤ)) = 0 := by
      rw [hsg, hpq, sub_self]; exact sign_zero
    exact Fin.val_injective
      (Nat.cast_injective (R := ℤ) (by have := sign_eq_zero_iff.mp h0; linarith))

open SignType in
/-- `a`-order `≤` ⟹ `b`-order `≤`. -/
private theorem beadOf_le {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) {p q : Fin n}
    (hpq : (beadOf a p : ℕ) ≤ (beadOf a q : ℕ)) : (beadOf b p : ℕ) ≤ (beadOf b q : ℕ) := by
  rcases eq_or_lt_of_le hpq with heq | hlt
  · exact le_of_eq (congrArg Fin.val (beadOf_tie h (Fin.val_injective heq)))
  · rcases chFace_le_disj h p q with heq | hsg
    · exact le_of_eq (congrArg Fin.val heq)
    · rw [(by rw [sign_eq_neg_one_iff]; omega :
        sign (((beadOf a p : ℕ) : ℤ) - ((beadOf a q : ℕ) : ℤ)) = -1)] at hsg
      have := sign_eq_neg_one_iff.mp hsg; omega

private theorem blockReindex_nonempty {a : Ch (□n)} (i : Fin a.dims.length) :
    (Finset.univ.filter (fun q => beadOf a q = i)).Nonempty :=
  (beadOf_surjective a i).elim fun q hq => ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩⟩

/-- **The block reindexing** (computable): each `a`-bead `i` maps to the `b`-bead of its least
coordinate representative.  No `choice`. -/
def blockReindex {a b : Ch (□n)} (i : Fin a.dims.length) : Fin b.dims.length :=
  beadOf b ((Finset.univ.filter (fun q => beadOf a q = i)).min' (blockReindex_nonempty i))

private theorem blockReindex_rep {a : Ch (□n)} (i : Fin a.dims.length) :
    beadOf a ((Finset.univ.filter (fun q => beadOf a q = i)).min' (blockReindex_nonempty i)) = i :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (blockReindex_nonempty i))).2

/-- `blockReindex` factors `beadOf b` through `beadOf a`. -/
theorem blockReindex_spec {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) (q : Fin n) :
    beadOf b q = blockReindex (beadOf a q) :=
  (beadOf_tie h (blockReindex_rep (beadOf a q))).symm

/-- `blockReindex` is monotone. -/
theorem blockReindex_mono {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) :
    Monotone (blockReindex (a := a) (b := b)) := fun i j hij => by
  rw [Fin.le_def]
  refine beadOf_le h ?_
  rw [blockReindex_rep, blockReindex_rep]; exact hij

open StdCube in
/-- The free coordinates of `a`-bead `i` inject into `b`-bead `blockReindex i` (block containment),
so the restricted sign vector has the right free count. -/
private theorem blockIncl_card {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1)
    (i : Fin a.dims.length) :
    (noneSet (fun k => (StdCube.ev (beadFace a.map.hom i)).val
      (faceEmb (beadFace b.map.hom (blockReindex i)) k))).card = (a.dims.get i : ℕ) := by
  have hprop : (noneSet (StdCube.ev (beadFace a.map.hom i)).val).card = (a.dims.get i : ℕ) :=
    (StdCube.ev (beadFace a.map.hom i)).prop
  have hcontain : ∀ q, beadOf a q = i →
      q ∈ Set.range (faceEmb (beadFace b.map.hom (blockReindex i))) := fun q hq => by
    rw [mem_range_iff_beadOf, blockReindex_spec h q, hq]
  refine (Finset.card_bij (fun k _ => faceEmb (beadFace b.map.hom (blockReindex i)) k)
    (fun k hk => ?_) (fun k _ k' _ he => (faceEmb _).injective he) (fun q hq => ?_)).trans hprop
  · rw [mem_noneSet] at hk ⊢; exact hk
  · rw [mem_noneSet] at hq
    obtain ⟨k, rfl⟩ := hcontain q ((ev_beadFace_eq_none_iff a i q).mp hq)
    exact ⟨k, mem_noneSet.mpr hq, rfl⟩

/-- **The block-face inclusion** (computable): `a`-bead `i`'s cube included into `b`-bead
`blockReindex i`'s, the restriction of `i`'s sign vector to `blockReindex i`'s free coordinates. -/
def blockIncl {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) (i : Fin a.dims.length) :
    ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (blockReindex i) : ℕ) :=
  Box.ofSign ⟨fun k => (StdCube.ev (beadFace a.map.hom i)).val
    (faceEmb (beadFace b.map.hom (blockReindex i)) k), blockIncl_card h i⟩

open StdCube in
/-- `a`-bead `i`'s face is `b`-bead `blockReindex i`'s pulled back along `blockIncl`. -/
theorem blockIncl_spec {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) (i : Fin a.dims.length) :
    beadFace a.map.hom i
      = (□n).toPsh.map (blockIncl h i).op (beadFace b.map.hom (blockReindex i)) := by
  change beadFace a.map.hom i = Box.ofSign ⟨fun k => (StdCube.ev (beadFace a.map.hom i)).val
    (faceEmb (beadFace b.map.hom (blockReindex i)) k), blockIncl_card h i⟩
      ≫ beadFace b.map.hom (blockReindex i)
  apply Box.hom_ext
  rw [Box.sign_comp, Box.sign_ofSign]
  refine Subtype.ext (funext fun q => ?_)
  rw [subst_val]
  simp only [Box.sign]
  by_cases hqn : (StdCube.ev (beadFace b.map.hom (blockReindex i))).val q = none
  · rw [substFun_of_none _ _ hqn]
    exact congrArg (StdCube.ev (beadFace a.map.hom i)).val
      (nones_nonesIdx (StdCube.ev (beadFace b.map.hom (blockReindex i))) q _).symm
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

/-- **The reflected refinement** (computable): `chFace b ⊑ chFace a` reconstructs a chain map
`a ⟶ b`, assembled from `blockReindex` + `blockIncl` through the wedge↔refine equivalence. -/
def reflectHom {a b : Ch (□n)} (h : (chFace b).1 ⊑ (chFace a).1) : a ⟶ b := by
  have hla := wedgeToCubes_length a.dims a.map.hom
  have hlb := wedgeToCubes_length b.dims b.map.hom
  have wac := wedgeToCubes_get a.dims a.map.hom
  have wbc := wedgeToCubes_get b.dims b.map.hom
  have hAget : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).1 = a.dims.get (i.cast hla) :=
    fun i => congrArg Sigma.fst (wac i)
  have hBget : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ((blockReindex (i.cast hla)).cast hlb.symm)).1
        = b.dims.get (blockReindex (i.cast hla)) := by
    intro i
    have hcast : ((blockReindex (i.cast hla)).cast hlb.symm).cast hlb = blockReindex (i.cast hla) :=
      Fin.ext (by simp only [Fin.val_cast])
    rw [congrArg Sigma.fst (wbc ((blockReindex (i.cast hla)).cast hlb.symm)), hcast]
  have hP : ∀ i' : Fin a.dims.length, yonedaEquiv (ιᵂ a.dims i' ≫ a.map.hom) = (□n).toPsh.map
      (blockIncl h i').op (yonedaEquiv (ιᵂ b.dims (blockReindex i') ≫ b.map.hom)) :=
    blockIncl_spec h
  have hX : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      (□n).toPsh.map (eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hAget i))).op
          (yonedaEquiv (ιᵂ a.dims (i.cast hla) ≫ a.map.hom))
        = ((wedgeToCubes ⟨a.dims, a.map.hom⟩).get i).2 :=
    fun i => map_eqToHom_op_cell _ (by rw [wac i])
  have hY : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      (□n).toPsh.map (eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hBget i).symm)).op
          ((wedgeToCubes ⟨b.dims, b.map.hom⟩).get ((blockReindex (i.cast hla)).cast hlb.symm)).2
        = yonedaEquiv (ιᵂ b.dims (blockReindex (i.cast hla)) ≫ b.map.hom) := by
    intro i
    have hcast : ((blockReindex (i.cast hla)).cast hlb.symm).cast hlb = blockReindex (i.cast hla) :=
      Fin.ext (by simp)
    exact map_eqToHom_op_cell _ (by rw [wbc ((blockReindex (i.cast hla)).cast hlb.symm), hcast])
  have m : wedgeToRefineObj a ⟶ wedgeToRefineObj b := by
    change ChainRefine (□n).init (□n).final (wedgeToCubes ⟨a.dims, a.map.hom⟩)
      (wedgeToCubes ⟨b.dims, b.map.hom⟩)
    refine
      { chainx := (wedgeToRefineObj a).isChain
        chainy := (wedgeToRefineObj b).isChain
        refinement := fun i => (blockReindex (i.cast hla)).cast hlb.symm
        incl := fun i => eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hAget i))
          ≫ blockIncl h (i.cast hla) ≫ eqToHom (congrArg (fun m : ℕ+ => ▫(m : ℕ)) (hBget i).symm)
        refinementMono := ?mono
        inclSpec := ?spec }
    case spec =>
      intro i
      rw [op_comp, op_comp, (□n).toPsh.map_comp, (□n).toPsh.map_comp, types_comp_apply,
        types_comp_apply, hY i, ← hP (i.cast hla), hX i]
    case mono =>
      intro i j hij
      have hh : blockReindex (i.cast hla) ≤ blockReindex (j.cast hla) :=
        blockReindex_mono h (by simpa only [Fin.le_def, Fin.val_cast] using hij)
      simpa only [Fin.le_def, Fin.val_cast] using hh
  exact eqToHom (refineToWedgeObj_wedgeToRefineObj a).symm
    ≫ (refineToWedge (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)).map m
    ≫ eqToHom (refineToWedgeObj_wedgeToRefineObj b)

/-! ## The base equivalence `(Ch (□n))ᵒᵖ ≌ Face (braidCOM n)`

`chFace` is a bijection on objects (`chFaceEquiv`) and an order-iso on the thin hom-sets
(`chFace_faceLE` forward, `reflectHom` converse), so it is an equivalence — the base of
`Ch⋆ ≌ Sal`.  Both categories are thin, so unit/counit/naturality are `Subsingleton.elim`. -/

instance : Quiver.IsThin (Ch (□n))ᵒᵖ :=
  haveI := chainCat_hom_subsingleton (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)
  fun _ _ => inferInstance
instance : Quiver.IsThin (COM.Face (braidCOM n)) := fun _ _ => inferInstance

/-- The forward functor: a chain to its braid face, a refinement to the face-order relation. -/
def chFaceFunctor : (Ch (□n))ᵒᵖ ⥤ COM.Face (braidCOM n) where
  obj X := chFace X.unop
  map f := homOfLE (chFace_faceLE f.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The inverse functor: a face to (the op of) its reconstructed chain, an order relation to the
reflected refinement `reflectHom`. -/
def chFaceInverse : COM.Face (braidCOM n) ⥤ (Ch (□n))ᵒᵖ where
  obj Z := op (chFaceEquiv.symm Z)
  map {Z W} g := (reflectHom (a := chFaceEquiv.symm W) (b := chFaceEquiv.symm Z) (by
    rw [show chFace (chFaceEquiv.symm Z) = Z from chFaceEquiv.apply_symm_apply Z,
      show chFace (chFaceEquiv.symm W) = W from chFaceEquiv.apply_symm_apply W]
    exact leOfHom g)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The base equivalence** `(Ch (□n))ᵒᵖ ≌ Face (braidCOM n)` — computable, from `chFaceEquiv`
(objects) and the order facts (morphisms).  Consumed by `Ch⋆ ≌ Sal`. -/
def chFaceCatEquiv : (Ch (□n))ᵒᵖ ≌ COM.Face (braidCOM n) where
  functor := chFaceFunctor
  inverse := chFaceInverse
  unitIso := NatIso.ofComponents
    (fun X => eqToIso (congrArg op (chFaceEquiv.symm_apply_apply X.unop).symm))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun Z => eqToIso (chFaceEquiv.apply_symm_apply Z))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end CubeChains
