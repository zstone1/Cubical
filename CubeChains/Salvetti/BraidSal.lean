import CubeChains.Salvetti.Runs
import CubeChains.Arrangements.SalElements
import CubeChains.Arrangements.Braid
import CubeChains.Salvetti.Elements
import CubeChains.Arrangements.BraidCovector
import Mathlib.Data.Int.Interval

/-!
# Salvetti/BraidSal — the braid Salvetti complex is the executions of the cube

The headline comparison `Sal (braidCOM n) ≌ Ch⋆ (□n)`.  Both sides are categories of elements, so
it factors through a comparison of bases and a comparison of fibres:

* base:   `(Ch (□n))ᵒᵖ ≌ Face (braidCOM n)` — a cube chain and a braid face are the same ordered
  set partition of `Fin n`;
* fibre:  `Lines (□n) ≅ _ ⋙ salFunctor (braidCOM n)` — runs of a chain are the topes above its face.

`salElementsEquiv` (`Arrangements/SalElements`) and the `Elements` scaffolding (`Salvetti/Elements`)
assemble the two into the equivalence.
-/

open CategoryTheory CubeChain ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## Braid faces -/

open SignType in
/-- **Coarsening is a face.**  If `x`'s order refines into `y`'s (`y p ≤ y q → x p ≤ x q`) then
`braidSign x ⊑ braidSign y`.  The base functor's monotonicity is this lemma with `blockIdx`
supplying the order-compatibility. -/
theorem braidSign_faceLE_of_le_comp {x y : Fin n → ℤ}
    (h : ∀ p q, y p ≤ y q → x p ≤ x q) : braidSign x ⊑ braidSign y := by
  intro e
  rcases eq_or_ne (x e.1.1) (x e.1.2) with hxe | hxe
  · exact Or.inl (by rw [braidSign_apply, hxe, sub_self, sign_zero])
  · refine Or.inr ?_
    rw [braidSign_apply, braidSign_apply]
    rcases lt_or_gt_of_ne hxe with hlt | hgt
    · have hy : y e.1.1 < y e.1.2 := not_le.mp fun hle => absurd (h _ _ hle) (not_le.mpr hlt)
      rw [sign_neg (by omega), sign_neg (by omega)]
    · have hy : y e.1.2 < y e.1.1 := not_le.mp fun hle => absurd (h _ _ hle) (not_le.mpr hgt)
      rw [sign_pos (by omega), sign_pos (by omega)]

/-! ## Faces → chains -/

/-- The bead cell of value `v` for a height `x`: free (`none`) on `x⁻¹{v}`, fixed `1` below `v` and
`0` above.  This is bead `v`'s face of `□n` when the chain is read off `x`. -/
def heightBeadCell (x : Fin n → ℤ) (v : ℤ) : Fin n → Option Bool :=
  fun q => if x q = v then none else some (decide (x q < v))

theorem noneSet_heightBeadCell (x : Fin n → ℤ) (v : ℤ) :
    StdCube.noneSet (heightBeadCell x v) = Finset.univ.filter (fun q => x q = v) := by
  ext q
  simp only [StdCube.mem_noneSet, Finset.mem_filter, Finset.mem_univ, true_and, heightBeadCell]
  by_cases h : x q = v <;> simp [h]

/-- `heightBeadCell` packaged as a cell of `□n`: its free coordinates are block `v`. -/
def heightBeadCellCell (x : Fin n → ℤ) (v : ℤ) :
    StdCube.Cell n (StdCube.noneSet (heightBeadCell x v)).card :=
  ⟨heightBeadCell x v, rfl⟩

/-- **The gluing computation.**  Setting bead-`v`'s free coordinates to a constant `ε` keeps the
coordinates outside block `v` at their fixed values, so `ε = 0` yields the prefix vertex
`q ↦ (x q < v)` and `ε = 1` yields `q ↦ (x q ≤ v)` (the `= v` coordinates flip). -/
theorem substFun_heightBeadCell (x : Fin n → ℤ) (v : ℤ) (ε : Bool) (q : Fin n) :
    StdCube.substFun (heightBeadCellCell x v) (StdCube.constVertex _ ε) q
      = some (if x q = v then ε else decide (x q < v)) := by
  by_cases hxv : x q = v
  · have h : (heightBeadCellCell x v).val q = none := by
      simp [heightBeadCellCell, heightBeadCell, hxv]
    rw [StdCube.substFun_of_none _ _ h]
    simp [StdCube.constVertex, hxv]
  · have h : (heightBeadCellCell x v).val q ≠ none := by
      simp [heightBeadCellCell, heightBeadCell, hxv]
    rw [StdCube.substFun_of_some _ _ h]
    simp [heightBeadCellCell, heightBeadCell, hxv]

/-- The junction vertex of `x` at threshold `v`: coordinate `q` is `1` iff `x q < v`. -/
def prefixVertexSign (x : Fin n → ℤ) (v : ℤ) : Fin n → Option Bool :=
  fun q => some (decide (x q < v))

/-- The junction vertex as a `0`-cell. -/
def prefixVertexCell (x : Fin n → ℤ) (v : ℤ) : StdCube.Cell n 0 :=
  ⟨prefixVertexSign x v, by simp [StdCube.noneSet, prefixVertexSign]⟩

/-- The junction `0`-cell of `□n`. -/
def prefixVertex (x : Fin n → ℤ) (v : ℤ) : (□n).cells 0 :=
  Box.ofSign (prefixVertexCell x v)

/-- Bead `v`'s cube face of `□n`. -/
def beadCube (x : Fin n → ℤ) (v : ℤ) :
    (□n).cells (StdCube.noneSet (heightBeadCell x v)).card :=
  Box.ofSign (heightBeadCellCell x v)

/-- Bead `v` starts at the prefix vertex `q ↦ (x q < v)`. -/
theorem vertex₀_beadCube (x : Fin n → ℤ) (v : ℤ) :
    (□n).toPsh.vertex₀ (beadCube x v) = prefixVertex x v := by
  apply Box.hom_ext
  rw [sign_vertex₀, beadCube, Box.sign_ofSign, prefixVertex, Box.sign_ofSign]
  apply Subtype.ext; funext q
  rw [StdCube.subst_val, substFun_heightBeadCell]
  simp only [prefixVertexCell, prefixVertexSign]
  by_cases h : x q = v <;> simp [h]

/-- Bead `v` ends at the prefix vertex `q ↦ (x q ≤ v) = (x q < v+1)` — the next bead's start. -/
theorem vertex₁_beadCube (x : Fin n → ℤ) (v : ℤ) :
    (□n).toPsh.vertex₁ (beadCube x v) = prefixVertex x (v + 1) := by
  apply Box.hom_ext
  rw [sign_vertex₁, beadCube, Box.sign_ofSign, prefixVertex, Box.sign_ofSign]
  apply Subtype.ext; funext q
  rw [StdCube.subst_val, substFun_heightBeadCell]
  simp only [prefixVertexCell, prefixVertexSign]
  by_cases h : x q = v
  · rw [if_pos h]; congr 1; symm; rw [decide_eq_true_eq]; omega
  · rw [if_neg h]; congr 1; rw [decide_eq_decide]; omega

/-! ## The chain of a height function

`denseRank` normalises `x` so its values are exactly `{0, …, k-1}`; bead `j` is `heightBeadCell` at
value `j`, and consecutive beads glue on the nose (`vertex₁ (bead j) = vertex₀ (bead (j+1))`, both
the prefix vertex at threshold `j+1`). -/

/-- A rank is strictly below the number of blocks — the `ℤ` form of
`denseRank_toNat_lt_numBlocks` (`Arrangements/BraidCovector`). -/
theorem denseRank_lt_numBlocks (x : Fin n → ℤ) (i : Fin n) :
    denseRank x i < (numBlocks x : ℤ) := by
  have h := denseRank_toNat_lt_numBlocks x i
  have := denseRank_nonneg x i
  omega

/-- Every block is non-empty: its rank is attained, since `blockMap` is surjective. -/
theorem blockSize_pos (x : Fin n → ℤ) (j : Fin (numBlocks x)) :
    0 < (StdCube.noneSet (heightBeadCell (denseRank x) ((j : ℕ) : ℤ))).card := by
  rw [noneSet_heightBeadCell, Finset.card_pos]
  obtain ⟨q, hq⟩ := blockMap_surjective x j
  have hval : (denseRank x q).toNat = (j : ℕ) := congrArg Fin.val hq
  have := denseRank_nonneg x q
  exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, by omega⟩⟩

/-- The cube list of the chain read off a height `x`: one bead per rank, in order. -/
def heightCubes (x : Fin n → ℤ) : List (Σ d : ℕ+, (□n).cells (d : ℕ)) :=
  List.ofFn fun j : Fin (numBlocks x) =>
    ⟨⟨_, blockSize_pos x j⟩, beadCube (denseRank x) ((j : ℕ) : ℤ)⟩

theorem length_heightCubes (x : Fin n → ℤ) : (heightCubes x).length = numBlocks x :=
  List.length_ofFn

/-- Below the smallest threshold the prefix vertex is the initial vertex. -/
theorem prefixVertex_eq_init {x : Fin n → ℤ} {v : ℤ} (hv : ∀ q, v ≤ x q) :
    prefixVertex x v = (□n).init := by
  apply Box.hom_ext
  simp only [prefixVertex, Box.sign_ofSign,
    show Box.sign ((□n).init) = StdCube.constVertex n false from StdCube.ev_canonicalMap _]
  apply Subtype.ext; funext q
  change some (decide (x q < v)) = some false
  rw [decide_eq_false_iff_not.mpr (not_lt.mpr (hv q))]

/-- Above every threshold the prefix vertex is the final vertex. -/
theorem prefixVertex_eq_final {x : Fin n → ℤ} {v : ℤ} (hv : ∀ q, x q < v) :
    prefixVertex x v = (□n).final := by
  apply Box.hom_ext
  simp only [prefixVertex, Box.sign_ofSign,
    show Box.sign ((□n).final) = StdCube.constVertex n true from StdCube.ev_canonicalMap _]
  apply Subtype.ext; funext q
  change some (decide (x q < v)) = some true
  rw [decide_eq_true_iff.mpr (hv q)]

/-- The chain of `□n` read off a height function `x`, as a `CubeChain`. -/
def heightCubeChain (x : Fin n → ℤ) : CubeChain (□n) where
  cubes := heightCubes x
  vtx j := prefixVertex (denseRank x) ((j : ℕ) : ℤ)
  vtx_zero := by
    change prefixVertex (denseRank x) (((0 : Fin ((heightCubes x).length + 1)) : ℕ) : ℤ) = _
    simp only [Fin.val_zero, Nat.cast_zero]
    exact prefixVertex_eq_init fun q => denseRank_nonneg x q
  vtx_last := by
    change prefixVertex (denseRank x)
      (((Fin.last (heightCubes x).length : Fin ((heightCubes x).length + 1)) : ℕ) : ℤ) = _
    rw [Fin.val_last, length_heightCubes]
    exact prefixVertex_eq_final fun q => denseRank_lt_numBlocks x q
  cube_src := fun i => by
    unfold heightCubes; rw [List.get_ofFn]; exact vertex₀_beadCube _ _
  cube_tgt := fun i => by
    unfold heightCubes; rw [List.get_ofFn]; exact vertex₁_beadCube _ _

/-! ## Covectors → canonical heights -/

/-- `p` ranks strictly below `q` in the covector `X` (its block fires earlier), read off the sign
of the ordered pair. -/
def covectorLt (X : SignVec (BraidGround n)) (p q : Fin n) : Bool :=
  if h : p < q then decide (X ⟨(p, q), h⟩ = -1)
  else if h : q < p then decide (X ⟨(q, p), h⟩ = 1)
  else false

/-- A canonical height realising a covector: `q ↦` the number of coordinates strictly below it.
This is the `SignVec → height` bridge (`BraidCovector` works with heights, not raw covectors). -/
def heightOfCovector (X : SignVec (BraidGround n)) (q : Fin n) : ℤ :=
  (Finset.univ.filter (fun p => covectorLt X p q = true)).card

open SignType in
/-- On a realised covector, `covectorLt` is exactly the height order. -/
theorem covectorLt_braidSign (x : Fin n → ℤ) (p q : Fin n) :
    covectorLt (braidSign x) p q = decide (x p < x q) := by
  unfold covectorLt
  by_cases h : p < q
  · rw [dif_pos h]
    simp only [braidSign_apply, decide_eq_decide, sign_eq_neg_one_iff]
    omega
  · rw [dif_neg h]
    by_cases h2 : q < p
    · rw [dif_pos h2]
      simp only [braidSign_apply, decide_eq_decide, sign_eq_one_iff]
      omega
    · obtain rfl : p = q := le_antisymm (not_lt.mp h2) (not_lt.mp h)
      simp

/-- `heightOfCovector` of a realised covector counts the coordinates strictly below. -/
theorem heightOfCovector_braidSign (x : Fin n → ℤ) (q : Fin n) :
    heightOfCovector (braidSign x) q = (Finset.univ.filter (fun p => x p < x q)).card := by
  rw [heightOfCovector]
  refine congrArg (fun s : Finset (Fin n) => (s.card : ℤ)) ?_
  ext p
  simp [Finset.mem_filter, covectorLt_braidSign]

/-- The strict-below set is monotone in the threshold coordinate. -/
private theorem below_subset {x : Fin n → ℤ} {p q : Fin n} (hpq : x p ≤ x q) :
    Finset.univ.filter (fun r => x r < x p) ⊆ Finset.univ.filter (fun r => x r < x q) := by
  intro r hr; rw [Finset.mem_filter] at hr ⊢; exact ⟨hr.1, lt_of_lt_of_le hr.2 hpq⟩

/-- **`heightOfCovector` realises the covector**: its `braidSign` is the original.  It has the same
order as any realising height (a coordinate-count rank), so the two `braidSign`s agree. -/
theorem braidSign_heightOfCovector (x : Fin n → ℤ) :
    braidSign (heightOfCovector (braidSign x)) = braidSign x := by
  refine SignVec.faceLE_antisymm (braidSign_faceLE_of_le_comp fun p q hpq => ?_)
    (braidSign_faceLE_of_le_comp fun p q hpq => ?_)
  · rw [heightOfCovector_braidSign, heightOfCovector_braidSign]
    exact_mod_cast Finset.card_le_card (below_subset hpq)
  · rw [heightOfCovector_braidSign, heightOfCovector_braidSign] at hpq
    by_contra hlt
    rw [not_le] at hlt
    have hss : Finset.univ.filter (fun r => x r < x q) ⊂ Finset.univ.filter (fun r => x r < x p) :=
      (Finset.ssubset_iff_of_subset (below_subset hlt.le)).mpr
        ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hlt⟩,
          fun hc => lt_irrefl (x q) (Finset.mem_filter.mp hc).2⟩
    exact absurd hpq (by exact_mod_cast Nat.not_le.mpr (Finset.card_lt_card hss))

/-! ## The face presheaf

Braid faces form a presheaf on `Box`, the covector analogue of `chainPresheaf`: restriction along a
cube face reindexes the ground set through `faceEmb`, so functoriality is inherited from
`faceEmb_id`/`faceEmb_comp`.  Single-vertex, since `BraidGround 0` is empty. -/

/-- A coordinate embedding lifts to the braid ground set: pairs of coordinates preserve `<`. -/
def braidGroundMap {a b : ℕ} (φ : Fin a ↪o Fin b) (e : BraidGround a) : BraidGround b :=
  ⟨(φ e.1.1, φ e.1.2), φ.strictMono e.2⟩

/-- Restrict a braid covector along a coordinate embedding by reindexing the ground set. -/
def braidComap {a b : ℕ} (φ : Fin a ↪o Fin b) (X : SignVec (BraidGround b)) :
    SignVec (BraidGround a) :=
  fun e => X (braidGroundMap φ e)

@[simp] theorem braidComap_braidSign {a b : ℕ} (φ : Fin a ↪o Fin b) (x : Fin b → ℤ) :
    braidComap φ (braidSign x) = braidSign (fun i => x (φ i)) := rfl

/-- Restriction preserves covectors: a reindexed height realises the restricted covector. -/
theorem braidComap_mem {a b : ℕ} (φ : Fin a ↪o Fin b) {X : SignVec (BraidGround b)}
    (hX : X ∈ braidCovectors b) : braidComap φ X ∈ braidCovectors a := by
  obtain ⟨x, rfl⟩ := hX
  exact ⟨fun i => x (φ i), rfl⟩

theorem braidComap_faceEmb_id {k : ℕ} (X : SignVec (BraidGround k)) :
    braidComap (faceEmb (𝟙 (▫k))) X = X := by
  funext e
  refine congrArg X (Subtype.ext ?_)
  change (faceEmb (𝟙 (▫k)) e.1.1, faceEmb (𝟙 (▫k)) e.1.2) = e.1
  rw [faceEmb_id, faceEmb_id]

theorem braidComap_faceEmb_comp {a b c : ℕ} (p : ▫a ⟶ ▫b) (q : ▫b ⟶ ▫c)
    (X : SignVec (BraidGround c)) :
    braidComap (faceEmb (p ≫ q)) X = braidComap (faceEmb p) (braidComap (faceEmb q) X) := by
  funext e
  refine congrArg X (Subtype.ext ?_)
  change (faceEmb (p ≫ q) e.1.1, faceEmb (p ≫ q) e.1.2)
      = (faceEmb q (faceEmb p e.1.1), faceEmb q (faceEmb p e.1.2))
  rw [faceEmb_comp, faceEmb_comp]

/-- **Braid faces form a presheaf on `Box`** — the covector analogue of `chainPresheaf`. -/
def facePresheaf : Boxᵒᵖ ⥤ Type where
  obj X := COM.Face (braidCOM X.unop.dim)
  map f := TypeCat.ofHom fun Y => ⟨braidComap (faceEmb f.unop) Y.1, braidComap_mem _ Y.2⟩
  map_id X := by
    apply ConcreteCategory.hom_ext; intro Y
    exact Subtype.ext (braidComap_faceEmb_id Y.1)
  map_comp f g := by
    apply ConcreteCategory.hom_ext; intro Y
    exact Subtype.ext (braidComap_faceEmb_comp g.unop f.unop Y.1)

/-- **`facePresheaf` is single-vertex**: `BraidGround 0` is empty, so there is one face of `□⁰`.
This is the `hP` that lets the wedge machinery classify faces of `⋁a` as products. -/
instance : Subsingleton (COM.Face (braidCOM 0)) :=
  ⟨fun _ _ => Subtype.ext (funext fun e => e.1.1.elim0)⟩

/-! ## The componentwise bijection `CubeChain(□n) ≃ Face(braidCOM n)`

The forward map reads a `CubeChain`'s stored junction vertices — bead `i`'s `⊤`-vertex is
`vtx i.succ` — so it matches `heightCubeChain`'s vertices, keeping the round trips clean. -/

/-- The value of a `0`-cell (vertex) of `□n` at coordinate `q`. -/
def vertexCoord (v : (□n).cells 0) (q : Fin n) : Bool := ((Box.sign v).val q).getD false

/-- The forward height of a `CubeChain`: coordinate `q ↦` the number of beads after which it has not
yet flipped, read off the stored junction vertices. -/
def cubeChainHeight (C : CubeChain (□n)) (q : Fin n) : ℤ :=
  (Finset.univ.filter (fun i : Fin C.cubes.length => vertexCoord (C.vtx i.succ) q = false)).card

/-- The braid face of a `CubeChain`. -/
def cubeChainFace (C : CubeChain (□n)) : COM.Face (braidCOM n) :=
  ⟨braidSign (cubeChainHeight C), cubeChainHeight C, rfl⟩

/-- Reading a prefix vertex back: coordinate `q` is `1` iff `x q < t`. -/
@[simp] theorem vertexCoord_prefixVertex (x : Fin n → ℤ) (t : ℤ) (q : Fin n) :
    vertexCoord (prefixVertex x t) q = decide (x q < t) := by
  rw [vertexCoord, prefixVertex, Box.sign_ofSign]; rfl

/-- The initial segment `{i : Fin m | i < k}` has `k` elements when `k ≤ m`. -/
theorem card_fin_val_lt {m k : ℕ} (h : k ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)).card = k := by
  have himg : Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)
      = Finset.univ.image (Fin.castLE h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun hi => ⟨⟨i.val, hi⟩, Fin.ext rfl⟩, by rintro ⟨j, rfl⟩; exact j.isLt⟩
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective h), Finset.card_univ,
    Fintype.card_fin]

/-- **Round trip on heights**: the forward height of `heightCubeChain y` is `denseRank y`.  Bead `i`
ends at the prefix vertex `denseRank y q < i+1`, so `q` is un-flipped after exactly the beads
`i < denseRank y q`, of which there are `denseRank y q` (it lies in `[0, numBlocks)`). -/
theorem cubeChainHeight_heightCubeChain (y : Fin n → ℤ) :
    cubeChainHeight (heightCubeChain y) = denseRank y := by
  funext q
  have hlen : (heightCubeChain y).cubes.length = numBlocks y := length_heightCubes y
  have hk : (denseRank y q).toNat ≤ (heightCubeChain y).cubes.length := by
    rw [hlen, Int.toNat_le]; exact le_of_lt (denseRank_lt_numBlocks y q)
  rw [cubeChainHeight]
  have hfilt : (Finset.univ.filter (fun i : Fin (heightCubeChain y).cubes.length =>
      vertexCoord ((heightCubeChain y).vtx i.succ) q = false))
      = Finset.univ.filter (fun i : Fin (heightCubeChain y).cubes.length =>
        (i : ℕ) < (denseRank y q).toNat) := by
    apply Finset.filter_congr; intro i _
    change (vertexCoord (prefixVertex (denseRank y) ((i.succ : ℕ) : ℤ)) q = false)
      ↔ ((i : ℕ) < (denseRank y q).toNat)
    rw [vertexCoord_prefixVertex, Fin.val_succ, decide_eq_false_iff_not, not_lt]
    push_cast; omega
  rw [hfilt, card_fin_val_lt hk]
  exact Int.toNat_of_nonneg (denseRank_nonneg y q)

/-! ### Reconstructing a chain from its height (the `left_inv` crux) -/

/-- Substituting a constant `ε` into a cell's free coordinates. -/
theorem substFun_constVertex {N k : ℕ} (w : StdCube.Cell N k) (ε : Bool) (q : Fin N) :
    StdCube.substFun w (StdCube.constVertex k ε) q
      = if w.val q = none then some ε else w.val q := by
  by_cases h : w.val q = none
  · rw [StdCube.substFun_of_none _ _ h, if_pos h]; rfl
  · rw [StdCube.substFun_of_some _ _ h, if_neg h]

/-- Reading a cube's `⊥`-vertex at `q`: `0` on the free coordinates, the fixed value elsewhere. -/
theorem vertexCoord_vertex₀ {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    vertexCoord ((□n).toPsh.vertex₀ c) q
      = if (Box.sign c).val q = none then false else ((Box.sign c).val q).getD false := by
  simp only [vertexCoord, sign_vertex₀, StdCube.subst_val, substFun_constVertex]
  by_cases h : (Box.sign c).val q = none <;> simp [h]

/-- Reading a cube's `⊤`-vertex at `q`: `1` on the free coordinates, the fixed value elsewhere. -/
theorem vertexCoord_vertex₁ {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    vertexCoord ((□n).toPsh.vertex₁ c) q
      = if (Box.sign c).val q = none then true else ((Box.sign c).val q).getD false := by
  simp only [vertexCoord, sign_vertex₁, StdCube.subst_val, substFun_constVertex]
  by_cases h : (Box.sign c).val q = none <;> simp [h]

/-- A coordinate is free in a cube iff the cube's two endpoints differ there. -/
theorem sign_eq_none_iff_vertexCoord_ne {k : ℕ} (c : (□n).cells k) (q : Fin n) :
    (Box.sign c).val q = none
      ↔ vertexCoord ((□n).toPsh.vertex₀ c) q ≠ vertexCoord ((□n).toPsh.vertex₁ c) q := by
  rw [vertexCoord_vertex₀, vertexCoord_vertex₁]
  by_cases h : (Box.sign c).val q = none <;> simp [h]

/-- Consecutive junctions only flip coordinates on: `vtx i ≤ vtx (i+1)` at `q`. -/
theorem vertexCoord_vtx_mono_step (C : CubeChain (□n)) (i : Fin C.cubes.length) (q : Fin n) :
    vertexCoord (C.vtx i.castSucc) q ≤ vertexCoord (C.vtx i.succ) q := by
  rw [← C.cube_src i, ← C.cube_tgt i, vertexCoord_vertex₀, vertexCoord_vertex₁]
  by_cases h : (Box.sign (C.cubes.get i).2).val q = none
  · rw [if_pos h, if_pos h]; exact Bool.false_le _
  · rw [if_neg h, if_neg h]

/-- The junction vertices are monotone in `q`. -/
theorem vertexCoord_vtx_monotone (C : CubeChain (□n)) (q : Fin n) :
    Monotone (fun k : Fin (C.cubes.length + 1) => vertexCoord (C.vtx k) q) :=
  Fin.monotone_iff_le_succ.mpr fun i => vertexCoord_vtx_mono_step C i q

/-- The first junction is the initial vertex: nothing has flipped. -/
theorem vertexCoord_vtx_zero (C : CubeChain (□n)) (q : Fin n) :
    vertexCoord (C.vtx 0) q = false := by
  simp only [vertexCoord, C.vtx_zero,
    show Box.sign ((□n).init) = StdCube.constVertex n false from StdCube.ev_canonicalMap _]
  rfl

/-- **The junctions read off the bead-index count.**  Coordinate `q` is un-flipped at junction `j`
iff `j` is at most `q`'s bead index — the monotone Bool sequence `vtx · q` has its false-block of
length `cubeChainHeight C q`. -/
theorem vertexCoord_vtx_eq_false_iff (C : CubeChain (□n)) (j : Fin (C.cubes.length + 1))
    (q : Fin n) :
    vertexCoord (C.vtx j) q = false ↔ (j : ℕ) ≤ (Finset.univ.filter
      (fun i : Fin C.cubes.length => vertexCoord (C.vtx i.succ) q = false)).card := by
  have hmono := vertexCoord_vtx_monotone C q
  have hjlen : (j : ℕ) ≤ C.cubes.length := Nat.lt_succ_iff.mp j.2
  constructor
  · intro hjf
    refine le_trans (le_of_eq (card_fin_val_lt hjlen).symm) (Finset.card_le_card ?_)
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ i, ?_⟩
    have hle : i.succ ≤ j := by rw [Fin.le_def, Fin.val_succ]; have := hi.2; omega
    have hmi := hmono hle
    dsimp only at hmi
    rw [hjf] at hmi
    exact le_antisymm hmi (Bool.false_le _)
  · intro hcard
    by_contra hjt
    rw [Bool.not_eq_false] at hjt
    have hj1 : 1 ≤ (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · rw [show j = 0 from Fin.ext h0, vertexCoord_vtx_zero] at hjt; exact absurd hjt (by decide)
      · exact h0
    have hsub : Finset.univ.filter
          (fun i : Fin C.cubes.length => vertexCoord (C.vtx i.succ) q = false)
        ⊆ Finset.univ.filter (fun i : Fin C.cubes.length => (i : ℕ) < (j : ℕ) - 1) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ i, ?_⟩
      by_contra hij
      rw [not_lt] at hij
      have hle : j ≤ i.succ := by rw [Fin.le_def, Fin.val_succ]; omega
      have hmi := hmono hle
      dsimp only at hmi
      rw [hjt] at hmi
      rw [le_antisymm (Bool.le_true _) hmi] at hi
      exact absurd hi.2 (by decide)
    have hle := Finset.card_le_card hsub
    rw [card_fin_val_lt (by omega : (j : ℕ) - 1 ≤ C.cubes.length)] at hle
    omega

/-- The junction vertex reads the count as a threshold: `1` iff the bead index exceeds `j`. -/
theorem vertexCoord_vtx (C : CubeChain (□n)) (j : Fin (C.cubes.length + 1)) (q : Fin n) :
    vertexCoord (C.vtx j) q = decide (cubeChainHeight C q < (j : ℕ)) := by
  rcases Bool.eq_false_or_eq_true (vertexCoord (C.vtx j) q) with hv | hv <;> rw [hv]
  · symm; rw [decide_eq_true_iff, cubeChainHeight]
    have hne : ¬ vertexCoord (C.vtx j) q = false := by rw [hv]; decide
    rw [vertexCoord_vtx_eq_false_iff] at hne
    omega
  · symm; rw [decide_eq_false_iff_not, cubeChainHeight]
    have := (vertexCoord_vtx_eq_false_iff C j q).mp hv
    omega

/-- **A coordinate is free in bead `j` iff its bead index is `j`.** -/
theorem sign_none_iff_height (C : CubeChain (□n)) (j : Fin C.cubes.length) (q : Fin n) :
    (Box.sign (C.cubes.get j).2).val q = none ↔ cubeChainHeight C q = (j : ℕ) := by
  rw [sign_eq_none_iff_vertexCoord_ne, C.cube_src j, C.cube_tgt j, vertexCoord_vtx, vertexCoord_vtx,
    Fin.val_castSucc, Fin.val_succ, ne_eq, decide_eq_decide]
  omega

/-- **Each of `C`'s cube cells is the reconstructed `heightBeadCell`.** -/
theorem sign_cube_eq (C : CubeChain (□n)) (j : Fin C.cubes.length) (q : Fin n) :
    (Box.sign (C.cubes.get j).2).val q = heightBeadCell (cubeChainHeight C) (j : ℤ) q := by
  rw [heightBeadCell]
  by_cases hj : cubeChainHeight C q = (j : ℤ)
  · rw [if_pos hj]; exact (sign_none_iff_height C j q).mpr (by exact_mod_cast hj)
  · rw [if_neg hj]
    have hne : (Box.sign (C.cubes.get j).2).val q ≠ none := fun hh =>
      hj (by exact_mod_cast (sign_none_iff_height C j q).mp hh)
    have hv := vertexCoord_vtx C j.castSucc q
    rw [← C.cube_src j, vertexCoord_vertex₀, if_neg hne, Fin.val_castSucc] at hv
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
    rw [hb, Option.getD_some] at hv
    rw [hb, hv]

/-- The last junction is the final vertex: everything has flipped. -/
theorem vertexCoord_vtx_last (C : CubeChain (□n)) (q : Fin n) :
    vertexCoord (C.vtx (Fin.last C.cubes.length)) q = true := by
  simp only [vertexCoord, C.vtx_last,
    show Box.sign ((□n).final) = StdCube.constVertex n true from StdCube.ev_canonicalMap _]
  rfl

/-- Every bead index is attained (each bead has a free coordinate). -/
theorem cubeChainHeight_surj (C : CubeChain (□n)) (j : Fin C.cubes.length) :
    ∃ q, cubeChainHeight C q = (j : ℤ) := by
  have hpos : 0 < (StdCube.noneSet (Box.sign (C.cubes.get j).2).val).card := by
    rw [(Box.sign (C.cubes.get j).2).prop]; exact (C.cubes.get j).1.pos
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  exact ⟨q, by exact_mod_cast (sign_none_iff_height C j q).mp (StdCube.mem_noneSet.mp hq)⟩

/-- Bead indices are `< C.cubes.length` (`q` flips by the final vertex). -/
theorem cubeChainHeight_lt (C : CubeChain (□n)) (q : Fin n) :
    cubeChainHeight C q < (C.cubes.length : ℤ) := by
  have h := vertexCoord_vtx_eq_false_iff C (Fin.last C.cubes.length) q
  rw [vertexCoord_vtx_last, Fin.val_last] at h
  rw [cubeChainHeight]
  have hn : ¬ C.cubes.length ≤ (Finset.univ.filter
      (fun i : Fin C.cubes.length => vertexCoord (C.vtx i.succ) q = false)).card :=
    fun hc => absurd (h.mpr hc) (by decide)
  omega

/-- The **bead-index map**: coordinate `q ↦` its bead, a surjection `Fin n → Fin C.cubes.length`
(`BraidCovector`'s `blockMap`, spelled on `cubeChainHeight`). -/
def beadOf (C : CubeChain (□n)) (q : Fin n) : Fin C.cubes.length :=
  ⟨(cubeChainHeight C q).toNat, by
    have h1 := cubeChainHeight_lt C q
    have h2 : (0 : ℤ) ≤ cubeChainHeight C q := by rw [cubeChainHeight]; positivity
    omega⟩

theorem beadOf_surjective (C : CubeChain (□n)) : Function.Surjective (beadOf C) := by
  intro j
  obtain ⟨q, hq⟩ := cubeChainHeight_surj C j
  exact ⟨q, Fin.ext (by change (cubeChainHeight C q).toNat = (j : ℕ); rw [hq]; simp)⟩

/-- `cubeChainHeight` is the canonical height of its bead-index map. -/
theorem cubeChainHeight_eq_beadOf (C : CubeChain (□n)) :
    cubeChainHeight C = fun q => ((beadOf C q : ℕ) : ℤ) := by
  funext q
  have h2 : (0 : ℤ) ≤ cubeChainHeight C q := by rw [cubeChainHeight]; positivity
  change cubeChainHeight C q = ((cubeChainHeight C q).toNat : ℤ)
  omega

/-- **The bead-index function is its own `denseRank`** — it is a block map's canonical height, so
`denseRank_natCast_val` applies. -/
theorem denseRank_cubeChainHeight (C : CubeChain (□n)) :
    denseRank (cubeChainHeight C) = cubeChainHeight C := by
  conv_lhs => rw [cubeChainHeight_eq_beadOf]
  funext q
  rw [cubeChainHeight_eq_beadOf]
  exact denseRank_natCast_val (beadOf C) (beadOf_surjective C) q

/-- The number of beads read off the height is the number of cubes (`numBlocks_of_surjective`). -/
theorem numBlocks_cubeChainHeight (C : CubeChain (□n)) :
    numBlocks (cubeChainHeight C) = C.cubes.length := by
  rw [cubeChainHeight_eq_beadOf]
  exact numBlocks_of_surjective (beadOf C) (beadOf_surjective C)

/-- The sign vector of a reconstructed bead is its `heightBeadCell`. -/
theorem sign_beadCube (x : Fin n → ℤ) (v : ℤ) (q : Fin n) :
    (Box.sign (beadCube x v)).val q = heightBeadCell x v q :=
  congrFun (congrArg Subtype.val (Box.sign_ofSign (heightBeadCellCell x v))) q

/-- **Beads are classified by their sign.**  A bead's dimension is its number of free coordinates,
so two beads of `□n` with equal sign vectors are equal — dimension included. -/
theorem box_cube_ext {d d' : ℕ+} {c : (□n).cells (d : ℕ)} {c' : (□n).cells (d' : ℕ)}
    (h : (Box.sign c).val = (Box.sign c').val) :
    (⟨d, c⟩ : Σ d : ℕ+, (□n).cells (d : ℕ)) = ⟨d', c'⟩ := by
  obtain rfl : d = d' := by
    have e1 : ((d : ℕ)) = (StdCube.noneSet (Box.sign c).val).card := (Box.sign c).prop.symm
    have e2 : (StdCube.noneSet (Box.sign c').val).card = (d' : ℕ) := (Box.sign c').prop
    have e12 : (StdCube.noneSet (Box.sign c).val).card
        = (StdCube.noneSet (Box.sign c').val).card := by rw [h]
    exact PNat.coe_injective (e1.trans (e12.trans e2))
  exact congrArg (Sigma.mk d) (Box.hom_ext (Subtype.ext h))

/-- **The chain rebuilt from `C`'s covector is `C`.**  Any height with the same `denseRank` as `C`'s
bead-index rebuilds `C`: the reconstructed beads are `C`'s (`sign_cube_eq`, with `box_cube_ext`
supplying the dimensions), the bead count matches (`numBlocks_cubeChainHeight`), and `denseRank`
normalises the input away. -/
theorem heightCubeChain_eq_of_denseRank (C : CubeChain (□n)) {z : Fin n → ℤ}
    (hz : denseRank z = cubeChainHeight C) : heightCubeChain z = C := by
  apply CubeChain.eq_of_cubes
  have hbs : braidSign z = braidSign (cubeChainHeight C) := by rw [← braidSign_denseRank z, hz]
  refine List.ext_get ?_ ?_
  · show (heightCubes z).length = C.cubes.length
    rw [length_heightCubes, numBlocks_congr hbs, numBlocks_cubeChainHeight]
  · intro i h1 h2
    change (heightCubes z).get ⟨i, h1⟩ = C.cubes.get ⟨i, h2⟩
    unfold heightCubes
    rw [List.get_ofFn]
    apply box_cube_ext
    funext q
    refine (sign_beadCube (denseRank z) _ q).trans ?_
    change heightBeadCell (denseRank z) (i : ℤ) q = (Box.sign (C.cubes.get ⟨i, h2⟩).2).val q
    rw [hz]
    exact (sign_cube_eq C ⟨i, h2⟩ q).symm

/-- **Chains of a cube are braid faces** — componentwise value of `chainPresheaf ≅ facePresheaf`.
The round trips are the retract structure: section and retraction undo each other. -/
def cubeChainFaceEquiv : CubeChain (□n) ≃ COM.Face (braidCOM n) where
  toFun := cubeChainFace
  invFun X := heightCubeChain (heightOfCovector X.1)
  left_inv := fun C => heightCubeChain_eq_of_denseRank C (by
    change denseRank (heightOfCovector (braidSign (cubeChainHeight C))) = cubeChainHeight C
    rw [denseRank_eq_of_braidSign_eq (braidSign_heightOfCovector (cubeChainHeight C)),
      denseRank_cubeChainHeight])
  right_inv := fun X => by
    apply Subtype.ext
    change braidSign (cubeChainHeight (heightCubeChain (heightOfCovector X.1))) = X.1
    rw [cubeChainHeight_heightCubeChain, braidSign_denseRank]
    obtain ⟨x, hx⟩ := X.2
    rw [← hx, braidSign_heightOfCovector]

/-- **The Salvetti complex of the braid arrangement `A_{n-1}` is the category of executions of the
`n`-cube.** -/
def braidSalEquiv (n : ℕ) : Sal (braidCOM n) ≌ Ch⋆ (□n) := sorry

end CubeChains
