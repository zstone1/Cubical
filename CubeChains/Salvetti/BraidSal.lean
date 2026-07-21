import CubeChains.Salvetti.Runs
import CubeChains.Arrangements.SalElements
import CubeChains.Arrangements.Braid
import CubeChains.Salvetti.Elements
import CubeChains.Arrangements.BraidCovector
import CubeChains.Chains.ChainRestrictions
import CubeChains.Chains.CoordFunctor
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Inv

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

/-! ### Junction-vertex combinatorics

Along a chain the junction vertices are monotone in the bead index and flip `0 → 1` at exactly the
bead a coordinate is free in — the primitive linking the coend height below to the stored vertices. -/

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

/-- Consecutive junctions only flip coordinates up: `vtx i ≤ vtx (i+1)` at `q`. -/
theorem vertexCoord_vtx_mono_step (C : CubeChain (□n)) (i : Fin C.cubes.length) (q : Fin n) :
    vertexCoord (C.vtx i.castSucc) q ≤ vertexCoord (C.vtx i.succ) q := by
  rw [← C.cube_src i, ← C.cube_tgt i, vertexCoord_vertex₀, vertexCoord_vertex₁]
  by_cases h : (Box.sign (C.cubes.get i).2).val q = none
  · rw [if_pos h, if_pos h]; exact Bool.false_le _
  · rw [if_neg h, if_neg h]

/-- The junction vertices are monotone in the bead index. -/
theorem vertexCoord_vtx_monotone (C : CubeChain (□n)) (q : Fin n) :
    Monotone (fun k : Fin (C.cubes.length + 1) => vertexCoord (C.vtx k) q) :=
  Fin.monotone_iff_le_succ.mpr fun i => vertexCoord_vtx_mono_step C i q

/-- **A coordinate free in bead `i` flips the junctions there** (`false` before, `true` after) — a
monotone `Bool` sequence has one ascent. -/
theorem vertexCoord_flip (C : CubeChain (□n)) (i : Fin C.cubes.length) (q : Fin n)
    (hf : vertexCoord (C.vtx i.castSucc) q ≠ vertexCoord (C.vtx i.succ) q) :
    vertexCoord (C.vtx i.castSucc) q = false ∧ vertexCoord (C.vtx i.succ) q = true := by
  have hle := vertexCoord_vtx_monotone C q
    (show i.castSucc ≤ i.succ by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
  refine ⟨?_, ?_⟩
  · by_contra h; rw [Bool.not_eq_false] at h
    exact hf (le_antisymm hle (h.symm ▸ Bool.le_true _))
  · by_contra h; rw [Bool.not_eq_true] at h
    exact hf (le_antisymm hle (h.symm ▸ Bool.false_le _))

/-! ### The coordinate assembly — the coend height

`chainMap C : ⋁C.dims ⟶ □n` classifies `C`.  The coordinate coend `Coord↓` sends it, after
collapsing both ends, to `assemble C : (Σ bead, its free coords) → Fin n`, `⟨i, k⟩ ↦` the `□n`
coordinate bead `i`'s `k`-th free direction occupies (`assemble_apply`).  It is a bijection — the
beads partition the coordinates — so a coordinate's bead (`beadOf`) is well-defined: the height. -/

/-- The dimension sequence and the cube list have the same length. -/
theorem dims_length (C : CubeChain (□n)) : C.dims.length = C.cubes.length := by
  simp [CubeChain.dims]

/-- The classifying wedge map of a chain (`§3` descent). -/
def chainMap (C : CubeChain (□n)) : ⋁C.dims ⟶ □n :=
  wedgeDescHom C.cubes (isCubeChain C)

/-- Bead `i`'s cube face of `□n`, read off `chainMap` by Yoneda. -/
def beadCell (C : CubeChain (□n)) (i : Fin C.dims.length) : (□n).cells (C.dims.get i : ℕ) :=
  yonedaEquiv (ιᵂ C.dims i ≫ (chainMap C).hom)

/-- `Box.sign`-value of the `i`-th entry is invariant under a list equality (with the index cast). -/
theorem sign_get_congr {l l' : List (Σ d : ℕ+, (□n).cells (d : ℕ))} (h : l = l')
    (i : Fin l.length) :
    (Box.sign (l.get i).2).val
      = (Box.sign (l'.get (Fin.cast (congrArg List.length h) i)).2).val := by
  subst h; rfl

/-- **The sign vector of the `i`-th bead cell equals that of the `i`-th cube** — `wedgeToCubes`
round-trips the classifying map. -/
theorem beadCell_sign (C : CubeChain (□n)) (i : Fin C.dims.length) :
    (Box.sign (beadCell C i)).val
      = (Box.sign (C.cubes.get (Fin.cast (dims_length C) i)).2).val := by
  have hW : wedgeToCubes ⟨C.dims, (chainMap C).hom⟩ = C.cubes :=
    wedgeToCubes_wedgeDescHom C.cubes (isCubeChain C)
  have hg := wedgeToCubes_get C.dims (chainMap C).hom
    (Fin.cast (wedgeToCubes_length C.dims (chainMap C).hom).symm i)
  rw [show (Fin.cast (wedgeToCubes_length C.dims (chainMap C).hom).symm i).cast
      (wedgeToCubes_length C.dims (chainMap C).hom) = i from Fin.ext rfl] at hg
  calc (Box.sign (beadCell C i)).val
      = (Box.sign ((wedgeToCubes ⟨C.dims, (chainMap C).hom⟩).get
          (Fin.cast (wedgeToCubes_length C.dims (chainMap C).hom).symm i)).2).val := by rw [hg]; rfl
    _ = (Box.sign (C.cubes.get (Fin.cast (dims_length C) i)).2).val := by
          rw [sign_get_congr hW (Fin.cast (wedgeToCubes_length C.dims (chainMap C).hom).symm i),
            show Fin.cast (congrArg List.length hW)
                (Fin.cast (wedgeToCubes_length C.dims (chainMap C).hom).symm i)
              = Fin.cast (dims_length C) i from Fin.ext rfl]

/-- **The assembly map**: `⟨i, k⟩ ↦` the `□n` coordinate bead `i`'s `k`-th free direction occupies. -/
def assemble (C : CubeChain (□n)) : beadEvent C.dims → Fin n :=
  fun p => coordCube n ((cotensorLift Coord).map (chainMap C) ((coordWedge C.dims).symm p))

/-- **The assembly computation** (the crux): `assemble` sends bead `i`'s `k`-th coordinate to
`faceEmb (beadCell C i) k`, the `□n` coordinate it occupies. -/
theorem assemble_apply (C : CubeChain (□n)) (i : Fin C.dims.length) (k : Fin (C.dims.get i : ℕ)) :
    assemble C ⟨i, k⟩ = faceEmb (beadCell C i) k := by
  rw [assemble, coordWedge_symm_apply, cotensorLift_map_apply, Cotensor.map_map]
  rfl

/-- **A coordinate lies in bead `i`'s free directions** iff its cell is `none` there. -/
theorem mem_range_faceEmb {m : ℕ} (g : (□n).cells m) (q : Fin n) :
    (∃ k, faceEmb g k = q) ↔ (Box.sign g).val q = none := by
  constructor
  · rintro ⟨k, rfl⟩
    exact StdCube.mem_noneSet.mp (StdCube.nones_mem (Box.sign g) k)
  · intro hq
    have hmem : q ∈ (StdCube.noneSet (Box.sign g).val : Set (Fin n)) := by
      rw [Finset.mem_coe, StdCube.mem_noneSet]; exact hq
    rw [← Finset.range_orderEmbOfFin (StdCube.noneSet (Box.sign g).val) (Box.sign g).prop] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk⟩

/-- **A coordinate is free in at most one bead** — a monotone `Bool` ascent happens once. -/
theorem cube_none_unique (C : CubeChain (□n)) {j j' : Fin C.cubes.length} (q : Fin n)
    (hj : (Box.sign (C.cubes.get j).2).val q = none)
    (hj' : (Box.sign (C.cubes.get j').2).val q = none) : j = j' := by
  have key : ∀ a b : Fin C.cubes.length, (a : ℕ) < (b : ℕ) →
      (Box.sign (C.cubes.get a).2).val q = none → (Box.sign (C.cubes.get b).2).val q = none →
      False := by
    intro a b hab ha hb
    have hfa := (sign_eq_none_iff_vertexCoord_ne (C.cubes.get a).2 q).mp ha
    rw [C.cube_src a, C.cube_tgt a] at hfa
    have hfb := (sign_eq_none_iff_vertexCoord_ne (C.cubes.get b).2 q).mp hb
    rw [C.cube_src b, C.cube_tgt b] at hfb
    have htop := (vertexCoord_flip C a q hfa).2
    have hbot := (vertexCoord_flip C b q hfb).1
    have hle : vertexCoord (C.vtx a.succ) q ≤ vertexCoord (C.vtx b.castSucc) q :=
      vertexCoord_vtx_monotone C q
        (show a.succ ≤ b.castSucc by rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega)
    rw [htop, hbot] at hle
    exact absurd hle (by decide)
  rcases lt_trichotomy (j : ℕ) (j' : ℕ) with h | h | h
  · exact absurd (key j j' h hj hj') not_false
  · exact Fin.ext h
  · exact absurd (key j' j h hj' hj) not_false

/-- **`assemble` is injective** — distinct beads occupy disjoint coordinates. -/
theorem assemble_injective (C : CubeChain (□n)) : Function.Injective (assemble C) := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ heq
  rw [assemble_apply, assemble_apply] at heq
  obtain rfl : i = i' := by
    have hi : (Box.sign (beadCell C i)).val (faceEmb (beadCell C i) k) = none :=
      (mem_range_faceEmb (beadCell C i) _).mp ⟨k, rfl⟩
    have hi' : (Box.sign (beadCell C i')).val (faceEmb (beadCell C i') k') = none :=
      (mem_range_faceEmb (beadCell C i') _).mp ⟨k', rfl⟩
    rw [heq, beadCell_sign] at hi
    rw [beadCell_sign] at hi'
    exact Fin.cast_injective (dims_length C) (cube_none_unique C _ hi hi')
  obtain rfl : k = k' := (faceEmb (beadCell C i)).injective heq
  rfl

/-- **The bead dimensions sum to `n`** — the chain's total altitude gap. -/
theorem dims_sum (C : CubeChain (□n)) : ∑ i : Fin C.dims.length, ((C.dims.get i : ℕ)) = n := by
  have hax : PrecubicalSet.IsAltitude (□n).toPsh (BPSet.cubeAlt n) :=
    fun ε i x => BPSet.cube_alt_axiom n ε i x
  have h := isCubeChain_alt_final (BPSet.cubeAlt n) hax C.cubes (□n).init (□n).final (isCubeChain C)
  have hinit : BPSet.cubeAlt n 0 (□n).init = 0 := by
    simp only [BPSet.cubeAlt]
    rw [show (□n).init = StdCube.canonicalMap (StdCube.constVertex n false) from rfl,
      StdCube.ev_canonicalMap, StdCube.trueCount_constVertex_false, Nat.cast_zero]
  have hfinal : BPSet.cubeAlt n 0 (□n).final = (n : ℤ) := by
    simp only [BPSet.cubeAlt]
    rw [show (□n).final = StdCube.canonicalMap (StdCube.constVertex n true) from rfl,
      StdCube.ev_canonicalMap, StdCube.trueCount_constVertex_true]
  rw [hinit, hfinal, zero_add] at h
  have hsum : ∑ i : Fin C.dims.length, ((C.dims.get i : ℕ))
      = (C.cubes.map (fun c => (c.1 : ℕ))).sum := by
    rw [sum_get_eq_sum_map C.dims (fun d : ℕ+ => (d : ℕ))]
    congr 1
    rw [CubeChain.dims, List.map_map]; rfl
  have : ((∑ i : Fin C.dims.length, ((C.dims.get i : ℕ)) : ℕ) : ℤ) = (n : ℤ) := by
    rw [hsum]; exact h.symm
  exact_mod_cast this

/-- **The assembly is a bijection** — beads partition the coordinates (injective + equal card). -/
theorem assemble_bijective (C : CubeChain (□n)) : Function.Bijective (assemble C) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨assemble_injective C, ?_⟩
  simp only [beadEvent, Fintype.card_sigma, Fintype.card_fin]
  exact dims_sum C

/-- **The coordinate ≃ bead-event bijection.** -/
def assembleEquiv (C : CubeChain (□n)) : beadEvent C.dims ≃ Fin n where
  toFun := assemble C
  invFun := Fintype.bijInv (assemble_bijective C)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

/-- The **bead-index map**: coordinate `q ↦` its bead, read off the assembly's inverse. -/
def beadOf (C : CubeChain (□n)) (q : Fin n) : Fin C.cubes.length :=
  Fin.cast (dims_length C) ((assembleEquiv C).symm q).1

/-- The **height** of a coordinate: its bead index. -/
def cubeChainHeight (C : CubeChain (□n)) (q : Fin n) : ℤ :=
  ((beadOf C q : ℕ) : ℤ)

/-- The braid face of a `CubeChain`. -/
def cubeChainFace (C : CubeChain (□n)) : COM.Face (braidCOM n) :=
  ⟨braidSign (cubeChainHeight C), cubeChainHeight C, rfl⟩

/-- `cubeChainHeight` is the canonical height of its bead-index map — definitional. -/
theorem cubeChainHeight_eq_beadOf (C : CubeChain (□n)) :
    cubeChainHeight C = fun q => ((beadOf C q : ℕ) : ℤ) := rfl

/-- Bead indices are `< C.cubes.length` (`q` flips by the final vertex). -/
theorem cubeChainHeight_lt (C : CubeChain (□n)) (q : Fin n) :
    cubeChainHeight C q < (C.cubes.length : ℤ) := by
  rw [cubeChainHeight]; exact_mod_cast (beadOf C q).isLt

/-- The sign of the `j`-th cube, reindexed to the bead cell. -/
theorem cube_sign_beadCell (C : CubeChain (□n)) (j : Fin C.cubes.length) :
    (Box.sign (C.cubes.get j).2).val
      = (Box.sign (beadCell C (Fin.cast (dims_length C).symm j))).val := by
  have h := (beadCell_sign C (Fin.cast (dims_length C).symm j)).symm
  rwa [show Fin.cast (dims_length C) (Fin.cast (dims_length C).symm j) = j from Fin.ext rfl] at h

/-- A `Sigma` reconstruction fact: the fibre over `a` of `p` is inhabited iff `a` is `p`'s index. -/
theorem exists_sigma_mk_eq {α : Type*} {β : α → Type*} (p : Σ a, β a) (a : α) :
    (∃ b : β a, (⟨a, b⟩ : Σ a, β a) = p) ↔ a = p.1 := by
  constructor
  · rintro ⟨b, rfl⟩; rfl
  · rintro rfl; exact ⟨p.2, rfl⟩

/-- **A coordinate is free in bead `j` iff its bead index is `j`** — the coend read of the height. -/
theorem sign_none_iff_height (C : CubeChain (□n)) (j : Fin C.cubes.length) (q : Fin n) :
    (Box.sign (C.cubes.get j).2).val q = none ↔ cubeChainHeight C q = (j : ℕ) := by
  have hjc : cubeChainHeight C q = (j : ℕ)
      ↔ Fin.cast (dims_length C).symm j = ((assembleEquiv C).symm q).1 := by
    rw [cubeChainHeight, beadOf]
    constructor
    · intro h
      have hv : (Fin.cast (dims_length C) ((assembleEquiv C).symm q).1).val = j.val := by
        exact_mod_cast h
      exact Fin.ext (by simp only [Fin.coe_cast] at hv ⊢; omega)
    · intro h; rw [← h]; simp [Fin.coe_cast]
  rw [congrFun (cube_sign_beadCell C j) q, ← mem_range_faceEmb, hjc,
    ← exists_sigma_mk_eq ((assembleEquiv C).symm q) (Fin.cast (dims_length C).symm j)]
  refine exists_congr fun k => ?_
  rw [← assemble_apply]
  exact Equiv.apply_eq_iff_eq_symm_apply (assembleEquiv C)

/-- **Every bead index is attained** — each bead has a free coordinate (`dims ≥ 1`). -/
theorem beadOf_surjective (C : CubeChain (□n)) : Function.Surjective (beadOf C) := by
  intro j
  have hpos : 0 < (C.dims.get (Fin.cast (dims_length C).symm j) : ℕ) :=
    (C.dims.get (Fin.cast (dims_length C).symm j)).pos
  refine ⟨assemble C ⟨Fin.cast (dims_length C).symm j, ⟨0, hpos⟩⟩, ?_⟩
  rw [beadOf,
    show assemble C ⟨Fin.cast (dims_length C).symm j, ⟨0, hpos⟩⟩
      = assembleEquiv C ⟨Fin.cast (dims_length C).symm j, ⟨0, hpos⟩⟩ from rfl,
    Equiv.symm_apply_apply]
  exact Fin.ext (by simp [Fin.coe_cast])

/-- Every bead index is realised as a height. -/
theorem cubeChainHeight_surj (C : CubeChain (□n)) (j : Fin C.cubes.length) :
    ∃ q, cubeChainHeight C q = (j : ℤ) := by
  obtain ⟨q, hq⟩ := beadOf_surjective C j
  exact ⟨q, by rw [cubeChainHeight, hq]⟩

/-- **The junction vertex reads the height as a threshold**: `1` iff the bead index is below `j`.
Re-derived from the coend height — the coordinate flips exactly at bead `beadOf C q`, and the
junction sequence is monotone. -/
theorem vertexCoord_vtx (C : CubeChain (□n)) (j : Fin (C.cubes.length + 1)) (q : Fin n) :
    vertexCoord (C.vtx j) q = decide (cubeChainHeight C q < (j : ℕ)) := by
  have hH : cubeChainHeight C q = ((beadOf C q : ℕ) : ℤ) := rfl
  have hnone : (Box.sign (C.cubes.get (beadOf C q)).2).val q = none :=
    (sign_none_iff_height C (beadOf C q) q).mpr rfl
  have hf := (sign_eq_none_iff_vertexCoord_ne (C.cubes.get (beadOf C q)).2 q).mp hnone
  rw [C.cube_src (beadOf C q), C.cube_tgt (beadOf C q)] at hf
  obtain ⟨hlo, hhi⟩ := vertexCoord_flip C (beadOf C q) q hf
  rcases Nat.lt_or_ge (beadOf C q : ℕ) (j : ℕ) with hj | hj
  · have hjge : vertexCoord (C.vtx (beadOf C q).succ) q ≤ vertexCoord (C.vtx j) q :=
      vertexCoord_vtx_monotone C q (by rw [Fin.le_def, Fin.val_succ]; omega)
    rw [hhi] at hjge
    rw [le_antisymm (Bool.le_true _) hjge]
    symm; rw [decide_eq_true_iff, hH]; exact_mod_cast hj
  · have hjle : vertexCoord (C.vtx j) q ≤ vertexCoord (C.vtx (beadOf C q).castSucc) q :=
      vertexCoord_vtx_monotone C q (by rw [Fin.le_def, Fin.val_castSucc]; omega)
    rw [hlo] at hjle
    rw [le_antisymm hjle (Bool.false_le _)]
    symm; rw [decide_eq_false_iff_not, hH, not_lt]; exact_mod_cast hj

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

/-- **Round trip on heights**: the height of `heightCubeChain y` is `denseRank y`.  Bead
`⌊denseRank y q⌋` is free at `q` (`sign_beadCube`), and `sign_none_iff_height` reads that off. -/
theorem cubeChainHeight_heightCubeChain (y : Fin n → ℤ) :
    cubeChainHeight (heightCubeChain y) = denseRank y := by
  funext q
  have hnn := denseRank_nonneg y q
  have hlt := denseRank_lt_numBlocks y q
  have hclen : (heightCubeChain y).cubes.length = numBlocks y := length_heightCubes y
  have hj0 : (denseRank y q).toNat < (heightCubeChain y).cubes.length := by
    rw [hclen]; omega
  set j0 : Fin (heightCubeChain y).cubes.length := ⟨(denseRank y q).toNat, hj0⟩ with hj0def
  have hjval : ((j0 : ℕ) : ℤ) = denseRank y q := by
    change ((denseRank y q).toNat : ℤ) = denseRank y q; omega
  have hnone : (Box.sign ((heightCubeChain y).cubes.get j0).2).val q = none := by
    show (Box.sign ((heightCubes y).get j0).2).val q = none
    unfold heightCubes
    rw [List.get_ofFn]
    simp [sign_beadCube, heightBeadCell, Fin.coe_cast, hjval]
  exact ((sign_none_iff_height (heightCubeChain y) j0 q).mp hnone).trans hjval

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
  · change (heightCubes z).length = C.cubes.length
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

/-! ## Naturality: `chainPresheaf ≅ facePresheaf`

The object comparison `cubeChainFaceEquiv` is natural in the cube: restricting a chain along a face
and reading its covector is reading the covector and reindexing it (`braidComap`).  Both sides are
the same ordered partition of the coordinates `faceEmb face` selects. -/

/-- A surviving bead's sign vector is the original's, reindexed through `faceEmb`. -/
theorem sign_restrictCube {n b : ℕ} (face : ▫n ⟶ ▫b)
    {c : Σ d : ℕ+, (□b).cells (d : ℕ)} {d : Σ d : ℕ+, (□n).cells (d : ℕ)}
    (h : restrictCube face c = some d) (p : Fin n) :
    (Box.sign d.2).val p = (Box.sign c.2).val (faceEmb face p) := by
  by_cases hpos : 0 < (StdCube.noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [restrictCube, dif_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    change (Box.sign (Box.ofSign (restrictCell face (Box.sign c.2)))).val p = _
    rw [Box.sign_ofSign]; rfl
  · rw [restrictCube, dif_neg hpos] at h; cases h

/-- The surviving beads of a `filterMap` are indexed by a strictly monotone map back into the
source, tracking which source element each survivor came from. -/
theorem exists_strictMono_getElem_filterMap {α β : Type*} (g : α → Option β) :
    ∀ l : List α, ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ (i : ℕ) (y : β), (l.filterMap g)[i]? = some y → ∃ x, l[f i]? = some x ∧ g x = some y
  | [] => ⟨id, strictMono_id, fun i y h => by simp at h⟩
  | a :: t => by
      obtain ⟨f, hf, hfget⟩ := exists_strictMono_getElem_filterMap g t
      rcases hga : g a with _ | b
      · refine ⟨fun i => f i + 1, ?_, fun i y h => ?_⟩
        · intro i j hij; exact Nat.add_lt_add_right (hf hij) 1
        · rw [List.filterMap_cons_none hga] at h
          obtain ⟨x, hx1, hx2⟩ := hfget i y h
          exact ⟨x, hx1, hx2⟩
      · refine ⟨fun i => match i with | 0 => 0 | k + 1 => f k + 1, ?_, fun i y h => ?_⟩
        · intro i j hij
          rcases i with _ | m
          · rcases j with _ | k
            · exact absurd hij (by omega)
            · exact Nat.succ_pos _
          · rcases j with _ | k
            · exact absurd hij (by omega)
            · exact Nat.add_lt_add_right (hf (Nat.lt_of_succ_lt_succ hij)) 1
        · rw [List.filterMap_cons_some hga] at h
          rcases i with _ | k
          · refine ⟨a, List.getElem?_cons_zero, ?_⟩
            rw [List.getElem?_cons_zero] at h; rw [hga]; exact h
          · rw [List.getElem?_cons_succ] at h
            obtain ⟨x, hx1, hx2⟩ := hfget k y h
            exact ⟨x, hx1, hx2⟩

/-- **The restricted height is the strictly-monotone image of the original.**  Coordinate `r` flips
in restricted bead `beadOf … r`; that bead is the projection of `C`-bead `surv (…)`, where `surv`
is the survivor-index map — so `r`'s free coordinate `faceEmb face r` flips there in `C`. -/
theorem exists_strictMono_height_restrict {n b : ℕ} (face : ▫n ⟶ ▫b) (C : CubeChain (□b)) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ∀ r : Fin n, cubeChainHeight C (faceEmb face r)
        = (f (cubeChainHeight (restrictCubeChain face C) r).toNat : ℤ) := by
  obtain ⟨surv, hmono, hsurv⟩ := exists_strictMono_getElem_filterMap (restrictCube face) C.cubes
  refine ⟨surv, hmono, fun r => ?_⟩
  have hfree : (Box.sign ((restrictCubeChain face C).cubes.get
        (beadOf (restrictCubeChain face C) r)).2).val r = none :=
    (sign_none_iff_height (restrictCubeChain face C) (beadOf (restrictCubeChain face C) r) r).mpr
      (congrFun (cubeChainHeight_eq_beadOf (restrictCubeChain face C)) r)
  have hget' : (C.cubes.filterMap (restrictCube face))[(beadOf (restrictCubeChain face C) r : ℕ)]?
      = some ((restrictCubeChain face C).cubes.get (beadOf (restrictCubeChain face C) r)) :=
    List.getElem?_eq_getElem (beadOf (restrictCubeChain face C) r).isLt
  obtain ⟨x, hx1, hx2⟩ := hsurv _ _ hget'
  obtain ⟨hlt, hxeq⟩ := List.getElem?_eq_some_iff.mp hx1
  subst hxeq
  have hnone : (Box.sign (C.cubes.get ⟨surv (beadOf (restrictCubeChain face C) r : ℕ), hlt⟩).2).val
      (faceEmb face r) = none :=
    (sign_restrictCube face hx2 r).symm.trans hfree
  exact (sign_none_iff_height C ⟨surv (beadOf (restrictCubeChain face C) r : ℕ), hlt⟩
    (faceEmb face r)).mp hnone

/-- **Restriction preserves the coordinate order.**  Coordinate `p` flips no later than `q` in the
restricted chain iff `faceEmb face p` flips no later than `faceEmb face q` in `C` — the surviving
beads keep their relative order. -/
theorem cubeChainHeight_restrict_le_iff {n b : ℕ} (face : ▫n ⟶ ▫b) (C : CubeChain (□b))
    (p q : Fin n) :
    cubeChainHeight (restrictCubeChain face C) p ≤ cubeChainHeight (restrictCubeChain face C) q
      ↔ cubeChainHeight C (faceEmb face p) ≤ cubeChainHeight C (faceEmb face q) := by
  obtain ⟨f, hf, hkey⟩ := exists_strictMono_height_restrict face C
  have hp0 : (0 : ℤ) ≤ cubeChainHeight (restrictCubeChain face C) p := by
    rw [cubeChainHeight]; positivity
  have hq0 : (0 : ℤ) ≤ cubeChainHeight (restrictCubeChain face C) q := by
    rw [cubeChainHeight]; positivity
  rw [hkey p, hkey q, Nat.cast_le, hf.le_iff_le]
  omega

/-- **Restriction reindexes the covector.**  The face of a restricted chain is the face of the
chain, reindexed through `faceEmb`: restriction preserves the coordinate order. -/
theorem cubeChainFace_restrict {n b : ℕ} (face : ▫n ⟶ ▫b) (C : CubeChain (□b)) :
    (cubeChainFace (restrictCubeChain face C)).1
      = braidComap (faceEmb face) (cubeChainFace C).1 := by
  change braidSign (cubeChainHeight (restrictCubeChain face C))
    = braidComap (faceEmb face) (braidSign (cubeChainHeight C))
  rw [braidComap_braidSign]
  refine SignVec.faceLE_antisymm
    (braidSign_faceLE_of_le_comp fun p q hpq => (cubeChainHeight_restrict_le_iff face C p q).2 hpq)
    (braidSign_faceLE_of_le_comp fun p q hpq => (cubeChainHeight_restrict_le_iff face C p q).1 hpq)

/-- **`chainPresheaf ≅ facePresheaf`**: cube chains and braid faces are the same presheaf on `Box`,
with `cubeChainFaceEquiv` the componentwise bijection. -/
def chainFaceNatIso : chainPresheaf ≅ facePresheaf :=
  NatIso.ofComponents (fun X => Equiv.toIso (cubeChainFaceEquiv (n := X.unop.dim)))
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro C
      exact Subtype.ext (cubeChainFace_restrict f.unop C))

/-- **The Salvetti complex of the braid arrangement `A_{n-1}` is the category of executions of the
`n`-cube.** -/
def braidSalEquiv (n : ℕ) : Sal (braidCOM n) ≌ Ch⋆ (□n) := sorry

end CubeChains
