import CubeChains.Foundations.BoxMonoidal
import CubeChains.Chains.Basic
import CubeChains.Chains.BlockDecomp

/-!
# Chains/ChainRestrictions — projecting a cube chain along a face

`restrictCubeChain face C` projects every cube of `C` onto the directions `face` uses, dropping
the ones that collapse to a point.  Dimension-decreasing, endpoints to endpoints.

The projection is not a precubical map — `Box` has no degeneracies, and it drops the dimension of
any cube whose free coordinates `face` omits.  It becomes a chain map because a collapsed cube has
*equal endpoints* after projection, so its neighbours still compose.

Everything routes through `faceEmb`, and that is forced: the restriction depends on `face` only
through the directions it uses, never through its `ε`s, so nothing natural in `face` as a cube map
can be it.  Do not look for a universal property over `Box`; there isn't one.
-/

open CategoryTheory Opposite CubeChain StdCube
open BPSet

namespace CubeChains

/-- **The projection.**  Restrict a sign vector to the directions `face` uses. -/
def restrictCoord {n b : ℕ} (face : ▫n ⟶ ▫b) {k : ℕ} (c : Cell b k) : Fin n → Option Bool :=
  fun i => c.val (faceEmb face i)

/-- **One cube at a time.**  The projected cell, with its dimension read off the sign vector. -/
def restrictCell {n b k : ℕ} (face : ▫n ⟶ ▫b) (s : Cell b k) :
    Cell n (noneSet (restrictCoord face s)).card :=
  ⟨restrictCoord face s, rfl⟩

/-- **Dimension-decreasing.**  A surviving free coordinate of the projection comes from a free
coordinate of the original, injectively (via `faceEmb`), so at most `k` survive. -/
theorem card_restrictCoord_le {n b k : ℕ} (face : ▫n ⟶ ▫b) (s : Cell b k) :
    (noneSet (restrictCoord face s)).card ≤ k := by
  have hle : (noneSet (restrictCoord face s)).card ≤ (noneSet s.val).card := by
    refine Finset.card_le_card_of_injOn (fun i => faceEmb face i) (fun i hi => ?_) ?_
    · have hfree : restrictCoord face s i = none := mem_noneSet.mp (Finset.mem_coe.mp hi)
      exact Finset.mem_coe.mpr (mem_noneSet.mpr hfree)
    · exact fun i _ j _ hij => (faceEmb face).injective hij
  rwa [s.prop] at hle

/-- **Project a cube**: keep it when something survives, drop it when it collapses.  The kept
dimension is `≤` the original (`restrictCube_dim_le`). -/
def restrictCube {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) :
    Option (Σ d : ℕ+, (cube n).cells (d : ℕ)) :=
  if h : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card then
    some ⟨⟨_, h⟩, Box.ofSign (restrictCell face (Box.sign c.2))⟩
  else none

/-- …and the same statement for a bundled cube: the projection never raises dimension. -/
theorem restrictCube_dim_le {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (d : Σ d : ℕ+, (cube n).cells (d : ℕ))
    (h : restrictCube face c = some d) : (d.1 : ℕ) ≤ (c.1 : ℕ) := by
  by_cases hpos : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [restrictCube, dif_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    exact card_restrictCoord_le face (Box.sign c.2)
  · rw [restrictCube, dif_neg hpos] at h; cases h

/-- The projected cube list. -/
def restrictChain {n b : ℕ} (face : ▫n ⟶ ▫b)
    (cubes : List (Σ n : ℕ+, (□b).cells n)) : List ((d : ℕ+) × (□n).cells d) :=
  cubes.filterMap (restrictCube face)

/-! ### Edges restrict to edges

A surviving cube has dimension `≤` the original and `> 0`; so at dimension `1` it stays at
dimension `1`.  This is what makes restriction carry runs to runs. -/

theorem restrictCube_dim_one {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (d : Σ d : ℕ+, (cube n).cells (d : ℕ))
    (h : restrictCube face c = some d) (hc : (c.1 : ℕ) = 1) : (d.1 : ℕ) = 1 := by
  have hle := restrictCube_dim_le face c d h
  have hpos := d.1.pos
  omega

theorem restrictChain_dim_one {n b : ℕ} (face : ▫n ⟶ ▫b)
    (cubes : List (Σ n : ℕ+, (□b).cells n)) (h : ∀ c ∈ cubes, (c.1 : ℕ) = 1) :
    ∀ d ∈ restrictChain face cubes, (d.1 : ℕ) = 1 := by
  intro d hd
  obtain ⟨c, hc, hcd⟩ := List.mem_filterMap.mp hd
  exact restrictCube_dim_one face c d hcd (h c hc)

/-- A cube list that is all edges *is* `1ᵐ` — the shape whose wedge is the all-edges wedge. -/
theorem dims_eq_replicate {K : BPSet} (cubes : List (Σ n : ℕ+, K.cells (n : ℕ)))
    (h : ∀ c ∈ cubes, (c.1 : ℕ) = 1) :
    cubes.map (·.1) = List.replicate cubes.length 1 := by
  refine List.eq_replicate_of_mem ?_ |>.trans (by rw [List.length_map])
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact PNat.coe_injective (h c hc)

/-! ### Vertices -/

/-- Vertices project to vertices — the `k = 0` case of `card_restrictCoord_le`. -/
theorem card_restrictCoord_zero {n b : ℕ} (face : ▫n ⟶ ▫b) (c : Cell b 0) :
    (noneSet (restrictCoord face c)).card = 0 :=
  Nat.le_zero.mp (card_restrictCoord_le face c)

/-- Project a vertex. -/
def restrictVertex {n b : ℕ} (face : ▫n ⟶ ▫b) (v : (cube b).cells 0) : (cube n).cells 0 :=
  Box.ofSign ⟨restrictCoord face (Box.sign v), card_restrictCoord_zero face (Box.sign v)⟩

theorem sign_restrictVertex {n b : ℕ} (face : ▫n ⟶ ▫b) (v : (cube b).cells 0) :
    (Box.sign (restrictVertex face v)).val = restrictCoord face (Box.sign v) :=
  congrArg Subtype.val (Box.sign_ofSign _)

/-! ### Endpoints, via composition

An extremal vertex is composition with a constant map (`sign_vertex₀/₁`), so a single
commutation — restriction commutes with `subst`ing a constant — gives *both* the kept case and
the collapsed case.  No case analysis on `restrictCube`. -/

theorem sign_vertex₀ {b k : ℕ} (c : (cube b).cells k) :
    Box.sign ((cube b).toPsh.vertex₀ c) = subst (Box.sign c) (constVertex k false) := by
  change Box.sign (PrecubicalSet.initVertexMap k ≫ c) = _
  rw [Box.sign_comp, show Box.sign (PrecubicalSet.initVertexMap k) = constVertex k false from
    ev_canonicalMap _]

theorem sign_vertex₁ {b k : ℕ} (c : (cube b).cells k) :
    Box.sign ((cube b).toPsh.vertex₁ c) = subst (Box.sign c) (constVertex k true) := by
  change Box.sign (PrecubicalSet.finalVertexMap k ≫ c) = _
  rw [Box.sign_comp, show Box.sign (PrecubicalSet.finalVertexMap k) = constVertex k true from
    ev_canonicalMap _]

/-- **The one commutation.**  Restriction commutes with composing a constant map — unconditionally,
whatever the projected dimension turns out to be. -/
theorem restrictCoord_subst_const {n b k : ℕ} (face : ▫n ⟶ ▫b) (s : Cell b k) (ε : Bool) :
    restrictCoord face (subst s (constVertex k ε))
      = (subst (restrictCell face s) (constVertex _ ε)).val := by
  funext i
  change (subst s (constVertex k ε)).val (faceEmb face i) = _
  rw [subst_val, subst_val]
  by_cases h : s.val (faceEmb face i) = none
  · rw [substFun_of_none s _ h, substFun_of_none (restrictCell face s) _ h]; rfl
  · rw [substFun_of_some s _ h, substFun_of_some (restrictCell face s) _ h]; rfl

/-- A cube with no surviving free coordinate is fixed by `subst`ing a constant — which is exactly
why a collapsed cube's two endpoints coincide. -/
theorem subst_const_of_no_free {n k : ℕ} (X : Cell n k) (ε : Bool) (h : ∀ j, X.val j ≠ none) :
    (subst X (constVertex k ε)).val = X.val := by
  funext j; rw [subst_val, substFun_of_some _ _ (h j)]

/-! ### Reading off the two cases -/

theorem restrictVertex_vertex₀ {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (d : Σ d : ℕ+, (cube n).cells (d : ℕ))
    (h : restrictCube face c = some d) :
    restrictVertex face ((cube b).toPsh.vertex₀ c.2) = (cube n).toPsh.vertex₀ d.2 := by
  by_cases hpos : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [restrictCube, dif_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    apply Box.hom_ext; apply Subtype.ext
    rw [sign_restrictVertex, sign_vertex₀ c.2, restrictCoord_subst_const, sign_vertex₀,
      Box.sign_ofSign]
    rfl
  · rw [restrictCube, dif_neg hpos] at h; cases h

theorem restrictVertex_vertex₁ {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (d : Σ d : ℕ+, (cube n).cells (d : ℕ))
    (h : restrictCube face c = some d) :
    restrictVertex face ((cube b).toPsh.vertex₁ c.2) = (cube n).toPsh.vertex₁ d.2 := by
  by_cases hpos : 0 < (noneSet (restrictCoord face (Box.sign c.2))).card
  · rw [restrictCube, dif_pos hpos] at h
    obtain rfl := (Option.some_inj.mp h).symm
    apply Box.hom_ext; apply Subtype.ext
    rw [sign_restrictVertex, sign_vertex₁ c.2, restrictCoord_subst_const, sign_vertex₁,
      Box.sign_ofSign]
    rfl
  · rw [restrictCube, dif_neg hpos] at h; cases h

/-- **A dropped cube collapses**: nothing survives, so `subst`ing a constant does nothing and both
endpoints land on the same vertex.  This is the whole reason the projection lifts. -/
theorem restrictVertex_collapse {n b : ℕ} (face : ▫n ⟶ ▫b)
    (c : Σ d : ℕ+, (cube b).cells (d : ℕ)) (h : restrictCube face c = none) :
    restrictVertex face ((cube b).toPsh.vertex₀ c.2)
      = restrictVertex face ((cube b).toPsh.vertex₁ c.2) := by
  have hne : ∀ j, (restrictCell face (Box.sign c.2)).val j ≠ none := by
    have hcard : (noneSet (restrictCoord face (Box.sign c.2))).card = 0 := by
      by_contra hc
      rw [restrictCube, dif_pos (Nat.pos_of_ne_zero hc)] at h; cases h
    intro j hj
    have hmem : j ∈ noneSet (restrictCoord face (Box.sign c.2)) := mem_noneSet.mpr hj
    rw [Finset.card_eq_zero.mp hcard] at hmem
    exact Finset.notMem_empty _ hmem
  apply Box.hom_ext; apply Subtype.ext
  rw [sign_restrictVertex, sign_restrictVertex, sign_vertex₀, sign_vertex₁,
    restrictCoord_subst_const, restrictCoord_subst_const,
    subst_const_of_no_free _ _ hne, subst_const_of_no_free _ _ hne]

/-- The cube's own endpoints are constant sign vectors, so they project to the cube's own
endpoints — one proof for both, since `(cube n).init/final` *are* `canonicalMap (constVertex n ε)`.
-/
theorem restrictVertex_cubeEnd {n b : ℕ} (face : ▫n ⟶ ▫b) (ε : Bool) :
    restrictVertex face (canonicalMap (constVertex b ε)) = canonicalMap (constVertex n ε) := by
  apply Box.hom_ext; apply Subtype.ext; funext i
  rw [sign_restrictVertex,
    show Box.sign (canonicalMap (constVertex b ε)) = constVertex b ε from ev_canonicalMap _,
    show Box.sign (canonicalMap (constVertex n ε)) = constVertex n ε from ev_canonicalMap _]
  rfl

theorem restrictVertex_init {n b : ℕ} (face : ▫n ⟶ ▫b) :
    restrictVertex face (cube b).init = (cube n).init := restrictVertex_cubeEnd face false

theorem restrictVertex_final {n b : ℕ} (face : ▫n ⟶ ▫b) :
    restrictVertex face (cube b).final = (cube n).final := restrictVertex_cubeEnd face true

/-! ### From one cube to a whole chain -/

/-- By induction on the cube list with moving endpoints — the shape `IsCubeChain` is defined in.
Kept cubes compose by `restrictVertex_vertex₀/₁`; dropped ones are absorbed by
`restrictVertex_collapse`. -/
theorem restrict_isCubeChain {n b : ℕ} (face : ▫n ⟶ ▫b) :
    ∀ (L : List (Σ d : ℕ+, (cube b).cells (d : ℕ))) (v w : (cube b).cells 0),
      IsCubeChain v L w →
      IsCubeChain (restrictVertex face v) (L.filterMap (restrictCube face))
        (restrictVertex face w)
  | [], v, w, h => by simpa [IsCubeChain] using congrArg (restrictVertex face) h
  | c :: rest, v, w, h => by
    obtain ⟨hsrc, htail⟩ := h
    rcases hc : restrictCube face c with _ | d
    · rw [List.filterMap_cons_none hc]
      have := restrict_isCubeChain face rest _ w htail
      rwa [← restrictVertex_collapse face c hc, hsrc] at this
    · rw [List.filterMap_cons_some hc]
      refine ⟨?_, ?_⟩
      · rw [← restrictVertex_vertex₀ face c d hc, hsrc]
      · have := restrict_isCubeChain face rest _ w htail
        rwa [restrictVertex_vertex₁ face c d hc] at this

/-- **Restrict a chain along a face.** -/
def restrictCubeChain {n b : ℕ} (face : ▫n ⟶ ▫b) (C : CubeChain (cube b)) : CubeChain (cube n) :=
  CubeChain.ofIsCubeChain (restrictChain face C.cubes) <| by
    have h := restrict_isCubeChain face C.cubes _ _ (isCubeChain C)
    rw [restrictVertex_init, restrictVertex_final] at h
    exact h

/-! ### All-edges chains

`EdgeChain` keeps the length out of the type, so restriction is `Subtype.mk` over
`restrictCubeChain` — no transports. -/

/-- An **all-edges chain** of `K`: a cube chain every one of whose cubes is an edge. -/
def EdgeChain (K : BPSet) : Type := {C : CubeChain K // ∀ c ∈ C.cubes, (c.1 : ℕ) = 1}

/-- **Restriction of all-edges chains — no transports.** -/
def EdgeChain.restrict {n b : ℕ} (face : ▫n ⟶ ▫b) (r : EdgeChain (cube b)) :
    EdgeChain (cube n) :=
  ⟨restrictCubeChain face r.1, restrictChain_dim_one face _ r.2⟩

end CubeChains
