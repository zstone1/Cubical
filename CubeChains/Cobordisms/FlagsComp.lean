import CubeChains.Cobordisms.Composition

/-!
# Cobordisms/FlagsComp — the cobordism flags are preserved by composition

The **flag-preservation** layer: how the coverage flags `Cospan.Spanning` and
`Cospan.Closed` (see `Cobordisms/Flags.lean`) behave under the pushout composite
`DirectedCobordism.comp` (`Cobordisms/Composition.lean`).

Write `W := pushout C₁.inr C₂.inl`, `p₁ := pushout.inl …`, `p₂ := pushout.inr …`
(both mono).  Composition.lean already supplies the combinatorial backbone we reuse:

* `comp_cell_cases` — every cell of `W` is a `p₁`-cell or a `p₂`-cell;
* `comp_srcImage_eq` / `comp_sinkImage_eq` — the composite source image is the
  `p₁`-image of `srcImage C₁`, the composite sink image the `p₂`-image of
  `sinkImage C₂`;
* `comp_isPullback_app` — the van Kampen pullback at each level (cross-block cells
  factor through the glued `Y`);
* `pushout_inl_image_isSieve` / `pushout_inr_image_isCosieve` — the composite source
  image is a sieve, the sink image a cosieve, in `W` (the reachability *barrier*).

plus `Reaches.map` (a precubical map preserves directed reachability).

## Results (what is preserved, and under what hypotheses)

* **`Cospan.Spanning.comp` — UNCONDITIONAL.**  If `C₁`, `C₂` are spanning then so is
  the composite.  Every composite cell is a `p₁`- or `p₂`-cell; in each block its
  block's spanning gives a src→cell and cell→sink dipath, and the cross to the *other*
  block is routed through the shared `Y` (= `sinkImage C₁` glued to `srcImage C₂`),
  using the pushout commutativity `p₁ ∘ C₁.inr = p₂ ∘ C₂.inl`.

* **`DirectedCobordism.Closed.comp` — UNCONDITIONAL.**  If `W₁`, `W₂` are closed then
  so is the composite.  A minimal vertex of `W` pushes down (the legs are mono, so a
  predecessor pulls back) to a minimal vertex of its block; closedness of that block
  places it in the block's source image.  The only subtlety is a *purely* `p₂`-minimal
  vertex: closedness of `C₂` puts it in `srcImage C₂ = ` the glued `Y`, whence it is
  *also* a `p₁`-cell and the first case applies.  Maximal vertices are dual.  (The
  bundle `DirectedCobordism` is what carries leg-disjointness, used implicitly through
  `comp`; the proof itself needs only the two `Closed` predicates.)

* **`Confined` is intentionally not treated here.**  It is *not* preserved by
  composition in general — a nontrivial directed loop living inside the shared gluing
  object `Y` becomes, in the composite, an interior loop lying in *neither* the
  composite source image nor its sink image — and the cobordism category does not need
  it.  (This failure is itself mild evidence that the bare cospan flags under-determine
  the cobordism.)

**Layer:** Cobordisms.  **Imports:** `Cobordisms.Composition`.
-/

set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open Precubical.Cobordism

namespace PrecubicalSet

universe u

variable {X Y Z : PrecubicalSet}

/-! ### Glued-cell identification

The single shared identity used in every cross-block step: the pushout square
commutes, so the `p₁`-image of a `C₁.inr`-cell equals the `p₂`-image of the
corresponding `C₂.inl`-cell.  (`Y`-cells become identified across the two blocks.) -/

/-- The pushout square commutes on cells: for a `Y`-cell `y`, its image through the
`C₁`-block leg `C₁.inr ≫ p₁` equals its image through the `C₂`-block leg
`C₂.inl ≫ p₂`. -/
theorem comp_glue_cell (C₁ : Cospan X Y) (C₂ : Cospan Y Z) (y : Y.TotalCell) :
    mapCell (pushout.inl C₁.inr C₂.inl) (mapCell C₁.inr y)
      = mapCell (pushout.inr C₁.inr C₂.inl) (mapCell C₂.inl y) := by
  obtain ⟨n, y'⟩ := y
  have hc : C₁.inr ≫ pushout.inl C₁.inr C₂.inl = C₂.inl ≫ pushout.inr C₁.inr C₂.inl :=
    pushout.condition (f := C₁.inr) (g := C₂.inl)
  have happ := NatTrans.congr_app hc (op ▫n)
  apply_fun (fun φ => φ y') at happ
  -- both sides are `mapCell` of a composite, which `mapCell_mk` unfolds.
  simp only [mapCell_mk]
  exact congrArg (Sigma.mk n) happ

/-! ### Mono pushforward of extremal vertices

A monomorphism `f` pushes minimality/maximality *backwards*: if `f a` is a minimal
(resp. maximal) vertex of the target, then `a` is one of the source — a predecessor
(resp. successor) of `a` would map to one of `f a`, forcing equality by minimality
and then injectivity of `f` on cells.  These feed the `Closed` descent: a minimal
vertex of the pushout pushes down to a minimal vertex of its block. -/

/-- If `f a` is a minimal vertex and `f` is mono, then `a` is a minimal vertex. -/
theorem isMinimalVertex_of_mono {A B : PrecubicalSet} (f : A ⟶ B) [Mono f]
    {a : A.cells 0} {v : B.cells 0} (hv : f⟪0⟫ a = v)
    (hmin : IsMinimalVertex B v) : IsMinimalVertex A a := by
  intro u hu
  -- push `u → a` forward by `f`: `f u → f a = v`, so minimality pins `f u = ⟨0, v⟩`.
  have hmap : Reaches B (mapCell f u) ⟨0, v⟩ := by
    have := hu.map f
    rwa [show mapCell f (⟨0, a⟩ : A.TotalCell) = (⟨0, v⟩ : B.TotalCell) from
      congrArg (Sigma.mk 0) hv] at this
  have hfu : mapCell f u = (⟨0, v⟩ : B.TotalCell) := hmin _ hmap
  -- pin `u` to level `0` and use injectivity of `f`.
  obtain ⟨u', rfl, hu'⟩ := mapCell_eq_sigma f u hfu
  exact congrArg (Sigma.mk 0) (app_injective_of_mono f 0 (hu'.trans hv.symm))

/-- If `f a` is a maximal vertex and `f` is mono, then `a` is a maximal vertex. -/
theorem isMaximalVertex_of_mono {A B : PrecubicalSet} (f : A ⟶ B) [Mono f]
    {a : A.cells 0} {v : B.cells 0} (hv : f⟪0⟫ a = v)
    (hmax : IsMaximalVertex B v) : IsMaximalVertex A a := by
  intro u hu
  have hmap : Reaches B ⟨0, v⟩ (mapCell f u) := by
    have := hu.map f
    rwa [show mapCell f (⟨0, a⟩ : A.TotalCell) = (⟨0, v⟩ : B.TotalCell) from
      congrArg (Sigma.mk 0) hv] at this
  have hfu : mapCell f u = (⟨0, v⟩ : B.TotalCell) := hmax _ hmap
  obtain ⟨u', rfl, hu'⟩ := mapCell_eq_sigma f u hfu
  exact congrArg (Sigma.mk 0) (app_injective_of_mono f 0 (hu'.trans hv.symm))

/-! ### Spanning is preserved (unconditional)

Every composite cell is a `p₁`- or `p₂`-cell (`comp_cell_cases`).  In its block the
block's `Spanning` gives a source-image cell reaching it and it reaching a sink-image
cell; the cross to the *other* block goes through the glued `Y` via `comp_glue_cell`,
then the other block's `Spanning` continues the dipath. -/

namespace Cospan

/-- **Spanning is preserved by composition (unconditional).**  If `C₁ : Cospan X Y`
and `C₂ : Cospan Y Z` are both `Spanning`, then so is their composite
`C₁.comp C₂`. -/
theorem Spanning.comp {C₁ : Cospan X Y} {C₂ : Cospan Y Z}
    (h₁ : C₁.Spanning) (h₂ : C₂.Spanning) : (C₁.comp C₂).Spanning := by
  set p₁ := pushout.inl C₁.inr C₂.inl with hp₁
  set p₂ := pushout.inr C₁.inr C₂.inl with hp₂
  -- src-image membership of the composite, in block-image form.
  have srcMem : ∀ a : C₁.mid.TotalCell, srcImage C₁ a →
      srcImage (C₁.comp C₂) (mapCell p₁ a) := by
    intro a ha
    rw [comp_srcImage_eq]; exact ⟨a, ha, rfl⟩
  -- sink-image membership of the composite, in block-image form.
  have sinkMem : ∀ b : C₂.mid.TotalCell, sinkImage C₂ b →
      sinkImage (C₁.comp C₂) (mapCell p₂ b) := by
    intro b hb
    rw [comp_sinkImage_eq]; exact ⟨b, hb, rfl⟩
  intro w
  obtain ⟨wn, wc⟩ := w
  -- The source half: every composite cell is reached from a composite source cell.
  -- The sink half: every composite cell reaches a composite sink cell.
  obtain ⟨c, hc⟩ | ⟨c, hc⟩ := comp_cell_cases C₁ C₂ wn wc
  · -- `w = p₁(c)`.
    have hwc : mapCell p₁ (⟨wn, c⟩ : C₁.mid.TotalCell) = (⟨wn, wc⟩ : (C₁.comp C₂).mid.TotalCell) :=
      congrArg (Sigma.mk wn) hc
    refine ⟨?_, ?_⟩
    · -- src side: directly from `C₁` spanning of `c`.
      obtain ⟨s, hs_src, hs_reach⟩ := (h₁ ⟨wn, c⟩).1
      refine ⟨mapCell p₁ s, srcMem s hs_src, ?_⟩
      rw [← hwc]; exact hs_reach.map p₁
    · -- sink side: `C₁` spanning gives a sink in `sinkImage C₁ = Y`, cross to `C₂`.
      obtain ⟨t, ht_sink, ht_reach⟩ := (h₁ ⟨wn, c⟩).2
      obtain ⟨y, hy⟩ := ht_sink
      -- `t = mapCell C₁.inr y`; `mapCell p₁ t = mapCell p₂ (mapCell C₂.inl y)`.
      have hcross : mapCell p₁ t = mapCell p₂ (mapCell C₂.inl y) := by
        rw [← hy]; exact comp_glue_cell C₁ C₂ y
      -- `mapCell C₂.inl y ∈ srcImage C₂`; `C₂` spanning gives a sink.
      obtain ⟨sink, hsink_sink, hsink_reach⟩ := (h₂ (mapCell C₂.inl y)).2
      refine ⟨mapCell p₂ sink, sinkMem sink hsink_sink, ?_⟩
      -- `w = p₁(c) → p₁(t) = p₂(C₂.inl y) → p₂(sink)`.
      rw [← hwc]
      exact (ht_reach.map p₁).trans (hcross ▸ hsink_reach.map p₂)
  · -- `w = p₂(c)`.
    have hwc : mapCell p₂ (⟨wn, c⟩ : C₂.mid.TotalCell) = (⟨wn, wc⟩ : (C₁.comp C₂).mid.TotalCell) :=
      congrArg (Sigma.mk wn) hc
    refine ⟨?_, ?_⟩
    · -- src side: `C₂` spanning gives a src in `srcImage C₂ = Y`, cross to `C₁`.
      obtain ⟨s, hs_src, hs_reach⟩ := (h₂ ⟨wn, c⟩).1
      obtain ⟨y, hy⟩ := hs_src
      -- `s = mapCell C₂.inl y`; `mapCell p₂ s = mapCell p₁ (mapCell C₁.inr y)`.
      have hcross : mapCell p₁ (mapCell C₁.inr y) = mapCell p₂ s := by
        rw [← hy]; exact comp_glue_cell C₁ C₂ y
      -- `mapCell C₁.inr y ∈ sinkImage C₁`; `C₁` spanning gives a source.
      obtain ⟨src, hsrc_src, hsrc_reach⟩ := (h₁ (mapCell C₁.inr y)).1
      refine ⟨mapCell p₁ src, srcMem src hsrc_src, ?_⟩
      -- `p₁(src) → p₁(C₁.inr y) = p₂(s) → p₂(c) = w`.
      rw [← hwc]
      exact (hsrc_reach.map p₁).trans (hcross ▸ hs_reach.map p₂)
    · -- sink side: directly from `C₂` spanning of `c`.
      obtain ⟨t, ht_sink, ht_reach⟩ := (h₂ ⟨wn, c⟩).2
      refine ⟨mapCell p₂ t, sinkMem t ht_sink, ?_⟩
      rw [← hwc]; exact ht_reach.map p₂

/-! ### Closed is preserved (unconditional)

A minimal vertex `v` of the pushout `W` is a `p₁`- or `p₂`-cell.  When `v = p₁(a)`,
`a` is minimal in `C₁.mid` (`isMinimalVertex_of_mono`), so `C₁.Closed` puts `a` in
`srcImage C₁`, whence `v ∈ comp.srcImage`.  When `v` is *purely* `p₂(b)`, `b` is
minimal in `C₂.mid`, so `C₂.Closed` puts `b` in `srcImage C₂ = ` the glued `Y`;
but a glued-`Y` cell is also a `p₁`-cell (`comp_glue_cell`), so `v` reduces to the
first case.  Maximal vertices and the sink side are dual.  No extra hypothesis is
needed beyond `Closed` of the two pieces. -/

/-- The composite source image, in `p₁`-block-image form, contains the `p₁`-image of
any `srcImage C₁` cell. -/
private theorem comp_srcImage_p₁ (C₁ : Cospan X Y) (C₂ : Cospan Y Z)
    {a : C₁.mid.TotalCell} (ha : srcImage C₁ a) :
    srcImage (C₁.comp C₂) (mapCell (pushout.inl C₁.inr C₂.inl) a) := by
  rw [comp_srcImage_eq]; exact ⟨a, ha, rfl⟩

/-- The composite sink image, in `p₂`-block-image form, contains the `p₂`-image of
any `sinkImage C₂` cell. -/
private theorem comp_sinkImage_p₂ (C₁ : Cospan X Y) (C₂ : Cospan Y Z)
    {b : C₂.mid.TotalCell} (hb : sinkImage C₂ b) :
    sinkImage (C₁.comp C₂) (mapCell (pushout.inr C₁.inr C₂.inl) b) := by
  rw [comp_sinkImage_eq]; exact ⟨b, hb, rfl⟩

/-- **Vertex-level glue.**  At level `0`, the `C₁`-block image `p₁ ∘ C₁.inr` of a
`Y`-vertex equals its `C₂`-block image `p₂ ∘ C₂.inl` — the pushout square commutes on
vertices.  (The cell-level `comp_glue_cell`, read off at level `0`.) -/
theorem comp_glue_vertex (C₁ : Cospan X Y) (C₂ : Cospan Y Z) (y : Y.cells 0) :
    (pushout.inl C₁.inr C₂.inl)⟪0⟫ (C₁.inr⟪0⟫ y)
      = (pushout.inr C₁.inr C₂.inl)⟪0⟫ (C₂.inl⟪0⟫ y) := by
  have h := comp_glue_cell C₁ C₂ (⟨0, y⟩ : Y.TotalCell)
  rw [show mapCell C₁.inr (⟨0, y⟩ : Y.TotalCell)
        = (⟨0, C₁.inr⟪0⟫ y⟩ : C₁.mid.TotalCell) from mapCell_mk _ _ _,
     show mapCell C₂.inl (⟨0, y⟩ : Y.TotalCell)
        = (⟨0, C₂.inl⟪0⟫ y⟩ : C₂.mid.TotalCell) from mapCell_mk _ _ _,
     mapCell_mk, mapCell_mk] at h
  exact eq_of_heq (Sigma.mk.inj h).2

/-- **Closed is preserved by composition (unconditional).**  If `C₁ : Cospan X Y` and
`C₂ : Cospan Y Z` are both `Closed`, then so is their composite `C₁.comp C₂`. -/
theorem Closed.comp {C₁ : Cospan X Y} {C₂ : Cospan Y Z}
    (h₁ : C₁.Closed) (h₂ : C₂.Closed) : (C₁.comp C₂).Closed := by
  -- A `p₁(a)`-minimal vertex lands in the composite source image.
  have srcOfP₁ : ∀ (a : C₁.mid.cells 0),
      IsMinimalVertex (C₁.comp C₂).mid ((pushout.inl C₁.inr C₂.inl)⟪0⟫ a) →
      srcImage (C₁.comp C₂) ⟨0, (pushout.inl C₁.inr C₂.inl)⟪0⟫ a⟩ := by
    intro a hmin
    -- `a` is minimal in `C₁.mid` (mono pushforward), so `Closed` places it in src.
    have ha : srcImage C₁ ⟨0, a⟩ :=
      h₁.1 a (isMinimalVertex_of_mono (pushout.inl C₁.inr C₂.inl) rfl hmin)
    have := comp_srcImage_p₁ C₁ C₂ ha
    rwa [mapCell_mk] at this
  -- A `p₂(b)`-maximal vertex lands in the composite sink image.
  have sinkOfP₂ : ∀ (b : C₂.mid.cells 0),
      IsMaximalVertex (C₁.comp C₂).mid ((pushout.inr C₁.inr C₂.inl)⟪0⟫ b) →
      sinkImage (C₁.comp C₂) ⟨0, (pushout.inr C₁.inr C₂.inl)⟪0⟫ b⟩ := by
    intro b hmax
    have hb : sinkImage C₂ ⟨0, b⟩ :=
      h₂.2 b (isMaximalVertex_of_mono (pushout.inr C₁.inr C₂.inl) rfl hmax)
    have := comp_sinkImage_p₂ C₁ C₂ hb
    rwa [mapCell_mk] at this
  refine ⟨?_, ?_⟩
  · -- minimal vertices land in the composite source image.
    intro v hmin
    obtain ⟨a, ha⟩ | ⟨b, hb⟩ := comp_cell_cases C₁ C₂ 0 v
    · -- `v = p₁(a)`: directly.
      subst ha; exact srcOfP₁ a hmin
    · -- `v = p₂(b)`: `b` minimal in `C₂.mid`, `Closed C₂` ⟹ `b ∈ srcImage C₂ = Y`,
      -- glued vertex ⟹ `v` is a `p₁`-cell, reduce to the first case.
      subst hb
      have hbmin : IsMinimalVertex C₂.mid b :=
        isMinimalVertex_of_mono (pushout.inr C₁.inr C₂.inl) rfl hmin
      obtain ⟨x, hx⟩ := h₂.1 b hbmin
      -- `x : Y.TotalCell` with `mapCell C₂.inl x = ⟨0, b⟩`; pin `x` to level 0.
      obtain ⟨x0, rfl, hx0⟩ := mapCell_eq_sigma C₂.inl x hx
      -- `p₂(b) = p₂(C₂.inl x0) = p₁(C₁.inr x0)` (vertex glue).
      have heq0 : (pushout.inr C₁.inr C₂.inl)⟪0⟫ b
          = (pushout.inl C₁.inr C₂.inl)⟪0⟫ (C₁.inr⟪0⟫ x0) := by
        rw [← hx0, comp_glue_vertex C₁ C₂ x0]
      rw [heq0]
      refine srcOfP₁ (C₁.inr⟪0⟫ x0) ?_
      rw [← heq0]; exact hmin
  · -- maximal vertices land in the composite sink image (dual argument).
    intro v hmax
    obtain ⟨a, ha⟩ | ⟨b, hb⟩ := comp_cell_cases C₁ C₂ 0 v
    · -- `v = p₁(a)`: `a` maximal in `C₁.mid`, `Closed C₁` ⟹ `a ∈ sinkImage C₁ = Y`,
      -- glued vertex ⟹ `v` is a `p₂`-cell, reduce to the `p₂` case.
      subst ha
      have hamax : IsMaximalVertex C₁.mid a :=
        isMaximalVertex_of_mono (pushout.inl C₁.inr C₂.inl) rfl hmax
      obtain ⟨x, hx⟩ := h₁.2 a hamax
      obtain ⟨x0, rfl, hx0⟩ := mapCell_eq_sigma C₁.inr x hx
      -- `p₁(a) = p₁(C₁.inr x0) = p₂(C₂.inl x0)` (vertex glue).
      have heq0 : (pushout.inl C₁.inr C₂.inl)⟪0⟫ a
          = (pushout.inr C₁.inr C₂.inl)⟪0⟫ (C₂.inl⟪0⟫ x0) := by
        rw [← hx0, ← comp_glue_vertex C₁ C₂ x0]
      rw [heq0]
      refine sinkOfP₂ (C₂.inl⟪0⟫ x0) ?_
      rw [← heq0]; exact hmax
    · -- `v = p₂(b)`: directly.
      subst hb; exact sinkOfP₂ b hmax

end Cospan

end PrecubicalSet
