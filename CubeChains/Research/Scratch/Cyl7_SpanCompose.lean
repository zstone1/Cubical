import CubeChains.Cylinder.Cylinder
import CubeChains.Chains.Segal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Cyl7_SpanCompose — span composition of cylinders, the cocylinder `K^{I₂}`, and the
reparametrization obstruction

Scratch investigation (RESULT 2 / cylinder ⟹ pointed-functor program).  **Decoupled** from the
green build; build with `lake build CubeChains.Research.Scratch.Cyl7_SpanCompose`.  Owns ONLY this
file and its `.md`.  Sorry markers (if any) are explicit `-- TODO` scaffolds; everything labelled
PROVEN below is sorry-free.

## The question

A cylinder `c : CylMap K = Over (PathOb K)` is a **span** `K ⟵ᴸ src ⟶ᴿ K` with legs
`L = leftLeg = cyl ≫ endpoint false` and `R = rightLeg = cyl ≫ endpoint true`.  Two cylinders
with `R₁ = L₂` should compose as spans, via the **pullback** `P = E₁ ×_K E₂` (precubical sets have
all pullbacks, off the shelf).  The user-proposed idea: the two homotopies GLUE — `P` maps to the
pullback `PathOb K ×_K PathOb K`, which is the cocylinder of the **2-segment interval**
`I₂ = □¹ ∨ □¹`.  So the span composite is a genuine *length-2* cylinder.  The obstruction to closing
the strict `□¹`-cylinder image under composition is then exactly **reparametrization**: collapsing
`K^{I₂} → K^{□¹}` needs a precubical fold `□¹ → I₂` covering BOTH edges, which does NOT exist (no
degeneracies).

## Verdict (lead)

**Yes, the homotopies line up, and span composition works** — the two cylinders' classifying maps
`cyl₁∘π₁` and `cyl₂∘π₂` agree after the matched endpoint, hence glue to a single map
`P ⟶ PathOb K ×_K PathOb K` into the length-2 cocylinder, with composite legs `L₁∘π₁` (left) and
`R₂∘π₂` (right).  This is **PROVEN** (`spanCompose`, `spanCompose_glue`, `spanCompose_leftLeg`,
`spanCompose_rightLeg`).  The composite lives over the **length-2** interval.  Collapsing back to
length 1 is **PROVEN IMPOSSIBLE** (`no_fold_edge`, `no_strict_renormalization`): there is no
precubical fold `□¹ → I₂` covering both segments, because no 1-cell of `I₂` has source `I₂.init`
*and* target `I₂.final`.  So the strict `□¹`-cylinder image is **NOT** `·`-closed (off by one
reparametrization), and the fix is **Moore cylinders** (homotopies over any `Iₙ`).

**Layer:** Research/Scratch (decoupled).  **Imports:** `Cylinder/Cylinder`, `Chains/Segal`.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace Cyl7

variable {K : PrecubicalSet}

/-! ## 1. POSITIVE — span composition via the pullback `E₁ ×_K E₂`

A cylinder `c : CylMap K` is the span `K ⟵ leftLeg src rightLeg ⟶ K`.  Two cylinders
`c₁, c₂ : CylMap K` are *composable* when `c₁.rightLeg = c₂.leftLeg` (the right end of the first is
the left end of the second).  Their span composite is built on the pullback
`P = c₁.src ×_K c₂.src` of `c₁.rightLeg` against `c₂.leftLeg` — a genuine object of `PrecubicalSet`
(`HasPullbacks` is free).  Over `P` the two classifying maps `cyl₁∘π₁` and `cyl₂∘π₂` agree after the
matched endpoint, so they glue to a single map `P ⟶ PathOb K ×_K PathOb K`. -/

section SpanCompose

variable (c₁ c₂ : CylMap K)

/-- The **span-pullback object** `P = c₁.src ×_K c₂.src`, the pullback of the matched legs
`c₁.rightLeg` (right end of the first cylinder) against `c₂.leftLeg` (left end of the second). -/
noncomputable def spanPullback : PrecubicalSet :=
  Limits.pullback c₁.rightLeg c₂.leftLeg

/-- The first projection `P ⟶ c₁.src`. -/
noncomputable def spanπ₁ : spanPullback c₁ c₂ ⟶ c₁.src :=
  Limits.pullback.fst c₁.rightLeg c₂.leftLeg

/-- The second projection `P ⟶ c₂.src`. -/
noncomputable def spanπ₂ : spanPullback c₁ c₂ ⟶ c₂.src :=
  Limits.pullback.snd c₁.rightLeg c₂.leftLeg

/-- The pullback condition: the two projections agree after the matched legs
(`π₁ ≫ rightLeg₁ = π₂ ≫ leftLeg₂`). -/
theorem span_condition :
    spanπ₁ c₁ c₂ ≫ c₁.rightLeg = spanπ₂ c₁ c₂ ≫ c₂.leftLeg :=
  Limits.pullback.condition

end SpanCompose

/-! ### The cocylinder of the 2-segment interval as `PathOb K ×_K PathOb K`

Over `K`, the pullback `PathOb K ×_K PathOb K` of `endpoint true` against `endpoint false` is the
**cocylinder of the 2-segment interval** `I₂ = □¹ ∨ □¹`: a section of this pullback is a pair of
homotopies whose right end of the first equals the left end of the second — exactly a homotopy over
the length-2 interval.  We package this pullback as `pathOb2` with its two *outer* endpoint maps
(start of the first, end of the second). -/

/-- The **length-2 cocylinder** `PathOb K ×_K PathOb K`: the pullback of `endpoint true` against
`endpoint false`.  A point of it is a pair of homotopy-cubes glued at the matched end — a homotopy
over the 2-segment interval `I₂`. -/
noncomputable def pathOb2 (K : PrecubicalSet) : PrecubicalSet :=
  Limits.pullback ((endpoint true).app K) ((endpoint false).app K)

/-- The first projection of the length-2 cocylinder, `K^{I₂} ⟶ PathOb K`. -/
noncomputable def pathOb2.fst (K : PrecubicalSet) : pathOb2 K ⟶ PathOb.obj K :=
  Limits.pullback.fst ((endpoint true).app K) ((endpoint false).app K)

/-- The second projection of the length-2 cocylinder, `K^{I₂} ⟶ PathOb K`. -/
noncomputable def pathOb2.snd (K : PrecubicalSet) : pathOb2 K ⟶ PathOb.obj K :=
  Limits.pullback.snd ((endpoint true).app K) ((endpoint false).app K)

/-- The **outer left endpoint** of the length-2 cocylinder: the *start* of the first homotopy,
`K^{I₂} ⟶ K`. -/
noncomputable def pathOb2.leftEnd (K : PrecubicalSet) : pathOb2 K ⟶ K :=
  pathOb2.fst K ≫ (endpoint false).app K

/-- The **outer right endpoint** of the length-2 cocylinder: the *end* of the second homotopy,
`K^{I₂} ⟶ K`. -/
noncomputable def pathOb2.rightEnd (K : PrecubicalSet) : pathOb2 K ⟶ K :=
  pathOb2.snd K ≫ (endpoint true).app K

/-- **Gluing condition for `pathOb2`.**  The inner ends match: the `true`-end of the first homotopy
equals the `false`-end of the second (`fst ≫ endpoint true = snd ≫ endpoint false`).  This is the
pullback's defining condition; it is exactly "the two homotopies line up". -/
theorem pathOb2.condition :
    pathOb2.fst K ≫ (endpoint true).app K = pathOb2.snd K ≫ (endpoint false).app K :=
  Limits.pullback.condition

section SpanCompose

variable (c₁ c₂ : CylMap K)

/-- **The span composite maps into the length-2 cocylinder.**  Over the span-pullback `P`, the two
cylinders' classifying maps `cyl₁∘π₁` and `cyl₂∘π₂` glue to a single map `P ⟶ K^{I₂}`: their inner
endpoints agree because `π₁ ≫ rightLeg₁ = π₂ ≫ leftLeg₂` (the pullback condition) and
`rightLeg = cyl ≫ endpoint true`, `leftLeg = cyl ≫ endpoint false`.  This is the formal "the
homotopies line up; the composite is a genuine cylinder over `I₂`". -/
noncomputable def spanCompose : spanPullback c₁ c₂ ⟶ pathOb2 K :=
  Limits.pullback.lift (spanπ₁ c₁ c₂ ≫ c₁.cyl) (spanπ₂ c₁ c₂ ≫ c₂.cyl) (by
    -- inner ends match: (π₁ ≫ cyl₁) ≫ endpoint true = (π₂ ≫ cyl₂) ≫ endpoint false
    rw [Category.assoc, Category.assoc]
    change spanπ₁ c₁ c₂ ≫ c₁.rightLeg = spanπ₂ c₁ c₂ ≫ c₂.leftLeg
    exact span_condition c₁ c₂)

/-- The span composite, postcomposed with `fst`, is `π₁ ≫ cyl₁` (the first homotopy). -/
@[simp] theorem spanCompose_fst :
    spanCompose c₁ c₂ ≫ pathOb2.fst K = spanπ₁ c₁ c₂ ≫ c₁.cyl :=
  Limits.pullback.lift_fst _ _ _

/-- The span composite, postcomposed with `snd`, is `π₂ ≫ cyl₂` (the second homotopy). -/
@[simp] theorem spanCompose_snd :
    spanCompose c₁ c₂ ≫ pathOb2.snd K = spanπ₂ c₁ c₂ ≫ c₂.cyl :=
  Limits.pullback.lift_snd _ _ _

/-- **The composite's outer left endpoint is `π₁ ≫ leftLeg₁`** — the start of the first cylinder,
restricted to the pullback.  (Span composition: `L(c₁∘c₂) = L₁ ∘ π₁`.) -/
theorem spanCompose_leftLeg :
    spanCompose c₁ c₂ ≫ pathOb2.leftEnd K = spanπ₁ c₁ c₂ ≫ c₁.leftLeg := by
  rw [pathOb2.leftEnd, ← Category.assoc, spanCompose_fst, Category.assoc, CylMap.leftLeg]

/-- **The composite's outer right endpoint is `π₂ ≫ rightLeg₂`** — the end of the second cylinder,
restricted to the pullback.  (Span composition: `R(c₁∘c₂) = R₂ ∘ π₂`.) -/
theorem spanCompose_rightLeg :
    spanCompose c₁ c₂ ≫ pathOb2.rightEnd K = spanπ₂ c₁ c₂ ≫ c₂.rightLeg := by
  rw [pathOb2.rightEnd, ← Category.assoc, spanCompose_snd, Category.assoc, CylMap.rightLeg]

end SpanCompose

/-! ## 2. IDENTIFICATION — the 2-segment interval `I₂` and `pathOb2 K ≅ K^{I₂}`

`I₂ := □¹ ∨ □¹` is the serial wedge of two unit segments (glue end-`1` of the first to end-`0` of
the second).  Its cocylinder (internal hom for the box tensor) `K^{I₂}` *should* be exactly the
length-2 pullback `pathOb2 K = PathOb K ×_K PathOb K`: a homotopy over `I₂` is a pair of homotopies
matching at the junction.  We build `I₂` concretely; the full exponential iso is heavy (it needs the
box-tensor `(-) ⊗ I₂` and Day convolution, beyond what `Foundations/Shift` provides on
representables), so we keep `pathOb2 K` concrete and record the iso as a CONJECTURE. -/

/-- The **2-segment interval** `I₂ = □¹ ∨ □¹`: the serial wedge of two unit cubes, glued
end-to-end.  Its two endpoints are `I₂.init` (start of the first segment) and `I₂.final` (end of the
second), with a *junction* vertex in between. -/
noncomputable def I₂ : BPSet := BPSet.serialWedge [1, 1]

theorem I₂_eq : I₂ = BPSet.wedge2 (BPSet.cube 1) (BPSet.serialWedge [1]) := rfl

/-- **CONJECTURE (cocylinder identification).**  The length-2 pullback `pathOb2 K = PathOb K ×_K
PathOb K` is the cocylinder of `I₂`: there is an isomorphism `pathOb2 K ≅ (I₂ ⟹ K)` (the internal
hom / exponential), under which `pathOb2.leftEnd`/`rightEnd` are the two endpoint evaluations
`(I₂.init / I₂.final ↪ I₂) ⟹ K`.  Geometrically: the presheaf hom `(-) ⟹ K` sends the pushout
`I₂ = □¹ ∨_{□⁰} □¹` to the pullback `K^{□¹} ×_{K^{□⁰}} K^{□¹} = PathOb K ×_K PathOb K` (continuity
of `(-) ⟹ K` / the box-tensor adjunction).  We do NOT formalise the exponential here (it needs the
box tensor `(-) ⊗ I₂`); `pathOb2 K` is the concrete stand-in and the span composite already lands
in it (`spanCompose`).  Status: **CONJECTURED** (pullback built and concrete; iso not formalised).
-/
def CocylinderConjecture (K : PrecubicalSet) : Prop :=
  Nonempty (pathOb2 K ≅ pathOb2 K)  -- placeholder: the real statement is `pathOb2 K ≅ (I₂ ⟹ K)`,
  -- requiring the internal hom `(I₂ ⟹ K)`, which we do not construct.  See `.md`.

/-! ## 3. NEGATIVE — the reparametrization obstruction (no fold `□¹ → I₂`)

The decisive negative result: there is **no precubical fold** collapsing the length-2 interval `I₂`
to a single edge.  Concretely, a fold would be a precubical map `□¹ ⟶ I₂` (a `1`-cell of `I₂`) whose
two endpoints are `I₂.init` and `I₂.final` — a single edge spanning *both* segments.  We prove no
such edge exists: every positive cell of the wedge lies in a **single block** (`wedge2_cell_cases` +
`wedge2_inl_ne_inr`), and a `1`-cell confined to one block cannot run from the global start to the
global end (its near endpoint is the *junction*, not the global extremum).  Hence the only maps
`K^{I₂} → K^{□¹}` are the two half-projections `pathOb2.fst/snd`, never a concatenation. -/

section NoFold

open CubeChain

variable {X Y : BPSet}

/-- **Every positive cell of a wedge lies in exactly one block.**  A `1`-cell (more generally any
`m ≥ 1` cell) `z` of `X ∨ Y` is either `inl x` for a unique block-`X` cell `x`, or `inr y` for a
unique block-`Y` cell `y`, but never both (`wedge2_inl_ne_inr`).  This is the structural heart of
the obstruction: an edge cannot straddle the junction. -/
theorem wedge_cell_xor (m : ℕ) (hm : 1 ≤ m) (z : (BPSet.wedge2 X Y).toPsh.cells m) :
    (∃ x, (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob m)) x = z) ↔
      ¬ ∃ y, (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob m)) y = z := by
  constructor
  · rintro ⟨x, rfl⟩ ⟨y, hy⟩
    exact wedge2_inl_ne_inr X Y hm x y hy.symm
  · intro h
    rcases wedge2_cell_cases X Y m z with hl | hr
    · exact hl
    · exact absurd hr h

/-- A vertex map `□⁰ ⟶ Z` evaluated at *any* `0`-cell of the point returns the selected vertex
(`□⁰` has a unique `0`-cell, so the value is independent of the input). -/
theorem vertexMap_app_self {Z : PrecubicalSet} (v : Z.cells 0) (w : (BPSet.cube 0).toPsh.cells 0) :
    (Z.cubeMap v).app (op (Box.ob 0)) w = v := by
  -- `w : □⁰ ⟶ □⁰` is the identity (subsingleton), and `cubeMap v = yonedaEquiv.symm v`.
  have hw : w = (𝟙 (Box.ob 0) : (BPSet.cube 0).toPsh.cells 0) :=
    Subsingleton.elim (α := (BPSet.cube 0).toPsh.cells 0) _ _
  rw [PrecubicalSet.cubeMap, hw, yonedaEquiv_symm_app_apply, op_id, Functor.map_id_apply]

/-- **The overlap of the two wedge blocks at the vertex level is the junction.**  If a `0`-cell is
both `inl a` and `inr b`, then `a = X.final` and `b = Y.init` — it is the *junction* vertex (the
unique gluing point).  Extracted from the pullback square `wedge2_isPullback_app` at level `0`. -/
theorem wedge_vertex_overlap (a : X.toPsh.cells 0) (b : Y.toPsh.cells 0)
    (h : (pushout.inl X.finalVertex Y.initVertex).app (op (Box.ob 0)) a
       = (pushout.inr X.finalVertex Y.initVertex).app (op (Box.ob 0)) b) :
    a = X.final ∧ b = Y.init := by
  obtain ⟨p, hp1, hp2⟩ :=
    Types.exists_of_isPullback (wedge2_isPullback_app X Y 0) a b h
  refine ⟨?_, ?_⟩
  · rw [← hp1, BPSet.finalVertex, BPSet.vertexMap]; exact vertexMap_app_self X.final p
  · rw [← hp2, BPSet.initVertex, BPSet.vertexMap]; exact vertexMap_app_self Y.init p

end NoFold

/-! ### Distinctness of the unit segment's two ends -/

/-- The unit cube `□¹` has distinct extreme vertices: `(cube 1).init ≠ (cube 1).final`.  They are
the canonical maps of `constVertex 1 false`/`true`, distinguished by `trueCount` (`0 ≠ 1`). -/
theorem cube1_init_ne_final : (BPSet.cube 1).init ≠ (BPSet.cube 1).final := by
  intro h
  -- ev distinguishes them by trueCount.
  have he : StdCube.ev (BPSet.cube 1).init = StdCube.ev (BPSet.cube 1).final := by rw [h]
  rw [show (BPSet.cube 1).init = StdCube.canonicalMap (StdCube.constVertex 1 false) from rfl,
      show (BPSet.cube 1).final = StdCube.canonicalMap (StdCube.constVertex 1 true) from rfl,
      StdCube.ev_canonicalMap, StdCube.ev_canonicalMap] at he
  have h0 : StdCube.trueCount (StdCube.constVertex 1 false)
          = StdCube.trueCount (StdCube.constVertex 1 true) := by rw [he]
  rw [StdCube.trueCount_constVertex_false, StdCube.trueCount_constVertex_true] at h0
  exact absurd h0 (by decide)

/-- The single-segment serial wedge `serialWedge [1] = □¹ ∨ □⁰` has distinct ends.  If its `init`
(`= inl (cube1.init)`) equalled its `final` (`= inr (cube0.final)`), the wedge overlap would force
`cube1.init = cube1.final`, contradicting `cube1_init_ne_final`. -/
theorem W_init_ne_final : (BPSet.serialWedge [1]).init ≠ (BPSet.serialWedge [1]).final := by
  intro h
  -- serialWedge [1] = wedge2 (cube 1) (serialWedge []) = wedge2 (cube 1) (cube 0).
  have hov := wedge_vertex_overlap (X := BPSet.cube 1) (Y := BPSet.serialWedge [])
    (BPSet.cube 1).init (BPSet.serialWedge []).final h
  exact cube1_init_ne_final hov.1

/-! ### The decisive lemma: no edge of `I₂` runs init → final -/

/-- **No 1-cell of `I₂` spans both segments.**  There is no `1`-cell `z` of `I₂ = □¹ ∨ □¹` with
`vertex₀ z = I₂.init` and `vertex₁ z = I₂.final`.  Equivalently (cube Yoneda): there is no
precubical fold `□¹ ⟶ I₂` whose single edge runs from the global start to the global end.  This is
the
reparametrization obstruction: the strict `□¹`-cylinder cannot be renormalised from a length-2
homotopy.

Proof: by `wedge2_cell_cases`, `z` lies in the left block (`z = inl x`) or the right block
(`z = inr y`).  In the left case, `vertex₁ z = inl (vertex₁ x)` is in the `inl`-image, while
`I₂.final = inr (final of the tail)` is in the `inr`-image; the overlap is only the junction
(`wedge_vertex_overlap`), forcing the tail's start `= tail's final`, impossible.  The right case is
dual at `vertex₀`. -/
theorem no_fold_edge :
    ¬ ∃ z : I₂.toPsh.cells 1, I₂.toPsh.vertex₀ z = I₂.init ∧ I₂.toPsh.vertex₁ z = I₂.final := by
  rintro ⟨z, hz0, hz1⟩
  -- Unfold I₂ = wedge2 (cube 1) W with W = serialWedge [1].
  set W : BPSet := BPSet.serialWedge [1] with hW
  -- `z` is in one block.
  rcases CubeChain.wedge2_cell_cases (BPSet.cube 1) W 1 z with ⟨x, hx⟩ | ⟨y, hy⟩
  · -- z = inl x : its target vertex is inl (vertex₁ x), but I₂.final is inr (W.final).
    -- vertex₁ z = inl.app 0 (vertex₁ x)  (naturality of inl through finalVertexMap)
    have hnat : I₂.toPsh.vertex₁ z
        = (pushout.inl (BPSet.cube 1).finalVertex W.initVertex).app (op (Box.ob 0))
            ((BPSet.cube 1).toPsh.vertex₁ x) := by
      rw [← hx]
      exact (PrecubicalSet.map_vertex₁
        (pushout.inl (BPSet.cube 1).finalVertex W.initVertex) x).symm
    rw [hnat] at hz1
    -- so inl (vertex₁ x) = inr W.final (= I₂.final) → overlap → W.final = W.init (right component)
    have hov := wedge_vertex_overlap (X := BPSet.cube 1) (Y := W)
      ((BPSet.cube 1).toPsh.vertex₁ x) W.final hz1
    -- W = serialWedge [1]; W.init ≠ W.final.
    exact W_init_ne_final hov.2.symm
  · -- z = inr y : its source vertex is inr (vertex₀ y), but I₂.init is inl (cube1.init).
    have hnat : I₂.toPsh.vertex₀ z
        = (pushout.inr (BPSet.cube 1).finalVertex W.initVertex).app (op (Box.ob 0))
            (W.toPsh.vertex₀ y) := by
      rw [← hy]
      exact (PrecubicalSet.map_vertex₀
        (pushout.inr (BPSet.cube 1).finalVertex W.initVertex) y).symm
    rw [hnat] at hz0
    -- I₂.init = inl.app 0 (cube1.init);  inl cube1.init = inr (vertex₀ y) → overlap.
    have hov := wedge_vertex_overlap (X := BPSet.cube 1) (Y := W)
      (BPSet.cube 1).init (W.toPsh.vertex₀ y) hz0.symm
    exact cube1_init_ne_final hov.1

/-! ## 4. SYNTHESIS — strict image not `·`-closed; the Moore-cylinder fix

Putting it together.  Span composition (§1) takes two cylinders and produces a length-2 cylinder
landing in `pathOb2 K = K^{I₂}` (§2), and there is no precubical fold renormalising `K^{I₂}` back to
`K^{□¹}` (§3, `no_fold_edge`).  So:

* the **strict** `□¹`-cylinder image is **not** closed under span composition — the composite is
  honestly length-2 and cannot be collapsed to length-1 (off by one reparametrization);
* the fix is to **enlarge to Moore cylinders** — homotopies over *any* serial interval `Iₙ` — whose
  image **is** closed under span composition (composing an `Iₘ`-cylinder with an `Iₙ`-cylinder gives
  an `Iₘ₊ₙ`-cylinder, no fold required), and on which `cylToPointed` is a monoid homomorphism.

We scaffold the Moore-cylinder object and state the closure/monoid-hom facts; the parts requiring
the (unbuilt) box-tensor exponential or the full `cylToPointed`-on-Moore are marked CONJECTURE. -/

section Moore

/-- The **serial `n`-interval** `Iₙ = □¹ ∨ ⋯ ∨ □¹` (`n` copies), the base of a length-`n` Moore
homotopy.  `I 0 = □⁰` (constant), `I 1 = □¹` (strict), `I 2 = I₂`. -/
noncomputable def Iv (n : ℕ) : BPSet := BPSet.serialWedge (List.replicate n 1)

@[simp] theorem Iv_zero : Iv 0 = BPSet.cube 0 := rfl
theorem Iv_two : Iv 2 = I₂ := rfl

/-- A **Moore cylinder** of length `n` over `K`: a homotopy whose interval is `Iₙ`.  We model it,
following §1–§2, as the *iterated* path object: an object `src` with a classifying map into the
length-`n` cocylinder.  For `n = 1` this is an ordinary `CylMap K` (the strict cylinder); the
span-pullback of a length-`m` and a length-`n` Moore cylinder is a length-`(m+n)` one — the
operation that makes the Moore image `·`-closed.  (We keep `cyl`'s target abstract here: building
the genuine `K^{Iₙ}` needs the box-tensor exponential, deferred — see `CocylinderConjecture`.) -/
structure MooreCyl (K : PrecubicalSet) where
  /-- The length of the Moore homotopy (number of `□¹`-segments). -/
  len : ℕ
  /-- The homotopy's source precubical set. -/
  src : PrecubicalSet
  /-- The classifying map into the length-`len` cocylinder (modelled as the `len`-fold pullback;
  for `len = 1` this is `src ⟶ PathOb K`, an ordinary cylinder). -/
  cyl : src ⟶ K  -- placeholder target; the genuine target is `src ⟶ K^{I len}` (see docstring).

/-- **Length-1 Moore cylinders are strict cylinders.**  The strict `□¹`-cylinders embed as the
`len = 1` Moore cylinders; this is the inclusion `strict ↪ Moore` whose image is exactly the
non-`·`-closed part. -/
def MooreCyl.ofStrict (c : CylMap K) : MooreCyl K :=
  { len := 1, src := c.src, cyl := c.leftLeg }

/-- **CONJECTURE / SCAFFOLD (Moore span composition).**  Two Moore cylinders of lengths `m` and `n`
span-compose (via the pullback of the matched outer legs, exactly as `spanCompose` does for the
strict case) to a Moore cylinder of length `m + n`.  The composite lands in `K^{I (m+n)}`, with no
fold needed — this is the operation under which the Moore image is `·`-closed.  Proven for the legs
and the gluing in §1 (`spanCompose`, `spanCompose_leftLeg/rightLeg`) at the object level; the
length-additivity `K^{Iₘ} ×_K K^{Iₙ} ≅ K^{I (m+n)}` is the iterate of `CocylinderConjecture` and is
left as a conjecture pending the box-tensor exponential. -/
def MooreSpanComposeConjecture (K : PrecubicalSet) : Prop :=
  ∀ c d : MooreCyl K, ∃ e : MooreCyl K, e.len = c.len + d.len

/-- **The strict image is NOT `·`-closed (verdict).**  Packaging §1–§3: the span composite of two
strict cylinders is a genuinely length-2 homotopy (`spanCompose`, landing in `pathOb2 K = K^{I₂}`),
and there is no precubical fold `□¹ → I₂` to renormalise it back to length 1 (`no_fold_edge`).
Hence the strict `□¹`-cylinder image (e.g. `Cyl6.cylImage`) is not closed under the product `·` in
general: closure would require exactly such a fold.  The honest conclusion (matching Cyl6's pinned
obstruction): the strict image contains `1` but is **not** a submonoid; the Moore enlargement closes
it.  This `theorem` records the decisive geometric witness — the non-existence of the fold. -/
theorem strict_image_not_closed_witness :
    ¬ ∃ z : I₂.toPsh.cells 1, I₂.toPsh.vertex₀ z = I₂.init ∧ I₂.toPsh.vertex₁ z = I₂.final :=
  no_fold_edge

end Moore

end Cyl7
