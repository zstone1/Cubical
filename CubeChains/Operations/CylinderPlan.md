# Plan: cylinder maps ⇒ pointed functors, and the adjunction

Goal: build the functor **{cylinder maps to K} ⥤ {pointed endofunctors of the d-path
homotopy theory of K}** (piece 1), then the adjunction (piece 2). Piece 3
(`Hom(K,K) ↪ cylinder maps`) is deferred.

This file is a **spec**: precise definitions and the main lemma *statements*, no
proofs. Agents implement modules in dependency order (§6). Policy: no `sorry`
outside `Conjectures.lean`; if a sub-lemma must be staged, it goes there.

---

## ⭐ REVISED STRATEGY (2026-06-18): endpoint-indexed `Ch'` + Segal monoidality

**Supersedes the `ChP` fence below (§0.1, §2's `toTransf` note).**  The basepoint-free
`ChP` was chosen for "more morphisms", but it pays for it: `ChP` has **no decomposition
of chains over a wedge**, so the comparison `toTransf` had to be hand-built as a
multi-block staircase fence.  The fix is to use the **bi-pointed** chain category — the
real `Ch` of Ziemiański — but *indexed by arbitrary endpoint vertices* so that local,
basepoint-non-preserving edits still fit.

### The three observations driving the pivot

1. **`Ch` is strong monoidal `(BPSet, ∨, □⁰) → (Cat, ×, 𝟙)`** — the **Segal property**:
   ```
   Ch(X ∨ Y) ≅ Ch X × Ch Y,        Ch(□⁰) ≅ 𝟙,
   Ch(serialWedge [d₁,…,dₘ]) ≅ ∏ᵢ Ch(cube dᵢ).
   ```
   A full chain `init → final` is *forced* through the junction vertex `v` of `X ∨_v Y`
   (the only bridge), so it splits canonically as `(init→v in X) ⊕ (v→final in Y)`; cubes
   never straddle `v`, so refinements split too.  This is **exactly the decomposition
   `ChP` lacks** (partial chains don't split).  The associator/unitors are the already-built
   `wedge2Assoc` / `wedge2Cube0Iso`.

2. **Endpoint-indexing keeps locality.**  Global basepoint-preservation is too rigid for
   "edit one part of `K`".  But a *local* edit respects its own **interface** `(s,t)`
   (the entry/exit vertices of the edited region) even when it ignores `init/final`.  So
   index chains by endpoints:
   ```
   Ch' (K : PrecubicalSet) (a b : K.cells 0) := ChainCat.Obj (⟨K, a, b⟩ : BPSet)
   ```
   Then `Ch K = Ch' K.init K.final` (defeq up to BPSet η), and **on objects**
   `ChP K = ⊔_{a,b} Ch' a b K` (`Ch' a b` is the endpoint-preserving subcategory of the
   fiber; `ChP` additionally has endpoint-*changing* sub-chain inclusions, recoverable
   later — so "`ChP` ≈ ∪ Ch'" holds for objects, and `ChP` is the richer total category).
   A local edit is an operation on `Ch' s t`, **promoted** to `Ch' init final` by Segal
   whiskering `Ch' init s × Ch' s t × Ch' t final → Ch' init final` (RefineObj-free; the
   "edit one part" is whiskering by the fixed context, identity outside the patch).

3. **Reuse, don't rebuild.**  `ChainCat`/`Refine`/`Correspondence`/`Slice`/`liftToCh` are
   all stated for `{K : BPSet}`.  Re-basepointing is just `⟨K, a, b⟩`, so **step 2
   ("generalize Ch to Ch' a b") is almost free** — the API already applies to any
   basepoints.  The genuinely new content is the Segal iso (1) and reworking the cylinder
   over `Ch'`.

### The 4-step refactor (the user's plan)

1. **`Ch'` endpoint-indexed** (`Chains/Endpoints.lean`): `Ch'`, `BPSet`-rebasing,
   `Ch'.pushforward` for interface-preserving maps, `Ch K = Ch' init final`, the
   `ChP`-objects-union note.  *Mostly reuse of `ChainCat`.*
2. **Segal monoidality** (`Chains/Segal.lean`): the keystone iso (1) — `serialWedge`
   append iso, the split/concat functors, `Ch(X∨Y) ≌ Ch X × Ch Y`, the unit `Ch □⁰ ≌ 𝟙`,
   and the n-ary `Ch(serialWedge dims) ≌ ∏ Ch(cube dᵢ)`.
3. **Cylinder over `Ch'`** (revise `Operations/Cylinder.lean`): bi-point `PathOb`/cylinder
   **rel the interface** so the legs `ℓ,r : E → K` are `BPSet` maps `⟨E,s_E,t_E⟩ →
   ⟨K,s,t⟩`; replace `ChP` by `Ch'` throughout (`DPathGrpd`, `Lgrpd`/`Rgrpd`, `CylMapWeq`).
   Most prism infra (`cylTranspose`, `coface_prism`, `prism_precomp`, `singleBlockComp`,
   `emptyBlockComp`, `prism_vertex₀/₁`) ports verbatim.
4. **`toTransf` via monoidality** (replaces the staircase fence): at a chain
   `a = (a₁,…,aₘ) ∈ ∏ᵢ Ch(cube dᵢ)`, `θ_a` is the **forced interchange composite** of the
   per-block single-cube homotopies (`singleBlockComp`), with junction level-mismatches
   bridged by the vertical edge (`emptyBlockComp`).  **Naturality reduces to per-factor
   (single cube)** — `prism_precomp`/`coface_prism` already supply it.  Recursion on the
   factor list; no `P_j`/`R_j` indexing.

### Why this is strictly better

The Segal product turns the **vertex-gluing/concatenation bookkeeping** (the old
`wedgeDescP`/`concatMap`/`P_j` machinery) into off-the-shelf product algebra, and makes
**naturality** per-factor instead of a global chase.  The only irreducible residue — the
single-block lift + the vertical edge at level-mismatched junctions — is `K`-side
(the prism is edge-glued because `(-)⊗□¹` is a left adjoint) and is **already built**.
"The 1-cell forces the n-cell" is literally the interchange law in `∏ᵢ Ch(cube dᵢ)`.

### Collision note

The legacy `ChP` fence in `Operations/Cylinder.lean` is being superseded; new foundations
(`Chains/Endpoints.lean`, `Chains/Segal.lean`) are **new files** and must not edit
`Cylinder.lean` (rewrite that in step 3, after the foundations land).

## 0. Two correctness points that shape the design

1. **The target is the groupoid reflection, not `ChP K`.** A cylinder gives, per
   chain, a *homotopy* of chains, i.e. a **zigzag** in `ChP K`, not a single
   refinement arrow. Zigzags are morphisms of `M K := FreeGroupoid (ChP.obj K)`
   (the d-path homotopy groupoid, `= ChP(K)[ChP(K)⁻¹]`). So the honest target is
   `PointedEndofunctor (M K)`. (A "pointed functor on `ChP K`" in the user's phrasing
   = a pointed endofunctor of its homotopy groupoid `M K`.)

2. **Path object via the COCYLINDER avoids the tensor.** Define `PathOb K` with
   `(PathOb K)_n = K_{n+1}` as a precomposition `Box.shift.op ⋙ K`. This is the
   internal hom for the **box tensor** (NOT the cartesian product): once a box tensor
   `⊗` with `□ᵐ ⊗ □ⁿ = □ᵐ⁺ⁿ` is defined, `(-) ⊗ □¹ ⊣ PathOb` and
   `(PathOb K)_n = Hom(□ⁿ ⊗ □¹, K) = Hom(□ⁿ⁺¹, K) = K_{n+1}`. **This is 100%
   certain** (Yoneda + `□ⁿ ⊗ □¹ = □ⁿ⁺¹`); the box tensor and this adjunction are
   deferred (§5) and not needed for pieces 1–2, which use `PathOb` directly.

## 1. Module A — `Operations/Shift.lean` (foundation; cube combinatorics CRUX)

```lean
namespace Box
/-- Append a free dimension: `shift ⟨n⟩ = ⟨n+1⟩`; on a precubical map it tensors with
the identity on the interval (the new last coordinate is free and preserved). -/
def shift : Box ⥤ Box                                         -- CRUX: on morphisms
@[simp] theorem shift_obj (n : ℕ) : shift.obj (Box.ob n) = Box.ob (n + 1)
/-- The two end-cofaces `⟨n⟩ ⟶ ⟨n+1⟩` (the `ε`-end of the appended direction),
natural in `n`. -/
def coface (ε : Bool) : 𝟭 Box ⟶ shift
end Box

/-- The path object (cocylinder): `(PathOb K)_n = K_{n+1}`. -/
def PathOb : PrecubicalSet ⥤ PrecubicalSet :=
  (whiskeringLeft _ _ _).obj Box.shift.op
@[simp] theorem PathOb_obj (K : PrecubicalSet) (n : ℕ) :
    (PathOb.obj K).obj (Opposite.op (Box.ob n)) = K.obj (Opposite.op (Box.ob (n + 1)))
/-- Endpoint evaluations `PathOb ⟹ 𝟭`, from `coface`. -/
def endpoint (ε : Bool) : PathOb ⟶ 𝟭 PrecubicalSet
```

Hard content (agent must supply): `Box.shift.map` on morphisms + `map_id`/`map_comp`
(the `StandardCube.face_face`-style `succAbove`/`Fin.snoc` combinatorics), and
`coface` naturality. Everything below this line is comparatively routine.

## 2. Module B — `Operations/Cylinder.lean` (piece 1)

```lean
open Operations
variable {K : PrecubicalSet}

/-- The d-path homotopy groupoid of `K`. -/
abbrev DPathGrpd (K : PrecubicalSet) := FreeGroupoid (ChP.obj K)

/-- A cylinder map to `K`: a precubical set with a map to the path object. -/
structure CylMap (K : PrecubicalSet) where
  src : PrecubicalSet
  cyl : src ⟶ PathOb.obj K

def CylMap.leftLeg  (c : CylMap K) : c.src ⟶ K := c.cyl ≫ (endpoint false).app K
def CylMap.rightLeg (c : CylMap K) : c.src ⟶ K := c.cyl ≫ (endpoint true).app K

/-- The two leg-functors on the d-path groupoid. -/
def CylMap.Lgrpd (c : CylMap K) : DPathGrpd c.src ⥤ DPathGrpd K :=
  FreeGroupoid.map (ChP.map c.leftLeg).toFunctor
def CylMap.Rgrpd (c : CylMap K) : DPathGrpd c.src ⥤ DPathGrpd K :=
  FreeGroupoid.map (ChP.map c.rightLeg).toFunctor

/-- **The geometric comparison (CRUX of piece 1).** A cylinder map induces a natural
transformation `Lgrpd ⟹ Rgrpd` between the leg-functors on the d-path groupoid. -/
def CylMap.toTransf (c : CylMap K) : c.Lgrpd ⟶ c.Rgrpd
/- Construction route (reduces the hard part to one geometric family):
   by `FreeGroupoid.liftNatIso`, since `DPathGrpd K` is a groupoid it suffices to give
   a natural iso after precomposing with `of (ChP src)`, i.e. a natural family
     `(ChP.map leftLeg).toFunctor ⋙ of  ≅  (ChP.map rightLeg).toFunctor ⋙ of`
   of functors `ChP src ⥤ DPathGrpd K`.  Its component at a chain
   `a = (dims, p : □^∨dims ⟶ src)` is the zigzag in `ChP K` from `(dims, p ≫ leftLeg)`
   to `(dims, p ≫ rightLeg)` built from `p ≫ c.cyl : □^∨dims ⟶ PathOb K`, whose value
   at a `k`-cell is a `(k+1)`-cell of `K` (the prism over that cell).  Naturality in
   `a` is the geometric lemma. -/

/-- Cylinder maps whose left leg is a groupoid-reflection weak equivalence (so `Lgrpd`
is an equivalence and the transport below exists). -/
structure CylMapWeq (K : PrecubicalSet) extends CylMap K where
  left_weq : toCylMap.Lgrpd.IsEquivalence

@[ext] structure CylMapWeq.Hom (c d : CylMapWeq K) where
  map : c.src ⟶ d.src
  w : map ≫ d.cyl = c.cyl
instance : Category (CylMapWeq K)

/-- **PIECE 1.** The pointed endofunctor of `M K` performed by a cylinder map:
`(Lgrpd⁻¹ ⋙ Rgrpd, 𝟭 ⟹ Lgrpd⁻¹⋙Rgrpd)`, via `pointedOfTransf` and `toTransf`. -/
noncomputable def cylToPointed (K : PrecubicalSet) :
    CylMapWeq K ⥤ PointedEndofunctor (DPathGrpd K)
/-  obj c := @pointedOfTransf _ _ _ _ c.Lgrpd c.Rgrpd c.left_weq c.toTransf
    map f := ⟨…, …⟩   -- naturality of `toTransf` along `f.map` (lemma to supply)  -/
```

## 3. Module C — `Operations/CylinderAdjunction.lean` (piece 2)

This is the publishable result and the **research** step: the right adjoint must be
*discovered*, not merely proved. Best current proposal (to be confirmed/adjusted):

```lean
/-- Proposed adjoint: a canonical cylinder realizing a pointed endofunctor of `M K`.
RESEARCH: pin down this construction. -/
noncomputable def pointedToCyl (K : PrecubicalSet) :
    PointedEndofunctor (DPathGrpd K) ⥤ CylMapWeq K

/-- **PIECE 2.** Expected shape: `cylToPointed` is a localization with fully faithful
right adjoint `pointedToCyl`, exhibiting `PointedEndofunctor (M K)` as a reflective
quotient of `CylMapWeq K` (the "freedom in `E`" is exactly what is quotiented; hence
adjunction, not iso). -/
noncomputable def cylAdjunction (K : PrecubicalSet) :
    cylToPointed K ⊣ pointedToCyl K
/-- `cylToPointed` inverts `pointedToCyl` up to iso (full faithfulness of the adjoint). -/
def cylToPointed_comp_iso (K) : pointedToCyl K ⋙ cylToPointed K ≅ 𝟭 _
```

If the clean adjoint resists, fall back to: localize `CylMapWeq K` at the maps
`cylToPointed` sends to isos and show the induced functor on the localization is an
equivalence onto `PointedEndofunctor (M K)` (a weaker but certain statement).

## 4. Endpoint compatibility (for later specialization to bi-pointed `Ch K`)

State `endpoint`’s naturality so that, when `K` is bi-pointed and legs preserve
`init`/`final`, the whole pipeline restricts from `ChP` to the bi-pointed `Ch`. Just
record the lemmas; not needed for pieces 1–2 over `ChP`.

```lean
theorem endpoint_naturality (ε : Bool) {K L : PrecubicalSet} (f : K ⟶ L) :
    (PathOb.map f) ≫ (endpoint ε).app L = (endpoint ε).app K ≫ f
```

## 5. Deferred (certain): path object = box-tensor cocylinder

```lean
-- Once the box tensor `(-) ⊗ □¹` is defined (`□ᵐ ⊗ □ⁿ = □ᵐ⁺ⁿ`):
def boxTensorInterval : PrecubicalSet ⥤ PrecubicalSet          -- (-) ⊗ □¹
def cylinderPathAdjunction : boxTensorInterval ⊣ PathOb          -- CERTAIN
theorem boxTensor_repr_interval (n : ℕ) :
    boxTensorInterval.obj (yoneda.obj (Box.ob n)) ≅ yoneda.obj (Box.ob (n+1))  -- CERTAIN
```
This justifies calling `PathOb` "the cocylinder" / cylinder maps "homotopies"; it is
**not** the cartesian exponential. Build last.

## 6. Agent task breakdown (dependency order)

- **A1 — `Box.shift` + `coface`** (Module A). *Blocks everything.* Pure cube
  combinatorics; the single hardest piece.
- **A2 — `PathOb`, `endpoint`, `endpoint_naturality`** (Module A, §4). Trivial given A1.
- **B1 — `CylMap`, legs, `Lgrpd`/`Rgrpd`, `CylMapWeq`, category instance** (Module B).
  Routine; needs A2.
- **B2 — `CylMap.toTransf`** (the geometric comparison). *Hard*; needs A2 + the prism
  reduction in §2. Independent of B1.
- **B3 — `cylToPointed`** (piece 1 functor). Easy given B1+B2 (`pointedOfTransf` exists).
- **C — `pointedToCyl` + `cylAdjunction`** (piece 2). Research; needs all of B.
- **D — box tensor + `cylinderPathAdjunction`** (§5). Deferred; independent.

Already built (sorry-free), the algebra these land in: `PointedEndofunctor`,
`pointedOfTransf` (`Operations/PointedFunctor.lean`); `transportTransf`,
`freeGroupoid_map_isEquivalence`, `FreeGroupoid` API (`Operations/GroupoidTarget.lean`);
`ChP`, `Weq`, `WeqGrpd` (`Operations/Precubical.lean`).
