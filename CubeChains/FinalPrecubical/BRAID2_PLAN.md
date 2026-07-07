# BRAID2_PLAN — a cleaner proof of `PhiEquiv : ChZ n ≌ (QC n)ᵒᵖ`

Architecture plan for a rebuilt braid main theorem, replacing the ~1800-line
event-permutation route in `CubeChains/FinalPrecubical/Ev.lean`.  **Read-only plan;
no `.lean` files were modified.**  All `file:line` citations verified against the
current tree (2026-07-07).

Papers: PZ = arXiv:2103.05336, Z = arXiv:1901.05206.

---

## 0. Executive summary

The current proof (`Ev.lean` + `MainFunctor.lean`) is sorry-free but re-derives, at the
presheaf level, the chain↔wedge decomposition that `Chains/Correspondence.lean`
(`equivWedgeCat`, RESULT 1) already proves.  The rebuild folds that plumbing through
RESULT 1 **applied to the ambient serial wedge `serialWedge B`** (not the terminal `Z`),
whose object bijection is unconditional and whose morphism/thinness half needs only
`AdmitsAltitude` (`serialWedge_admitsAltitude`, proven) plus a new **`serialWedge` is
`NonSelfLinked`** lemma (currently unproven, but true — the memory's "serialWedge is not
NSL" remark conflates it with `Z`; see §Risk R1).  The single-cube heart
(`chainCoordMono`/`OwnerData`/`cornerChain`, already green in `Ev.lean`) becomes a packaged
equivalence `cubeChainEquiv` reused per target block.  The RHS layout switches from
`Salvetti.blockOf`/`psum`/private-`dimSum`/`Ev.globalEquiv` to mathlib `Composition n`.

**Sorry verdict (§4, headline):** the rebuild MUST NOT use
`Research/Conjectures.chSegal`/`chSegalProd`/`chConcat_full`/`chConcat_essSurj` — those
inject `sorryAx` and would break `#print axioms PhiEquiv`.  It does **not** need them: the
serial-wedge Segal split it actually requires is a *different, weaker* statement (block
decomposition of a wedge map **between serial wedges**), which is latent **sorry-free** in
`WedgeMap.lean` + `Correspondence.wedgeToRefineMap`, and is exactly what
`Ev.ev`/`ev_reconstruct`/`evValid_exists` already assemble sorry-free today.  Verified: the
current `PhiEquiv` import chain (MainFunctor → Ev/Salvetti/QuotientCat →
SegalAltitude/WedgeMap/Correspondence/Category) contains **no** import of `Chains.Segal` or
`Research.Conjectures` (`SegalAltitude ≠ Segal`).

---

## 1. Module layout (new files under `CubeChains/FinalPrecubical/`)

The rebuild **keeps** `QuotientCat.lean` verbatim and **keeps most of** `Salvetti.lean`
(the poset `BrFace`/`Sal₀Br`/`OrderFreeAction`) and `MainFunctor.lean`'s §1 terminal-`Z`
scaffolding.  It **replaces** `Ev.lean` and the layout-arithmetic parts of `Salvetti`/
`MainFunctor`.  Proposed new modules (each a thin, single-purpose file):

| New module | Contains | Replaces / reuses |
|---|---|---|
| `Layout.lean` | `List ℕ+ ↔ Composition n` bridge; `ofDims`, `dimSum = blocks.sum`, `blockOf = Composition.index`, `psum = sizeUpTo`, `globalEquiv = Composition.blocksFinEquiv`. One home for block/prefix-sum arithmetic. | kills the triplicated arithmetic: Salvetti `blockOf`/`psum`/`blockOf_iff_psum`, the `private dimSum` name-clash dodge, and `Ev.dimSum`/`globalEquiv`/MainFunctor §3 bridge. Adopts mathlib `Composition` (Combinatorics/Enumerative/Composition.lean). |
| `CubePartition.lean` | **`cube_nonSelfLinked (N) : (cube N).NonSelfLinked`**; the single-cube equivalence **`cubeChainEquiv a N : {x : RefineObj (cube N) // x.dims = a} ≃ OwnerData a N`** (chains of shape `a` in `□ᴺ` ↔ ordered set partitions of `Fin N` of shape `a`); the poset/order match. | reuses the whole `Ev` single-cube core (`chainCoordMono`, `OwnerData`, `chainOwner`, `cornerChain`, `chainFace_eq_owner`, `cornerChain_isChain` — all green) hoisted out of `Ev`; adds only the packaging + NSL. |
| `SerialNSL.lean` | **`serialWedge_nonSelfLinked (B) : (serialWedge B).NonSelfLinked`** (from `cube_nonSelfLinked` + block routing `serialWedge_cell_exists`/`_block_unique`/`_ι_app_injective`). | new; unlocks `equivWedgeCat (serialWedge B)`. Optional if the fallback hom-route (§2 route B) is chosen. |
| `HomAnalysis.lean` | The hom-level classification **`homEquiv A B : (serialWedge A ⟶ serialWedge B) ≃ Σ bm : BlockMap A B, Π j, OwnerData (fibre A bm j) (B.get j)`** — a wedge map = a monotone block map + a per-target-block ordered partition. Built by `equivWedgeCat (serialWedge B)` applied to shape-`A` objects (= the wedge maps, since `Z` terminal), whose unique refinement to the top `B`-chain gives `(bm, incl)`, and `cubeChainEquiv` per block. Proves `homEquiv` functorial (`ev_id`/`ev_comp` analogues). | **the replacement for `Ev`'s `ev`/`ev_reconstruct`/`evValid_exists`/`IsEvValid` tower** (≈ lines 97–1977). |
| `SalvettiComp.lean` | **`salEquiv : Sal₀Br n ≃ Composition n × Perm (Fin n)`** via `(F,C) ↦ (F∘C⁻¹, C)`; the `Perm` action in coordinates (`σ • (D,C) = (D, C∘σ⁻¹)`, trivial on `Composition`); the Paris order restated in `(Composition, Perm)` coordinates. | folds `Salvetti`'s `stdPairAt`/`levelSizes`/`exists_smul_stdPairAt`/`orbit_rep_unique` onto `Composition`; keeps `BrFace`/`Sal₀Br`/`OrderFreeAction`. |
| `MainFunctor2.lean` | The capstone: `Φ' n : ChZ n ⥤ (QC n)ᵒᵖ` built from `homEquiv` + `homEquivUpSet` + `salEquiv`; Full/Faithful/EssSurj; **`PhiEquiv`**. | rebuilds `MainFunctor` §4–§10 on the `homEquiv`/`Composition` API instead of `evPermN`; keeps §1 (`Z`, `toZ`, `zTerminal`, `zHom_subsingleton`), §2 (`ChZ`, `ZGrade`), and §11 (`objEquiv`/`Ψ`, strict form) essentially verbatim. |

Dependency order (deeper imports shallower): `Layout` → `CubePartition` → `SerialNSL` →
`HomAnalysis` → `MainFunctor2`; and `Layout` → `SalvettiComp` → `MainFunctor2`.  `Layout`
imports `Chains/WedgeMap` + mathlib `Composition`; `CubePartition`/`SerialNSL`/`HomAnalysis`
import `Chains/Correspondence` (RESULT 1); `SalvettiComp`/`MainFunctor2` import `QuotientCat`.

---

## 2. Exact Lean statements in dependency order

Namespaces: keep `FinalPrecubical`; single-cube helpers reuse `CubeChain`/`StdCube`.

### 2.1 `Layout.lean` — adopt mathlib `Composition`

Mathlib API used (`Mathlib/Combinatorics/Enumerative/Composition.lean`):
`Composition n` (struct `blocks : List ℕ`, `blocks_pos`, `blocks_sum`, line 100);
`length` (147), `blocksFun` (155), `sizeUpTo` (217, `= (blocks.take i).sum`),
`sizeUpTo_succ` (236), `monotone_sizeUpTo` (249), `index` (316, block of a coordinate),
`embedding`/`invEmbedding` (294/337), **`blocksFinEquiv : (Σ i, Fin (blocksFun i)) ≃ Fin n`**
(415), `mem_range_embedding_iff` (352, the `[sizeUpTo i, sizeUpTo (i+1))` interval),
`composition_card = 2^(n-1)` (1029).  There is **no** smart constructor from `List ℕ+`.

```lean
/-- A `List ℕ+` as a composition of its dims-sum. -/
def Comp.ofDims (A : List ℕ+) : Composition (dimSum A)  -- blocks := A.map (·:ℕ); positivity from PNat.pos
def Comp.toDims {n} (c : Composition n) : List ℕ+        -- c.blocks.pmap (⟨·, ·⟩) c.blocks_pos
theorem Comp.toDims_ofDims (A) : Comp.toDims (Comp.ofDims A) = A
theorem Comp.dimSum_toDims {n} (c) : dimSum (Comp.toDims c) = n     -- = c.blocks_sum
theorem Comp.length_ofDims (A) : (Comp.ofDims A).length = A.length
/-- Salvetti↔Composition identifications (proved once, then `Salvetti.blockOf` etc. retire). -/
theorem blockOf_eq_index (A) (i) : blockOf A i = ((Comp.ofDims A).index ⟨i,_⟩ : ℕ)
theorem psum_eq_sizeUpTo (A) (j) : psum A j = (Comp.ofDims A).sizeUpTo j
theorem globalEquiv_eq_blocksFinEquiv (A) : globalEquiv A = (Comp.ofDims A).blocksFinEquiv ∘ ...
```
where `dimSum A := (A.map (·:ℕ)).sum` is the single surviving copy (the `Salvetti.dimSum`
`private` dodge and `Ev.dimSum` collapse to it).

### 2.2 `CubePartition.lean` — single cube = ordered set partition

Reuse (hoisted from `Ev.lean`, all green, NSL-free): `OwnerData a N` (Ev:728),
`chainFace` (651), `chainCoordMono` (694), `chainStarSet`/`_disjoint`/`_cover` (754/737/791),
`chainOwner`/`_mem`/`_unique` (821/827/834), `cornerFaceVal`/`cornerFace`/`cornerCell`/
`cornerChain` (846/863/868/886), `chainFace_eq_owner` (898), `cornerChain_isChain` (930),
`isCubeChain_ofFn` (628), `isCubeChain_junction` (614), `toStar_injective` (139),
`toStar_vertex₀_val`/`toStar_vertex₁_val` (596/586), `cellZero_ext` (881).

```lean
/-- Read a chain in `□ᴺ` as its ownership partition (owner of each coord = the unique face
    it is free in). -/
noncomputable def chainToOwner {N} (x : RefineObj (cube N).init (cube N).final)
    (hx : x.dims = a) : OwnerData a N            -- owner := chainOwner x.cubes x.isChain (recast)

/-- **The single-cube equivalence.**  Chains of shape `a` in `□ᴺ` ↔ ordered set partitions
    of `Fin N` of shape `a`.  Forward = `chainToOwner`; inverse = `cornerChain`. -/
noncomputable def cubeChainEquiv (a : List ℕ+) (N : ℕ) :
    {x : RefineObj (cube N).init (cube N).final // x.dims = a} ≃ OwnerData a N where
  toFun x  := chainToOwner x.1 x.2
  invFun o := ⟨⟨cornerChain o, cornerChain_isChain o⟩, cornerChain_dims o⟩
  left_inv  := ...   -- chainFace_eq_owner (a chain equals the corner model of its owner)
  right_inv := ...   -- chainOwner (cornerChain o) = o.owner  (from cornerFaceVal_none_iff)

/-- **`□ᴺ` is non-self-linked.**  Every cube's canonical map is injective (representable +
    box morphisms are monos).  Route: `(cubeMap c).app = post-comp by box coface`; injective
    ⟸ `StdCube.app` injective (`app_val` + `nones_nonesIdx`) ⟸ `toStar_injective`/`cubeRepr`. -/
theorem cube_nonSelfLinked (N : ℕ) : (cube N).NonSelfLinked
```

With `cube_nonSelfLinked` + `cube_admitsAltitude` (SegalAltitude:105), RESULT 1 gives the
**poset structure** for free:
```lean
/-- `Ch (□ᴺ)` is thin. -/
example (N) := chainCat_hom_subsingleton (cube_nonSelfLinked N) (cube_admitsAltitude N)
/-- `RefineObj (□ᴺ)` ≌ `Ch (□ᴺ)`. -/
noncomputable def cubeEquivWedge (N) :=
  equivWedgeCat (cube_nonSelfLinked N) (cube_admitsAltitude N)
```
The **order match** (refinement of chains = refinement of ordered partitions) is the one new
order lemma: `a-chain ≤ b-chain` in the thin `RefineObj (□ᴺ)` iff `OwnerData a ≤ OwnerData b`
in the coarsening order (a's owner factors monotonically through b's).

### 2.3 `SerialNSL.lean`

```lean
/-- **`serialWedge B` is non-self-linked.**  A positive cell lies in a unique block
    (`serialWedge_cell_exists`/`_block_unique`), block inclusions are monos
    (`serialWedge_ι_app_injective`), and each block is a cube (`cube_nonSelfLinked`); a
    vertex's canonical map is injective trivially. -/
theorem serialWedge_nonSelfLinked (B : List ℕ+) : (serialWedge B).NonSelfLinked
```
This is the linchpin that lets RESULT 1 apply to the ambient wedge (§Risk R1).

### 2.4 `HomAnalysis.lean` — the wedge-map classification (replaces the `ev` tower)

Since `Z` is terminal, `Hom_{ChZ}(A,B)` is literally `{wedge maps serialWedge A → serialWedge B}`
(`ChZ.wedgeMap`, MainFunctor:92; triangle over `Z` free by `zHom_subsingleton`).  A wedge map
`serialWedge A → serialWedge B` is an **object of `Ch (serialWedge B)` of shape `A`** (via
`equivWedgeHom (serialWedge B)`, Correspondence:75 — unconditional).  Under
`serialWedge_nonSelfLinked B` + `serialWedge_admitsAltitude B`, `Ch (serialWedge B)` is thin
(`chainCat_hom_subsingleton`), so this object has a **unique** refinement morphism to the
top `B`-chain (identity chain of shape `B`), i.e. a `wedgeToRefineMap` (Correspondence:661) of
the `A`-chain into the `B`-chain.  That morphism's data is exactly:

```lean
/-- The monotone block map: source block `i` ↦ its unique target block. Reuses
    `wedgeToRefineMap`.refinement (monotone by `refinementMono`, needs only altitude). -/
noncomputable def blockMap (g : serialWedge A ⟶ serialWedge B) : Fin A.length → Fin B.length
theorem blockMap_monotone (g) : Monotone (blockMap g)     -- = refinementMono

/-- Fibre of the block map over target block `j`: the sub-shape of `A` landing in `j`. -/
def fibreShape (g) (j : Fin B.length) : List ℕ+

/-- **The hom classification.**  A wedge map = a monotone block map together with, per target
    block `j`, an ordered set partition of `Fin (B.get j)` of shape `fibreShape g j`. -/
noncomputable def homEquiv (A B : List ℕ+) :
    (serialWedge A ⟶ serialWedge B) ≃
      Σ bm : {m : Fin A.length → Fin B.length // Monotone m},
        Π j : Fin B.length, OwnerData (fibreOf A bm.1 j) (B.get j)
--  forward: blockMap + (per j) `cubeChainEquiv` applied to the block-`j` sub-chain
--  inverse: assemble per-block `cornerChain`s into a chain in serialWedge B, descend

theorem homEquiv_id : homEquiv A A (𝟙 _) = ⟨⟨id, monotone_id⟩, fun j => trivialOwner⟩
theorem homEquiv_comp (g h) : homEquiv A C (g ≫ h) = homEquiv_compose (homEquiv .. g) (homEquiv .. h)
```

`homEquiv.injective` **is** `ev_reconstruct` (Ev:1357) and `homEquiv.surjective`/`.symm` **is**
`evValid_exists` (Ev:1863) — but here they are `Equiv` round-trips inherited from
`equivWedgeHom` + `cubeChainEquiv`, *not* re-proved cell-by-cell.  The single-cube owner rule
is applied once (in `cubeChainEquiv`), per block, instead of being threaded through
`blockIdx`-wrapped `faceStar_*` casts as in the current `evCell_determined`/`starCoord` towers.

### 2.5 `SalvettiComp.lean` — the RHS in `Composition × Perm` coordinates

Keep `BrFace` (Salvetti:48), `Sal₀Br` (207), the Paris order (227), `OrderFreeAction` instance
(312), `IsChamber.toPerm` (432).

```lean
/-- `Sal₀Br n ≃ Composition n × Perm (Fin n)` via `(F,C) ↦ (F ∘ C⁻¹, C)`: `F ≤ C` makes
    `F∘C⁻¹` a monotone surjection = a composition; `C` bijective = a permutation. -/
noncomputable def salEquiv (n : ℕ) : Sal₀Br n ≃ Composition n × Equiv.Perm (Fin n)

/-- The `Perm` action in coordinates: `σ • (D,C) = (D, C ∘ σ⁻¹)` — **trivial on the
    `Composition` factor**, free on `Perm`.  Hence orbits ≃ `Composition n`. -/
theorem salEquiv_smul (σ) (x) :
    salEquiv n (σ • x) = ((salEquiv n x).1, (salEquiv n x).2 * σ⁻¹)

/-- Orbit representatives = compositions (recovers `exists_smul_stdPairAt`/`orbit_rep_unique`
    as: the `Composition` factor is the invariant, the `Perm` factor is the free coordinate). -/
noncomputable def qcObjEquiv (n) : QC n ≃ Composition n     -- QC n = Sal₀Br n // Perm

/-- Paris' order in `(Composition, Perm)` coordinates (needed for `homEquivUpSet` matching). -/
theorem le_iff_comp (x y : Sal₀Br n) : x ≤ y ↔ <condition on salEquiv x, salEquiv y>
```

### 2.6 `MainFunctor2.lean` — assembly

Keep from `MainFunctor.lean`: §1 `Zpsh`/`Z`/`toZ`/`zTerminal`/`zHom_subsingleton` (37–73),
§2 `ZGrade`/`ChZ`/`ChZ.dims`/`ChZ.wedgeMap`/`ChZ.grade` (79–95), and §11 `objEquiv`/`Ψ` shape.
Replace `evPermN` and the Salvetti-`blockOf` bridge with `homEquiv` + `salEquiv`.

```lean
abbrev QC (n) := QuotCat (Sal₀Br n) (Equiv.Perm (Fin n))            -- unchanged (:308)

/-- Object map: chain `a` ↦ its composition class.  Via `qcObjEquiv`. -/
noncomputable def stdObj' (a : ChZ n) : QC n

/-- **Well-definedness / the span of `Φ.map g`.**  From `homEquiv A B g = (bm, part)`: `bm`
    is the `BrFace.le` monotone-merge witness; `part` (per-block `OwnerData`) is the tie /
    per-block interleaving of the Salvetti chambers.  Assembled through `homEquivUpSet`
    (QuotientCat:266) + `salEquiv`/`le_iff_comp`. -/
theorem Phi_welldef' (g : a ⟶ b) : stdPair'... ≤ (homEquivPerm g) • stdPair'...

noncomputable def Φ' (n) : ChZ n ⥤ (QC n)ᵒᵖ
instance : (Φ' n).Faithful    -- = homEquiv.injective   (was ev_reconstruct)
instance : (Φ' n).Full        -- = homEquiv.surjective  (was evValid_exists) via homEquivUpSet
instance : (Φ' n).EssSurj     -- = qcObjEquiv surjective (was stdObj_surjective)
noncomputable def PhiEquiv (n) : ChZ n ≌ (QC n)ᵒᵖ := (Φ' n).asEquivalence
```

The Full/Faithful now bottom out on `homEquiv` being an `Equiv` (round-trips) rather than on
the 900-line cell-level `evCell_determined`/`starCoord`/`realFace` machinery.

---

## 3. Reuse map (existing vs. genuinely new)

### Reused **verbatim / as instances** (no change)
- **`QuotientCat.lean`** in full: `OrderFreeAction` (:31), `QuotCat`/`category` (:112/:184),
  `align`/`align_existsUnique`/`align_smul`/`align_eq` (:77–:99), **`homEquivUpSet`** (:266),
  `homToUpSet` (:240). Generic, K-agnostic.
- **`Salvetti.lean`** poset core: `BrFace` (:48), `BrFace.le`+`PartialOrder` (:66/:69),
  `IsChamber`/`.bijective`/`.injective` (:132–:139), `Sal₀Br` (:207), Paris `Sal₀Br.le`+
  `PartialOrder` (:227/:231), `MulAction`+**`OrderFreeAction (Perm)`** (:256/:312),
  `IsChamber.toPerm` (:432).
- **`MainFunctor.lean`** §1/§2/§11: `Z` terminal machinery (:37–:73), `ChZ`/`ZGrade` (:79–:95),
  `objEquiv`/`Ψ` (:576/:584).
- **RESULT 1** (`Chains/Correspondence.lean`): `equivWedgeCat` (:887), `equivWedgeHom` (:75),
  `wedgeToRefineObj`/`refineToWedgeObj` (:568/:321), **`wedgeToRefineMap`** (:661, monotone
  reindexing under *altitude only*), `wedgeToRefineMap_refinement_spec` (:817),
  `chainCat_hom_subsingleton` (:309), `descent_mono` (:287), `isCubeChain_alt_final` (:602),
  `isCubeChain_alt_get` (:622).
- **`Chains/WedgeMap.lean`**: `wedgeMap_block` (:647), `serialWedge_cell_exists` (:584),
  `serialWedge_block_unique` (:612), `serialWedge_ι_app_injective` (:598), `serialWedge_hom_ext`
  (:223), `wedgeDesc`/`wedgeDescHom`/`wedgeToCubes` (:97/:125/:136), block-ι injectivity
  (`vertexMap_app_injective` :524, `wedge2_inl/inr_app_injective` :564/:569).
- **`Chains/SegalAltitude.lean`**: `cube_admitsAltitude` (:105), `serialWedge_admitsAltitude`
  (:224), `wedge2_admitsAltitude` (:199).
- **`Chains/Refine.lean`**: `ChainRefine` (:42), `RefineObj` (:71), `refineCategory` (:81).
- **`Chains/Basic.lean`**: `CubeChain`/`IsCubeChain` (:38/:56), `isCubeChain`/`ofIsCubeChain`,
  `vtxCanon`, `dims`.
- **mathlib `Composition n`**: `blocks`/`length`/`blocksFun`/`sizeUpTo`/`index`/`embedding`/
  `invEmbedding`/**`blocksFinEquiv`** (line 415)/`monotone_sizeUpTo`/`mem_range_embedding_iff`/
  `composition_card`.

### Reused by **hoisting** (move `Ev` single-cube core into `CubePartition.lean`, unchanged bodies)
`OwnerData` (Ev:728) and everything in Ev §"Single-cube owner rule" (Ev:604–970):
`chainFace`, `chainCoordStep`, `chainCoordMono`, `chainStarSet(_disjoint/_card/_cover)`,
`chainTotalDim`, `chainOwner(_mem/_unique)`, `cornerFaceVal(_none_iff)`, `cornerFace(_card)`,
`cornerCell`, `cornerVtxVec`, `cellZero_ext`, `cornerChain`, `chainFace_eq_owner`,
`cornerChain_isChain`, plus `isCubeChain_junction`/`isCubeChain_ofFn` (candidates to relocate
to `Chains/Basic.lean`), `toStar`/`toStar_injective`/`toStar_canonicalMap`,
`toStar_vertex₀_val`/`toStar_vertex₁_val`.

### Genuinely **new** (the rebuild's actual content)
1. **`Layout.lean`** — `Comp.ofDims`/`toDims` round-trip and the `blockOf/psum/globalEquiv ↔
   index/sizeUpTo/blocksFinEquiv` identifications (mathlib `Composition` has **no**
   `List ℕ+` constructor, so `ofDims` + positivity/sum proofs are new; ~60 lines).
2. **`cubeChainEquiv`** (§2.2) — packaging the hoisted core into one `Equiv` + the
   refinement-order ↔ partition-coarsening-order lemma.  ~60–100 lines.
3. **`cube_nonSelfLinked`** (§2.2) — new (does **not** exist anywhere in the tree; verified).
   ~50–80 lines via `toStar_injective`/`app_val`/`nones_nonesIdx`.
4. **`serialWedge_nonSelfLinked`** (§2.3) — new. ~40–80 lines on top of (3).
5. **`homEquiv`** + functoriality (§2.4) — the assembly of `equivWedgeHom(serialWedge B)` +
   per-block `cubeChainEquiv`; the conceptual replacement of the `ev` tower.  This is the
   largest new piece but is **combinator glue over `Equiv`s**, not cell chasing.
6. **`salEquiv`** + `salEquiv_smul` + `le_iff_comp` (§2.5) — new coordinate change; recovers
   `levelSizes`/`exists_smul_stdPairAt`/`orbit_rep_unique` as corollaries.
7. **`Φ'`/`Phi_welldef'`/Full/Faithful/EssSurj/`PhiEquiv`** (§2.6) — rebuilt on the new API.

---

## 4. The `sorry` question — verdict

**Q: does the new proof depend on `Research/Conjectures.lean`'s staged Segal sorries?**
**A: No — and it must not.  Verdict: AVOID `chSegal`/`chSegalProd`; realize the split
sorry-free through `WedgeMap` + `Correspondence`.**

Facts (verified in `Research/Conjectures.lean` + `Chains/Segal.lean`):
- `chConcat_essSurj` (Conjectures:202–205, `sorry` at :205) and `chConcat_full`
  (Conjectures:211–214, `sorry` at :214) each contain a `sorry -- [RESEARCH]`.
- `chConcat_isEquivalence` (Conjectures:219) uses both; `chSegal` (:229) =
  `(chConcat X Y).asEquivalence` built on `chConcat_isEquivalence`; `chSegalProd` (:255)
  recurses through `chSegal` in its `n :: rest` branch.  So **all of
  `chConcat_isEquivalence`/`chSegal`/`chSegalProd` transitively contain `sorryAx`** (the
  `[]` base of `chSegalProd` is `chUnit.symm`, sorry-free, and the altitude side conditions
  discharge sorry-free via `SegalAltitude`, so the *only* sorry source in `chSegalProd` is
  the two `chConcat` halves).
- `chConcat` itself (`ChainCat.chConcat`, Segal:636) and its `Faithful` instance (Segal:712)
  are **sorry-free**, but they are not enough — the equivalence needs the two sorried halves.
- **Reusable nuance:** the product *type* `Conjectures.chainProd` (:242) and its `Category`
  instance (:246) are **sorry-free** (pure `Type`-level recursion `Πᵢ Ch(cube Bᵢ)`); only the
  *equivalence* `chSegalProd` to it carries `sorryAx`.  So the rebuild may freely use
  `chainProd`-shaped products; it just must build the equivalence itself (via §2.4 `homEquiv`).
- Using any of the above in the rebuild would put `sorryAx` into `#print axioms PhiEquiv`
  (currently `[propext, Classical.choice, Quot.sound]`), regressing the headline result.

Why the rebuild does not need them:
- The general `chConcat X Y` splits a chain in an **arbitrary** wedge `X ∨ Y` and its open
  content is ruling out junction re-crossing for arbitrary `X`,`Y`.  The rebuild only ever
  splits a wedge map **between serial wedges of cubes**, where each block is a single positive
  cube (a representable) landing in a **unique** target block (`serialWedge_cell_exists`/
  `_block_unique`, sorry-free) and block-index **monotonicity** is already delivered by
  `Correspondence.wedgeToRefineMap`.refinementMono under *altitude alone*
  (`serialWedge_admitsAltitude`, proven).  This is strictly weaker than `chConcat_*`.
- Concretely, the split the rebuild needs is exactly what `Ev.ev`/`ev_reconstruct`/
  `evValid_exists` compute **sorry-free today** (the current `PhiEquiv` uses none of the
  Conjectures Segal lemmas — its import chain is Segal-free, verified).  The rebuild reorganizes
  that same content behind `equivWedgeHom`/`cubeChainEquiv` `Equiv`s instead of re-deriving it.

Recommendation and a bonus:
- Realize `Ch(serialWedge B) ≌ Πⱼ Ch(cube Bⱼ)` via **route A**: `equivWedgeCat (serialWedge B)`
  (needs new `serialWedge_nonSelfLinked`, §2.3) — this is the shortest, most reuse-heavy path,
  and is what `homEquiv` (§2.4) is written against.
- **Fallback route B** (if `serialWedge_nonSelfLinked` proves stubborn): keep the block route
  literally — `wedgeMap_block` + the hoisted single-cube core — i.e. a thin re-packaging of the
  present `ev` decomposition.  Still sorry-free, still shorter than today (the owner rule is
  applied once in `cubeChainEquiv`, not inlined per seam), but reuses less of RESULT 1.
- **Separate opportunity (not on the critical path):** the Conjectures Segal sorries
  `chConcat_full`/`chConcat_essSurj` are *stated with* the `AdmitsAltitude` hypothesis that
  rules out re-crossing, and `Correspondence.wedgeToRefineMap` now proves the block
  monotonicity under altitude — so those sorries are plausibly dischargeable by the same
  machinery.  Doing so would let a future rebuild use `chSegalProd` directly.  This is a
  worthwhile but *independent* effort; the braid rebuild should not block on it.

---

## 5. Risk register + suggested build order

### Risks
- **R1 (highest) — `serialWedge_nonSelfLinked` / `cube_nonSelfLinked` truth & cost.**
  Neither exists in the tree (verified: no proof of `NonSelfLinked` anywhere — only hypotheses).
  The braid-final memory says "serialWedge B is NOT NSL", but that remark conflates it with the
  **terminal `Z`** (which is genuinely not NSL); the `Correspondence` counterexamples are
  pathological `K` (corner-identified `□²`, cross-glued cubes), *not* plain serial wedges.  A
  plain serial wedge of cubes has each block a cube (NSL) meeting others only at vertices, and
  it already `AdmitsAltitude` — so it **should** be NSL.  *Mitigation:* prove `cube_nonSelfLinked`
  first (small, self-contained, route given in §2.2); if `serialWedge_nonSelfLinked` is harder
  than expected, fall back to route B (§4), which needs neither NSL lemma.
- **R2 — order/tie matching (`le_iff_comp`, §2.5, and the refinement↔coarsening order in
  §2.2).**  The Paris order's tie clause (`Sal₀Br.le`, Salvetti:227) must be shown equivalent
  to the block-map-monotone + per-block-partition-refinement data of `homEquiv`.  This is the
  genuine combinatorial matching (the "event-perm ↔ chamber translation", memory finding #C);
  it is *irreducible* and survives any reorganization.  *Mitigation:* prove it at the
  `(Composition, Perm)` level (§2.5), where the action is diagonal-trivial, before wiring `Φ'`.
- **R3 — `Composition` friction.**  `blocks : List ℕ` (not `List ℕ+`) with a separate
  `blocks_pos`, and **no** `List ℕ+` constructor — so `Comp.ofDims`/`toDims` carry `pmap`/
  positivity bookkeeping and `Fin (blocks.length)` vs `Fin length` casts.  *Mitigation:* keep
  `dimSum`/`List ℕ+` as the surface type and use `Composition` only for the arithmetic lemmas
  (`sizeUpTo`/`index`/`blocksFinEquiv`), via the `Layout.lean` bridge.
- **R4 — scope creep / net size.**  If `homEquiv` (§2.4) is written cell-by-cell it will not be
  shorter than `Ev`.  The win depends on it being *`Equiv` glue* over `equivWedgeHom` +
  `cubeChainEquiv`.  *Mitigation:* build `cubeChainEquiv` as a genuine `Equiv` first and force
  `homEquiv` to consume only its `.toFun`/`.symm`/round-trips.
- **R5 — HEq/`eqToHom` dependent-type bookkeeping** at the `List.get`/`map`/`Fin.cast` seams
  (the memory's recurring gotcha: `List.get_map` absent, `Fin (l.map g).length` not defeq).
  *Mitigation:* copy the established idioms from `Correspondence.inducedCell`/`wedgeToRefineMap`.
- **R6 — build hygiene.** Use `erw` (not `rw`) for `PrecubicalSet` compositions and convert out
  from under `yonedaEquiv` before rewriting (memory); `lake build` per module, trust it over IDE.

### Suggested build order (prove first → last)
1. **`Layout.lean`** — `dimSum`, `Comp.ofDims`/`toDims` round-trip, `blockOf/psum/globalEquiv`
   ↔ `index/sizeUpTo/blocksFinEquiv`.  *(De-risks R3; unblocks everything; independently
   testable.)*
2. **`cube_nonSelfLinked`** (`CubePartition.lean`).  *(De-risks R1 early and cheaply.)*
3. **Hoist the single-cube core** into `CubePartition.lean`; build **`cubeChainEquiv`** + the
   refinement/partition order lemma.  *(The reusable heart; de-risks R4.)*
4. **`serialWedge_nonSelfLinked`** (`SerialNSL.lean`).  *(Confirms route A; if it stalls, switch
   to route B before step 5.)*
5. **`homEquiv`** + `homEquiv_id`/`homEquiv_comp` (`HomAnalysis.lean`).  *(Replaces the `ev`
   tower; the size payoff.)*
6. **`salEquiv`** + `salEquiv_smul` + `qcObjEquiv` + **`le_iff_comp`** (`SalvettiComp.lean`).
   *(De-risks R2 in clean coordinates.)*
7. **`Φ'`, Faithful, EssSurj, Full, `PhiEquiv`** (`MainFunctor2.lean`); then port §11
   (`objEquiv`/`Ψ`/strict `PhiCatIso`) and the nerve wiring (`NerveQuot.nerve_chZ_iso`).
8. **Retire** `Ev.lean` and the superseded `Salvetti`/`MainFunctor` arithmetic; update
   `CubeChains.lean` registration + `STATUS.md`/`CONSOLIDATION.md`.  Re-check
   `#print axioms PhiEquiv = [propext, Classical.choice, Quot.sound]` (no `sorryAx`).

### Success criterion
`lake build CubeChains.FinalPrecubical.MainFunctor2` green, `#print axioms PhiEquiv` free of
`sorryAx`, and total `FinalPrecubical` line count materially below today's 4228 (the removal of
`Ev`'s ~1800 lines net of the ~300–500 new lines in `Layout`/`CubePartition`/`HomAnalysis`).
