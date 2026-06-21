# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of Ziemiański's cube-chain category
`Ch(K)` and the lifting/lowering of automorphisms between a bi-pointed precubical set
`K` and `Ch(K)`. **Read this first to find the right file**, then open that one file (+
its module docstring) — you should never need the whole tree in context.

Two models of precubical sets coexist: the **concrete/computable** one
(`Foundations/PrecubicalConstructions/`, graded cells + face maps) and the **topos**
one (`PrecubicalSet := Boxᵒᵖ ⥤ Type`), bridged by the cube Yoneda lemma
(`Foundations/Representable.lean`). The topos model is the default everywhere downstream.

## The two headline results

| Result | Statement | Lives in |
|---|---|---|
| **RefineObj ⇔ Ch** | `equivWedgeCat : RefineObj K ≌ ChainCat.Obj K` (under `NonSelfLinked` + `AdmitsAltitude`) | `Chains/Correspondence.lean`; keystone `Refine.pushforward` in `Chains/RefineFunctor.lean` |
| **Cylinder ⇒ pointed functor** | `cylToPointedR : CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)` | `Cylinder/CylinderRefine.lean` (built on `CylinderSweep`/`CylinderRefineCore`) |

Both are sorry-free. The only `sorry`s in the repo live in `Research/Conjectures.lean` (by policy).

## Layered layout (folders = areas; deeper layer imports shallower)

### `Foundations/` — stable math fundamentals (no cube-chain specifics)
- `PrecubicalConstructions/Basic.lean` — concrete precubical sets; `face ε i`, category instance.
- `PrecubicalConstructions/StandardCube.lean` — `□ⁿ` concretely (sign-vector cells), `face`, `topCell`.
- `Box.lean` — the box category `Box`; `PrecubicalSet := Boxᵒᵖ ⥤ Type` (topos; `HasPushouts` free).
- `Representable.lean` — **cube Yoneda** (`canonicalMap`, `cubeRepr`); `trueCount`/`canonicalMap_*`
  combinatorics; `coface`.
- `Bipointed.lean` — `BPSet` (bi-pointed presheaf) + `Hom` + category; `cells`, `vertex₀/₁` and their
  Yoneda/naturality lemmas; `faceMap`/`cubeMap`; the `IsAltitude` predicate.
- `Wedge.lean` — `cube n`, `wedge2` (pushout), `vertexMap` (= `cubeMap`), `serialWedge`.
- `Shift.lean` — box `shift` endofunctor, `PathOb` (cocylinder), `snocFree`/`snocFix`, `endpoint`;
  the geometric `⊗□¹ ⊣ PathOb` infra.
- `Altitude.lean` — the side conditions `NonSelfLinked` / `AdmitsAltitude` / `Accessible` (`Reach`),
  all `PrecubicalSet`-level, + the `alt_*` lemmas.

### `Chains/` — the cube-chain category and its theory
- `Basic.lean` — `CubeChain` (junction-vertex rep), `IsCubeChain`, `ofIsCubeChain`, `vtxCanon`.
- `WedgeMap.lean` — wedge-map ↔ cube-list decomposition; `serialWedge_hom_ext`; the reusable
  presheaf-level `glue0_*` pushout/injectivity cores (+ `BPSet` `wedge2_*` wrappers) and mono infra.
- `Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category.
- `RefineConcat.lean` — **generic** `RefineObj.append` + `appendLeft` whiskering kernel (reusable;
  no cylinder content).
- `Category.lean` — `ChainCat`, `Ch : BPSet ⥤ Cat`, **`Aut.liftToCh`** (the lift).
- `Correspondence.lean` — **`equivWedgeCat`** [RESULT 1]; `descent_mono`; thinness via `Quiver.IsThin`.
- `RefineFunctor.lean` — **`Refine.pushforward`** (refinement functorial in `K`); imports Correspondence.
- `Lifting.lean` — `refineAut σ := Refine.pushforward σ.hom` (geometric action of the lift).
- `Slice.lean` — `Ch K ↪ Over K` fully faithful (exemplary mathlib reuse: `Over`, Kan extension).
- `Segal.lean` (+ `SegalAltitude.lean`) — `Ch(X∨Y) ≌ Ch X × Ch Y` monoidality (faithful via adhesive).

### `Cylinder/` — the cylinder ⇒ pointed-endofunctor program  (was `Operations/`)
- `PointedFunctor.lean` — `PointedEndofunctor` + the groupoid conjugation API
  (`pointedOfPaths`/`pointedFunctorOfObj`/`pointedHomOfGroupoid`); uses mathlib `FreeGroupoid`.
- `Cylinder.lean` — the prism core: `cylTranspose`, `CylMap` (= `Over (PathOb K)`), `prism`,
  `coface_prism`, `isCubeChain_append`.
- `CylinderRefineCore.lean` — geometry: `DPathGrpdR`, `CylMapR` (+ `CylMapWeqR`), `Refine.pushforwardBP`,
  `blockQ`, the cospan pieces `refineEndG`/`refinePrismG`/`refineCofaceG`/`refineEdgeG` + bridge cofaces.
- `CylinderSweep.lean` — the `sweepR` fence-staircase (`BlockRec`, `leftPush`/`rightPush`, `sweepTail`,
  `sweepFirst`, `sweepR`, `blocksOf`).
- `CylinderRefine.lean` — **`cylToPointedR`** [RESULT 2], the thin deliverable.

### `Research/` — open conjectures + counterexamples
- `Conjectures.lean` — the **only** `sorry`-bearing file (by policy): open inputs
  (`chainsJointlySurjective_of_accessible`, the poset lemmas, the staged Segal `Full`/`EssSurj`).
- `Unrealizable.lean` — the four-square-loop counterexample (lowering existence is **false**).
- `Examples.lean` — type-level sanity checks.
- `Scratch/` — owner work-in-progress (e.g. `Cyl*` algebra/injectivity/generation probes). **Not
  imported by the root** `CubeChains.lean`, so `lake build CubeChains` does not build it; it may carry
  `sorry`s while in flight. Build a probe directly: `lake build CubeChains.Research.Scratch.<File>`.

### `Testing/` — decoupled property-testing harness (NOT built by `lake build CubeChains`)
A computable `FinBPSet` surrogate for `Ch K` (`Model.lean`) driving `native_decide`/`#eval` checks
(`Lowering.lean`, `Examples.lean`, the cylinder probes). See `[[cubechains-property-testing]]`.

## Where do I find…?

- **the box / precubical-set definition** → `Foundations/Box.lean`
- **cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n`** → `Foundations/Representable.lean` (`cubeRepr`)
- **`vertex₀/₁`, `BPSet.Hom`, `cubeMap`/`faceMap`** → `Foundations/Bipointed.lean`
- **the wedge / serial wedge / `wedge2` pushout** → `Foundations/Wedge.lean` (+ decomposition in `Chains/WedgeMap.lean`)
- **`NonSelfLinked` / `AdmitsAltitude` / altitude lemmas** → `Foundations/Altitude.lean`
- **the chain category `Ch` / the lift `liftToCh`** → `Chains/Category.lean`
- **the refinement ≌ chains equivalence [RESULT 1]** → `Chains/Correspondence.lean`
- **`Refine.pushforward` (refinement functorial in K)** → `Chains/RefineFunctor.lean`
- **generic chain concatenation `RefineObj.append`** → `Chains/RefineConcat.lean`
- **Segal monoidality** → `Chains/Segal.lean`
- **`PathOb` / box shift / `⊗□¹⊣PathOb`** → `Foundations/Shift.lean`
- **`PointedEndofunctor` + groupoid API** → `Cylinder/PointedFunctor.lean`
- **the cylinder prism core / `CylMap`** → `Cylinder/Cylinder.lean`
- **the cylinder ⇒ pointed functor [RESULT 2]** → `Cylinder/CylinderRefine.lean`
- **open conjectures / `sorry`s** → `Research/Conjectures.lean`

## Build & conventions

- Whole project: `lake build CubeChains`. One module: `lake build CubeChains.Chains.Correspondence`
  (the slow one, ~45s). Testing harness: `lake build CubeChains.Testing.Examples`.
- **Trust `lake build`, not the IDE** (cross-file diagnostics are stale).
- `sorry` is allowed **only** in `Research/Conjectures.lean`.
- Use `erw` (not `rw`) for `PrecubicalSet` (functor-category) compositions; rewriting under
  `yonedaEquiv` fails the motive — convert to a plain morphism equation first.
- Dimensions are `ℕ+`; coerce to `ℕ` only inside `cube`.
- Prefer reusing a mathlib construction (Over/comma cats, `FullSubcategory`, Kan extensions,
  `FreeGroupoid`, `Quiver.IsThin`, adhesive/pushout API) over hand-rolling — see `Chains/Slice.lean`
  as the in-repo exemplar.

## Other docs

- `DESIGN.md` — the conventions/decisions log (with PZ/Z paper references).
- `CLEANUP.md` — the cleanup-pass tracker (what was deleted/moved/generalized and why).
- `/orient` skill — fast session bootstrap (module map mirrors this file).
- Papers: PZ = arXiv:2103.05336, Z = arXiv:1901.05206.
