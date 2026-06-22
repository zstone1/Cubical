# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of Ziemiański's cube-chain category
`Ch(K)` and the lifting/lowering of automorphisms between a bi-pointed precubical set
`K` and `Ch(K)`. **Read this first to find the right file**, then open that one file (+
its module docstring) — you should never need the whole tree in context.

Two models of precubical sets coexist: the **concrete/computable** one
(`Foundations/PrecubicalConstructions/`, graded cells + face maps) and the **topos**
one (`PrecubicalSet := Boxᵒᵖ ⥤ Type`), bridged by the cube Yoneda lemma
(`Foundations/Representable.lean`). The topos model is the default everywhere downstream.

## The headline results

| Result | Statement | Lives in |
|---|---|---|
| **RefineObj ⇔ Ch** | `equivWedgeCat : RefineObj K ≌ ChainCat.Obj K` (under `NonSelfLinked` + `AdmitsAltitude`) | `Chains/Correspondence.lean`; keystone `Refine.pushforward` in `Chains/RefineFunctor.lean` |
| **Cylinder ⇒ pointed functor** | `cylToPointedR : SecCyl K ⥤ PointedEndofunctor (DPathGrpdR K)` (section-primary; an equivalence of the left leg is *one* supplier of the section, not a gate) | `Cylinder/CylinderRefine.lean` (built on `CylinderSweep`/`CylinderRefineCore`) |
| **Directed cobordisms `dCob`** | the category of directed cobordisms of precubical sets (cospans + sieve/cosieve + collars), `idCob = ` cylinder; non-trivial (not indiscrete, not a groupoid) | `Cobordisms/DCob.lean` + `NonTriviality.lean`; geometric tensor `Foundations/Tensor.lean`, cylinder `Foundations/Cylinder.lean` |

All are sorry-free. The only `sorry`s in the repo live in `Research/Conjectures.lean` (by policy)
— which now also holds the one deferred `dCob` coherence input (pushout associativity).

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
- `PathIterate.lean` — the **iterated cocylinder** `PathObPow n` (`PathObPow 0 = 𝟭`,
  `PathObPow (n+1) = PathObPow n ×_K PathOb`) + the general length-additivity iso `pathObPowGlueIso`.
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
  (`pointedOfPaths`/`pointedFunctorOfObj`/`pointedHomOfGroupoid`); the **section** datum `DPathSection`
  (`= Lstar + unit : 𝟭 ≅ Lstar ⋙ F`, a one-sided section up to iso, strictly weaker than
  `IsEquivalence`) with `ofEquivalence`/`comp`/`transport`/`mapFreeGroupoid`; uses mathlib `FreeGroupoid`.
- `Cylinder.lean` — the prism core: `cylTranspose`, `CylMap` (= `Over (PathOb K)`), `prism`,
  `coface_prism`, `isCubeChain_append`.
- `CylinderRefineCore.lean` — geometry: `DPathGrpdR`, `CylMapR`, `Refine.pushforwardBP`, `blockQ`,
  the cospan pieces `refineEndG`/`refinePrismG`/`refineCofaceG`/`refineEdgeG` + bridge cofaces.
  (The old `CylMapWeqR` equivalence gate was **removed** — the construction is section-primary now.)
- `CylinderSweep.lean` — the `sweepR` fence-staircase (`BlockRec`, `leftPush`/`rightPush`, `sweepTail`,
  `sweepFirst`, `sweepR`, `blocksOf`).
- `CylinderRefine.lean` — **`cylToPointedObjOfSection`** (section-primary object map) + the primary
  object `SecCyl K` (a `CylMapR K` + a `DPathSection` of its left leg) with `Category (SecCyl K)`,
  `SecCyl.ofEquiv`, and **`cylToPointedR : SecCyl K ⥤ …`** [RESULT 2].
- `MooreCylinder.lean` — the geometric **Moore cylinder** `MooreCyl K` (`E → PathObPow n K`),
  `mooreCompose` (span-pullback into `PathOb^{n+m}`), length-`0` unit `mooreId`, `End(K) ↪ MooreCyl K`.
- `MooreMonoid.lean` — `mooreSubmonoid K = Submonoid.closure (range SecCyl.toPointedObj)` (composition
  via the geometric `mooreCompose`); the `Monoid (PointedEndofunctor 𝒞)` instance.
- `SectionCompose.lean` — composing two sectioned cylinders yields a **forced** section of the
  composite's left leg (`composeSectionRefine`/`composedPointedObj`); sorry-free, carrying two explicit
  hypotheses `PushforwardBPComp` + `RefinePreservesPullback` (see Open questions below).

### Open questions — cylinder track (for a fresh agent)
The cylinder ⇒ pointed-functor construction is **invariant-trivial**: a cylinder is a homotopy between
its legs, so `sweepR : Lgrpd ≅ Rgrpd`, hence the induced `F₀ = Rgrpd ∘ Lgrpd⁻¹` acts as the **identity
on `π₀`** of the d-path category. So cylinders cannot realize non-geometric d-path symmetries (the
`Unrealizable` ρ is invisible to them); their only iso-invariant output is the identity. Open items:
1. **Formalize the π₀-identity theorem** (the negative verdict above) — clean, direct proof from
   `sweepR : Lgrpd ≅ Rgrpd`; was confirmed by the deleted `native_decide` probe `Cyl12`.
2. **`RefinePreservesPullback`** (`Cylinder/SectionCompose.lean`) — `RefineObj` preserves span pullbacks
   (pointwise: a chain in `E₁ ×_K E₂` is a compatible pair of chains). Discharging it makes the section
   composition-closure unconditional. The genuine combinatorial input.
3. **`PushforwardBPComp`** — functoriality of `Refine.pushforwardBP` in the `BPSet` map (object halves
   proven in `SectionCompose`); routine `eqToHom`/`Fin.cast` chase, should be discharged outright.
4. **Strategic** — given invariant-triviality, decide whether to (a) treat the on-the-nose homotopy
   datum as genuine structure (hard: codiscrete target), (b) use a non-groupoid target, or (c) pursue
   subdivision, which needs degeneracy maps precubical sets lack. See `[[cubechains-cylinder-roadmap]]`.

### `Cobordisms/` — directed cobordisms of precubical sets (`dCob`)
Built on a geometric-tensor / cylinder layer added to `Foundations/`:
`CubeConcat` (`MonoidalCategory Box`), `Tensor` (Day-convolution `⊗` via mathlib `DayFunctor`),
`Nerve` (the concrete↔topos model bridge `realize`/`Nerve`/`nerveRealizeIso`), `Cylinder`
(the geometric cylinder `Cyl = realize ⋙ cylC ⋙ Nerve`, `cylCellEquiv`, ends, sieve/cosieve),
`Reachability` (`Reaches`, `π₀`).
- `DirectedBoundary.lean` — `IsSieve`/`IsCosieve`, `StronglyConnected`, loop-barrier lemmas (M1/M3).
- `Loops.lean` — `IsLoopFree`/`LoopConfined`, loop-freeness inheritance (M3).
- `Cospan.lean` — `Cospan` + pushout composition `Cospan.comp`, disjoint legs via van Kampen (M2).
- `Flags.lean` — `srcImage`/`sinkImage`, `Closed`/`Spanning`; the ∅-bottom theorem
  `no_closed_cobordism_from_empty` (M6a).
- `Union.lean`, `Collar.lean` — the `⊔` operation; `SourceCollar`/`SinkCollar` + `cylCospan` (M4/M1).
- `Cobordism.lean` — the `DirectedCobordism X Y` bundle; `idCob = ` cylinder (M4a).
- `Composition.lean` — the pushout-closure `DirectedCobordism.comp` (the reachability-in-pushout
  **barrier**, the M4 technical heart).
- `DCob.lean` — the rel-∂ quotient `cobordismRel`/`HomCob` and the `Category dCob` (M5).
- `NonTriviality.lean` — the merge `{a,b} ⇒ {*}` is non-invertible via a π₀ invariant (M6).
- `MAP.md` / `SORRIES.md` — the dCob build's inventory + scaffolding log.

### `Research/` — open conjectures + counterexamples
- `Conjectures.lean` — the **only** `sorry`-bearing file (by policy): open inputs
  (`chainsJointlySurjective_of_accessible`, the poset lemmas, the staged Segal `Full`/`EssSurj`).
- `Unrealizable.lean` — the four-square-loop counterexample (lowering existence is **false**).
- `Examples.lean` — type-level sanity checks.
- `Scratch/` — convention for owner work-in-progress probes (**currently empty** — cleared). When
  present it is **not imported by the root** `CubeChains.lean`, so `lake build CubeChains` does not
  build it; probes may carry `sorry`s while in flight and are built directly:
  `lake build CubeChains.Research.Scratch.<File>`. Findings that matter get promoted to the main
  library or recorded in memory; the probes themselves are disposable (recoverable from git).

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
- **directed cobordisms / the category `dCob`** → `Cobordisms/DCob.lean` (overview: `Cobordisms/MAP.md`)
- **the geometric tensor `⊗` (Day) / the cylinder object `Cyl`** → `Foundations/Tensor.lean` / `Foundations/Cylinder.lean`
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Foundations/Nerve.lean`
- **`PrecubicalSet` reachability / `π₀`** → `Foundations/Reachability.lean`
- **`dCob` non-triviality (∅-bottom, merge not invertible)** → `Cobordisms/NonTriviality.lean` (+ `Flags.lean`)
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
