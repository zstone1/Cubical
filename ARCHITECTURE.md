# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of the **concurrency braid groupoid** of a
precubical set: the schedules of a cube chain, made into a groupoid, and the theorem that this
groupoid is the (pure) braid group. **Read this first to find the right file**, then open that
one file (+ its module docstring) — you should never need the whole tree in context.

Two models of precubical sets coexist: the **concrete/computable** one
(`Foundations/PrecubicalConstructions/`, graded cells + face maps) and the **topos** one
(`PrecubicalSet := Boxᵒᵖ ⥤ Type`), bridged by the cube Yoneda lemma
(`Foundations/Representable.lean`). The topos model is the default everywhere downstream.

**Why braids.** `(BPSet, ⊗)` is monoidal but has **no swap** — `Box` is rigid (`Aut ▫k = {id}`,
the symmetry-free convention), so no block transposition `▫(m+n) ⟶ ▫(n+m)` exists. The braiding
is *created* by the passage to executions (`ConcGrpd`), not inherited: two interleavings of
independent events are isomorphic, not equal, and the iso has a winding number. Independent
actions do not commute — they braid.

## The headline results

`Ch K = ChainCat.Obj K`, `□n = BPSet.cube n`, `⋁d = BPSet.serialWedge d`, `Int(F) = F.Elements`,
`ConcGrpd K = FreeGroupoid (Int(Lines K))`.

| Result | Statement | Lives in |
|---|---|---|
| **Chains are wedge maps** | `equivWedgeCat : RefineObj K ≌ Ch K` (under `NonSelfLinked` + `AdmitsAltitude`) — a refinement of a chain is the same as a bi-pointed map out of a serial wedge | `Chains/Correspondence.lean` |
| **Salvetti = executions** | `braidSalEquiv n : Sal(braidCOM n) ≌ Int(Lines(□ⁿ))` — the Salvetti complex of the braid arrangement *is* the cube-chain execution model. The interpretation bridge that lets you call the target "braids". | `Salvetti/BraidIso.lean` |
| **The cube is the pure braid group** | `cube_concBraid_pureBraid n : ConcBraid(□n) x ≃* PureBraid n` — the concurrency braid group of the standard cube is `Pₙ` (labelled cubes ⟹ pure) | `Braid/CubePureBraidResult.lean` |
| **The terminal five-lemma** | `braidMonodromy_bijective n x … : Function.Bijective (braidMonodromy n x)` — the middle map of a non-abelian short-five ladder (`ShortFive.bijective_middle`) between the reorient-quotient monodromy and `Bₙ ↠ Sₙ`; the left iso is the cube→pure map, the outer covering is the deck sequence | `Braid/SalvettiDeckCompat.lean` |
| **Terminal descent is injective** | `concToZAut_injective n x : Function.Injective (concToZAut n x)` — the cube→terminal comparison `φ_x` is injective on vertex groups (categorically: `coverZ` is faithful) | `Braid/CubeTerminalDescent.lean` |

**Retained infrastructure** not on the results' path but kept as finished mathematics:
- the **geometric tensor** `⊗` — full `MonoidalCategory` on `Box`, on `PrecubicalSet` (Day
  convolution), and on `BPSet`, with `cubeDayIso`/`cubeTensorIso`
  (`Foundations/BoxMonoidal.lean`, `DayTensor.lean`, `BPTensor.lean`);
- the **nerve bridge** `realize ⊣ Nerve` between the concrete and topos models
  (`Foundations/Nerve.lean`, `Reachability.lean`).

## Layered layout (folders = areas; deeper layer imports shallower)

`CubeChains.lean` imports the five result modules (+ `Nerve`, `BPTensor` for the retained infra),
so `lake build CubeChains` builds exactly their import cone. Layers:
`Foundations` → `Chains` → `Arrangements` → `Salvetti`, with `Events/` and `Braid/` on top.
`Testing/` is decoupled (not built by `lake build CubeChains`).

### `Foundations/` — stable math fundamentals

*Precubical sets, two models.*
- `PrecubicalConstructions/Basic.lean` — the concrete/computable model: graded cells, `face ε i`,
  the precubical identity, the `Category` instance, extremal vertices.
- `PrecubicalConstructions/StandardCube.lean` — `□ⁿ` concretely (sign-vector cells `Fin N → Option
  Bool`, `none = ∗`), `face`, `nones`.
- `Box.lean` — the box category `Box` (objects = dimensions, maps inherited from the concrete
  model) and the topos `PrecubicalSet := Boxᵒᵖ ⥤ Type` (`HasPushouts` free).
- `Representable.lean` — **cube Yoneda**: `cubeRepr : (□ⁿ ⟶ K) ≃ K.cells n`; `canonicalMap`,
  `trueCount`, `coface`.
- `Bipointed.lean` — `BPSet` (a presheaf with two chosen `0`-cells) + `Hom` + category; `cells`,
  `vertex₀/₁`, `faceMap`/`cubeMap`, `IsAltitude`.
- `Wedge.lean` — `cube n` (representable, bi-pointed), `wedge2 X Y` (pushout of a point),
  `vertexMap`, `serialWedge`.
- `Altitude.lean` — the side conditions `NonSelfLinked` / `AdmitsAltitude` / `Accessible` (`Reach`),
  all `PrecubicalSet`-level, + the `alt_*` lemmas.

*The geometric tensor.*
- `BoxMonoidal.lean` — the **parallel tensor** on `Box`: `▫m ⊗ ▫n = ▫(m+n)`, morphisms concatenate
  sign vectors; `MonoidalCategory Box`. **`Box` is NOT braided** — no block swap exists.
- `DayTensor.lean` — the geometric product on `PrecubicalSet`: Day convolution on `Boxᵒᵖ ⊛⥤ Type`
  (mathlib's `DayFunctor`); `cubeDayIso : □m ⊗ □n ≅ □(m+n)`.
- `BPTensor.lean` — the tensor on `BPSet`: `MonoidalCategory BPSet`, `cubeTensorIso`.

*The model bridge.*
- `Nerve.lean` — `realize : PrecubicalSet ⥤ PrecubicalConstructions`, the nerve
  `Nerve : PrecubicalConstructions ⥤ PrecubicalSet`, `nerveCellEquiv`, `nerveRealizeIso`.
- `Reachability.lean` — `PrecubicalSet`-level reachability and connected components `π₀`.

*Terminal object and computable pushouts.*
- `Terminal.lean` — the terminal precubical set `Z` (one cell per dimension), `Zbp`.
- `GluePushout.lean` — a **computable** pushout of presheaves (mathlib's is `Classical.choice`-opaque).

*The regular-covering / free-groupoid toolkit (the five-lemma's engine).*
- `QuotientCat.lean` — the quotient category `P // G` of an order-free group action on a poset.
- `QuotientCovering.lean` — `quotFunctor : P ⥤ P // G` is a covering of quivers.
- `NerveQuot.lean` — the nerve of `P // G` is the levelwise `G`-quotient of `nerve P`.
- `DeckSequence.lean` — the deck-transformation sequence of the covering (monodromy endpoint,
  middle exactness, injectivity).
- `DeckExact.lean` — packages it as a full short exact sequence with the deck map `deck : Aut → G`.
- `FreeGroupoidLift.lean` — `FreeGroupoid.lift` is **strict** (`lift_spec`/`lift_unique` are
  equalities); a terminal object collapses a free groupoid.
- `ShortFive.lean` — the **non-abelian** short five lemma (`ShortFive.bijective_middle`); mathlib's
  abelian four/five lemma does not apply.

### `Chains/` — the cube-chain category and its theory
- `Basic.lean` — `CubeChain` (junction-vertex representation), `IsCubeChain`, `ofIsCubeChain`.
- `WedgeMap.lean` — bi-pointed maps out of a serial wedge ↔ cube-list data (`wedgeDesc`/
  `wedgeToCubes`); `serialWedge_hom_ext`; the `glue0_*` pushout/mono cores.
- `Correspondence.lean` — **`equivWedgeCat`** [RESULT]; the chain↔wedge-map bijection; thinness.
- `Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category.
- `Category.lean` — `ChainCat`, `chFunctor : BPSet ⥤ Cat`, `Aut.liftToCh`.
- `CubeNonSelfLinked.lean` — `cube_nonSelfLinked`; the concrete↔topos bridge `toStar` for cube cells.
- `BlockDecomp.lean` — block decomposition of a serial-wedge map (`faceEmb`/`blockIdx`/`blockFace`);
  shared by `Salvetti/Lines`.
- `ChainSkeletal.lean` — `Ch(K)` is acyclic and skeletal for **every** `K` (only identity
  endomorphisms); `serialWedge_blockIdx_monotone` — a refinement never reorders beads.
- `ChainPartition.lean` — the chain of an ordered partition of a chain's events.
- `Segal.lean` (+ `SegalAltitude.lean`) — `Ch : BPSet ⥤ Cat` is strong monoidal (wedge ↦ product);
  `chConcat`, `wedgeInclL/R` (the unconditional concatenation).
- `SegalSplit.lean` — the combinatorial heart: a chain in `X ∨ Y` splits `X`-prefix / `Y`-suffix.
- `SegalProd.lean` — `chSegal X Y : Ch X × Ch Y ≌ Ch (X ∨ Y)` and the n-ary `chSegalProd`.

### `Events/` — the events of a cube chain (no side conditions)
- `EventNaming.lean` — `EventObj a` (the events `(bead, direction)` of a chain), `eventMap`,
  `HasGlobalEventNaming`.
- `EventLocalSystem.lean` — functoriality of `eventMap`, the constant event count, the cube base case.
- `EventMapBij.lean` — **`eventMap_bijective` for every `K`, no side conditions**; `eventEquiv`.

### `Arrangements/` — COMs, the braid arrangement, Salvetti posets
See `Arrangements/README.md`.
- `COM.lean` — complexes of oriented matroids (sign vectors, composition `⊙`, `faceLE`), the BCK axioms.
- `Sal.lean` — the Salvetti face poset `Sal L` of a COM (cells `(X, T)` with `X ⊑ T`).
- `SalElements.lean` — `Sal L` as a category of elements of the "topes above" presheaf.
- `ElementsProd.lean` — the external product `F ⊠ G` and `extProdEquiv` on categories of elements.
- `COMSum.lean` — the direct sum `L₁ ⊕ L₂` and `salSumEquiv : Sal(L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`.
- `Braid.lean`, `BraidPreorder.lean`, `BraidCovector.lean` — the braid arrangement `braidCOM n`
  (ground set = ordered pairs of `Fin n`) and its `Fin n` dictionary (`braidSign`, heights,
  ordered set partitions).
- `BraidGeometry.lean` — the braid arrangement as **open convex cones** in `ℝⁿ` (`starCone`).
- `BraidCone.lean` — the **bead cone**: the series timings realize `braidDirectSum dims = ⊕ᵢ A_{dᵢ−1}`.
- `BraidSymmetry.lean` — the `Sₙ` reorientation action on `braidCOM n` (`reorient σ`).

### `Salvetti/` — the concurrency groupoid and the Salvetti comparison
See `Salvetti/README.md` and `Salvetti/BRAID.md`.

*Executions and their groupoid.*
- `Lines.lean` — the chamber presheaf `Lines K : (Ch K)ᵒᵖ ⥤ Type`: a chain ↦ one **chamber** (a
  strict total order of each bead's directions); restriction along the block data.
- `Elements.lean` — `Int(Lines) = (Lines _).Elements` scaffolding + `Ch(□ⁿ) ≌ RefineObj(□ⁿ)`.
- `ConcGroupoid.lean` — `ConcCat K = Int(Lines K)` (objects = **executions**),
  `ConcGrpd K = FreeGroupoid (ConcCat K)`, `PureBraid n`.
- `Normalize.lean` — `evKey` (the total order a line induces — the *frame*) and
  `concGrpdRunEquiv : ConcGrpd K ≌ RunGrpd K` (every execution is 2-iso to a run).
- `LinesWedge.lean` — `linesWedgeEquiv : Int(Lines(P ∨ Q)) ≌ Int(Lines P) × Int(Lines Q)`.

*The Salvetti comparison `braidSalEquiv` (the interpretation bridge).*
- `BraidIso.lean` — **`braidSalEquiv n : Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`** [RESULT].
- `BraidFaceEquiv.lean` — the object dictionary `Face(braidCOM n) ≌ (RefineObj □ⁿ)ᵒᵖ`.
- `BraidSalObj.lean` — the object-map characterization of `braidSalEquiv`.
- `SalBraidPartition.lean` — a cube chain of `□ⁿ` **is** an ordered set partition of `Fin n`.
- `SalBraidChain.lean` — the inverse: the chain built from the partition, + both round trips.
- `SalBraidChamberRank.lean` — the integer rank of a direction in a chamber.
- `SalBraidTope.lean` — chamber tuples on a chain ↔ topes above its covector (`heightOf`).
- `WallCrossing.lean` — the wall-crossing law (the naturality half of `braidSalEquiv`).
- `SalWedge.lean` — `braidSerialSalEquiv dims : Sal(braidDirectSum dims) ≌ Int(Lines(⋁dims))`.
- `BraidReindex.lean` — the `Sₙ` action on the Salvetti category (`salReindex σ`), transported.
- `FZSurj.lean` — essential surjectivity of `FZ = braidSalEquiv ⋙ concToZ` onto the `nEvents = n`
  stratum.

### `Braid/` — the braid group and the cube/terminal identifications

*The braid group and the grading functor.*
- `Germ.lean` — `Braid n` as a `PresentedGroup` by its Garside germ: one generator `[σ]` per
  permutation, one relation per **length-additive** product; `permHom : Bₙ ↠ Sₙ`, `PureBraid n`.
- `Category.lean` — the braid category `𝔅 = Σ n, SingleObj (Braid n)` (objects = strand counts).
- `Artin.lean` — the classical Artin presentation vs. the germ (`GarsideBraid n = ArtinBraid n`).
- `Generated.lean` — adjacent transpositions generate `Braid n` (length-additivity).
- `PermWord.lean`, `BraidWord.lean` — the Artin-word emitter `permWord σ` and `braidWord f`.
- `Crossing.lean` — a pair of events is crossed exactly when its bead is split (the germ relation
  from chain/line semantics — no arrangement).
- `Frame.lean` — the event frame `evKey`/`evIdx` and the transition permutation of an execution.
- `Functor.lean`, `Grading.lean` — `braidGrading K : Int(Lines K) ⥤ 𝔅` (graded by event count);
  functoriality = composable refinements never cross a pair twice.
- `ChGrading.lean` — the same over `Ch K`; the standard line `stdSection` (the cubes are rigid).
- `Naturality.lean` — `braidGrading` is natural in `K`, so it factors through the terminal set.

*The cube is the pure braid group.*
- `CubeViaZ.lean` — `braidGrpd` on `□n` factors through the terminal set (`concToZ`).
- `CubeCovering.lean` — injectivity of the cube→terminal comparison `φ_x` (`concToZAut`).
- `CubeIso.lean` — `braidGrpd (□n)` on the vertex group is an iso onto `Pₙ`.
- `SalvettiConstruction.lean` — the **computable** braid-word map off the Salvetti complex
  (`salvettiConstruction`, faithful by the `salvettiConstruction_faithful` axiom — the sole axiom
  in the cone).
- `SalvettiBridge.lean` — `cubeFrameDiff (braidSalEquiv.obj a) = topePerm a` (cube side = Salvetti side).
- `CubePureBraid.lean`, `CubePureBraidResult.lean` — **`cube_concBraid_pureBraid`** [RESULT].
- `SalQuotZ.lean` — the coverings `coverZ`/`coverSal` of the braid Salvetti model into `ConcGrpd`.

*The terminal five-lemma and descent.*
- `CubeLegOne.lean` — `FZ` is star-bijective (every outgoing morphism lifts uniquely).
- `CubeTerminalDescent.lean` — the descent functor `Ψ`; **`concToZAut_injective`** [RESULT].
- `TerminalSurj.lean` — on the terminal `Zbp` the vertex-group image is the whole `Bₙ`.
- `SalvettiQuotient.lean` — the Salvetti braid grading descended to the `Sₙ`-quotient.
- `SalvettiDeckCompat.lean` — **`braidMonodromy_bijective`** [RESULT]: the right square of the
  five-lemma ladder + `ShortFive.bijective_middle`.
- `Surjectivity.lean` — every pure braid is a concurrency loop (Schreier's lemma on `Pₙ`).
- `ElementaryBraiding.lean` — the elementary adjacent-transposition braiding step.

### `Testing/` — decoupled property-testing harness (NOT built by `lake build CubeChains`)
`native_decide`/`#eval` checks on a computable surrogate. `BraidTest`, `BraidWordCompute`,
`CubeBoundaryBraids`, `CubeRefineBraid`, `EvPermCompute`, `NerveSequences`, `SalvettiSpotCheck`,
`TerminalBraids`, `TerminalPi1`. Helpers `Braid/BraidWord.lean`, `Braid/PermWord.lean` exist only
for these.

## Where do I find…?

- **the box / precubical-set definition** → `Foundations/Box.lean`
- **cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n`** → `Foundations/Representable.lean` (`cubeRepr`)
- **`vertex₀/₁`, `BPSet.Hom`, `cubeMap`/`faceMap`** → `Foundations/Bipointed.lean`
- **the wedge / serial wedge / `wedge2` pushout** → `Foundations/Wedge.lean` (+ `Chains/WedgeMap.lean`)
- **`NonSelfLinked` / `AdmitsAltitude` / altitude lemmas** → `Foundations/Altitude.lean`
- **the geometric tensor `⊗` (`MonoidalCategory`, `cubeTensorIso`)** → `Foundations/BPTensor.lean`
  (built on `DayTensor.lean` / `BoxMonoidal.lean`)
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Foundations/Nerve.lean`
- **the chain category `Ch` / the lift `liftToCh`** → `Chains/Category.lean`
- **chains-are-wedge-maps [RESULT]** → `Chains/Correspondence.lean` (`equivWedgeCat`)
- **Segal monoidality of `Ch`** → `Chains/Segal.lean` (`chSegal` in `SegalProd.lean`)
- **events of a chain / `eventMap` is bijective** → `Events/EventNaming.lean`, `Events/EventMapBij.lean`
- **the braid arrangement `braidCOM n` / COMs** → `Arrangements/Braid.lean`, `Arrangements/COM.lean`
- **executions: `Lines`, `ConcCat`, `ConcGrpd`** → `Salvetti/Lines.lean`, `Salvetti/ConcGroupoid.lean`
- **Salvetti = executions [RESULT]** → `Salvetti/BraidIso.lean` (`braidSalEquiv`)
- **`evKey` (the frame) / normalization to runs** → `Salvetti/Normalize.lean`, `Braid/Frame.lean`
- **the braid group itself (Garside germ), `permHom`, `PureBraid`** → `Braid/Germ.lean`
- **the braid category `𝔅` (objects = strand counts)** → `Braid/Category.lean`
- **the graded braid functor `Int(Lines K) ⥤ 𝔅`** → `Braid/Grading.lean` (`braidGrading`)
- **the cube is the pure braid group [RESULT]** → `Braid/CubePureBraidResult.lean`
- **the terminal five-lemma [RESULT]** → `Braid/SalvettiDeckCompat.lean` (`braidMonodromy_bijective`)
- **terminal descent is injective [RESULT]** → `Braid/CubeTerminalDescent.lean` (`concToZAut_injective`)
- **the deck-covering short exact sequence** → `Foundations/DeckExact.lean` (built on `DeckSequence`,
  `QuotientCovering`, `QuotientCat`, `NerveQuot`)
- **the non-abelian short five lemma** → `Foundations/ShortFive.lean`
- **the strict free-groupoid universal property** → `Foundations/FreeGroupoidLift.lean`

## Build & conventions

- Whole project: `lake build CubeChains` — this builds exactly the import cone of the five results
  (+ `Nerve`/`BPTensor`), so a break here is a break in the results. One slow module:
  `lake build CubeChains.Chains.Correspondence` (~45s). Testing harness (decoupled):
  `lake build CubeChains.Testing.<Module>`.
- The cone rests on a single axiom, `salvettiConstruction_faithful` (`Braid/SalvettiConstruction.lean`)
  — the asphericity / `K(π,1)` input. Everything else is `[propext, Classical.choice, Quot.sound]`.
- **Trust `lake build`, not the IDE** (cross-file diagnostics are stale).
- Use `erw` (not `rw`) for `PrecubicalSet` (functor-category) compositions; rewriting under
  `yonedaEquiv` fails the motive — convert to a plain morphism equation first.
- Dimensions are `ℕ+`; coerce to `ℕ` only inside `cube`.
- **`equivWedgeCat` silently carries `NonSelfLinked` + `AdmitsAltitude`.** Routing through the
  `RefineObj ⟷ Ch` bridge imports both while the statement *looks* unconditional. `Chains/Segal.lean`'s
  `chConcat` / `wedgeInclL/R` are the unconditional replacements.
- Prefer reusing a mathlib construction (Over/comma cats, `FullSubcategory`, Kan extensions,
  `FreeGroupoid`, `Quiver.IsThin`, adhesive/pushout API) over hand-rolling.

## Other docs

- `DESIGN.md` — the conventions/decisions log (precubical identities, universe policy, the
  topos+concrete architecture), with PZ/Z paper references.
- Per-area: `Arrangements/README.md`, `Salvetti/README.md` + `Salvetti/BRAID.md` (why braids).
- `/orient` skill — fast session bootstrap (build, mathlib-reuse table, gotchas).
- Papers: PZ = arXiv:2103.05336, Z = arXiv:1901.05206.
