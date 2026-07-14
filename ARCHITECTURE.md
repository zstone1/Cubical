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
| **Braid enrichment — HDA ⟺ pure braid** | `hasGlobalEventNaming_iff_braidPure : HasGlobalEventNaming K ↔ BraidPure K` — `K` is an HDA exactly when every loop of the flow category gives a **pure** braid. No side conditions on `K`. | `Salvetti/PurityHDA.lean` — **the full account is `BRAID_ENRICHMENT.md` (repo root); read it before touching this thread** |
| **The braid functor** | `braidPhi K n : ConcGrpdN K n ⥤ BraidFib n` into the **germ** braid group for every `K` (`Φ = FreeGroupoid.lift Ψ`; no presentation theorem, no π₁ bridge). `braidGrading K : Int(Lines K) ⥤ 𝔅` is the globally graded form: an execution ↦ the object naming its **event count**, a refinement ↦ `ofPerm (evPerm f)`. `𝔅` is already a groupoid, so `braidGrpd` is a bare `FreeGroupoid.lift` — no `Localization.uniq`. | `Braid/Germ.lean`, `Braid/Functor.lean`, `Braid/Grading.lean` |
| **The enrichment: `CFund`, `Fund`, and the projection** | `EnrichedCategory Cat (CFund K)` (1-cells = executions) and `EnrichedCategory Cat (Fund K)` (1-cells = chains); mathlib's `CatEnriched` makes each a `Bicategory.Strict`, so the strict 2-category costs three laws, not pentagon + triangle + whiskers. `cfundToFund : EnrichedFunctor Cat (CFund K) (Fund K)` forgets the line. | `Flow/CFund.lean`, `Flow/Fund.lean`, `Flow/Project.lean` |
| **Forgetting the line loses only *pure* braids** | A loop of executions whose **chain**-zigzag is trivial has a braid with trivial permutation. So the `Sₙ`-shadow of the braid is a *chain* invariant; the line buys exactly the lift `Sₙ → Bₙ`, and the whole discrepancy lands in `Pₙ`. Split exact, by the standard line. | `Braid/Purity.lean`, `Braid/ChGrading.lean` |
| **A pair of events is crossed at most once** | The germ relation, from the chain/line semantics alone: a `ConcCat` morphism *restricts* the line, so a pair changes order only when its bead is **split**. Different coarse beads are pinned by `blockIdx` monotonicity; a shared fine bead by `Chamber.restrict_lt`. | `Braid/Crossing.lean` |
| **The flow 2-category** | 0-cells = vertices, 1-cells = executions (chain + line), 2-cells = braids; composition of 1-cells is concatenation and is **strict**. `flowHom K u v = ConcGrpd (K.repoint u v)`; the `Cat`-enrichment itself is `Flow/CFund.lean`. | `Flow/Flow.lean`, `Flow/ChainConcat.lean`, `Flow/CFund.lean` |
| **RefineObj ⇔ Ch** | `equivWedgeCat : RefineObj K ≌ ChainCat.Obj K` (under `NonSelfLinked` + `AdmitsAltitude`) | `Chains/Correspondence.lean`; keystone `Refine.pushforward` in `Chains/RefineFunctor.lean` |
| **Cylinder ⇒ pointed functor** | `cylToPointedR : SecCyl K ⥤ PointedEndofunctor (DPathGrpdR K)` (section-primary; an equivalence of the left leg is *one* supplier of the section, not a gate) | `Cylinder/CylinderRefine.lean` (built on `CylinderSweep`/`CylinderRefineCore`) |
| **Directed cobordisms `dCob`** | the category of directed cobordisms of precubical sets (cospans + sieve/cosieve + collars), `idCob = ` cylinder; the merge `{a,b} ⇒ {∗}` has no boundary-fixing iso inverse | `Cobordisms/DCob.lean` + `NonTriviality.lean`; cylinder `Foundations/Cylinder.lean` |
| **Sal(cube) = Int(Lines)** | `braidSalEquiv n : Sal(braidCOM n) ≌ Int(Lines(□ⁿ))` + the serial-wedge generalization. This is the *interpretation* bridge — it is what lets you call the target "braids"; it is **not** an input to `braidFunctor`. | `Salvetti/BraidIso.lean`, `Salvetti/SalWedge.lean` |
| **Schedule space `Sched K`** | timed cube chains, as an **atlas of braid cones** over `Ch K`; stars, principal fibre posets, coarsest-chain cover; needs no labelling | `Schedule/Space.lean`, `Schedule/Cover.lean` — **design: `Schedule/DESIGN.md`** |
| **Local COM at a schedule** | `localCOM x = braidDirectSum x.chain.dims`; realizability (braid ∩ chain cone = `braidDirectSum`); `Sal(localCOM x) ≌ Int(Lines)`; it **measures concurrency** | `Arrangements/BraidCone.lean`, `Arrangements/COMLocal.lean`, `Schedule/LocalCOM.lean`, `Salvetti/SalLocal.lean` |
| **The global chart folds** | two 2-cubes with one boundary: NSL + altitude + run-injective, `Ch K = K_{2,2}` (so `≃ S¹`), yet identical labels ⟹ no global coordinate ambient can model `Sched K` | `Testing/TwoSquares.lean` (`native_decide`) |

**Notation** (global, and it prints): `□n` = `BPSet.cube n`, `⋁d` = `BPSet.serialWedge d`,
`Ch K` = `ChainCat.Obj K`.  (The functor `BPSet ⥤ Cat` is `chFunctor`.)

## Layered layout (folders = areas; deeper layer imports shallower)

`CubeChains.lean` is the root build: `Foundations` → `Chains` → {`Cylinder`, `Cobordisms`,
`Arrangements` → `Salvetti` → `Schedule` → `Flow`}, with `Braid/` a sibling of `Flow/` on top of
`Salvetti`.  `Testing/` is outside it.

`CubeChains/FinalPrecubical/` is **quarantined** — do not read, import, or edit it.

### `Foundations/` — stable math fundamentals (no cube-chain specifics)
- `PrecubicalConstructions/Basic.lean` — concrete precubical sets; `face ε i`, category instance.
- `PrecubicalConstructions/StandardCube.lean` — `□ⁿ` concretely (sign-vector cells), `face`, `topCell`.
- `Box.lean` — the box category `Box`; `PrecubicalSet := Boxᵒᵖ ⥤ Type` (topos; `HasPushouts` free).
- `Representable.lean` — **cube Yoneda** (`canonicalMap`, `cubeRepr`); `trueCount`/`canonicalMap_*`
  combinatorics; `coface`.
- `Bipointed.lean` — `BPSet` (bi-pointed presheaf) + `Hom` + category; `cells`, `vertex₀/₁` and their
  Yoneda/naturality lemmas; `faceMap`/`cubeMap`; the `IsAltitude` predicate.
- `Wedge.lean` — `cube n`, `wedge2` (pushout), `vertexMap` (= `cubeMap`), `serialWedge`.
- `BoxMonoidal.lean` — the **parallel tensor** on `Box`: `▫m ⊗ ▫n = ▫(m+n)`, morphisms concatenate
  sign vectors (`appendCell`); `subst` (= composition, computed), `sign`/`ofSign` (cube Yoneda),
  `MonoidalCategory Box`. **`Box` is NOT braided** — no block swap exists.
- `DayTensor.lean` — the **geometric product** of precubical sets: Day convolution
  (`Boxᵒᵖ ⊛⥤ Type`, mathlib's `DayFunctor`); `cubeDayIso : □m ⊗ □n ≅ □(m+n)` via `CorepBy`
  (LKE of a corepresentable is corepresentable at the image point).
- `BPTensor.lean` — the tensor on `BPSet`: `dayCell` (product cells), `MonoidalCategory BPSet`,
  `cubeTensorIso : □m ⊗ □n ≅ □(m+n)`, `vertex₀/₁_dayCell`.
- `Shift.lean` — box `shift` endofunctor, `PathOb` (cocylinder), `snocFree`/`snocFix`, `endpoint`;
  the geometric `⊗□¹ ⊣ PathOb` infra.
- `PathIterate.lean` — the **iterated cocylinder** `PathObPow n` (`PathObPow 0 = 𝟭`,
  `PathObPow (n+1) = PathObPow n ×_K PathOb`) + the general length-additivity iso `pathObPowGlueIso`.
- `Altitude.lean` — the side conditions `NonSelfLinked` / `AdmitsAltitude` / `Accessible` (`Reach`),
  all `PrecubicalSet`-level, + the `alt_*` lemmas.
- `Nerve.lean` — the concrete↔topos model bridge (`realize`/`Nerve`/`nerveRealizeIso`).
- `Cylinder.lean` — the geometric cylinder `Cyl = realize ⋙ cylC ⋙ Nerve`, `cylCellEquiv`, ends,
  sieve/cosieve. The sole cylinder *object* the build uses.
- `Reachability.lean` — `Reaches`, `π₀`.
- `QuotientCat.lean`, `NerveQuot.lean` — the quotient category `P // G` and its nerve.

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
- `ChainSlice.lean` — **the slice of `Ch K` over a chain `a` is a wedge**:
  `sliceEquiv : Over a ≌ Ch(⋁a.dims)`. Why the braid functor is local (it never reads `K`).
- `CubeNonSelfLinked.lean` — `cube_nonSelfLinked`; the concrete↔topos bridge `toStar` for cube cells.
- `Segal.lean` (+ `SegalAltitude.lean`) — `chConcat : Ch X × Ch Y ⥤ Ch (X ∨ Y)` and its faithfulness
  (via adhesive); `wedgeInclL/R`.
- `SegalSplit.lean` — the combinatorial heart: a chain in `X ∨ Y` splits as an `X`-prefix and a
  `Y`-suffix (`chain_split`).
- `SegalProd.lean` — `chSegal X Y : Ch X × Ch Y ≌ Ch (X ∨ Y)` and the n-ary `chSegalProd`.
- `BlockDecomp.lean` — block decomposition of a serial-wedge map (`faceEmb`/`blockIdx`/`blockFace`);
  pure cube-chain data shared by `Salvetti/Lines` and `Schedule/`.
- `ChainSkeletal.lean` — `Ch(K)` is skeletal for **every** `K`: only identity endomorphisms
  (`ChainCat.eq_of_hom_hom`). Also `serialWedge_blockIdx_monotone` — **a refinement never reorders
  beads** — the face half of the braid functor's functoriality.

### `Arrangements/` — COMs, the braid arrangement, Salvetti posets
See `Arrangements/README.md`.
- `COM.lean` — conditional oriented matroids (`COM`), sign vectors, composition `⊙`, `faceLE` (`⊑`),
  comp-closure (needs FS alone).
- `Sal.lean` — the Salvetti/Paris poset `Sal : COM → Poset` (pairs face ⊑ tope).
- `SalElements.lean` — `Sal L` as a category of elements: `salFunctor L : Face L ⥤ Type`,
  `X ↦ {topes above X}`.
- `Braid.lean`, `BraidPreorder.lean`, `BraidCovector.lean` — the braid arrangement `braidCOM n`
  (ground set = pairs of `Fin n`) and its `Fin n` dictionary (`braidSign`, heights).
- `BraidGeometry.lean` — the braid arrangement as **open convex cones** in `ℝⁿ`: `starCone`,
  `starCone_antitone`.
- `BraidCone.lean` — the **bead cone**: for `dims`, the timings running the beads in series realize
  `braidDirectSum dims = ⊕ᵢ A_{dᵢ−1}`.
- `COMSum.lean` — the direct sum `COM.directSum` and `salSumEquiv : Sal(L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`.
- `SalSum.lean` — the presheaf-level form: `salFunctor (L₁ ⊕ L₂) ≅ faceSum ⋙ (salFunctor L₁ ⊠ salFunctor L₂)`.
- `COMLocal.lean` — `COM.localAt X`, the local COM at a covector (restrict to the walls through the point).
- `ElementsProd.lean` — the external product `F ⊠ G : C × D ⥤ Type` and
  `extProdEquiv : (F ⊠ G).Elements ≌ F.Elements × G.Elements` (mathlib-only, fully general).

### `Salvetti/` — the braid enrichment
**Start at `BRAID_ENRICHMENT.md` (repo root)**; live design notes in `Salvetti/BRAID.md`,
inventory in `Salvetti/README.md`.

*The executions and their groupoid.*
- `Lines.lean` — the chamber presheaf `Lines K : (Ch K)ᵒᵖ ⥤ Type`: a chain ↦ one **chamber** (a
  strict total order of that bead's directions) per bead; restriction along the block data.
- `Elements.lean` — `Int(Lines) = (Lines _).Elements` scaffolding + a reusable mathlib `Elements` API
  (`mapEquivalence`, `pre`/`preEquivalence`, thinness).
- `ConcGroupoid.lean` — `ConcCat K = Int(Lines K)` (objects = **executions** = chain + line) and
  `ConcGrpd K = FreeGroupoid (ConcCat K)`; `PureBraid n`.
- `Normalize.lean` — `evKey` (the total order on events a line induces — *the frame*) and
  `concGrpdRunEquiv : ConcGrpd K ≌ RunGrpd K` (every execution is 2-iso to a run).
- `LinesSlice.lean` — `Lines` is invariant under `ChainCat.pushforward` (`linesPushforward`).
- `LinesWedge.lean` — `linesWedgeEquiv : Int(Lines (P ∨ Q)) ≌ Int(Lines P) × Int(Lines Q)`.
- `FreeGroupoidProd.lean` — `FreeGroupoid (C × D) ≌ FreeGroupoid C × FreeGroupoid D`
  (mathlib `Localization.uniq`; **do not hand-roll**).
- `Reversal.lean` — time reversal `concGrpdReverse : ConcGrpd (K.reverse) ≌ ConcGrpd K`.

*The functor and its characters.*
- `BraidFunctor.lean` — **`braidFunctor K n`**. `Ψ` on objects: face = bead covector, tope = `evKey`
  rank; on morphisms: `evPerm` (the event monodromy). `BraidCat n` = the action category of `Sₙ` on
  `Sal (braidCOM n)`, vertex groups `B n`. Functoriality is `evPerm_smul_le`.
- `BraidCharacters.lean` — the invariants as characters of `Φ`: `writhe_braidPsi` (writhe = inversion
  number of `evPerm`), `salIncl_comp_writhe`, the orientation character `sign_evPerm`.
- `PurityHDA.lean` — **`hasGlobalEventNaming_iff_braidPure`**; `linesRestrict_surjective` /
  `exists_conc_zigzag` (fullness of "forget the line").
- `BraidDeloop.lean` — juxtaposition `BraidCat n × BraidCat m ⥤ BraidCat (n+m)`, the delooping
  `braidDeloopComp` (composition = tensor = `+` on strand counts), the closure of a loop.
- `Braiding.lean` — the interchange of two concurrent blocks **exists and is a braid, not a symmetry**
  (doing it twice is the full twist); `salCross`/`salWind`, the winding character of any finite-ground COM.

*The Salvetti comparison (the interpretation bridge — not an input to `braidFunctor`).*
- `BraidIso.lean` — `braidSalEquiv n : Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`.
- `BraidFaceEquiv.lean` — the object dictionary `Face (braidCOM n) ≌ (RefineObj □ⁿ)ᵒᵖ`.
- `SalBraidPartition.lean` — a cube chain of `□ⁿ` **is** an ordered set partition of `Fin n` (`blockOf`).
- `SalBraidChain.lean` — the inverse: the chain built from the partition, + both round trips.
- `SalBraidChamberRank.lean` — the integer rank of a direction in a chamber.
- `SalBraidTope.lean` — chamber tuples on a chain ↔ topes above its covector (`heightOf`).
- `WallCrossing.lean` — the wall-crossing law (the naturality half of `braidSalEquiv`).
- `SalWedge.lean` — `braidSerialSalEquiv dims : Sal(braidDirectSum dims) ≌ Int(Lines(⋁dims))`.
- `SerialSalLines.lean` — the presheaf-level form; the slice corollary **`salFunctorSlice`**.
- `SalLocal.lean` — the same, read at a *schedule*: `Sal (localCOM x)` = the strata of `x`'s open star.

### `Events/` — the events of a cube chain (the braid thread depends on these)
Depends only on `Chains/` + `Salvetti/Lines`-`SalBraidPartition`; **never on `Schedule/`**.
- `EventNaming.lean` — `EventObj a` (the events `(bead, direction)` of a chain), `eventMap`,
  `HasGlobalEventNaming`; coherence is free, the content is fibre-injectivity.
- `EventLocalSystem.lean` — functoriality of `eventMap`, the constant event count
  (`card_eventObj_eq_of_hom`), and the cube base case of fibre-injectivity.
- `EventMapBij.lean` — **`eventMap_bijective` for every `K`, no side conditions**; the event
  bijection `eventEquiv`. Everything about the monodromy `ρ` rests on this.
- `OrdSign.lean` — `ordSign` (compares two *explicit* linear orders on one finite type, cocycle
  `ordSign_trans`); the orientation character `orSign` = `w₁(Sched K)` and `Orientable`.

### `Schedule/` — the schedule space `Sched K` (an atlas of braid cones)
**Start at `Schedule/DESIGN.md`** (inventory: `Schedule/README.md`; Morse theory: `Schedule/MORSE.md`).

*The atlas.*
- `Space.lean` — `Sched K = Σ c : Ch K, Stratum c` (a chain + strictly increasing bead times); charts
  `Chart a ↪ ℝ^(EventObj a)`; `IsAtlas`.
- `Cone.lean` — `schedCone a`, THE chart cone (one coordinate per **event**, so nothing folds).
- `Atlas.lean` — the chart of a chain is a **bijection** onto its cone (the tie-block decomposition).
- `Cover.lean` — stars, `mem_star_iff`, the fibre over a schedule is a **principal** up-set,
  the coarsest-chain cover.
- `Orientation.lean` — a coherent event naming trivialises `w₁(Sched K)`
  (`orientable_of_hasGlobalEventNaming`); `orChar : Ch K ⥤ SingleObj ℤˣ`.

*The local COM.*
- `LocalCOM.lean` — `localCOM x = braidDirectSum x.chain.dims`; trivial exactly at generic schedules.
- `COMSheaf.lean` — the local COM is the **localization** of any chart's COM at the point; refining a
  stratum deletes walls (a COM minor).

*The label / global-chart layer (kept, but it folds — `Testing/TwoSquares.lean` — so it is not foundational).*
- `HDA.lean` — an `EdgeLabelling` (opposite edges of a square get the same label) as **input data**;
  `evLabel`, `RunInjective`.
- `Sculpture.lean` — a `K` embedded in one big cube is run-injective.
- `LabelChart.lean` — `labelTime : Sched K → (A → ℝ)`; a chart, **not** injective.
- `LabelSpace.lean` — the image `labelSpace ℓ`, its cover and Galois connection.
- `ChainCone.lean` — the chain → open-convex-cone functor (`labelCone`, the label-indexed cone).
- `Horizon.lean` — occurrence signs: fix the time origin at the horizon, read "did it fire" off the
  sign of the coordinate.

### `Flow/` — the directed flow 2-category, and its `Cat`-enrichment
- `ChainConcat.lean` — **`BPSet.repoint K u v`** (re-point `K` at chosen vertices; `K.repoint K.init
  K.final = K` is `rfl`), so `Ch (K.repoint u v)` is "the chains from `u` to `v`"; and the strictly
  associative/unital concatenation `chConcatAt K u v w`.
- `Flow.lean` — the 2-category: 0-cells = vertices, 1-cells = executions, 2-cells = braids;
  `flowHom K u v = ConcGrpd (K.repoint u v)`, `flowComp`. Composition is **strict** (`List.append`).
  The hard theorem is `linesRestrict_chConcMor` — refining each factor restricts the concatenated
  line blockwise, i.e. composition is a functor.
- `CFund.lean` — `EnrichedCategory Cat (CFund K)`. Enrich in `Cat`, not `Grpd` (mathlib gives `Grpd`
  no monoidal structure) and not the slice; `CatEnriched` then hands back `Bicategory.Strict`.
  Composition is `concGrpdConc` via `lift₂` — **not** `freeGroupoidProdEquiv`, which is
  `Localization.uniq` and so pinned only up to natural iso.
- `Fund.lean` — `EnrichedCategory Cat (Fund K)`: `CFund` with the line deleted. Hom-object is
  `FreeGroupoid ((Ch (K;u,v))ᵒᵖ)` — the *opposite*, since `ConcCat` is a category of elements over
  `Ch`, which is what makes it `CFund`'s projection target.
- `Project.lean` — `cfundToFund : EnrichedFunctor Cat (CFund K) (Fund K)`. `map_comp` is the content
  (forgetting the line commutes with concatenation) and on generators it is `rfl`.

### `Braid/` — the braid group by its Garside germ, and the graded functor
- `Germ.lean` — `Braid n` as a `PresentedGroup`: one generator `[σ]` per permutation, one relation
  per **length-additive** product. Artin's relations are consequences, not axioms. `permHom : Bₙ ↠ Sₙ`,
  `PureBraid n = ker permHom`, and `writheHom` (which the germ makes a two-line `toGroup`).
- `BlockPerm.lean`, `Jux.lean` — juxtaposition: no strand of one block ever crosses a strand of the
  other, so `permLen` adds and the germ relations survive.
- `Category.lean` — `Braids = Σ n, SingleObj (Braid n)`. Objects carry **only** the strand count, so
  `⊗` associativity is `Nat.add_assoc`, not a `HEq` across Salvetti cells. It is a groupoid.
- `Crossing.lean` — the crossing criterion (see the headline table). No arrangement.
- `Functor.lean`, `Grading.lean` — `braidPhi` (per stratum) and `braidGrading`/`braidGrpd` (graded by
  event count). `Grading` bridges the strata: `ConcCatN K n` is a *full* subcategory, so an execution
  sits in any stratum its count allows (`homAt`), and `permLen` is blind to the `finCongr` transport.
- `ChGrading.lean` — `chBraid`, the same functor over `Ch K`. It exists because `faceEmb` is an
  **order embedding** (the cubes are rigid), so the standard line — order each bead by axis index — is
  coherent. Hence a strict section `stdSection` of "forget the line". *The line is not what makes a
  braid functor definable; it is what supplies the loops.*
- `Purity.lean` — the short exact sequence (see the headline table).

### `Cylinder/` — the cylinder ⇒ pointed-endofunctor program
- `PointedFunctor.lean` — `PointedEndofunctor` + the groupoid conjugation API
  (`pointedOfPaths`/`pointedFunctorOfObj`/`pointedHomOfGroupoid`); the **section** datum `DPathSection`
  (`= Lstar + unit : 𝟭 ≅ Lstar ⋙ F`, a one-sided section up to iso, strictly weaker than
  `IsEquivalence`) with `ofEquivalence`/`comp`/`transport`/`mapFreeGroupoid`; uses mathlib `FreeGroupoid`.
- `Cylinder.lean` — the prism core: `cylTranspose`, `CylMap` (= `Over (PathOb K)`), `prism`,
  `coface_prism`, `isCubeChain_append`.
- `CylinderRefineCore.lean` — geometry: `DPathGrpdR`, `CylMapR`, `Refine.pushforwardBP`, `blockQ`,
  the cospan pieces `refineEndG`/`refinePrismG`/`refineCofaceG`/`refineEdgeG` + bridge cofaces.
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
  composite's left leg (`composeSectionRefine`/`composedPointedObj`), carrying two explicit
  hypotheses `PushforwardBPComp` + `RefinePreservesPullback`.

### `Cobordisms/` — directed cobordisms of precubical sets (`dCob`)
Built on the `Foundations` cylinder layer (`Nerve`/`Cylinder`/`Reachability`). Inventory: `Cobordisms/MAP.md`.
- `DirectedBoundary.lean` — `IsSieve`/`IsCosieve`, `StronglyConnected`, loop-barrier lemmas.
- `Loops.lean` — `IsLoopFree`/`LoopConfined`, loop-freeness inheritance.
- `Cospan.lean` — `Cospan` + pushout composition `Cospan.comp`, disjoint legs via van Kampen.
- `Flags.lean` — `srcImage`/`sinkImage`, `Closed`/`Spanning`; the ∅-bottom theorem
  `no_closed_cobordism_from_empty`.
- `FlagsComp.lean` — `Spanning`/`Closed` are preserved by the pushout composite.
- `Union.lean`, `Collar.lean` — the `⊔` operation; `SourceCollar`/`SinkCollar` + `cylCospan`.
- `Cobordism.lean` — the `DirectedCobordism X Y` bundle; `idCob = ` cylinder.
- `Composition.lean` — the pushout-closure `DirectedCobordism.comp` (the reachability-in-pushout
  **barrier**, the technical heart).
- `Associativity.lean` — the pushout **associator**: composition is associative only up to a
  boundary-fixing iso of the middle objects.
- `DCob.lean` — the rel-∂ quotient `cobordismRel`/`HomCob` and the `Category dCob`.
- `NonTriviality.lean` — the merge `{a,b} ⇒ {*}` is non-invertible via a π₀ invariant.

### `Testing/` — decoupled property-testing harness (NOT built by `lake build CubeChains`)
A computable `FinBPSet` surrogate for `Ch K` (`Model.lean`) driving `native_decide`/`#eval` checks.
The load-bearing witnesses: `TwoSquares.lean` (the global chart folds),
`EventNamingCounterexample.lean` (the "trinity" — NSL + altitude does **not** give a global event
naming), `Lowering.lean`, `Examples.lean`, the cylinder probes.

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
- **the slice of `Ch K` over a chain (it is a wedge)** → `Chains/ChainSlice.lean`
- **the braid enrichment, HDA ⟺ pure braid [headline]** → `Salvetti/PurityHDA.lean` (account: `BRAID_ENRICHMENT.md`)
- **the braid group itself (Garside germ), `permHom`, `PureBraid`, `writheHom`** → `Braid/Germ.lean`
- **the braid category `𝔅` (objects = strand counts)** → `Braid/Category.lean`
- **the graded braid functor `Int(Lines K) ⥤ 𝔅`** → `Braid/Grading.lean` (`braidGrading`, `braidGrpd`)
- **why composable refinements never cross a pair twice** → `Braid/Crossing.lean`
- **forgetting the line loses only pure braids / the exact sequence** → `Braid/Purity.lean`
- **the standard line, and the Ch-side braid functor** → `Braid/ChGrading.lean` (`stdSection`, `chBraid`)
- **the *older* Salvetti-cell braid functor `Φ : ConcGrpdN K n ⥤ BraidGrpd n`** → `Salvetti/BraidFunctor.lean` (its **characters** — event monodromy, writhe, `w₁` — are `Salvetti/BraidCharacters.lean`, and are still load-bearing)
- **executions: the chamber presheaf `Lines`, `ConcCat`, `ConcGrpd`** → `Salvetti/Lines.lean`, `Salvetti/ConcGroupoid.lean`
- **`evKey` (the frame) / normalization to runs** → `Salvetti/Normalize.lean`
- **the flow 2-category / `BPSet.repoint`** → `Flow/Flow.lean`, `Flow/ChainConcat.lean`
- **`CFund` / `Fund` / the projection between them** → `Flow/CFund.lean`, `Flow/Fund.lean`, `Flow/Project.lean`
- **`lift₂` (the *strict* product universal property) / a terminal object collapses a free groupoid** → `Foundations/FreeGroupoidLift.lean`
- **events of a chain / `eventMap` is bijective** → `Events/EventNaming.lean`, `Events/EventMapBij.lean`
- **`orSign` / `Orientable` / comparing two explicit orders (`ordSign`)** → `Events/OrdSign.lean`
- **`w₁(Sched K)` is trivial for an HDA** → `Schedule/Orientation.lean`
- **`PathOb` / box shift / `⊗□¹⊣PathOb`** → `Foundations/Shift.lean`
- **`PointedEndofunctor` + groupoid API** → `Cylinder/PointedFunctor.lean`
- **the cylinder prism core / `CylMap`** → `Cylinder/Cylinder.lean`
- **the cylinder ⇒ pointed functor [RESULT 2]** → `Cylinder/CylinderRefine.lean`
- **directed cobordisms / the category `dCob`** → `Cobordisms/DCob.lean` (overview: `Cobordisms/MAP.md`)
- **the cylinder object `Cyl` (the geometric tensor `- ⊗ □¹`)** → `Foundations/Cylinder.lean`
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Foundations/Nerve.lean`
- **`PrecubicalSet` reachability / `π₀`** → `Foundations/Reachability.lean`
- **`dCob` non-triviality (∅-bottom, merge not invertible)** → `Cobordisms/NonTriviality.lean` (+ `Flags.lean`)
- **`Sal(braidCOM n) ≌ Int(Lines)` [Salvetti]** → `Salvetti/BraidIso.lean`
- **the schedule space (the atlas)** → `Schedule/Space.lean`
- **the local COM (it measures concurrency)** → `Schedule/LocalCOM.lean`, `Arrangements/COMLocal.lean`
- **the label-chart image / Galois connection / good cover** → `Schedule/LabelSpace.lean`
- **the quotient category `P // G` + its nerve** → `Foundations/QuotientCat.lean`, `Foundations/NerveQuot.lean`

## Build & conventions

- Whole project: `lake build CubeChains`. One module: `lake build CubeChains.Chains.Correspondence`
  (the slow one, ~45s). Testing harness: `lake build CubeChains.Testing.Examples`.
- **Trust `lake build`, not the IDE** (cross-file diagnostics are stale).
- Use `erw` (not `rw`) for `PrecubicalSet` (functor-category) compositions; rewriting under
  `yonedaEquiv` fails the motive — convert to a plain morphism equation first.
- Dimensions are `ℕ+`; coerce to `ℕ` only inside `cube`.
- **`equivWedgeCat` / `refineToWedge` / `RefineConcat.append` carry `NonSelfLinked` + `AdmitsAltitude`.**
  Routing through the `RefineObj ⟷ Ch` bridge silently imports both while the statement *looks*
  unconditional. `Chains/Segal.lean`'s `chConcat` / `wedgeInclL/R` are the unconditional replacements.
- Prefer reusing a mathlib construction (Over/comma cats, `FullSubcategory`, Kan extensions,
  `FreeGroupoid`, `Quiver.IsThin`, adhesive/pushout API) over hand-rolling — see `Chains/Slice.lean`
  as the in-repo exemplar.

## Other docs

- `BRAID_ENRICHMENT.md` — the braid-enrichment result: what it is, its proof structure, the
  load-bearing lemmas, and the two places the naive statement is false. **The single most important
  doc here.** (The Lean landmines and the cleanup plan are *not* in it — they are in beads; the
  landmines are pinned at `Cubical-hic`.)
- `DESIGN.md` — the conventions/decisions log (with PZ/Z paper references).
- Per-area: `Arrangements/README.md`, `Salvetti/README.md` + `Salvetti/BRAID.md`,
  `Schedule/README.md` + `Schedule/DESIGN.md` + `Schedule/MORSE.md`, `Cobordisms/MAP.md`.
- `/orient` skill — fast session bootstrap.
- Papers: PZ = arXiv:2103.05336, Z = arXiv:1901.05206.
