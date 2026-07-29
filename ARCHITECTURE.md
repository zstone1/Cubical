# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of the **concurrency braid groupoid** of a
precubical set: the executions of a cube chain, made into a groupoid, and the theorem that this
groupoid is the (pure) braid group. **Read this first to find the right file**, then open that
one file (+ its module docstring) — you should never need the whole tree in context.

Two models of precubical sets coexist: the **concrete/computable** one
(`Foundations/PrecubicalConstructions/`, graded cells + face maps) and the **topos** one
(`PrecubicalSet := Boxᵒᵖ ⥤ Type`), bridged by the cube Yoneda lemma
(`Foundations/Representable.lean`). The topos model is the default everywhere downstream.

**Why braids.** `(GeoBP, ⊗ᵍ)` is monoidal but has **no swap** — `Box` is rigid (`Aut ▫k = {id}`,
the symmetry-free convention), so no block transposition `▫(m+n) ⟶ ▫(n+m)` exists. The braiding
is *created* by the passage to executions, not inherited: two interleavings of independent events
are isomorphic, not equal, and the iso has a winding number. Independent actions do not commute —
they braid.

## The headline results

`Ch K = ChainCat.Obj K`, `□n = BPSet.cube n`, `⋁d = BPSet.serialWedge d`, `Int(F) = F.Elements`,
`Ch⋆ K = (Lines K).Elements`, `Run K` = the all-edges full subcategory of `Ch K`.

| Result | Statement | Lives in |
|---|---|---|
| **Chains are wedge maps** | `equivWedgeCat : RefineObj K ≌ Ch K` (under `NonSelfLinked` + `AdmitsAltitude`) — a refinement of a chain is the same as a bi-pointed map out of a serial wedge | `Chains/Correspondence.lean` |
| **Chains are braid faces** | `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)`, `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face` — a chain of `□ⁿ` is an ordered set partition of `Fin n`; `reflectHom` is the computable converse | `Salvetti/ChainBraidFace.lean` |
| **No double crossing** | `permOf_noDoubleCross` — crossing permutations are length-additive, hence `braidFunctor : RunWedge ⥤ FullBraid` and `ConcPos K = proj K ⋙ braidFunctor` | `Salvetti/EventBraid.lean` |
| **Executions are word + composition** | `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` — an execution is a chain together with a run word linearizing it; `fexecChStarEquiv` is the enumerable model | `Salvetti/ExecData.lean`, `Testing/FastEquiv.lean` |
| **The crossing permutation is the word change** | `stepPerm_eq : stepPerm f = (runWord x).trans (runWord y).symm` — `ConcPos`'s label is "position in the source's run word ↦ position in the target's" | `Salvetti/RunWord.lean` |
| **Salvetti = executions** | `braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□ⁿ)` — a cell is a face below a tope, i.e. a chain plus a word; the wall crossing `T' = X' ⊙ T` is the arrow rule | `Salvetti/SalExec.lean` |
| **`ConcPos` reads the cell structure** | `outLabels_eq_parabolic` — the crossing permutations out of an execution are exactly the parabolic `S_{d₁}×⋯×S_{d_k}` of its bead dimensions, so `Δ` is available iff the top cell is present | `Testing/Parabolic.lean` |
| **Vertex group of a free groupoid, presented** | `presentationEquiv (S : Spanning C x) : End (mk x : FreeGroupoid C) ≃* Pres S` — for a **general** category: no thinness, finiteness or acyclicity | `Foundations/FreeGroupoidPresentation.lean` |

**Not in this tree.** `conc_loop_iff` is *not* here — commit `0f60540` deleted the nine-file layer
that carried it (`Conc`, `ConcPure`, `ConcCube`, `ConcNontrivial`, `BraidSal`, `CubeTope`, `Flips`,
`TopeLines`, `TopeSal`). What replaced it is shorter: `Flips` (470 lines, the braid functor) is now
`Salvetti/EventBraid` (236), `CubeTope` (260, the tope map) is now `Salvetti/RunWord` (200), and
`BraidSal`+`TopeSal` (250 lines of Yoneda `betaMap`) are now `Salvetti/SalExec`, which reads the
Salvetti order off run words instead of comparing presheaves.

⚠ `CubeChains.lean` still imports the deleted `Salvetti/ConcCube`, so **`lake build CubeChains` is
red** and has been since `0f60540`. Sweep with the `find` command below instead.

**Retained infrastructure** not on the results' path but kept as finished mathematics:
- the **geometric tensor** `⊗ᵍ` — full `MonoidalCategory` on `Box`, on `PrecubicalSet` (Day
  convolution), and on the alias `GeoBP := BPSet`, with `cubeDayIso`/`cubeTensorIsoBP`
  (`Foundations/BoxMonoidal.lean`, `DayTensor.lean`, `GeoTensor/BP.lean`);
- the **nerve bridge** `realize ⊣ Nerve` between the concrete and topos models
  (`Foundations/Nerve.lean`, `Reachability.lean`).

## Layered layout (folders = areas; deeper layer imports shallower)

`CubeChains.lean` is a hand-picked list of results, not a sweep: `lake build CubeChains` builds
exactly its import cone, and modules outside that cone are not checked by it. Layers:
`Foundations` → `Chains` → `Arrangements` → `Salvetti` (the executions and the Salvetti
comparison), with `Braid/` (the braid group itself: `Germ`, `Category`, `Artin`, `Generated`,
`PermWord`, `SalvettiConstruction`) as an independent sibling that nothing else imports.

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
- `Wedge.lean` — `cube n` (representable, bi-pointed), `wedge2 X Y` = `X ∨ Y` (pushout of a point),
  `vertexMap`, `serialWedge` = `⋁d` (the fold `List.foldr (□· ∨ ·) (□0)`).
- `WedgeMonoidal.lean` — the wedge as the **default** `instance : MonoidalCategory BPSet`
  (tensor `∨`, unit `□0`, associator `wedge2Assoc`, unitors, pentagon + triangle).
- `Altitude.lean` — the side conditions `NonSelfLinked` / `AdmitsAltitude` / `Accessible` (`Reach`),
  all `PrecubicalSet`-level, + the `alt_*` lemmas.
- `HomMonoidal.lean` — the three instances mathlib lacks (the two-variable `Functor.hom` is lax
  monoidal; `F.op` is monoidal when `F` is; `discreteOp`), so a functor `k ↦ (A k ⟶ B k)`
  *inherits* its lax monoidal structure through `D ⥤ Cᵒᵖ × C ⥤ Type` instead of carrying
  hand-written coherence; plus `LaxMonoidal.Graded F`, the total monoid `Σ m, F m`.
- `MonoidalTransport.lean` — transporting `⊗ₘ` along a tensorator `μ : A ⊗ B ≅ P`, stated in an
  arbitrary monoidal category so that `rw`/`simp`/`monoidal` behave where they would not at `BPSet`.

*The geometric tensor.*
- `BoxMonoidal.lean` — the **parallel tensor** on `Box`: `▫m ⊗ ▫n = ▫(m+n)`, morphisms concatenate
  sign vectors; `MonoidalCategory Box`. **`Box` is NOT braided** — no block swap exists.
- `DayTensor.lean` — the geometric product on `PrecubicalSet`: Day convolution on `Boxᵒᵖ ⊛⥤ Type`
  (mathlib's `DayFunctor`); `cubeDayIso : □m ⊗ □n ≅ □(m+n)`.
- `GeoTensor/BP.lean` — the geometric tensor on bi-pointed sets, written `X ⊗ᵍ Y`
  (`GeoTensor.tensorObjBP`), carried by the alias `GeoBP := BPSet`; `cubeTensorIsoBP : □m ⊗ᵍ □n ≅
  □(m+n)`.  It lives on its own alias because bare `⊗` on `BPSet` is the **wedge**.

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
- `FreeGroupoidPresentation.lean` — `presentationEquiv` / `autPresentationEquiv` for a general
  category, with `Spanning` (a transversal) and `Spanning.ofInitial`. Imports nothing from
  `CubeChains`.
- `ShortFive.lean` — the **non-abelian** short five lemma (`ShortFive.bijective_middle`); mathlib's
  abelian four/five lemma does not apply.

### `Chains/` — the cube-chain category and its theory
- `Basic.lean` — `CubeChain` (junction-vertex representation), `IsCubeChain`, `ofIsCubeChain`.
- `WedgeMap.lean` — bi-pointed maps out of a serial wedge ↔ cube-list data; `wedgeDesc … :
  ⋁(cubes.map (·.1)) ⟶ K.repoint a b` (re-pointing the target is what makes the endpoint
  conditions the morphism's own `app_init`/`app_final`), `wedgeToCubes`, `serialWedge_hom_ext`,
  the `glue0_*` pushout/mono cores.
- `Correspondence.lean` — **`equivWedgeCat`** [RESULT]; the chain↔wedge-map bijection; thinness.
- `Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category.
- `Category.lean` — `ChainCat`, `chFunctor : BPSet ⥤ Cat`, `Aut.liftToCh`.
- `CubeNonSelfLinked.lean` — `cube_nonSelfLinked`; the concrete↔topos bridge `toStar` for cube cells.
- `BlockDecomp.lean` — block decomposition of a serial-wedge map (`faceEmb`/`blockIdx`/`blockFace`);
  shared by `Salvetti/`.
- `ChainRestrictions.lean` — `restrictCubeChain face C` projects a chain of `□ᵇ` onto the directions
  a face uses, dropping the cubes that collapse. Not a precubical map (`Box` has no degeneracies)
  and **not** natural in `face` as a cube map — it factors through `faceEmb`, so there is no
  universal property over `Box` to look for. `EdgeChain K` and `EdgeChain.restrict` (+ `_id`/`_comp`)
  are the all-edges subpresheaf this cuts out.
- `ChainSkeletal.lean` — `Ch(K)` is acyclic and skeletal for **every** `K` (only identity
  endomorphisms); `serialWedge_blockIdx_monotone` — a refinement never reorders beads.
- `Segal.lean` (+ `SegalAltitude.lean`) — the append iso `serialWedgeAppend : ⋁x ∨ ⋁y ≅ ⋁(x ++ y)`,
  built **structurally** from `λ_`/`α_`/whiskering (so its coherence is monoidal, not a pushout
  chase); `wedgeInclL/R` are derived from it; `concatChainMap = (serialWedgeAppend …).inv ≫
  (a.map ⊗ₘ b.map)`; `chConcat` (the unconditional concatenation).
- `WedgeLaxMonoidal.lean` — `chFunctor` is lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`; its coherence is
  *derived* from `serialWedgeAppendIso_assoc` rather than re-proved.
  `Segal.lean` also carries `⋁` as a **strong monoidal** functor
  `serialWedgeFunctor : DimList ⥤ BPSet`, where `abbrev DimList := Discrete (FreeMonoid ℕ+)`
  (tensor = list append), with the reusable coherence squares `serialWedgeAppend_assoc` /
  `_left_unitality` / `_right_unitality`.
- `Split.lean` — the **choice-free** inverse of `chConcat`: a chain in `X ∨ Y` splits into an
  `X`-prefix and a `Y`-suffix (`splitObj`, both round trips on the nose; `chSplit`, `chSegal`),
  built on the computable cell-side discriminator `Glue.cellSide`; and `splitWedgeMorphism`, the
  same split for a bare map `⋁as ⟶ X ∨ Y`, which is the form `Salvetti/Runs.lean` consumes.
- `WedgeExtend.lean` — extension of wedge maps along the append iso.
- `CubeVtx.lean` — vertices of cube faces (`cubeVtx`), the monotonicity the coordinate coend needs.
- `PshExtMonoidal.lean` — `pshExtFunctor F = BPSet.toPshFunctor.op ⋙ yoneda.obj F`, so
  `Lines K a = (⋁a.dims).toPsh ⟶ runPresheaf` literally, and its monoidal structure.
- `CoordFunctor.lean` — the **coordinate coend**: `coordFlip χ : beadEvent a ≃ Fin m` for
  `χ : ⋁a ⟶ □m`, `coordMap`/`coordMapEquiv` for wedge maps, `coordFlip_comp` (the engine behind the
  label theorem) and `coordMap_eq` (its `blockIdx`/`blockFace` form).

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
- `BraidSymmetry.lean` / `SalSymmetry.lean` — the `Sₙ` reorientation action on `braidCOM n`
  (`reorient σ`) and the induced action on `Sal`.

### `Salvetti/` — executions
See `Salvetti/README.md` and `Salvetti/BRAID.md`.
- `Runs.lean` — the **run presheaf** `Lines K : (Ch K)ᵒᵖ ⥤ Type`, `a ↦ Run a.dims`. A *run* is an
  all-edges cube chain: `Run K` is the full subcategory of `Ch K` cut out by `IsRun`, and it is
  discrete. Runs of a cube assemble into `runPresheaf : Boxᵒᵖ ⥤ Type`, so by `Chains/PshExtMonoidal`
  a run of `⋁a` *is* a map `(⋁a).toPsh ⟶ runPresheaf` (`runPshEquiv`), and `runRestrict` along a
  wedge map is transpose–precompose–assemble. `runFunctor : BPSet ⥤ Cat` is lax monoidal, by
  restricting `chFunctor`'s structure to runs.
- `Elements.lean` — `Ch⋆ K = (Lines K).Elements` scaffolding: `Functor.elements_isThin`,
  `mapEquivalence`, `pre`/`preEquivalenceComp`, and the thinness of `Ch (□ⁿ)`.
- `Covering.lean` — `proj`/`π` are discrete opfibrations, so a `Ch⋆` morphism out of `p` is *forced*
  by a base `Ch` morphism.
- `EventPerm.lean` — `beadEvent`, the run-free flattening `pos = finSigmaFinEquiv`, the event
  relabelling `eventEquiv f = coordMapEquiv (wedgeMap f)`, and `eventEquiv_mk` (its `blockIdx` /
  `blockFace` form) — the computational handle on everything downstream.
- `RunSegal.lean` — **the Segal decomposition of a linearization**: a run performs bead `i` at
  exactly the prefix-sum interval, in that bead's own order (`coordMap_fst_run_iff` as an *iff*,
  `coordFlip_run_concat`). Gives `runProj` its first computational characterization
  (`runProj_zero`/`_succ`, via `pshOfRun_inr`), so the sealed `runSplit`/`runSegalProd` stay sealed.
- `RunRestrict.lean` — **face restriction preserves the run order**: `EdgeChain.restrict` is a
  `List.filterMap`, which keeps survivors in order (`exists_strictMono_filterMap`), hence
  `localStep_restrict{,_lt_iff,_rank}`.
- `EventBraid.lean` — the **run order** `runOrd`, the crossing permutation `permOf`, and
  `permOf_noDoubleCross` [RESULT]. Its two former `sorry`s are the leaves
  `runOrd_within_localStep` (from `RunSegal`) and `localStep_restrict_lt_iff` (from `RunRestrict`).
  Then `braidFunctor`, `ConcPos K = proj K ⋙ braidFunctor`, and `Conc K = FreeGroupoid.lift (ConcPos K)`.
- `ChainBraidFace.lean` — the **base comparison** `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)` and
  `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face`. `beadOf b q` is the bead flipping coordinate `q`;
  `ofBlockMap` rebuilds a chain from its block map; `reflectHom` is the **computable** converse
  (`chFace b ⊑ chFace a` reconstructs `a ⟶ b`).
- `RunWord.lean` — the **run word** `runWord x : Perm (Fin n)` (which direction fires at each step),
  `stepPerm_eq` [RESULT], and the **arrow rule** `runWord_group` / `runWord_within`: across beads the
  finer execution runs in its own bead order, inside a bead it inherits the coarser one's. The route
  factors `permOf` through `coordFlip` of the *total* run map, so it needs neither the Segal
  decomposition nor `coordMapEquiv`'s inverse.
- `ExecData.lean` — `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` [RESULT], a chain plus a linearization
  refining it. `ofWord` builds one from `reflectHom`, so it computes; `ext_runWord` (thinness of
  `Ch (□ⁿ)`) is what makes an enumeration of words complete.
- `SalExec.lean` — `braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□ⁿ)` [RESULT]. `wordTopeEquiv` reads
  topes as run words (a tope's chain has injective `beadOf`, hence one direction per bead);
  `wordTope_runWord` is the wall crossing `T' = X' ⊙ T`, whose two branches are exactly the arrow
  rule's two clauses; `exists_hom` is the converse, via `reflectHom` plus opfibration forcing.
- `ConeRelations.lean` — the cone lemma in usable form: `cmp hy hz` compares two objects *through a
  lower bound* and `cmp_trans` telescopes, so any two routes through `↑b` with the same endpoints
  agree. Since a tope absorbs, every tope over a face `X` lies over the one cell `(X, T₀)`, so
  **both Artin relations are `cross_trans`** (`cross_square`, `cross_hexagon`). `chamber_le` /
  `homMk_eq_cmp_chamber` are the dual move for generation: every arrow is a `cmp` at the chamber of
  its source's run word.
- `SalBraid.lean` — `crossPerm = stepPerm` across `braidSalEquiv` (`topeRank` of a run word is the
  step at which the coordinate fires), so `crossPerm_noDoubleCross` **is** `permOf_noDoubleCross`;
  then `salvettiGrading` / `salvettiConstruction` and the `salvettiConstruction_faithful` axiom.
- `RunWedgeZ.lean` — `RunWedge ≌ Ch⋆ Zbp`, with a hand-built inverse so it computes.

### `Braid/` — the braid group itself
- `Germ.lean` — `Braid n` as a `PresentedGroup` by its Garside germ: one generator `[σ]` per
  permutation, one relation per **length-additive** product; `permHom : Bₙ ↠ Sₙ`, `PureBraid n`.
- `Kernel.lean` — Schreier for a group with a set-section `t` of `φ : G →* Q`:
  `ker φ = ⟨t q · t s · t (q·s)⁻¹⟩`. Here the transversal `ofPerm` *is* the generating set, so
  `pureBraid_le` asks only for the conjugated cocycles — the words a zigzag of refinements reads.
- `Category.lean` — the braid category `𝔅 = Σ n, SingleObj (Braid n)` (objects = strand counts).
- `Artin.lean` — the classical Artin presentation vs. the germ (`GarsideBraid n = ArtinBraid n`).
- `Generated.lean` — adjacent transpositions generate `Braid n` (length-additivity).
- `PermWord.lean` — the Artin-word emitter `permWord σ`.
- `SalvettiConstruction.lean` — the **computable** reading of a tope as a linear order (`topeBefore`,
  `topeRank`, `topePerm`) and the crossing cocycle `crossPerm`, plus `permBraidFunctor`, the shared
  "length-additive cocycle ⟹ braid-valued functor" builder. Its length-additivity and the
  construction itself live in `Salvetti/SalBraid.lean`, transported from the run side.

### `Testing/` — the fast execution model, and computing `π₁`

Strictly downstream: nothing outside `Testing/` imports it. Not built by `lake build CubeChains`.

An execution of `□ⁿ` is a **linear order on the `n` directions plus a composition of `n`** — the run
linearizes each bead, and beads are consecutive blocks of that word. So `Ch⋆(□ⁿ)` has `n!·2^{n−1}`
objects (192 for `n = 4`), enumerable in output-linear time.

- `Cells.lean` — cells of `□ⁿ` as sign vectors; `SubCube n` (a face-closed `Bool` predicate),
  `full`/`boundary`/`skeleton`, `beadCell`. `(cube n).init` is `some false`, so `some false` = a
  direction not yet performed.
- `FastExec.lean` — `FExec n` (nonempty blocks whose concatenation is a permutation), `Refines`
  (decidable), `fperm`, the DFS `execs` with `mem_execs_iff` (sound **and** complete), `buildPoset`.
- `FastEquiv.lean` — the bridge `fexecChStarEquiv : FExec n ≃ Ch⋆ (□ⁿ)` between the enumerable
  block-list model and `Salvetti/ExecData`, plus `fperm_eq_stepPerm`.
- `Parabolic.lean` — `outLabels_eq_parabolic`, `dims_eq_of_outLabels_eq`, `outLabels_eq_top_iff`.
- `Presentation.lean` — `PosetData ↦ Presentation`: spanning forest, cover generators, 3-chain
  relations, `homology` (bespoke Smith normal form — mathlib's is noncomputable), GAP rendering.
  `thenW w v = v ++ w`, because `Conc (f ≫ g) = Conc g * Conc f` while `wordZToBraid` sends `++` to `*`.
- `Pi1.lean` — the pipeline `SubCube n ↦ concPi1`, plus `concSummary`, `linkVec`, `concPure`.
- `Demo.lean` — the live numbers. `Enumerate`/`Morphisms`/`Boundary` are the **slow oracle**: the
  by-definition route through the `Glue` quotients, kept to check the fast model against.

## Where do I find…?

- **the box / precubical-set definition** → `Foundations/Box.lean`
- **cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n`** → `Foundations/Representable.lean` (`cubeRepr`)
- **`vertex₀/₁`, `BPSet.Hom`, `cubeMap`/`faceMap`** → `Foundations/Bipointed.lean`
- **the wedge / serial wedge / `wedge2` pushout** → `Foundations/Wedge.lean` (+ `Chains/WedgeMap.lean`)
- **`NonSelfLinked` / `AdmitsAltitude` / altitude lemmas** → `Foundations/Altitude.lean`
- **the geometric tensor `⊗ᵍ` (`MonoidalCategory GeoBP`, `cubeTensorIsoBP`)** →
  `Foundations/GeoTensor/BP.lean` (built on `DayTensor.lean` / `BoxMonoidal.lean`)
- **the wedge as the default monoidal product on `BPSet`** → `Foundations/WedgeMonoidal.lean`
- **`⋁` as a strong monoidal functor (`serialWedgeAppend` as tensorator)** →
  `Chains/Segal.lean` (`serialWedgeFunctor : DimList ⥤ BPSet`)
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Foundations/Nerve.lean`
- **the chain category `Ch` / the lift `liftToCh`** → `Chains/Category.lean`
- **chains-are-wedge-maps [RESULT]** → `Chains/Correspondence.lean` (`equivWedgeCat`)
- **Segal monoidality of `Ch`** → `Chains/Segal.lean`; `chSegal` / the splitting → `Chains/Split.lean`
- **`chFunctor` lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`** → `Chains/WedgeLaxMonoidal.lean`
- **generic monoidal helpers (transport, associativity juggling)** → `Foundations/MonoidalTransport.lean`
- **the braid arrangement `braidCOM n` / COMs** → `Arrangements/Braid.lean`, `Arrangements/COM.lean`
- **runs, the run presheaf `Lines`, `runPresheaf`, `runRestrict`** → `Salvetti/Runs.lean`
- **Segal for runs (`runSplitEquiv`)** → `Salvetti/Runs.lean`; the wedge-map split it rests on is
  `splitWedgeMorphism` in `Chains/Split.lean`
- **a chain of `□ⁿ` as an ordered set partition (`beadOf`, `ofBlockMap`)** →
  `Salvetti/ChainBraidFace.lean` (`chFaceEquiv`, `chFaceCatEquiv`, `reflectHom`)
- **the run order `runOrd`, `permOf`, no-double-crossing** → `Salvetti/EventBraid.lean`; its two
  inputs are `Salvetti/RunSegal.lean` (Segal) and `Salvetti/RunRestrict.lean` (face restriction)
- **an execution as a word + composition, and enumerating them** → `Testing/FastExec.lean`
  (`FExec`, `execs`, `mem_execs_iff`), identified with `Ch⋆` in `Testing/FastEquiv.lean`
- **computing `π₁` of a `SubCube`, with braid words** → `Testing/Pi1.lean` (`concPi1`), on
  `Testing/Presentation.lean`; the theorem that it *is* a presentation →
  `Foundations/FreeGroupoidPresentation.lean`
- **restricting a chain along a face / `EdgeChain`** → `Chains/ChainRestrictions.lean`
- **hom functors and opposites, monoidally** → `Foundations/HomMonoidal.lean`
- **the braid group itself (Garside germ), `permHom`, `PureBraid`** → `Braid/Germ.lean`
- **the braid category `𝔅` (objects = strand counts)** → `Braid/Category.lean`
- **the deck-covering short exact sequence** → `Foundations/DeckExact.lean` (built on `DeckSequence`,
  `QuotientCovering`, `QuotientCat`, `NerveQuot`)
- **the non-abelian short five lemma** → `Foundations/ShortFive.lean`
- **the strict free-groupoid universal property** → `Foundations/FreeGroupoidLift.lean`

## Build & conventions

- ⚠ `lake build CubeChains` is **not** a full sweep — it builds only the root module's import cone,
  so a broken module outside it passes silently. To gate the whole tree, sweep every module:
  `lake build $(find CubeChains -name '*.lean' | sed 's#/#.#g; s#\.lean$##')`.
  **No file sets `maxHeartbeats`**; if you find yourself needing one, you have hit a spelling
  mismatch (see below), not a hard proof.
- The tree is **`sorry`-free**. `Salvetti/SalBraid.lean` carries the sole axiom,
  `salvettiConstruction_faithful` (the asphericity / `K(π,1)` input), and nothing else imports it;
  everything else is `[propext, Classical.choice, Quot.sound]`.
- **Asphericity is not needed for π₁.** `π₁` depends only on the 2-skeleton, so faithfulness of
  `Conc` on `□ⁿ` is a van Kampen argument, not a `K(π,1)` one. `conc_faithful_of_loop`
  (`Salvetti/ConeRelations.lean`) states it and reduces it to loop-triviality; the relations are
  `cross_square`/`cross_hexagon` there, and what is left is generation.
  (Earlier drafts of this file claimed otherwise.)
- **`FreeGroupoid` is mathlib's *localization*** (`Groupoid/FreeGroupoidOfCategory.lean`), so
  composition relations are imposed and the vertex group of `Conc K` is `π₁` of the **nerve** — not
  the free group on the graph. `E − V + components` is right only for posets of height 1.
- **`End`/`Aut`/`SingleObj` multiply flipped** (`u * v = v ≫ u`) while `Groupoid.vertexGroup` does
  not. `End` is the one that pairs with `SingleObj`, which is why braid words compose with the
  *later* arrow first — the `thenW` convention in `Testing/Presentation.lean`. Getting it backwards
  leaves every group count unchanged and shows up only as loops failing to be pure braids.
- **Trust `lake build`, not the IDE** (cross-file diagnostics are stale).
- **Foundational machinery proves the strongest `BPSet`-level statement available.** Never weaken a
  definition or lemma to the presheaf level (`.toPsh ⟶ .toPsh`) so a tactic will fire; callers
  project with `.hom`. `BPSet.Hom` bundles `app_init`/`app_final`, so `BPSet`-level statements carry
  the endpoint conditions for free and keep `⊗`/`▷`/`◁`/`α_`/`λ_`/`ρ_` and `monoidal` applicable.
  When a proof wants to track endpoint data beside a map, **re-point the target** (`BPSet.repoint`)
  rather than pairing value with proof by hand.
- **If you need `erw`, suspect a spelling mismatch, not a hard proof — and it is _not_ an instance
  mismatch.** Traced with `pp.explicit`: both `≫` in a failing goal use the *identical*
  `@Category.toCategoryStruct (Functor Boxᵒᵖ Type) (@Functor.category …)`. The gap is in
  `CategoryStruct.comp`'s **object argument** — the outer `≫` may carry `Y := (X ∨ Y).toPsh` while
  the inner carries `Z := Glue.gluePsh X.finalVertex Y.initVertex`. Those are `rfl`-equal but not
  syntactically equal, and `rw`'s `kabstract` key-matches at `.instances` transparency, which will
  **not** unfold a plain `def` (`wedge2`) to reach `Glue.gluePsh`; `erw`'s full transparency will.
  So `Category.assoc`'s pattern `(?f ≫ ?g) ≫ ?h` can fail on a goal that *prints as exactly that*.
  Other instances: `⋁(n::da)` vs `□n ∨ ⋁da`, and `(K.repoint a b).toPsh` vs `K.toPsh` (a type
  ascription does **not** fix that one). Cures, in order: unify the spelling with a reducible
  wrapper typed the way callers see it; or use `exact`/`.trans`, since elaboration unifies at
  default transparency where `kabstract` will not. Rewriting under `yonedaEquiv` still fails the
  motive — convert to a plain morphism equation first.
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
