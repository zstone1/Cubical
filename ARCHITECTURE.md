# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of the **concurrency braid groupoid** of a
precubical set: the executions of a cube chain, made into a groupoid, and the comparison of that
groupoid with the braid group. **Read this first to find the right file**, then open that one file
(+ its module docstring) — you should never need the whole tree in context.

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

`Ch K = ChainCat.Obj K`, `□n = BPSet.cube n`, `⋁d = BPSet.serialWedge d`,
`Ch⋆ K = (Lines K).Elements`, `Run K` = the all-edges full subcategory of `Ch K`,
`RunWedge` = a wedge with a chosen run.

| Result | Statement | Lives in |
|---|---|---|
| **Salvetti = executions** | `braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□ⁿ)` — a cell is a face below a tope, i.e. a chain plus a word linearizing it; the wall crossing `T' = X' ⊙ T` is the arrow rule | `Salvetti/SalExec.lean` |
| **`Conc` is well defined** | `permOf_noDoubleCross` — crossing permutations are length-additive, hence `braidFunctor : RunWedge ⥤ FullBraid`, `ConcPos K = proj K ⋙ braidFunctor`, `Conc K = FreeGroupoid.lift (ConcPos K)` | `Salvetti/EventBraid.lean` |
| **Germ = Artin** | `garside_equiv_artin : Matsumoto n → (GarsideBraid n ≃* ArtinBraid n)`; the easy direction `garsideOfArtin` is unconditional. `Matsumoto n` (the positive lift `σ ↦ σ̂`) is an explicit hypothesis — mathlib has no type-A Coxeter instance | `Braid/Artin.lean` |
| **Chains are braid faces** | `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)`, `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face` — a chain of `□ⁿ` is an ordered set partition of `Fin n`; `reflectHom` is the computable converse | `Salvetti/ChainBraidFace.lean` |
| **Executions are word + composition** | `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` — a chain together with a run word refining it; `fexecChStarEquiv` is the enumerable model | `Salvetti/ExecData.lean`, `Testing/FastEquiv.lean` |
| **The crossing permutation is the word change** | `stepPerm_eq : stepPerm f = (runWord x).trans (runWord y).symm` — `ConcPos`'s label is "position in the source's run word ↦ position in the target's" | `Salvetti/RunWord.lean` |
| **The two gradings agree** | `crossPerm_eq_stepPerm` across `braidSalEquiv`, so `crossPerm_noDoubleCross` *is* `permOf_noDoubleCross` and `salvettiGrading` is `ConcPos` read on cells | `Salvetti/SalBraid.lean` |
| **The terminal object carries the full braid group** | `runWedgeEquivChStarZbp : Ch⋆ Zbp ≌ RunWedge` — `Z`'s events have no axis names, so nothing forces purity | `Salvetti/RunWedgeZ.lean` |
| **Chains are wedge maps** | `equivWedgeCat : RefineObj K ≌ Ch K` (under `NonSelfLinked` + `AdmitsAltitude`) — a refinement of a chain is the same as a bi-pointed map out of a serial wedge | `Chains/Correspondence.lean` |
| **`ConcPos` reads the cell structure** | `outLabels_eq_parabolic` — the crossing permutations out of an execution are exactly the parabolic `S_{d₁}×⋯×S_{d_k}` of its bead dimensions | `Testing/Parabolic.lean` |
| **Vertex group of a free groupoid, presented** | `presentationEquiv (S : Spanning C x) : End (mk x : FreeGroupoid C) ≃* Pres S` — for a **general** category: no thinness, finiteness or acyclicity | `Foundations/FreeGroupoidPresentation.lean` |

**Retained infrastructure** not on the results' path but kept as finished mathematics:
- the **geometric tensor** `⊗ᵍ` — a computable `MonoidalCategory` on `PrecubicalSet` and on the
  alias `GeoBP := BPSet` (`Foundations/GeoTensor/`), plus the abstract Day-convolution version
  and their comparison (`DayTensor.lean`, `CubeTensor.lean`);
- the **nerve bridge** `realize ⊣ Nerve` between the concrete and topos models
  (`Foundations/Nerve.lean`, `Reachability.lean`);
- the **regular-covering toolkit** (`QuotientCat` → `DeckExact`) and the non-abelian short five
  lemma, for reading a group off a quotient of the execution poset.

## Layered layout (folders = areas; deeper layer imports shallower)

`Foundations` → `Chains` → `Salvetti` is the spine. `Arrangements/` (COMs, the braid arrangement) is
a **second root** — it imports nothing else in the tree — and feeds `Braid/`; the two join the spine
at `Salvetti/ChainBraidFace` and `Salvetti/EventBraid`. `CubeChains.lean` imports the results and
the retained infrastructure; only `Testing/` sits outside its cone.

### `Foundations/` — stable math fundamentals

*Precubical sets, two models.*
- `PrecubicalConstructions/Basic.lean` — the concrete/computable model: graded cells, `face ε i`,
  the precubical identity, the `Category` instance, extremal vertices.
- `PrecubicalConstructions/StandardCube.lean` — `□ⁿ` concretely (sign-vector cells `Fin N → Option
  Bool`, `none = ∗`), `faceCell`, `nones`.
- `Box.lean` — the box category `Box` (objects = dimensions, maps inherited from the concrete
  model) and the topos `PrecubicalSet := Boxᵒᵖ ⥤ Type` (`HasPushouts` free).
- `SortPerm.lean` — `Tuple.eq_sort_inv`: an injective tuple is put in order by exactly one
  permutation, so `Monotone (f ∘ σ⁻¹)` forces `σ = (Tuple.sort f)⁻¹`.
- `SymBox.lean` — the **symmetric box category** `SBox` (`▪n`): the injections `Fin m ↪ Fin n` plus
  signs, so `Aut ▪n = Perm (Fin n)`.  `J : Box ⥤ SBox` is the monotone wide subcategory, and
  `sHomEquiv : (▪m ⟶ ▪n) ≃ Perm (Fin m) × (▫m ⟶ ▫n)` is the sorting factorization.
- `SymPresheaf.lean` — the round trip `H = J* ∘ J₍!₎` on `PrecubicalSet`: `symFree.obj K` at `▪n` is
  `Perm (Fin n) × K.cells n`, restricted by the sorting factorization of `u ≫ symHom σ`; `symUnit`
  exhibits it as the left Kan extension along `J.op`, and `symFreeIsoLan`/`HIsoLan` identify it with
  mathlib's `J.op.lan`.
- `Representable.lean` — **cube Yoneda**: `cubeRepr : (□ⁿ ⟶ K) ≃ K.cells n`; `canonicalMap`,
  `trueCount`, `coface`.
- `Bipointed.lean` — `BPSet` (a presheaf with two chosen `0`-cells) + `Hom` + category; `cells`,
  `vertex₀/₁`, `faceMap`/`cubeMap`, `IsAltitude`, and `comp_app_cell` (the `ConcreteCategory`
  bundling that defeats `rfl` on a composite application).
- `BipointedProd.lean` — the levelwise product with paired base points, as the binary product:
  `BPSet.prod` with `prodFst`/`prodSnd`/`prodLift` (computable, both legs `rfl`), shown to be the
  binary product by `prodFanIsLimit`, so `instance : HasBinaryProducts BPSet` and mathlib's `⨯`
  API apply.  Downstream spells `X.prod Y`; mathlib's chosen `X ⨯ Y` is `noncomputable`.
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
- `SkeletalEquiv.lean` — an equivalence of skeletal categories is a bijection on objects, with
  `toFun` *definitionally* `e.functor.obj` (so a transported group action still computes).

*The geometric tensor.*
- `BoxMonoidal.lean` — the **parallel tensor** on `Box`: `▫m ⊗ ▫n = ▫(m+n)`, morphisms concatenate
  sign vectors; `MonoidalCategory Box`. **`Box` is NOT braided** — no block swap exists.
- `GeoTensor.lean` + `GeoTensor/{Hom,Unit,Assoc,Monoidal}.lean` — the **computable** geometric
  tensor on `PrecubicalSet`, from the closed form of the Day coend:
  `(X ⊗ Y)(▫n) = Σ p q, (p + q = n) × X(▫p) × Y(▫q)`, restriction = split the cell and restrict
  each half. `GeoTensor/Cube.lean` is `□m ⊗ □n ≅ □(m+n)` at the representable level.
- `GeoTensor/BP.lean` — the same on bi-pointed sets, written `X ⊗ᵍ Y`, carried by the alias
  `GeoBP := BPSet`; `cubeTensorIsoBP`. It lives on its own alias because bare `⊗` on `BPSet` is
  the **wedge**. Unit is `□0` on the nose.
- `DayTensor.lean` — the abstract alternative: Day convolution on `Boxᵒᵖ ⊛⥤ Type` (mathlib's
  `DayFunctor`), with the Yoneda-strong-monoidality `cubeDayIso` mathlib lacks. `noncomputable`.
- `CubeTensor.lean` — the computable universal property of `□m ⊗ □n = □(m+n)`
  (`cubeTensorPair`/`cubeTensorDesc`/`cubeTensor_hom_ext`), bypassing the Day wrapper.

*The model bridge.*
- `Nerve.lean` — `realize : PrecubicalSet ⥤ PrecubicalConstructions`, the nerve
  `Nerve : PrecubicalConstructions ⥤ PrecubicalSet`, `nerveCellEquiv`, `nerveRealizeIso`.
- `Reachability.lean` — `PrecubicalSet`-level reachability and connected components `π₀`.

*Terminal object and computable pushouts.*
- `Terminal.lean` — the terminal precubical set `Z` (one cell per dimension), `Zbp`.
- `GluePushout.lean` — a **computable** pushout of presheaves (mathlib's is `Classical.choice`-opaque).

*The regular-covering / free-groupoid toolkit.*
- `QuotientCat.lean` — the quotient category `P // G` of an order-free group action on a poset.
- `QuotientCovering.lean` — `quotFunctor : P ⥤ P // G` is a covering of quivers.
- `NerveQuot.lean` — the nerve of `P // G` is the levelwise `G`-quotient of `nerve P`.
- `DeckSequence.lean` — the deck-transformation sequence of the covering (monodromy endpoint,
  middle exactness, injectivity).
- `DeckExact.lean` — packages it as a full short exact sequence with the deck map `deck : Aut → G`.
- `FreeGroupoidLift.lean` — `FreeGroupoid.lift` is **strict** (`lift_spec`/`lift_unique` are
  equalities); `lift₂` lifts one variable at a time to keep that strictness.
- `FreeGroupoidPresentation.lean` — `presentationEquiv` / `autPresentationEquiv` for a general
  category, with `Spanning` (a transversal) and `Spanning.ofInitial`. Imports nothing from
  `CubeChains`.
- `ShortFive.lean` — the **non-abelian** short five lemma (`ShortFive.bijective_middle`); mathlib's
  abelian four/five lemma does not apply.
- `ElementsProd.lean` — the external product `F ⊠ G` and `extProdEquiv` on categories of elements.

### `Chains/` — the cube-chain category and its theory
- `Basic.lean` — `CubeChain` (a list of cubes satisfying the folded `IsCubeChain`; the junction
  vertices are forced, not stored), `ofIsCubeChain`.
- `WedgeMap.lean` — bi-pointed maps out of a serial wedge ↔ cube-list data; `wedgeDesc … :
  ⋁(cubes.map (·.1)) ⟶ K.repoint a b` (re-pointing the target is what makes the endpoint
  conditions the morphism's own `app_init`/`app_final`), `wedgeToCubes`, `serialWedge_hom_ext`,
  the `glue0_*` pushout/mono cores.
- `Correspondence.lean` — **`equivWedgeCat`**; the chain↔wedge-map bijection; thinness.
- `Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category. The face inclusion is
  carried as *data*, not as a `Prop`.
- `Category.lean` — `ChainCat`, `chFunctor : BPSet ⥤ Cat`, `Aut.liftToCh`.
- `CubeNonSelfLinked.lean` — `cube_nonSelfLinked`; the concrete↔topos bridge `toStar` for cube cells.
- `BlockDecomp.lean` — block decomposition of a serial-wedge map (`faceEmb`/`blockIdx`/`blockFace`),
  and its numerics from the serial wedge's own altitude: a source bead sits inside its target block
  (`serialWedge_beadStart_blockIdx`), so `blockIdx` is monotone and `∑ ad = ∑ cd`.
  Shared by `Salvetti/`.
- `ChainRestrictions.lean` — `restrictCubeChain face C` projects a chain of `□ᵇ` onto the directions
  a face uses, dropping the cubes that collapse. Not a precubical map (`Box` has no degeneracies)
  and **not** natural in `face` as a cube map — it factors through `faceEmb`, so there is no
  universal property over `Box` to look for. `EdgeChain K` and `EdgeChain.restrict` (+ `_id`/`_comp`)
  are the all-edges subpresheaf this cuts out.
- `ChainSkeletal.lean` — `Ch(K)` is acyclic and skeletal for **every** `K` (only identity
  endomorphisms); `blockIdx_surjective` — a refinement never drops a target bead.
- `Degree.lean` — the grading `degree = Σ (dim − 1)` on `Ch K` and the **codimension** of a
  refinement (beads lost).  `codimNat : chFunctor ⟶ gradeFunctor` is a *monoidal* transformation, so
  codimension is additive along the tensorator; `codimOneWedge`/`CutData` locate the single merge.
- `Segal.lean` — the append iso `serialWedgeAppend : ⋁x ∨ ⋁y ≅ ⋁(x ++ y)`, built **structurally**
  from `λ_`/`α_`/whiskering (so its coherence is monoidal, not a pushout chase); `⋁` as a **strong
  monoidal** functor `serialWedgeFunctor : DimList ⥤ BPSet` where `abbrev DimList := Discrete
  (FreeMonoid ℕ+)`; the concatenation `chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)` and its
  faithfulness; `chUnit : Ch(□⁰) ≌ Discrete PUnit`.
- `SegalAltitude.lean` — `cube_admitsAltitude` / `wedge2_admitsAltitude` /
  `serialWedge_admitsAltitude`, which is what makes the n-ary decomposition hypothesis-free.
- `WedgeLaxMonoidal.lean` — `chFunctor` is lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`; each coherence
  square is the matching `MonoidalTransport` lemma fed the append iso's own coherence.
- `Split.lean` — the **choice-free** inverse of `chConcat`, in three layers: `Split Z A B` ("`Z` is
  `A ∨ B`" as data, on the computable `Glue.cellSide`), `Split.chainSplit` (the *order* — the only
  place altitude is used), and the interface `chObjEquiv : Ch Z ≃ Ch A × Ch B`. Also
  `splitWedgeMorphism`, the same split for a bare map `⋁as ⟶ X ∨ Y`, which is the form
  `Salvetti/Runs.lean` consumes.
- `WedgeExtend.lean` — lifting a (co)presheaf on `Box` to serial wedges, in both variances:
  contravariant `F↑ X = (X.toPsh ⟶ F)` (precomposition) and covariant `F↓ X = X.toPsh ⊗_Box F`
  (the cubical coend as a plain computable `Quot`, not `Functor.lan`).
- `PshExtMonoidal.lean` — `pshExtFunctor F = BPSet.toPshFunctor.op ⋙ yoneda.obj F` is oplax
  monoidal, strong under single-vertexness — so `Lines K a = (⋁a.dims).toPsh ⟶ runPresheaf`
  literally, with its splitting for free.
- `CubeVtx.lean` — vertices of cube faces (`cubeVtx`), the monotonicity the coordinate coend needs
  (`cubeVtxOfCell_bot_le_top`).
- `CoordFunctor.lean` — the **coordinate coend**: `coordFlip χ : beadEvent a ≃ Fin m` for
  `χ : ⋁a ⟶ □m`, `coordMap`/`coordMapEquiv` for wedge maps, `coordFlip_comp` (the engine behind the
  label theorem) and `coordMap_eq` (its `blockIdx`/`blockFace` form).

### `Arrangements/` — COMs, the braid arrangement, Salvetti posets
See `Arrangements/README.md`.
- `COM.lean` — complexes of oriented matroids (sign vectors, composition `⊙`, `faceLE`), the BCK axioms.
- `Sal.lean` — the Salvetti face poset `Sal L` of a COM (cells `(X, T)` with `X ⊑ T`).
- `SalElements.lean` — `Sal L` as a category of elements of the "topes above" presheaf.
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
  by a base `Ch` morphism. Neither is a covering — the fibres vary, which is what lets the total
  space be non-contractible over a contractible base.
- `EventPerm.lean` — `beadEvent`, the run-free flattening `pos = finSigmaFinEquiv`, the event
  relabelling `eventEquiv f = coordMapEquiv (wedgeMap f)`, and `eventEquiv_mk` (its `blockIdx` /
  `blockFace` form) — the computational handle on everything downstream.
- `RunSegal.lean` — **the Segal decomposition of a linearization**: a run performs bead `i` at
  exactly the prefix-sum interval, in that bead's own order (`coordMap_fst_run_iff` as an *iff*,
  `coordFlip_run_concat`), so `runProj` gets a computational characterization and the sealed
  `runSplit`/`runSegalProd` stay sealed.
- `RunRestrict.lean` — **face restriction preserves the run order**: `EdgeChain.restrict` is a
  `List.filterMap`, which keeps survivors in order (`exists_strictMono_filterMap`), hence
  `localStep_restrict{,_lt_iff,_rank}`.
- `RunPerm.lean` — **a run of `□ⁿ` is a permutation of its axes**: `runPermEquiv : Run (□ⁿ) ≃
  Perm (Fin n)`, whose `toFun` is `localStep` on the nose and whose inverse `runOfPerm` is the
  singleton-bead `blockChain`. Restriction along a face is *sorting*: `runPermEquiv_restrict`
  reads `runPresheaf.map g.op` as the inverse of `Tuple.sort (localStep r ∘ faceEmb g)` — the
  permutation form of `localStep_restrict_rank`.
- `SymRun.lean` — **`H Z ≅ runPresheaf`** (`HZIsoRun`): a cell of the symmetric round trip of the
  terminal precubical set at `▫n` is an order on its axes, hence a run of `□ⁿ` (`symRunEquiv`), and
  both sides restrict by `Tuple.sort`.
- `EventBraid.lean` — the **run order** `runOrd`, the crossing permutation `permOf`, and
  `permOf_noDoubleCross` [RESULT]. Events are ordered by the run linearizing the execution, *not*
  by the run-free `pos` — ordering by `pos` makes `permOf` a function of the chain morphism alone,
  which trivializes every loop. The two leaves are `runOrd_within_localStep` (from `RunSegal`) and
  `localStep_restrict_lt_iff` (from `RunRestrict`). Then `braidFunctor`,
  `ConcPos K = proj K ⋙ braidFunctor`, and `Conc K = FreeGroupoid.lift (ConcPos K)`.
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
- `SalBraid.lean` — `crossPerm = stepPerm` across `braidSalEquiv` (`topeRank` of a run word is the
  step at which the coordinate fires), so `crossPerm_noDoubleCross` **is** `permOf_noDoubleCross`;
  then `salvettiGrading` / `salvettiConstruction`.
- `RunWedgeZ.lean` — `Ch⋆ Zbp ≌ RunWedge`, with a hand-built inverse so it computes; and the
  decomplexification `toChainZ : Ch⋆ K ⥤ (Ch Zbp)ᵒᵖ`.
- `ChStarProduct.lean` — `Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ`, an **isomorphism** of categories: `runBp` is
  `runPresheaf` bi-pointed at its unique vertex, and a run is the second leg of `prodLift`.  Both
  round trips are `rfl` — the cone's universal property is definitional.
  Side-condition-free — the wedge never has to be split.

### `Braid/` — the braid group itself
- `Germ.lean` — `Braid n` as a `PresentedGroup` by its Garside germ: one generator `[σ]` per
  permutation, one relation per **length-additive** product; `permHom : Bₙ ↠ Sₙ`, `PureBraid n`.
- `Artin.lean` — the classical Artin presentation vs. the germ. `garsideOfArtin : ArtinBraid n →*
  GarsideBraid n` is unconditional; the inverse is Matsumoto's theorem for `Sₙ`, taken as the
  explicit hypothesis `Matsumoto n`.
- `Generated.lean` — adjacent transpositions generate `Braid n` (length-additivity).
- `PermWord.lean` — the Artin-word emitter `permWord σ`, and the signed `schreierWordZ`.
- `Kernel.lean` — Schreier for a group with a set-section `t` of `φ : G →* Q`:
  `ker φ = ⟨t q · t s · t (q·s)⁻¹⟩`. Here the transversal `ofPerm` *is* the generating set, so
  `pureBraid_le` asks only for the conjugated cocycles — the words a zigzag of refinements reads.
- `Sum.lean` — juxtaposition `braidSum : Braid m × Braid n →* Braid (m+n)`, on the block-diagonal
  `permSum`; the crossing count adds because the blocks never interact.
- `Full.lean` — `FullBraid`: strand counts as objects, `End n = Braid n`. A morphism carries its
  braid on the **source** count, so the strand-count transport lives once, in composition. This is
  what `braidFunctor` maps into.
- `Category.lean` — the braid category `𝔅 = Σ n, SingleObj (Braid n)`, whose `SigmaHom` encoding
  pushes that transport onto every client instead.
- `SalvettiConstruction.lean` — the **computable** reading of a tope as a linear order (`topeBefore`,
  `topeRank`, `topePerm`) and the crossing cocycle `crossPerm`, plus `permBraidFunctor`, the shared
  "length-additive cocycle ⟹ braid-valued functor" builder. Its length-additivity is transported
  from the run side in `Salvetti/SalBraid.lean`.

### `Testing/` — the fast execution model, and computing `π₁`

Strictly downstream: nothing outside `Testing/` imports it, and it is the only part of the tree
`lake build CubeChains` does not build.

An execution of `□ⁿ` is a **linear order on the `n` directions plus a composition of `n`** — the run
linearizes each bead, and beads are consecutive blocks of that word. So `Ch⋆(□ⁿ)` has `n!·2^{n−1}`
objects (192 for `n = 4`), enumerable in output-linear time.

- `Cells.lean` — cells of `□ⁿ` as sign vectors; `SubCube n` (a face-closed `Bool` predicate),
  `full`/`boundary`/`skeleton`, `beadCell`. `(cube n).init` is `some false`, so `some false` = a
  direction not yet performed.
- `Boundary.lean` — `∂□ⁿ ↪ □ⁿ` as a genuine subfunctor (cells of dimension `< n`), so `Ch⋆(∂□ⁿ)`
  is `ChStar` of an actual `BPSet`.
- `FastExec.lean` — `FExec n` (nonempty blocks whose concatenation is a permutation), `Refines`
  (decidable), `fperm`, the DFS `execs` with `mem_execs_iff` (sound **and** complete), `buildPoset`.
- `FastEquiv.lean` — the bridge `fexecChStarEquiv : FExec n ≃ Ch⋆ (□ⁿ)` between the enumerable
  block-list model and `Salvetti/ExecData`, plus `fperm_eq_stepPerm`.
- `Parabolic.lean` — `outLabels_eq_parabolic`, `dims_eq_of_outLabels_eq`, `outLabels_eq_top_iff`.
- `Presentation.lean` — `PosetData ↦ Presentation`: spanning forest, cover generators, 3-chain
  relations, `homology` (bespoke Smith normal form — mathlib's is noncomputable), GAP rendering.
  `thenW w v = v ++ w`, because `Conc (f ≫ g) = Conc g * Conc f` while `wordZToBraid` sends `++` to `*`.
- `Pi1.lean` — the pipeline `SubCube n ↦ concPi1`, plus `concSummary`, `linkVec`, `concPure`.
- `Demo.lean` — the live numbers. `Enumerate`/`Morphisms` are the **slow oracle**: the
  by-definition route through the `Glue` quotients, kept to check the fast model against.

## Where do I find…?

- **the box / precubical-set definition** → `Foundations/Box.lean`
- **cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n`** → `Foundations/Representable.lean` (`cubeRepr`)
- **`vertex₀/₁`, `BPSet.Hom`, `cubeMap`/`faceMap`** → `Foundations/Bipointed.lean`
- **the wedge / serial wedge / `wedge2` pushout** → `Foundations/Wedge.lean` (+ `Chains/WedgeMap.lean`)
- **`NonSelfLinked` / `AdmitsAltitude` / altitude lemmas** → `Foundations/Altitude.lean`
- **the geometric tensor `⊗ᵍ`, computably** → `Foundations/GeoTensor/` (`BP.lean` for the `BPSet`
  version and `cubeTensorIsoBP`); the Day-convolution version is `Foundations/DayTensor.lean`
- **the wedge as the default monoidal product on `BPSet`** → `Foundations/WedgeMonoidal.lean`
- **`⋁` as a strong monoidal functor (`serialWedgeAppend` as tensorator)** →
  `Chains/Segal.lean` (`serialWedgeFunctor : DimList ⥤ BPSet`)
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Foundations/Nerve.lean`
- **the chain category `Ch` / the lift `liftToCh`** → `Chains/Category.lean`
- **chains-are-wedge-maps** → `Chains/Correspondence.lean` (`equivWedgeCat`)
- **concatenation `chConcat` and its inverse** → `Chains/Segal.lean` / `Chains/Split.lean`
- **`chFunctor` lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`** → `Chains/WedgeLaxMonoidal.lean`
- **generic monoidal helpers (transport, associativity juggling)** → `Foundations/MonoidalTransport.lean`
- **the braid arrangement `braidCOM n` / COMs** → `Arrangements/Braid.lean`, `Arrangements/COM.lean`
- **runs, the run presheaf `Lines`, `runPresheaf`, `runRestrict`** → `Salvetti/Runs.lean`; the
  wedge-map split it rests on is `splitWedgeMorphism` in `Chains/Split.lean`
- **`runBp`, `K.prod runBp`, and `Ch⋆` as a chain category** → `Salvetti/ChStarProduct.lean`
  (`chStarProdIso`/`chStarProdEquiv`); products of `BPSet` → `Foundations/BipointedProd.lean`
- **a chain of `□ⁿ` as an ordered set partition (`beadOf`, `ofBlockMap`)** →
  `Salvetti/ChainBraidFace.lean` (`chFaceEquiv`, `chFaceCatEquiv`, `reflectHom`)
- **the run order `runOrd`, `permOf`, no-double-crossing** → `Salvetti/EventBraid.lean`; its two
  inputs are `Salvetti/RunSegal.lean` (Segal) and `Salvetti/RunRestrict.lean` (face restriction)
- **`Conc` / `ConcPos` themselves** → `Salvetti/EventBraid.lean`
- **the Salvetti comparison** → `Salvetti/SalExec.lean` (`braidSalEquiv`), graded in `SalBraid.lean`
- **an execution as a word + composition, and enumerating them** → `Testing/FastExec.lean`
  (`FExec`, `execs`, `mem_execs_iff`), identified with `Ch⋆` in `Testing/FastEquiv.lean`
- **computing `π₁` of a `SubCube`, with braid words** → `Testing/Pi1.lean` (`concPi1`), on
  `Testing/Presentation.lean`; the theorem that it *is* a presentation →
  `Foundations/FreeGroupoidPresentation.lean`
- **restricting a chain along a face / `EdgeChain`** → `Chains/ChainRestrictions.lean`
- **hom functors and opposites, monoidally** → `Foundations/HomMonoidal.lean`
- **the braid group itself (Garside germ), `permHom`, `PureBraid`** → `Braid/Germ.lean`
- **the Artin presentation and the Matsumoto hypothesis** → `Braid/Artin.lean`
- **the braid groupoid `FullBraid` (the target of `Conc`)** → `Braid/Full.lean`
- **the deck-covering short exact sequence** → `Foundations/DeckExact.lean` (built on `DeckSequence`,
  `QuotientCovering`, `QuotientCat`, `NerveQuot`)
- **the non-abelian short five lemma** → `Foundations/ShortFive.lean`
- **the strict free-groupoid universal property** → `Foundations/FreeGroupoidLift.lean`

## Build & conventions

- `lake build CubeChains` builds the results and the retained infrastructure — everything except
  `Testing/`. To gate the whole tree including `Testing/`, sweep every module:
  `lake build $(find CubeChains -name '*.lean' | sed 's#/#.#g; s#\.lean$##')`.
  **No file sets `maxHeartbeats`**; if you find yourself needing one, you have hit a spelling
  mismatch (see below), not a hard proof.
- The tree is **`sorry`-free and axiom-free**: every result reduces to
  `[propext, Classical.choice, Quot.sound]`. `Matsumoto n` (`Braid/Artin.lean`) is a *hypothesis*
  on a definition, not an `axiom` — nothing depends on it unless it is supplied.
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
