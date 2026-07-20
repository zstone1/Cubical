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
`Run k = (runObj (dimSum k) ⟶ ⋁k)`.

| Result | Statement | Lives in |
|---|---|---|
| **Chains are wedge maps** | `equivWedgeCat : RefineObj K ≌ Ch K` (under `NonSelfLinked` + `AdmitsAltitude`) — a refinement of a chain is the same as a bi-pointed map out of a serial wedge | `Chains/Correspondence.lean` |
| **Salvetti = executions** | `braidSalEquiv n : Sal (braidCOM n) ≌ Int(Lines (□ⁿ))` — the Salvetti complex of the braid arrangement `A_{n−1}` is the category of executions of the `n`-cube | `Salvetti/BraidIso.lean` |

What lies downstream of `braidSalEquiv` is **not in this tree**: the concurrency groupoid
`ConcGrpd K = FreeGroupoid (Int(Lines K))` and the identifications built on it —
`cube_concBraid_pureBraid` (the cube is the pure braid group), `braidMonodromy_bijective` (the
non-abelian terminal five-lemma), `concToZAut_injective` (terminal descent is injective) — nor
are `Events/`, `Testing/`, or the serial-wedge generalization
`braidSerialSalEquiv : Sal(⊕ᵢ braidCOM dᵢ) ≌ Int(Lines(⋁dims))`. `main` carries them.

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
- `SegalSplit.lean` — the combinatorial heart: a chain in `X ∨ Y` splits `X`-prefix / `Y`-suffix.
- `SegalProd.lean` — `chSegal X Y : Ch X × Ch Y ≌ Ch (X ∨ Y)` and the n-ary `chSegalProd`.
- `WedgeSplit.lean` / `WedgeSplitMap.lean` — the **choice-free** inverse of `chConcat`
  (`splitObj`, both round trips on the nose; `chSplit`, `chSegalC`), built on the computable
  cell-side discriminator `Glue.cellSide`.
- `WedgeSplitHom.lean` — the same split for a bare map `⋁as ⟶ X ∨ Y` (`splitWedgeMorphism`), which
  is the form the run-level recursions in `Salvetti/Runs.lean` consume.
- `WedgeStrong.lean` — where the wedge tensor is genuinely *strong* for `Ch`: not on `BPSet` (the
  tensorator `chConcat` is an equivalence, never an iso in `Cat`), but on the monoidal full
  subcategory `AltBP` of altitude-admitting objects.
- `SerialWedgeFunctor.lean` — `⋁` as a **strong monoidal** functor
  `serialWedgeFunctor : DimList ⥤ BPSet` (tensorator `serialWedgeAppend`), where
  `abbrev DimList := Discrete (FreeMonoid ℕ+)` is the discrete index category of dimension
  sequences (tensor = list append).  Reusable coherence squares: `serialWedgeAppend_assoc` /
  `_left_unitality` / `_right_unitality`.

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

### `Salvetti/` — executions
See `Salvetti/README.md` and `Salvetti/BRAID.md`.
- `Runs.lean` — the **run presheaf** `Lines K : (Ch K)ᵒᵖ ⥤ Type`, `a ↦ Run a.dims`. A *run* of a
  shape `k` is a map out of the all-edges wedge, `Run k = (runObj (dimSum k) ⟶ ⋁k)` — an
  interleaving of the beads' edges. `RunF : DimList ⥤ Type` gives runs their concatenation
  (`runAppend = μ RunF`) by inheritance from `HomMonoidal`, and `runRestrict` pulls a run back
  along a wedge map in three layers (face → wedge-to-cube → wedge-to-wedge).
- `Elements.lean` — `Int(Lines) = (Lines _).Elements` scaffolding: `Functor.elements_isThin`,
  `mapEquivalence`, `pre`/`preEquivalenceComp`, and the thinness of `Ch (□ⁿ)`.
- `BraidPartition.lean` — a cube chain of `□ⁿ` **is** an ordered set partition of `Fin n`: bead `i`'s
  block is the set of coordinates it flips. `blockIndex`, `covectorHeight`, and the functoriality
  `faceLE_of_chainRefine`.
- `BraidFace.lean` — the **base comparison** `chFaceEquiv n : (Ch □ⁿ)ᵒᵖ ≌ Face (braidCOM n)`.
  Contravariant (`a ⟶ b` means `a` subdivides `b`, so `b`'s covector is coarser), and choice-free:
  `signHeight` *computes* a height off a covector rather than picking a `braidSign` witness.
- `SalLines.lean` — objectwise, `runTopeEquiv a : Run a.dims ≃ TopeOver a`: a run of `a` traces out
  an all-edges chain whose partition is a linear order, i.e. a tope above `a`'s covector.
- `RunOrderFace.lean` / `WallCrossing.lean` — the naturality of that bijection (the Salvetti wall
  crossing), bead-locally then globally: restriction along a face is `List.filterMap`, which never
  reorders, and `flipIdx` is the height on *raw* cube lists that survives a cut at a junction.
  `salLinesIso n : Lines (□ⁿ) ≅ chFaceEquiv.functor ⋙ salFunctor (braidCOM n)` is the **presheaf
  comparison**.
- `BraidIso.lean` — **`braidSalEquiv`** [RESULT]: both sides are categories of elements, so the
  assembly is three `trans`es of `chFaceEquiv` and `salLinesIso`. Nothing is matched cell by cell.

### `Braid/` — the braid group itself
- `Germ.lean` — `Braid n` as a `PresentedGroup` by its Garside germ: one generator `[σ]` per
  permutation, one relation per **length-additive** product; `permHom : Bₙ ↠ Sₙ`, `PureBraid n`.
- `Category.lean` — the braid category `𝔅 = Σ n, SingleObj (Braid n)` (objects = strand counts).
- `Artin.lean` — the classical Artin presentation vs. the germ (`GarsideBraid n = ArtinBraid n`).
- `Generated.lean` — adjacent transpositions generate `Braid n` (length-additivity).
- `PermWord.lean` — the Artin-word emitter `permWord σ`.
- `SalvettiConstruction.lean` — the **computable** braid-word map off the Salvetti complex
  (`salvettiConstruction`, faithful by the `salvettiConstruction_faithful` axiom).

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
  `Chains/SerialWedgeFunctor.lean` (`serialWedgeFunctor : DimList ⥤ BPSet`)
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Foundations/Nerve.lean`
- **the chain category `Ch` / the lift `liftToCh`** → `Chains/Category.lean`
- **chains-are-wedge-maps [RESULT]** → `Chains/Correspondence.lean` (`equivWedgeCat`)
- **Segal monoidality of `Ch`** → `Chains/Segal.lean` (`chSegal` in `SegalProd.lean`)
- **`chFunctor` lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`** → `Chains/WedgeLaxMonoidal.lean`
- **generic monoidal helpers (transport, associativity juggling)** → `Foundations/MonoidalTransport.lean`
- **the braid arrangement `braidCOM n` / COMs** → `Arrangements/Braid.lean`, `Arrangements/COM.lean`
- **runs, the run presheaf `Lines`, `runRestrict`, `runAppend`** → `Salvetti/Runs.lean`
- **Segal for runs (`Run.splitEquiv`)** → `Salvetti/Runs.lean`; the wedge-map split it rests on is
  `splitWedgeMorphism` in `Chains/WedgeSplitHom.lean`
- **a chain of `□ⁿ` as an ordered set partition (`blockIndex`)** → `Salvetti/BraidPartition.lean`
- **Salvetti = executions [RESULT]** → `Salvetti/BraidIso.lean` (`braidSalEquiv`), assembled from
  `chFaceEquiv` (`Salvetti/BraidFace.lean`) and `salLinesIso` (`Salvetti/WallCrossing.lean`)
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
- `Braid/SalvettiConstruction.lean` carries the sole axiom, `salvettiConstruction_faithful` (the
  asphericity / `K(π,1)` input), and nothing else in the tree imports it. Everything else,
  `braidSalEquiv` included, is `[propext, Classical.choice, Quot.sound]`.
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
