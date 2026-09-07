# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of the **concurrency braid groupoid** of a
precubical set: the executions of a cube chain, the braid monoid that grades their refinements, and
a presentation of `Ch(K)[W⁻¹]` built from a presentation of that monoid. **Read this first to find
the right file**, then open that one file (+ its module docstring) — you should never need the whole
tree in context.

Two models of precubical sets coexist: the **concrete/computable** one
(`Precubical/Basic/`, graded cells + face maps) and the **topos** one
(`PrecubicalSet := Boxᵒᵖ ⥤ Type`), bridged by the cube Yoneda lemma
(`Precubical/Basic/Representable.lean`). The topos model is the default everywhere downstream.

**Why braids.** `(GeoBP, ⊗ᵍ)` is monoidal but has **no swap** — `Box` is rigid (`Aut ▫k = {id}`,
the symmetry-free convention), so no block transposition `▫(m+n) ⟶ ▫(n+m)` exists. The braiding
is *created* by the passage to executions, not inherited: two interleavings of independent events
are isomorphic, not equal, and the iso has a winding number. Independent actions do not commute —
they braid.

## The goal statements

**A presentation of the braid monoid goes in; a presentation of `Ch(K)[W⁻¹]` comes out, for every
`K`, with no hypothesis on `K`.** Everything in *The supporting results* below is in service of that
— infrastructure, comparisons, and the refutations that pin the definitions down.

`K` ranges over **all** of `BPSet`, and that is the whole quantifier: `presentsBr` takes `K` and
nothing else — no instance argument, no decidability, no smallness side-condition. Two narrowings
are built into the *types* rather than into the theorems, and are stated here rather than left to be
discovered: `PrecubicalSet.cells` is fixed at `Type 0` (see `DESIGN.md`), and the polygraphs are
`Polygraph.{0,0,0}`, since `Polygraph` has colimits only on the universe diagonal
(`Machinery/Presentation/Coequalizer.lean`: a coequalizer of `Polygraph.{w,u',w₂}` lands in
`Polygraph.{max u' w, u', max u' w₂}`).

The **goal-statement tables** below (claims 1–10) are each stated as an `example` in
`CubeChains.lean`, so `lake build CubeChains` checks those statements as well as their proofs. *The
supporting results* table names declarations rather than restating them; many are reached only as
inputs to an anchored claim. The steps still open are **not** restated here; the board
(`bd ready`) is the status.

### The input

A **`BraidPresentation`** (`Concurrency/Presentation/BasePresentation.lean`) is a presentation of
each `SingleObj (PosBraid N)` as a *one-object* category:

```
P      : ℕ → Polygraph
comp   : ∀ N, Presents (P N) ((SingleObj (PosBraid N))ᵒᵖ)
vertex : ∀ N, Unique (P N).V
```

`vertex` is not decoration — it is what names `pt N` and `S N` at all, and a second 0-cell at a
strand count would name every run twice, so `runPtEquiv` would be a surjection and not a bijection.
It is *not* a hypothesis of the gluing theorem, which asks nothing of the 0-cells. `ofMonoids
rels e` builds one from a monoid presentation of each braid monoid, and `germBP` / `artinBP` are
its two values.

| # | Claim | Declaration | Lives in |
|---|---|---|---|
| 1 | `Ch(Z)[W⁻¹]` at strand count `N` is **one object**, carrying the positive braid monoid | `strandComponentGarside N : (SingleObj (PosBraid N))ᵒᵖ ≌ (AtStrands N).FullSubcategory` | `Concurrency/Presentation/BaseComponent.lean` |
| 2 | …and that monoid is the **Artin** monoid on `N−1` generators | `strandComponentArtin N` | ” |
| 3 | the base is the disjoint union of those components, so a `BraidPresentation` presents it | `p.base : Presents p.poly ((W Zbp).op.Localization)`, from `strandDecomposition` + `zLocOfComponents` | `Concurrency/Presentation/BaseDecomposition.lean`, `.../BasePresentation.lean` |
| 4 | the loops at the run of `N` events **are** the positive braid monoid, in either naming | `runBraidEquiv N : PosBraid N ≃* RunLoops N`, `runArtinEquiv N` | `Concurrency/Presentation/Retraction.lean` |

### The output

| # | Claim | Declaration | Lives in |
|---|---|---|---|
| 5 | **`Ch(K)[W⁻¹]` is presented, for every `K`, with no hypothesis on `K`** — one copy of `p`'s cells per run of a chain, glued as a colimit over the arrows of `Ch K` | `p.Br K := colimit (elementsPoly (wedgeHoms K) p.fam)` and `p.presentsBr K : Presents (p.Br K) ((W K).Localization)` | `Concurrency/Presentation/SliceInherit.lean` |
| 6 | at the base, `Br p Zbp` is `p`'s own polygraph — generator to generator, no word chosen | `p.brZMap_cells hp` (the spelling is one letter) and `p.bijective_brZPt` (the 0-cells are the strand counts) carry the claim; `p.brZMap hp : Presents.Map p.base.op _` and `p.brZEquiv hp` are the packaging, and *alone* say nothing — a `Presents.Map` and hence an equivalence exist between any two presentations of one category (`Machinery/Presentation/Comparison.lean`). A bijection of the **1**-cells is not claimed here; contrast `bijective_genQuiver` at `Hbp □ⁿ`. `hp : p.BySimples` | `Concurrency/Presentation/BrBase.lean` |
| 7 | at the cube, `Br p (□n)` presents the **weak Bruhat order** | `p.presentsBrCube n : Presents (p.Br (□n)) ((WeakOrder n)ᵒᵖ)` | `Concurrency/Presentation/BrCube.lean` |
| 8 | at the decorated cube, it presents the **positive braid action**, whose loops at *every* object are `PosPureBraid n` | `p.presentsBrAction n`, `p.endBrAction n x : End _ ≃* PosPureBraid n` | ” |
| 9 | `Br p` is a **functor** on `BPSet`, and on the runs it is `Ch f` | `p.brFunctor : BPSet ⥤ Polygraph`, `p.brMap_glueRunV`, `p.brMapRunNat` | `Concurrency/Presentation/BrFunctor.lean` |
| 10 | …and a map of braid presentations is **spelled** in `Br`, strictly naturally in `K` | `m.brCells K : GenObj (p.Br K).Gen ⥤q (q.Br K).Word` with `m.brCells_brMap` (the naturality square, an equality of prefunctors) and `m.braid_word` (the word performs the generator's braid); `m.presentsMap K` packages it, and as a *type* asks nothing, `Presents.Map` being inhabited between any two presentations of one category | `Concurrency/Presentation/BrMap.lean` |

1–4 are the base `Ch(Z)`, twice over: as a category (1–2) and as the monoid of loops at the run (4),
each in both the Garside and the Artin naming. 5 is the lift, and it names no braid: the input is
an arbitrary `BraidPresentation` and the construction is `presentsChainsSliceColimit`, the colimit
of the inherited slice presentations. 6–8 read that one polygraph in three categories that have
already been identified — the polygraph never moves, only the category it is read in; 9–10 are its
two functorialities, in the space and in the presentation.

**What comes out is what went in.** The generators of `Br p K` are `p`'s own, crossed above a run
(`p.exists_runGen`): `germBr_gen` says a germ generator is a Garside simple acting on a run by
length-additive multiplication, `artinBr_gen` that an Artin generator is an atom gaining exactly one
crossing. `Testing/Pi1/GlueCount` measures the difference — `(0, 6, 72)` Artin 2-cells against
`(8, 144)` germ ones — and that difference is what says the relations are inherited rather than
manufactured.

The word problem is a **retraction**, not a normal form: the target is not thin, so
`presentsSliceColimit` builds an inverse `Ψ` with `Φ ⋙ Ψ ≅ 𝟭` instead of rewriting words to a
canonical shape.

### The special case

`chLocEquivElements` / `hLocEquiv` / `hLocArtinEquiv` (`Concurrency/Presentation/HAction.lean`) run
the lift by **pulling back along the discrete fibration** instead, and `hLocPresentation` /
`hLocActionPresentation` are the presentations that route gives. It asks the fibration to survive
localization (`IsSegal`), which buys a smaller presentation where it holds — `Ch(H□ⁿ)[W⁻¹]` is
`PosBraid n` acting on the `n!` orderings of the axes — but it is a special case, not the main road.
`Concurrency/Presentation/GlueArtin.lean` compares the two, generator for generator.

## The supporting results

`Ch K = ChainCat.Obj K`, `□n = BPSet.cube n`, `⋁d = BPSet.serialWedge d`,
`Ch⋆ K = (Lines K).Elements`, `Run K` = the all-edges full subcategory of `Ch K`,
`RunWedge` = a wedge with a chosen run.

| Result | Statement | Lives in |
|---|---|---|
| **Salvetti = executions** | `salCompare chFaceCatEquiv linesTopeIso : Ch⋆ (□ⁿ) ≌ Sal (braidCOM n)` — a cell is a face below a tope, i.e. a chain plus a word linearizing it; the wall crossing `T' = X' ⊙ T` is the arrow rule.  Both sides are categories of elements, so the comparison splits into a base (`chFaceCatEquiv`) and a presheaf over it (`linesTopeIso`, whose fibres are `linesTopeEquiv`); `hbpBraidSalEquiv` is the same assembly on `Ch (Hbp □ⁿ)` | `Concurrency/Salvetti/SalExec.lean`, `Concurrency/Salvetti/SalCompare.lean` |
| **The reorientation lives on `H`, not on the product** | `reorientCh_comp_hbpBraidSalEquiv` — across `hbpBraidSalEquiv : Ch (Hbp □ⁿ) ≌ (Sal (braidCOM n))ᵒᵖ` the `Sₙ`-action on the decorated cube *is* `salReorientFunctor`; `not_reorientCh_of_over_base` — no endomorphism of `□ⁿ × run` over the base induces it, `□ⁿ` being rigid | `Concurrency/Complexification/SymReorient.lean` |
| **`H` lies over the runs and over nothing else** | `HOverRun : H ⟶ const runPresheaf` from `H` of the terminal map; `isEmpty_cubeHom` — for `n ≥ 2` there is no map `H(□ⁿ) ⟶ □ⁿ`, hence none `H(□²) ⟶ □² × runBp`, so the product model's `prodFst` has no counterpart on `H` | `Concurrency/Complexification/SymOverRun.lean` |
| **`H` is a twist, not a product** | `not_desym_natural` — the `desym` bijection `(⋁d ⟶ Hbp K) ≃ (⋁d ⟶ K) × (⋁d ⟶ runBp)` does not commute with restriction along the merge `⋁[2,1] ⟶ ⋁[3]`; `not_invertsMerges_runBp`/`not_invertsMerges_Hbp_Zbp` — the run factor takes the square's two orders to its edges' one order, so any natural product splitting would refute `InvertsMerges (Hbp K)` (`not_invertsMerges_of_splitting`) | `Concurrency/Complexification/RunClassifier.lean` |
| **The merges act bijectively exactly when the wedge is the tensor** | `IsSegal K` — `K` inverts the comparison `wedgeToTensor : X ∨ Y ⟶ X ⊗ᵍ Y` at every pair of cubes, i.e. (`isSegal_iff_existsUnique`) a `p`-cell and a `q`-cell meeting at a vertex are the front and back faces of exactly one `(p+q)`-cell.  `isSegal_iff_invertsMerges_repoint` (in `Concurrency/Presentation/ElementsFibration.lean`) — it *is* `InvertsMerges` at every choice of base points, a unit bead contributing nothing (`IsLocal.of_isIso`).  The one comparison map fails in two opposite ways: `□²` has too few cells and the missing filler is the reordering staircase (`not_surjective_faceComparison_cube_two`, from `cubeMerge_ne_cubeReorder`), `H Z` has too many (`not_injective_faceComparison_H_Z`) | `Concurrency/Merge/SegalCondition.lean` |
| **`H` closes the gap** | `sbox_existsUnique` — `▪(p+q)` **is** the wedge `▪p ∨ ▪q` in the symmetric box category, so `isSegal_H_of_symFree_repr`: `H K` is Segal as soon as `symFree K` is representable.  Hence `isSegal_H_cube : IsSegal (H □ⁿ)` | `Concurrency/Complexification/HSegal.lean` |
| **`H` supplies the arrows, the cube supplies the objects** | `run_HbpZbp_eq` — `Hbp Zbp` has one all-edges chain per degree, and `exists_W_from_onesH` merges it into every chain of that degree; whereas `runHbpCubeEquivPerm : Run (Hbp □ⁿ) ≃ Perm (Fin n)` gives `n!` rigid all-edges chains, so `not_exists_hom_to_all_cube` — for `n ≥ 2` no decorated chain of `□ⁿ` maps to every one | `Concurrency/Complexification/RunClassifier.lean` |
| **`ConcPos` is well defined** | `permOf_noDoubleCross` — crossing permutations are length-additive, hence `braidFunctor : RunWedge ⥤ FullBraid` and `ConcPos K = proj K ⋙ braidFunctor`, a chain's refinement graded by the *positive* braid of its crossing permutation, before anything is inverted | `Concurrency/Salvetti/EventBraid.lean` |
| **Germ = Artin** | `garside_equiv_artin n : GarsideBraid n ≃* ArtinBraid n` and `posBraid_equiv_artinPos n : PosBraid n ≃* ArtinPosBraid n`, group and monoid.  The positive lift `σ ↦ σ̂` is `matsuLift`: peel adjacent descents, confluent by `matsuLift_mul_adjT` — **Matsumoto's theorem for `Sₙ`**, which mathlib lacks | `Machinery/Braid/Matsumoto.lean` |
| **Chains are braid faces** | `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)`, `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face` — a chain of `□ⁿ` is an ordered set partition of `Fin n`; `reflectHom` is the computable converse | `Concurrency/Salvetti/ChainBraidFace.lean` |
| **Executions are word + composition** | `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` — a chain together with a run word refining it; `fexecChStarEquiv` is the enumerable model | `Concurrency/Executions/ExecData.lean`, `Testing/Enumerate/FastEquiv.lean` |
| **The crossing permutation is the word change** | `stepPerm_eq : stepPerm f = (runWord x).trans (runWord y).symm` — `ConcPos`'s label is "position in the source's run word ↦ position in the target's" | `Concurrency/Executions/RunWord.lean` |
| **The arrangement's order and the flattening order label the same arrow** | `crossPerm_eq_topeCross` — on `Ch (Hbp □ⁿ)` both `ChainCat.crossPerm` and `topeCross` are the coboundary of `fibrePerm`, the cell's `topePerm` being that order (`topePerm_hbpBraidSalEquiv`); hence `W_wallLegFlip`, the far leg of a wall span is a bead merge.  `topePerm_eq` is what makes `topePerm` readable at all — a cell's permutation is its run word inverted, `topeRank` counting predecessors and a run word's predecessor count at `p` being the step at which `p` fires (`topeRank_wordTope`) | `Concurrency/Salvetti/CrossCompare.lean`, `Concurrency/Salvetti/SalBraid.lean` |
| **Chains are wedge maps** | `equivWedgeCat : RefineObj K ≌ Ch K` (under `NonSelfLinked` + `AdmitsAltitude`) — a refinement of a chain is the same as a bi-pointed map out of a serial wedge | `Precubical/Chains/Correspondence.lean` |
| **A wedge map is a chart refining a chart** | `chartHomEquiv : (⋁a ⟶ ⋁b) ≃ {x : ⋁a ⟶ □N // Nonempty ((a,x) ⟶ (b,χ))}` for a fixed chart `χ` of `⋁b` — every serial wedge maps into the cube of its own total dimension (`nonempty_toCube`), a chart is a monomorphism (`descent_mono`), and `Ch (□N)` is a poset.  Hom-sets are then read off `boundaries` alone: `nonempty_wedgeHom_iff_coarser` — a hom exists exactly at a coarsening, realised by merging one junction at a time (`exists_W_of_coarser`) | `Concurrency/Grading/ChartHom.lean` |
| **The merges are the crossing-free refinements** | `W K := (merge K).multiplicativeClosure` — one bead merge at a time, a merge being a cut whose middle map is the comparison `cubeMerge`.  `W_iff_crossPerm_eq_one`: that is exactly `crossPerm h f = 1`, at any strand count.  Crossings *add* along a composite, so a crossing-free refinement splits into crossing-free pieces, and cutting at a junction the target does not separate peels one bead off | `Concurrency/Merge/MergeClass.lean`, `Concurrency/Merge/MergeBraid.lean`, `Concurrency/Merge/MergeGenerate.lean` |
| **The two comparisons are the merge and the atom** | `cubeMerge = wedgeToTensor ≫ ≅` and `cubeReorder = wedgeSwapTensor ≫ ≅` are the two maps `□m ∨ □n ⟶ ⊗`, `⊗ᵍ` having no swap; spliced at a cut they are `mergeHom` (`W_mergeHom`) and `atomHom` (`not_W_atomHom`) | `Precubical/Wedge/WedgeTensor.lean`, `Concurrency/Merge/TotalMerge.lean` |
| **The generators exhaust the crossing-free refinements** | `W_iff_crossPerm_eq_one` — a crossing-free refinement that loses a bead factors through the canonical merge at any junction its target does not separate, so peeling merges off terminates; `merge_iff` says the generators are the codimension-one members.  `W_iff_monotone_coordMap` reads the same class order-theoretically: `W K f ↔ Monotone (coordMap f.φ)`, since `pos` is the unique monotone bijection of events | `Concurrency/Merge/MergeGenerate.lean` |
| **A hom-set is pinned by the two extreme ones** | `exists_crossPerm_mid` — for `o ⟶ a ⟶ b ⟶ z` whose outer legs cross nothing, a permutation realised `o ⟶ b` and `a ⟶ z` is realised `a ⟶ b`.  Uniqueness of factorisation (`factor_ext`) forces the leg out of `b` to be the merge, so the middle arrow carries the permutation the extremes already do.  With `exists_crossPerm_ones` (out of the run, the parabolic) and `exists_crossPerm_single` (into one bead, the Young-coset representatives) as the only coordinate input, this answers "which permutations does `a ⟶ b` realise" with no coordinates | `Concurrency/Grading/Coarser.lean`, `Concurrency/Merge/AtomPair.lean` |
| **A chain morphism is its permutation** | `hom_ext_of_crossPerm` — merges into the coarsest chain exist out of every chain (`exists_W_to_top`) and are pinned by their endpoints (`eq_of_W`), and out of the run every permutation is realised exactly once: `⋁(topDims n)` *is* `□n`, so `onesTopEquiv` counts the arrows `1ⁿ ⟶ [n]` as the runs of the cube (`onesChartEquiv`, `runPermEquiv`) | `Concurrency/Grading/Coarser.lean`, `Concurrency/Grading/TopBead.lean` |
| **Into the group it is not full** | `not_surjective_posToBraid` — a positive braid's writhe never goes negative, so no `σᵢ⁻¹` is in the image of `PosBraid n →* Braid n` | `Machinery/Braid/PosGerm.lean` |
| **`ConcPos` reads the cell structure** | `outLabels_eq_parabolic` — the crossing permutations out of an execution are exactly the parabolic `S_{d₁}×⋯×S_{d_k}` of its bead dimensions | `Testing/Pi1/Parabolic.lean` |
| **The atoms out of a run satisfy the Artin relations** | `atomLoop N k` is the `k`-th coordinate flip `1ᴺ ⟶ [1,…,2,…,1]` read as a loop once the merges are inverted; `atomLoop_comm` for far-apart cuts and `atomLoop_braid` for adjacent ones, both off the codimension-two cell the two atoms share (`exists_pairCell`) — the second leg of each is the other atom, a leg being pinned by its crossing permutation (`exists_leg`, `conj_eq_of_crossPerm`).  `Cut.exists_eq_atom` says those `N−1` flips are the only codimension-one generators out of the run that are not merges | `Concurrency/Presentation/LocPresentation.lean` |
| **…and they generate** | `exists_atomWord` — a loop at the run is the word its crossing permutation spells: `runLoop N σ` factors as `permLen σ` atoms, one per inversion, built by peeling an adjacent descent (`exists_adjacent_descent`) and appending across the ascent (`runLoop_mul_adjT`).  `conj_eq_runLoop` says every refinement's loop is one of these — its source merged back to the run, its target coarsened to one bead — so `exists_atomWord_conj` factors *every* `⋁a ⟶ ⋁b` as a word in atoms conjugated by the two merges | `Concurrency/Presentation/LocPresentation.lean` |
| **A factorisation is its middle shape** | `factorisationEquiv f : Factorisation f ≃ MidShape a b` — the two-step factorisations of `f` are exactly the shapes whose junctions lie between the two ends', `exists_factor` for existence and `factor_ext` for the legs.  Counting factorisations is then counting an interval: `exists_atomPair_of_codim_two` says a codimension-two refinement of the run has **exactly two** atoms below it, the two junctions it drops read as indices (`boundaries_atomComp`), and `artin_of_codim_two` splits them by species — adjacent cuts give the hexagon, apart cuts the square | `Concurrency/Merge/Factorisation.lean`, `Concurrency/Merge/AtomPair.lean`, `Concurrency/Presentation/LocPresentation.lean` |
| **Only adjacent cuts need a 3-cell** | `wedge2Map_isPushout` — the **interchange square of the wedge is a pushout**, so two refinements re-shaping opposite halves of a wedge descend to one, uniquely, with nothing assumed of the four sets.  Read in `Ch K` (`exists_join_of_split`, splitting at the shared junction) that is `hasDiamonds_disjoint`: cuts **separated by a junction** join, for *every* `K`.  Of the three species of a codimension-two join only the *adjacent* one is left as a hypothesis (`HasDiamonds`, the 3-cell); the third is empty — cuts at the same junction are the same cut, and at equal target shapes `eq_of_join_of_dims_eq` says there is no join at all, a factorisation being its middle shape.  `exists_join_of_dims_ne` assembles the three | `Precubical/Wedge/WedgeMonoidal.lean`, `Concurrency/Grading/Degree.lean`, `Concurrency/Grading/Coarser.lean` |

| **A discrete fibration localizes fibrewise** | `isLocalization_elementsDescent : ∫P` localized at the cartesian lifts of `W` is `∫P̄` over `B[W⁻¹]`, for any `W`-inverting `P : B ⥤ Type` — proved by turning the (presentation-free) universal property of `∫P̄` into that of `B[W⁻¹]`, a functor `∫G ⥤ E` being the same as a functor `D ⥤ Fam E` lifting `G` | `Machinery/Localization/FibrationLocalize.lean` |
| **A chain is its dimension sequence plus its classifying map** | `chEquivElements : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ` for `wedgeHoms K = ⋁- ⟶ K` on `(Ch Zbp)ᵒᵖ`, and `W K` is its `W Zbp`; hence `isLocalization_chDescent` — once `wedgeHoms K` inverts the merges, localizing `Ch K` only localizes the base | `Concurrency/Presentation/ElementsFibration.lean` |
| **`C ≌ ⟨generators \| relations⟩`** | A `Polygraph` is combinatorial data alone — 0-cells `V`, 1-cells `Gen`, 2-cells `rel` on the words they spell — presenting `presented = Quotient rel` on `Paths (GenObj Gen)`, naming no category.  `Polygraph.Hom` sends a cell to a cell in *every* dimension, so polygraphs form a category and `Hom.functor` is functorial; `Polygraph.Spelling` is the weaker gadget that lets a 1-cell spell a whole *word*, which is what a comparison of two presentations needs and a `Hom` cannot give.  `Polygraph.comap` reads `P`'s 2-cells on a quiver over `P`'s, which is what both `elements` and `restrict` are.  `Presents P C` is the *theorem* that `P` presents `C`: a functor `P.presented ⥤ C` with `IsEquivalence`.  So `transport` along an equivalence is a composition, and spanning / completeness / covering are `p.eval.map_surjective`, `p.E.map_injective` and `p.eval` being `EssSurj` — mathlib's, not a bespoke four axioms.  `ofDesc` is the constructor that takes those obligations; `presentedMonoidPresentation` turns a `PresentedMonoid` into one on `(SingleObj M)ᵒᵖ`, the `ᵒᵖ` being the composition order and not a choice | `Machinery/Presentation/Basic.lean`, `Machinery/Presentation/Monoid.lean` |
| **A presented base presents the total category** | `Presents.elements p F : Presents (p.elementsPoly F) ∫F` for `F : C ⥤ Type` — generators the base's acting on an element, relations the base's on projected words.  Words lift uniquely because the projection of generating quivers is a covering (`exists_lift`), and a relation downstairs imposes exactly its lifts upstairs (`gen_onElements`).  `ActionCategory M A` *is* `∫(actionAsFunctor M A)`, so a presented monoid presents its action category with nothing further to prove | `Machinery/Presentation/Elements.lean` |
| **…and the *defined* part of it, when lifting is only partial** | A functor with *at most one* lift of each arrow is classified by a presheaf of **partial** functions; since `Par ≃ Set⋆` and `[Cᵒᵖ, Set⋆] = 1/PSh C`, that is an ordinary `G` with a global section `bot`, and the category is `∫G` minus it.  So nothing new is presented: `partialElements = (p.elements G).restrict (defined G bot)`, and `restrict` is free because `bot` is **absorbing** — a word reaching it stays there, so a word between defined objects never passes through it (`ObjectProperty.Convex`, `convex_of_absorbing`).  `bot` unreachable is the total case, where the defined part is `∫` of an honest presheaf (`definedEquiv`) and the restriction discards nothing | `Machinery/Presentation/Partial.lean` |
| **`Ch Zbp` is presented by its bead cuts** | `zCutPresentation : Presents Cut.poly ((Ch Zbp)ᵒᵖ)` — generators the codimension-one refinements, relations the codimension-two ones (two paths of length two with the same value).  The engine is `exists_factor` / `factor_ext` (`Concurrency/Grading/Coarser.lean`): read in a chart of the target, a factorisation *is* an intermediate chain of the cube, and there is exactly one of each shape — `exists_mid_chain` sends a coordinate to the block of the shape in which its own bead starts, `chain_ext_of_dims` pins it because down-sets of the source's bead order are linearly ordered by inclusion.  `boundaries d` (mathlib's `Composition.boundaries` for the dimension list) turns the shapes into a lattice — `nonempty_hom_iff` says `a ⟶ b` exists exactly when `boundaries b ⊆ boundaries a`, one way by splitting the source at each junction of the target, the other by merging one junction at a time — and `boundaries` is injective, so a one-cut step is pinned by the boundary it removes (`mid_eq_of_cuts_eq`), and two steps out of one shape close a diamond over any common coarsening (`exists_diamond`), which `Cut.exists_front` runs down a generating path | `Concurrency/Presentation/CutPresentation.lean`, `Concurrency/Grading/Coarser.lean`, `Concurrency/Grading/Boundaries.lean` |
| **A thin category is presented by any spanning quiver** | `Presents.ofThin` — relating *every* parallel pair of words leaves no word problem, so a presentation of a preorder is a spanning family of generators on a covering family of 0-cells and nothing else (`Polygraph.thin`; soundness, completeness and faithfulness are all free).  At the cube that is `cubePresentation n : Presents (Polygraph.thin (CubeStep n)) ((W (□n)).Localization)` — 0-cells the runs, generators the **atom steps**, one per descent — since `Ch (□n)[W⁻¹]` is a poset (`locCube_isThin`; `locCubeWeakOrder` names it as the weak Bruhat order): `exists_word` read as a path is fullness — and `exists_word` is the base's spanning theorem, spelled (`exists_word_of_hom` applied to `nonempty_loc_hom`) — while the merge out of a chain's own run (`classRunIso`) is essential surjectivity | `Machinery/Presentation/Basic.lean`, `Concurrency/Presentation/CubePresentation.lean`, `Concurrency/Merge/CubeThin.lean` |
| **A product of polygraphs presents the product** | `Presents.prod : Presents P A → Presents Q B → Presents (Polygraph.prod P Q) (A × B)`, hypothesis-free — 0-cells the pairs, 1-cells a copy of `P`'s with the `Q`-coordinate frozen and a copy of `Q`'s with the `P`-coordinate frozen (`ProdGen`, an indexed inductive, so no transport is spelled), and the 2-cells are the two factors' **plus `ProdRel.interchange`**: `(g,1)·(1,h) = (1,h)·(g,1)`, without which the words would present a free product.  Completeness is the normal form it buys, `exists_normalForm`: every word is a `P`-word then a `Q`-word | `Machinery/Presentation/Product.lean` |
| **The localized slice splits over the beads** | `locChConsEquiv n rest : (W (□n)).Localization × (W (⋁rest)).Localization ≌ (W (⋁(n :: rest))).Localization`, from `chConcat_isEquivalence : Ch X × Ch Y ≌ Ch (X ∨ Y)` and the binary `IsLocalization.prod`: `serialWedge_cons` is `rfl`, so the wedge splitting already *is* the recursion on a dimension list — no reindexing, no `eqToHom`.  `locOverEquivWedge` reads it on the base's slice; `locOverEquivBase K c` says the localized slice of `Ch K` under a chain is the base's under that chain's *shape*, unconditionally in `K`, since `toChZ K` is a discrete fibration and `W K` is `W Zbp` pulled back; and `locSlice_isThin` / `locOver_isThin` say both are posets.  This is a description of the **category**.  It is deliberately *not* a way to build the presentation — the slice presentations are inherited from the base (below), so that there is one route and not two | `Concurrency/Merge/WedgeLocalize.lean`, `Concurrency/Presentation/SlicePresentation.lean` |
| **Gluing the slices wants a functor of them, and the cells of the colimit are read on a leg** | `glueV`/`glueE` name a copy's 0- and 1-cell in `colimit (elementsPoly (wedgeHoms K) P)`, `glueV_leg`/`glueE_leg` are the colimit's own naturality, and `at_glueV`/`arrow_glueE` say which object and which arrow a cell names — `glueIncl_desc` computed on a leg, so no cell of the colimit is ever unfolded.  The compatibility `hP` is an equality of *functors* — the slice presentations commute with pushing the base; for the inherited family it is `slicePoly_hP`, whose object half is `overMapLoc_obj` (`overMapLoc` is `Over.map` on objects) and whose morphism half is `Subsingleton.elim` in the poset `locOver_isThin` — the one place the route spends thinness | `Concurrency/Presentation/SlicePresentation.lean`, `Machinery/Presentation/Glue.lean` |
| **…and each localized slice is the weak order on its run-arrows, for every `d`** | `nonempty_locOver_hom_of_le` and `RunOver.eq_of_locIso`, **unconditional in `K`**.  Two halves.  A *grading*: `weakOver_le_of_loc_hom` — `Machinery/Grading`'s `degLoc` chain, at `weakOver` at an arbitrary base, with `crossOver` for `cross` and nothing in it about the cube.  And one *geometric* fact, `index_crossPerm`: **an arrow permutes each block of its target and no more** — read the target in its own standard chart, where the source's firing order inverts `crossPerm` (`crossPerm_flatten`) and a coarsening's beads are the target's blocks read in that order (`beadOf_of_hom`).  So a descent at `k` puts `k` and `k+1` in one block (`index_adj_eq_of_descent`), which *is* the arrow `zObj (atomComp N k) ⟶ d` (`nonempty_hom_of_index`); and `exists_crossPerm_of_blocks` then realises `σ * adjT k`, because the only pair `adjT k` reorders is that one (`exists_run_mul_adjT`).  Fullness is `exists_cover_of_lt` picking the descent and this realising it, on an induction over `permLen`; essential surjectivity is `runMerge`, which the localization inverts.  `locOverWeakOrder` packages the three as an equivalence `(Ch(Z)/d)[W⁻¹] ≌ (WeakOrder N)ᵒᵖ`, wherever every permutation is realised.  **The cube is that statement at `d = zObj (topDims n)`**: `cubeTop n` is terminal so `Ch (□n)` is its own slice, `locOverEquivBase` moves that slice to the base's, and `onesTopEquiv` realises all of `Sₙ` there — which is `locCubeWeakOrder`, not a second argument.  The *spanning* half moves the same way and needs no equivalence, only that both comparisons localize one class (`nonempty_loc_hom_of_isLocalization`): `nonempty_loc_hom` is the cube's arrows, read off the base's, and `Merge/CubeThin` spells them rather than finding them | `Concurrency/Presentation/SliceRuns.lean`, `Concurrency/Merge/CubeSpanning.lean`, `Concurrency/Presentation/SliceExchange.lean`, `Concurrency/Merge/CubeWeakEquiv.lean`, `Concurrency/Grading/ChartHom.lean`, `Concurrency/Merge/CubeFaces.lean` |
| **…and by the base's own cells, at whichever presentation the base carries** | The runs over `d` are a **downward-closed** set of permutations for the right weak order — that is the exchange `exists_runOver_mul_adjT`, iterated (`runSet_of_le`) — so `PosBraid N` acts on them partially by length-additive right multiplication (`weakActionOn`, built with `PosBraid.lift`, never through Artin), `sliceFibre d = chartFibre (sliceActionAt d)` is the presheaf on the localized base that the action gives — one fibre per strand count, glued by `strandDecomposition` — and its defined part **is the localized slice, reversed** (`definedSliceLoc`): a braid raises the weak order where a slice arrow lowers it, which is the only `ᵒᵖ` in the family.  `strandDecomposition.functor` is a `Functor.inv` and is never evaluated on objects: `preDefinedEquiv` transports the *defined* part along `runBase N` (`chartFibreEquiv`), asking covering only of the objects carrying a defined element — which `isEquivalence_pre` cannot ask, since `bot` sits over every object.  So `slicePolyFunctor p := (p.elements (sliceFibre ·)).restrictPoly (defined ·) ⋙ opFunctor` lifts the *base's* cells — a 1-cell is a generator of `p` acting on a run, a 2-cell a relation of `p` holding there — and moves when `p` does: `(0, 6, 72)` Artin relations against `(8, 144)` germ ones, where the thin family gives `(4, 54, 9888)` at every `p`.  Functoriality is **lax and not natural**: pushing a run along `f : d' ⟶ d` commutes with the action only where both ends are defined (over `𝟙²` the atom is undefined; over `[2]` it is), which is exactly what a morphism of polygraphs asks and what `PartialFam`/`partialElementsMap` consume.  `hP` is the whole obligation, and it is free — the 0-cells name their own slice objects (`sliceCellOver`) and pushing them is `Over.map` — so there is no condition on the base at all | `Concurrency/Presentation/SliceInherit.lean`, `Concurrency/Presentation/SliceFibre.lean`, `Concurrency/Presentation/ChartFibre.lean`, `Machinery/Braid/WeakAction.lean`, `Machinery/Presentation/Partial.lean` |
| **The word problem is a retraction, slice by slice** | `presentsSliceColimit` *proves* Φ faithful rather than assuming it, and takes only `hP` — an equality of *functors*: nothing is asked of the target categories and nothing whatever of the 0-cells.  The retraction is the **choice-free** one — a 0-cell naming each slice's identity (`sliceTop`, from `EssSurj` alone), and every other object entered by pushing that one along its own structure map (`sliceRetObj`) — so `sliceRetObj_push` is `P`'s functoriality on the nose and `sliceRetObjIso_push`, the single coherence, is `overMapLoc_comp`.  `sliceRet` is then `Functor.invOfPreimage`, the inverse of a fully faithful functor read at a chosen preimage of each object, and its two comparisons with `𝟭` and all four squares (`sliceRet_square`, `sliceRetComp_square`, `sliceRetArrow_square`, `sliceUnitArrow_square`) are that gadget's.  What is then *false* is that `Φ ⋙ Ψ = 𝟭`: several 0-cells may name one slice object, and `presentsGlue₂` is data where two do and are not glued.  So both the unit and the counit are only isomorphisms, and both travel the same way — carried as a functor into `Arrow` (`NatTrans.toArrow`) whose two projections are the functors being compared, so every compatibility stays an *equality*.  The unit descends along the colimit of polygraphs (`sliceUnitArrow_square`, `glueUnitLeg`, `glueUnitArrow`, `glueUnitArrow_left`/`_right`, `glueUnitArrow_isIso`, using `exists_colimit_ι_obj` for the components), the counit along the slices of `∫X` (`glueCounitCocone`, `glueCounitDesc_left`/`_right`, `glueCounitArrow_isIso`).  The colimit's universal property on presented categories (`glueLift`, `glueInclFun_lift`, `glue_functor_ext`) comes straight from `catHomEquiv`.  A levelwise *isomorphism* is out of reach in any case — a localized slice is thin but never skeletal, since a `W`-arrow makes distinct objects isomorphic, and `exists_not_isRun_over` witnesses the failure at `Ch K` | `Machinery/Presentation/Glue.lean`, `Machinery/Localization/SliceFamily.lean`, `Machinery/Presentation/ColimitCells.lean` |
| **The cube's atom steps are an Artin family** | `isArtinFamily_cubeAtom n` — the cube's partial atom action satisfies commutation and braid, so it *is* a monoid hom `chartActionAt : PosBraid N →* (strictEnd (RunChart (□n) N))ᵐᵒᵖ` (`PosBraid.liftArtin`), landed in the `none`-preserving submonoid and read contravariantly (`IsArtinFamily.op`: the relations are reversal-invariant, so the base's `ᵒᵖ` costs nothing).  The braid case needs **no 3-cell**: `atomAct` is defined exactly at an *ascent* and multiplies `cross` by `adjT k` (`atomAct_eq_some_iff`), so each three-letter route is defined exactly when its window increases — the same three inequalities in a different order.  Nothing here uses `hasDiamonds_cube` or `CubeFaces`' meet layer, which stay load-bearing for thinness alone | `Concurrency/Presentation/CubeChartAction.lean`, `Concurrency/Presentation/PartialAtom.lean`, `Machinery/Braid/Artin.lean` |
| **…and the charts they act on are the weak order** | `chartWeakEquiv n : ChartCat n ≌ WeakOrder n`.  A chart over the run *is* its crossing permutation (`crossOnesEquiv`), and a braid is defined at it exactly where it adds all of its own crossings — one length equation, `permLen (crossOnes x) + toAdd (posLen n β) = permLen (crossOnes y)` (`chartActionAt_eq_some_iff`), which by subadditivity of `permLen` forces both that `β` is a simple (`eq_posPerm_of_posLen`) and that the product is length-additive, i.e. exactly the right weak Bruhat order.  Neither of those is argued at the cube: a hom out of `PosBraid n` is its atoms (`posBraid_hom_ext`, from the descent recursion's uniqueness), and the cube's atoms are `weakActionOn`'s, so `chartActionAt_eq_weakActionOn` identifies the whole action with the weak one and `chartsWeakEquiv` reads the charts off it.  This is a second, independent route to the order that `locCubeWeakOrder` reaches through the base's slice | `Concurrency/Presentation/CubeChartWeakOrder.lean`, `Concurrency/Presentation/ChartFibre.lean`, `Machinery/Braid/Matsumoto.lean` |
| **A presentation of `Ch Zbp` lifts to `Ch K`, but not to its vertex monoids** | `chPresentation : Presents (p.elementsPoly (wedgeHoms K)) ((Ch K)ᵒᵖ)` pulls a presentation of `(Ch Zbp)ᵒᵖ` back along the fibration, and `chCutPresentation` is it with the base presentation supplied — unconditionally.  Under `IsSegal` the fibration survives the localization, and `hLocPresentation` is the same pullback there; `hLocActionPresentation = (hLocPresentation n).transport (hLocEquiv n).op` is *that same 2-polygraph*, read on the action category. `End` does **not** follow: `endEquivStabilizer` says it is a stabilizer, and `end_not_generated_by_simples` — in `PosBraidAction n` the only generator that is a loop is the identity, while the loops are `PosPureBraid n` — says a stabilizer is not spanned by the generators sitting at it | `Concurrency/Presentation/LiftPresentation.lean` |
| **The decorated chains act on the orderings** | `chToAction : Ch (Hbp □ⁿ) ⥤ PosBraidAction n` — a chain goes to the order its events perform the axes in (`fibrePerm`, the step at which each axis is performed), a refinement to the simple of its crossing permutation, `fibrePerm_comp` being the action condition; `chToAction_obj_surjective` says the runs exhaust the orderings | `Concurrency/Complexification/HPosAction.lean`, `Machinery/Braid/PosAction.lean` |
| **Crossing a wall** | A codimension-one chain lies *below* both chambers it separates, so `wallCross w k` is the apex of a span whose legs are `wallLeg` (crossing `adjT k`) and `wallLegFlip` (a merge, `W_wallLegFlip`); `wallCrossLoc` inverts the second and turns the span into an arrow of chambers | `Concurrency/Complexification/HPresentation.lean`, `Concurrency/Salvetti/CrossCompare.lean` |

**Retained infrastructure** not on the results' path but kept as finished mathematics:
- the **geometric tensor** `⊗ᵍ` — a computable `MonoidalCategory` on `PrecubicalSet` and on the
  alias `GeoBP := BPSet` (`Precubical/Wedge/GeoTensor/`), plus the abstract Day-convolution version
  and their comparison (`DayTensor.lean`, `CubeTensor.lean`);
- the **nerve bridge** `nerveRealizeIso : Nerve (realize X) ≅ X` between the concrete and topos
  models (`Precubical/Basic/Nerve.lean`, `Reachability.lean`) — a natural iso, not an adjunction.

## Layered layout — three provenance tiers

`Machinery/` → `Precubical/` → `Concurrency/` is the spine, and it is a **provenance** order as much
as a dependency one: tier 1 is what a paper would cite, tier 2 what it would recall from the
precubical literature, tier 3 the contribution. `Machinery/Arrangement/` (COMs, the braid
arrangement) is a **second root** — it imports nothing else in the tree — and feeds
`Machinery/Braid/`; the two join the spine at `Concurrency/Salvetti/ChainBraidFace` and
`Concurrency/Salvetti/EventBraid`. `CubeChains.lean` imports the results and the retained
infrastructure; only `Testing/` sits outside its cone.

A module listed nowhere below and holding a single comment line is **retired**: the file survives
because it cannot be removed from the working tree, and nothing imports it. `Scratch/`,
`Scratch.lean`,
`Machinery/Presentation/{Scratch,Scratch2,Scratch3,Sigma,CellularAdjunction,GlueOn}.lean` and
`Concurrency/Presentation/SliceFunctor.lean` are the current ones. Do not read them.

### `Machinery/` — tier 1: generic mathematics, cited rather than proved

*The cube category (`Machinery/Cube/`).*
- `Box.lean` — the box category `Box` (objects = dimensions, maps inherited from the concrete
  model) and the topos `PrecubicalSet := Boxᵒᵖ ⥤ Type` (`HasPushouts` free).
- `BoxMonoidal.lean` — the **parallel tensor** on `Box`: `▫m ⊗ ▫n = ▫(m+n)`, morphisms concatenate
  sign vectors; `MonoidalCategory Box`. **`Box` is NOT braided** — no block swap exists.
- `SymBox.lean` — the **symmetric box category** `SBox` (`▪n`): the injections `Fin m ↪ Fin n` plus
  signs, so `Aut ▪n = Perm (Fin n)`.  `J : Box ⥤ SBox` is the monotone wide subcategory, and
  `sHomEquiv : (▪m ⟶ ▪n) ≃ Perm (Fin m) × (▫m ⟶ ▫n)` is the sorting factorization.
- `SymPresheaf.lean` — the round trip `H = J* ∘ J₍!₎` on `PrecubicalSet`: `symFree.obj K` at `▪n` is
  `Perm (Fin n) × K.cells n`, restricted by the sorting factorization of `u ≫ symHom σ`; `symUnit`
  exhibits it as the left Kan extension along `J.op`, and `symFreeIsoLan`/`HIsoLan` identify it with
  mathlib's `J.op.lan`.  `symFreeAdj : symFree ⊣ symRestrict` is that universal property read as
  an adjunction, with `symUnit` for its unit.
- `SymRepresentable.lean` — **`symFree (□ⁿ) ≅ y(▪n)`** (`symFreeCube`, the sorting factorization
  made natural), hence `HCube : H(□ⁿ) ≅ J*y(▪n)` and the faithful `reorientH : Sₙ →* Aut (H □ⁿ)`,
  which is left multiplication of orders on the top cell and permutes every face's axes.
  `cellDir` — the axis a cell performs at step `j`, i.e. the `SBox` map's own `pos` — is the form
  the action is cleanest in: `cellDir_reorientH` says `σ` relabels every step.  The same rigidity
  gives `isEmpty_cubeHom`: for `n ≥ 2` there is **no** map `H(□ⁿ) ⟶ □ⁿ`.

*Localization, and categories of elements (`Machinery/Localization/`).*
- `FibrationLocalize.lean` — localizing a discrete fibration `∫P → B` fibrewise.  `Fam E` is the
  free coproduct completion and `Fam.pack`/`Fam.unpack` is the bijection between functors
  `∫G ⥤ E` and functors `D ⥤ Fam E` lifting `G` — the device that gives `∫P̄` a universal
  property.  Also the generic `Elements` toolkit — base transport `CategoryOfElements.pre` (kept
  local: it computes, and `pack_pre` closes by `rfl`), `mapEquivalence`, and the equivalence along
  an equivalence of bases, which is mathlib's `Grothendieck.preEquivalence` read through
  `grothendieckTypeToCat` — and `endEquivStabilizer` (loops = stabilizer).
- `ElementsAction.lean` — a functor on a one-object category is an action.  `SingleObj M`'s
  `f ≫ g = g * f` already reverses, so a **covariant** `F : SingleObj M ⥤ Type` is a left `M`-set —
  no `ᵐᵒᵖ`.  The twist lives in the contravariant reading: `invActionPresheaf` (a `Γ`-set pulled
  back along `φ : M →* Γ`, restricting by `φ β⁻¹`) has `(∫ -)ᵒᵖ ≌ ActionCategory M`.  Also
  `isEquivalence_pre`: base transport is an equivalence when the base functor is fully faithful
  and covers everything carrying an element.
- `ElementsProd.lean` — the external product `F ⊠ G`, what `BPSet.prod` is the diagonal of.
- `SliceLocalize.lean` — the slices of a discrete fibration, localized: `over_inverseImage` says the
  two slices carry the same class, so `sliceLocEquiv` says they localize alike.  `overMapLoc` is a
  `Construction.lift`, hence **strict** — `overMapLoc_id`/`_comp` are equalities, which is what lets
  the slice diagram be a plain functor to `Cat`.
- `SliceFamily.lean` — **a functor on `C` is a cocone on its slices** (`overCoconeLocEquiv`), an
  `Equiv` of types rather than an equivalence of categories, because `Over.map` and `overMapLoc` are
  both strictly functorial.  A comparison that is only an *isomorphism* still needs no pseudo-cocone:
  read it as a cocone valued in `Arrow E` (`NatTrans.toArrow`), whose two projections are the
  functors being compared, and every compatibility stays an equality.
- `HomInduction.lean` — `hom_induction`: `morphismProperty_eq_top` with the `objEquiv` bookkeeping
  paid once, so a caller gets a predicate on `W.Q.obj c ⟶ W.Q.obj c'` with no transport in sight.

*The braid group itself (`Machinery/Braid/`).*
- `Germ.lean` — `Braid n` as a `PresentedGroup` by its Garside germ: one generator `[σ]` per
  permutation, one relation per **length-additive** product; `permHom : Bₙ ↠ Sₙ`, `PureBraid n`.
- `PosGerm.lean` — `PosBraid n`, the same germ presentation read as a **monoid** (`[1] = 1` must be
  imposed: without it every generator may go to one idempotent). `germ_of_atom` cuts the relations
  down to those whose right factor is an adjacent transposition — the only shape the geometry
  realises. `posToBraid` is not surjective (`writhe_nonneg`). `posPermHom` is `permHom` read on the
  monoid, `PosPureBraid n = mker (posPermHom n)` its positive pure braids, and `posPureToPure`
  compares them with `PureBraid n ≤ Braid n` — injective exactly as far as `posToBraid n` is,
  Garside's theorem, carried as a hypothesis.
- `PosAction.lean` — `PosBraidAction n = ActionCategory (PosBraid n) (Perm (Fin n))`: the orderings
  of the strands, with the positive braids realising the changes of ordering.  The action must be
  **left** multiplication through `posPermHom` (`x * posPermHom β` is a right action); the
  endomorphism monoid at every ordering is `PosPureBraid n`.  `eq_one_of_mul_eq_one` — the writhe
  is additive and non-negative, so there are no non-trivial units — makes `isIso_iff_eq_id`: a
  category, not a groupoid.
- `Artin.lean` — the adjacent transpositions `adjT k` and the Artin relations they satisfy.
  `IsArtinFamily g` is the pair of relations on a family; `isArtinFamily_of_atom` says **every**
  germ has one, multiplicativity across an ascent being the only input, so `ofPerm ∘ adjT`,
  `posPerm ∘ adjT` and `artinGen` are all instances.  `ArtinRel` states the two relations once, as
  words: `artinRels` reads them in the free group for `ArtinBraid n`, and
  `Machinery/Braid/Matsumoto`'s `ArtinPosBraid n` reads the same inductive as a monoid
  presentation.  Hence the comparison `garsideOfArtin : ArtinBraid n →* GarsideBraid n`.
- `Matsumoto.lean` — **Matsumoto's theorem for `Sₙ`** [RESULT].  `matsuLift g σ` peels an arbitrary
  adjacent descent off `σ` and recurses; `matsuLift_mul_adjT` is the local confluence — two descents
  are far apart (`hg.comm`) or consecutive (`hg.braid`) — and `permLen` is the termination.  Hence
  `PosBraid.liftArtin`, `posBraid_equiv_artinPos` and `garside_equiv_artin`, with no hypothesis.
- `Generated.lean` — adjacent transpositions generate `Braid n` (length-additivity).
- `Sum.lean` — the block-diagonal `permSum : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m+n))`; the
  crossing count adds because the blocks never interact.
- `WeakAction.lean` — **a downward-closed set of permutations is a partial braid action**:
  `weakAction X` has `β` defined at `σ` when `σ·β` is still in `X` and crosses every pair `β` names.
  Downward-closure for the right weak order is the only hypothesis — it supplies the intermediate of
  a two-step composite, which is exactly multiplicativity.  `weakActionOn` carries the action across
  a bijection, so a geometric set of runs carries it without being replaced by its permutations.

*COMs, the braid arrangement, Salvetti posets (`Machinery/Arrangement/`).*  See
`Machinery/Arrangement/README.md`.
- `COM.lean` — complexes of oriented matroids (sign vectors, composition `⊙`, `faceLE`), the BCK
  axioms.
- `Sal.lean` — the Salvetti face poset `Sal L` of a COM (cells `(X, T)` with `X ⊑ T`).
- `SalElements.lean` — `Sal L` as a category of elements of the "topes above" presheaf.
- `COMSum.lean` — the direct sum `L₁ ⊕ L₂` and `salSumEquiv : Sal(L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`.
- `Braid.lean`, `BraidPreorder.lean`, `BraidCovector.lean` — the braid arrangement `braidCOM n`
  (ground set = ordered pairs of `Fin n`) and its `Fin n` dictionary (`braidSign`, heights,
  ordered set partitions).
- `BraidSymmetry.lean` / `SalSymmetry.lean` — the `Sₙ` reorientation action on `braidCOM n`
  (`reorient σ`) and the induced action on `Sal`.

*Generators and relations (`Machinery/Presentation/`).*
- `Basic.lean` — `Polygraph`, the standard 2-polygraph: 0-cells `V`, 1-cells `Gen`, 2-cells `Rel`
  with a `src` and a `tgt` word, and `presented`, the words modulo the congruence `homRel` the
  2-cells generate.  A `Polygraph.Hom` sends a cell to a cell in every dimension, commuting with
  the boundaries, so polygraphs form a `Category` and `Hom.functor : P.presented ⥤ Q.presented`
  is functorial; `Spelling` is the weaker gadget that lets a 1-cell spell a whole *word*, which a
  `Hom` cannot; `comap` reads `P`'s 2-cells on a quiver over `P`'s.
  Separately, `Presents P C` is the *theorem* that `P` presents `C` — a functor `P.presented ⥤ C`
  that is an equivalence — so `transport` is a composition and `ofDesc` is the only place the
  classical obligations appear.  `Polygraph.thin` + `Presents.ofThin` are the thin case, where
  there is no word problem at all.
- `Adjunction.lean` — `presentedFunctor ⊣ catPolyFunctor` (`presentedAdj`), where `catPoly C` reads
  a category as a polygraph (every arrow a 1-cell, every parallel pair of words that compose alike
  a 2-cell).  Hence `presented` preserves colimits, and `presentsColimit`: a colimit of polygraphs
  presents the colimit of what they present.  **This adjunction is not the core theorem**: strict
  colimits do not respect levelwise equivalence, so a family of *equivalences* of slices does not
  descend through `colim` (see `SliceColimit.lean`).
- `Coproduct.lean` / `Coequalizer.lean` — the disjoint union and the levelwise quotient, each with
  its `IsColimit`, giving `Polygraph` all colimits.  `Coproduct`'s 1-cells are the indexed inductive
  `CoproductGen`, so no transport is spelled.
- `ColimitCells.lean` — **a colimit's cells are the colimit of the cells**: a prefunctor out of `P`'s
  generating quiver *is* a morphism `P ⟶ thin Gen'`, so cells are a left adjoint and carry colimits.
  `colimitCells` descends a compatible family, and joint surjectivity of the legs
  (`exists_colimit_ι_obj`, `exists_colimit_ι_map`) is one test against a quiver of *propositions*.
  Nothing is ever unfolded.
- `Elements.lean` — `Presents.elements`: a presented base presents `∫F`, on the `comap` of the
  base along the projection of generating quivers.
- `Monoid.lean` — `presentedMonoidPresentation`: a `PresentedMonoid` presents `(SingleObj M)ᵒᵖ`.
- `Opposite.lean` — `Polygraph.op` and `Presents.op`: a presentation of `C` is **not** one of `Cᵒᵖ`,
  because a word composes source-first, so comparing across a variance means reversing words.
  Reversal is an involution, which is what carries a chain of rewrites (`quot_map_of_rev`).
- `Comparison.lean` — `Presents.Map p q`: a `Spelling` whose induced functor commutes with the two
  comparisons, automatically an equivalence (`isEquivalence`).  A mere *choice* of word makes the
  statement vacuous; the comparisons worth building send generators to generators.
- `Partial.lean` — `Presents.restrict` to a convex full subcategory; the partial case, `∫G` minus an
  absorbing global section (`Presents.partialElements`, `definedEquiv`); `PartialFam` /
  `partialElementsMap` for the **lax** functoriality a partially-defined family has; and
  `partialActionFunctor`, the presheaf a monoid acting by partial maps gives, which is how a client
  produces one without naming a presentation.
- `Product.lean` — `Polygraph.prod` and `Presents.prod`, hypothesis-free; the interchange 2-cells are
  what stops the words presenting a free product, and `exists_normalForm` is what they buy.
- `ChosenInverse.lean` — `Functor.invOfPreimage r θ` inverts a fully faithful functor at a *chosen*
  preimage of each object, so a family of such inverses is **strictly** natural in a parameter,
  which `Functor.inv` cannot be.
- `Glue.lean` — the glued polygraph **is** `Limits.colimit (elementsPoly X P)`; `presentsSliceColimit`
  is the theorem, taking only `hP` — an equality of *functors*, so nothing is asked of the target
  categories — and `glueSliceEval` / `elementsLift` the
  strict-on-objects comparison the cells are interpreted through.
- `SliceColimit.lean` — `C[W⁻¹]` **is** the colimit of `overLocFunctor W : C ⥤ Cat`
  (`isColimitOverLocCocone`), so `presentsColimitOfLocalizedSlices` reads the same theorem with a
  colimit on both sides.
- `GlueRefutation.lean` — `presentsGlue₂`: two 0-cells naming one slice object, the colimit
  presenting anyway, and hence why the unit can only be an isomorphism.  The 0-cells of the colimit
  are the *copies'*, never their image in `∫X`.

*Loose at `Machinery/` — small generic facts belonging to no chapter.*
- `Slice.lean` — `Functor.IsDiscreteFibration F`: `Over.post F : Over c ⥤ Over (F.obj c)` is an
  equivalence for every `c`, said without choice.  `MorphismProperty.over_inverseImage` holds of
  *any* `F`, and `π_leftOp_isDiscreteFibration` is the example — mathlib's `Elements` is the
  opfibration convention, so the fibration over `C` is `(π X).leftOp`, and **that bookkeeping lives
  here and nowhere else**.
- `SigmaComponents.lean` — `ObjectProperty.sigmaEquiv`: a family of object properties covering every
  object with no morphism between different members exhibits the category as the disjoint union of
  the corresponding full subcategories.  Mathlib's `decomposedEquiv` is the case where the index is
  the set of components; here it is supplied.
- `StrictInverse.lean` — `Equivalence.ofStrictInverse`: between **thin** categories, a pair of
  functors inverting each other on objects is already an equivalence, every coherence being a
  `Subsingleton.elim`.
- `Grading.lean` — a **grading** gives every morphism a natural number, additive along composition:
  a functor to `Grade`, the delooping of `(ℕ, +)` spelled additively so that `omega` can use it.
  `ofRise` builds one from an object degree morphisms only ever raise;
  `op`/`comap` carry one along a functor, and vanishing on isomorphisms is then formal.
- `SortPerm.lean` — `Tuple.eq_sort_inv`: an injective tuple is put in order by exactly one
  permutation, so `Monotone (f ∘ σ⁻¹)` forces `σ = (Tuple.sort f)⁻¹`; hence
  `Equiv.Perm.monotone_iff`, a monotone permutation of `Fin n` is the identity.
- `MonoidalTransport.lean` — transporting `⊗ₘ` along a tensorator `μ : A ⊗ B ≅ P`, stated in an
  arbitrary monoidal category so that `rw`/`simp`/`monoidal` behave where they would not at `BPSet`.
- `HomMonoidal.lean` — the three instances mathlib lacks (the two-variable `Functor.hom` is lax
  monoidal; `F.op` is monoidal when `F` is; `discreteOp`), so a functor `k ↦ (A k ⟶ B k)`
  *inherits* its lax monoidal structure through `D ⥤ Cᵒᵖ × C ⥤ Type` instead of carrying
  hand-written coherence; plus `LaxMonoidal.Graded F`, the total monoid `Σ m, F m`.
- `DayTensor.lean` — the abstract alternative: Day convolution on `Boxᵒᵖ ⊛⥤ Type` (mathlib's
  `DayFunctor`), with the Yoneda-strong-monoidality `cubeDayIso` mathlib lacks. `noncomputable`.
- `Graded.lean` — `Graded M`, the total category of a family of monoids indexed by `ℕ`: degrees as
  objects, `End n = M n`, the degree transport living once in composition.  `FullBraid` is it at
  `Braid` — the groupoid `braidFunctor` maps into, hence the receptacle of `ConcPos`; `Graded.Germ` is
  what a target must supply for a permutation cocycle to compose, and `Germ.hom_comp` discharges
  that law once for every germ family.
- `Composition.lean` — mathlib's `Composition.index` (the block a position falls in) read off the
  prefix sums: `index_lt_iff` is the sandwich with no side condition, and everything about blocks
  follows — monotonicity, which block a junction starts, that a composition is determined by the
  partition it cuts (`eq_of_index_iff`), and the Young subgroup `Composition.parabolic`.

### `Precubical/` — tier 2: the precubical literature's cube chains

*Precubical sets, two models (`Precubical/Basic/`).*
- `Basic.lean` — the concrete/computable model: graded cells, `face ε i`,
  the precubical identity, the `Category` instance.
- `StandardCube.lean` — `□ⁿ` concretely (sign-vector cells `Fin N → Option
  Bool`, `none = ∗`), `faceCell`, `nones`.
- `Representable.lean` — **cube Yoneda**: `cubeRepr : (□ⁿ ⟶ K) ≃ K.cells n`; `canonicalMap`,
  `trueCount`, `coface`.
- `Bipointed.lean` — `BPSet` (a presheaf with two chosen `0`-cells) + `Hom` + category; `cells`,
  `vertex₀/₁`, `faceMap`/`cubeMap`, `IsAltitude`, and `comp_app_cell` (the `ConcreteCategory`
  bundling that defeats `rfl` on a composite application).
- `BipointedProd.lean` — the levelwise product with paired base points, as the binary product:
  `BPSet.prod` with `prodFst`/`prodSnd`/`prodLift` (computable, both legs `rfl`), shown to be the
  binary product by `prodFanIsLimit`, so `instance : HasBinaryProducts BPSet` and mathlib's `⨯`
  API apply.  Downstream spells `X.prod Y`; mathlib's chosen `X ⨯ Y` is `noncomputable`.
- `Nerve.lean` — `realize : PrecubicalSet ⥤ PrecubicalConstructions`, the nerve
  `Nerve : PrecubicalConstructions ⥤ PrecubicalSet`, and both round trips `realizeNerveIso`,
  `nerveRealizeIso` (each componentwise the cube Yoneda lemma `cubeRepr`).
- `Reachability.lean` — `PrecubicalSet`-level reachability and connected components `π₀`.
- `Terminal.lean` — the terminal precubical set `Z` (one cell per dimension), `Zbp`.
- `Altitude.lean` — the side conditions `NonSelfLinked` / `AdmitsAltitude`,
  all `PrecubicalSet`-level, + the `alt_*` lemmas.

*Wedges, and the geometric tensor (`Precubical/Wedge/`).*
- `Wedge.lean` — `cube n` (representable, bi-pointed), `wedge2 X Y` = `X ∨ Y` (pushout of a point),
  `vertexMap`, `serialWedge` = `⋁d` (the fold `List.foldr (□· ∨ ·) (□0)`).
- `WedgeMonoidal.lean` — the wedge as the **default** `instance : MonoidalCategory BPSet`
  (tensor `∨`, unit `□0`, associator `wedge2Assoc`, unitors, pentagon + triangle).
- `GluePushout.lean` — a **computable** pushout of presheaves (mathlib's is
  `Classical.choice`-opaque).
- `GeoTensor.lean` + `GeoTensor/{Hom,Unit,Assoc,Monoidal}.lean` — the **computable** geometric
  tensor on `PrecubicalSet`, from the closed form of the Day coend:
  `(X ⊗ Y)(▫n) = Σ p q, (p + q = n) × X(▫p) × Y(▫q)`, restriction = split the cell and restrict
  each half. `GeoTensor/Cube.lean` is `□m ⊗ □n ≅ □(m+n)` at the representable level.
- `GeoTensor/BP.lean` — the same on bi-pointed sets, written `X ⊗ᵍ Y`, carried by the alias
  `GeoBP := BPSet`; `cubeTensorIsoBP`. It lives on its own alias because bare `⊗` on `BPSet` is
  the **wedge**. Unit is `□0` on the nose.
- `CubeTensor.lean` — the computable universal property of `□m ⊗ □n = □(m+n)`
  (`cubeTensorPair`/`cubeTensorDesc`/`cubeTensor_hom_ext`), bypassing the Day wrapper.
- `WedgeTensor.lean` — the **two wedge-to-tensor comparisons** `wedgeToTensor : X ∨ Y ⟶ X ⊗ᵍ Y`
  and `wedgeSwapTensor : X ∨ Y ⟶ Y ⊗ᵍ X`, descended from the two slices meeting at the glued
  vertex (`slice_corner`).  There are two because `⊗ᵍ` has no swap; at cubes they are the two
  staircases `cubeMerge`/`cubeReorder` (`cubeMerge_ne_cubeReorder`), whose legs run complementary
  coordinate blocks (`faceEmb_of_sign_append_left`/`_right`).

*The cube-chain category (`Precubical/Chains/`).*
- `Basic.lean` — `Beads K d` (cube data at a *given* shape `d`) with its flat view
  `beadsEquiv : (Σ d, Beads K d) ≃ List (Σ n, K.cells n)`; `CubeChain` (a cube list satisfying the
  folded `IsCubeChain`; the junction vertices are forced, not stored), `ofIsCubeChain`.
- `WedgeMap.lean` — bi-pointed maps out of a serial wedge ↔ shape-indexed cube data; `wedgeDesc
  (c : Beads K.toPsh d) … : ⋁d ⟶ K.repoint a b` (re-pointing the target is what makes the endpoint
  conditions the morphism's own `app_init`/`app_final`), `beadCell`, `serialWedge_hom_ext`,
  the `glue0_*` pushout/mono cores.
- `Correspondence.lean` — **`equivWedgeCat`**; the chain↔wedge-map bijection; thinness.
- `Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category. The face inclusion is
  carried as *data*, not as a `Prop`.
- `Category.lean` — `ChainCat`, `chFunctor : BPSet ⥤ Cat`, `Aut.liftToCh`.
- `CubeVtx.lean` — vertices of cube faces (`cubeVtx`), the monotonicity the coordinate coend needs
  (`cubeVtxOfCell_bot_le_top`).
- `CubeNonSelfLinked.lean` — `cube_nonSelfLinked`; the concrete↔topos bridge `toStar` for cube
  cells.
- `ChainSkeletal.lean` — `Ch(K)` is acyclic and skeletal for **every** `K` (only identity
  endomorphisms); `blockIdx_surjective` — a refinement never drops a target bead.
- `ChainRestrictions.lean` — `restrictCubeChain face C` projects a chain of `□ᵇ` onto the directions
  a face uses, dropping the cubes that collapse. Not a precubical map (`Box` has no degeneracies)
  and **not** natural in `face` as a cube map — it factors through `faceEmb`, so there is no
  universal property over `Box` to look for. `EdgeChain K` and `EdgeChain.restrict` (+
  `_id`/`_comp`) are the all-edges subpresheaf this cuts out.

*Concatenation, splitting, and the lifts along a wedge (`Precubical/Segal/`).*
- `Segal.lean` — the append iso `serialWedgeAppend : ⋁x ∨ ⋁y ≅ ⋁(x ++ y)`, built **structurally**
  from `λ_`/`α_`/whiskering (so its coherence is monoidal, not a pushout chase); `⋁` as a **strong
  monoidal** functor `serialWedgeFunctor : DimList ⥤ BPSet` where `abbrev DimList := Discrete
  (FreeMonoid ℕ+)`; the concatenation `chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)` and its
  faithfulness.
- `SegalAltitude.lean` — `cube_admitsAltitude` / `wedge2_admitsAltitude` /
  `serialWedge_admitsAltitude`, which is what makes the n-ary decomposition hypothesis-free.
- `Split.lean` — the **choice-free** inverse of `chConcat`, in three layers: `Split Z A B` ("`Z` is
  `A ∨ B`" as data, on the computable `Glue.cellSide`), `Split.chainSplit` (the *order* — the only
  place altitude is used), and the interface `chObjEquiv : Ch Z ≃ Ch A × Ch B`. Also
  `splitWedgeMorphism`, the same split for a bare map `⋁as ⟶ X ∨ Y`, which is the form
  `Concurrency/Executions/Runs.lean` consumes.
- `WedgeLaxMonoidal.lean` — `chFunctor` is lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`; each coherence
  square is the matching `MonoidalTransport` lemma fed the append iso's own coherence.
- `WedgeExtend.lean` — lifting a (co)presheaf on `Box` to serial wedges, in both variances:
  contravariant `F↑ X = (X.toPsh ⟶ F)` (precomposition) and covariant `F↓ X = X.toPsh ⊗_Box F`
  (the cubical coend as a plain computable `Quot`, not `Functor.lan`).
- `PshExtMonoidal.lean` — `pshExtFunctor F = BPSet.toPshFunctor.op ⋙ yoneda.obj F` is oplax
  monoidal, strong under single-vertexness — so `Lines K a = (⋁a.dims).toPsh ⟶ runPresheaf`
  literally, with its splitting for free.

### `Concurrency/` — tier 3: the concurrency braid groupoid

See `Concurrency/README.md` and `Concurrency/BRAID.md`.

*The two gradings on `Ch K` — crossings, and codimension (`Concurrency/Grading/`).*
- `CoordFunctor.lean` — the **coordinate coend**: `coordFlip χ : beadEvent a ≃ Fin m` for
  `χ : ⋁a ⟶ □m`, `coordMap`/`coordMapEquiv` for wedge maps, `coordFlip_comp` (the engine behind the
  label theorem), `coordMap_eq` (its `blockIdx`/`blockFace` form), the run-free **lexicographic
  event order** `beadOrder` with `pos = finSigmaFinEquiv` as its monotone enumeration — hence
  `pos_eq_of_monotone`, the only monotone bijection of events — and the **monoidality of `coordMap`
  over `++`**: `eventInl`/`eventInr` split `beadEvent (a ++ b)` (`eventAppendCases`), and
  `coordMap_inclL`/`coordMap_inclR` say a wedge map restricting along the half-inclusions moves each
  block by its own restriction — the coordinate content of `chConcat`'s tensorator.
- `WedgeBraid.lean` — the **braid grading of `Ch K` from the wedge map alone**: `crossPerm h g` is
  `coordMap g.φ` read through `pos` at a strand count `h : dimSum a.dims = N` the source meets,
  length-additive (`permLen_crossPerm_comp`, from `coordMap_noDoubleCross`) and **monoidal over the
  wedge** (`crossPerm_chConcat`: on the tensorator it is the block sum `permSum`, so crossings add —
  `permLen_crossPerm_chConcat`).  Carrying the count rather than transporting afterwards is what
  makes the cocycle law a plain anti-homomorphism (`crossPerm_comp`): the target numbering of `g`
  and the source numbering of the next map are proofs of the same equation, hence the same term.
  `crossPerm_recount` is the only transport left, and it is `rfl`.  Everything geometric about
  `crossPerm` goes through `ChartHom`'s `crossPerm_flatten` instead of this definition.
- `ChartHom.lean` — **a wedge map is a chart refining a chart**: `chartHomEquiv` identifies
  `(⋁a ⟶ ⋁b)` with the charts of `⋁a` lying over a fixed chart of `⋁b`, the fibre description of
  the discrete fibration `Ch (□N) ⥤ Ch Zbp` with `Ch (□N)` thin.  `Coarser d d'` is then the
  boundary inclusion itself, and `nonempty_wedgeHom_iff_coarser` is `boundaries_subset_of_wedgeHom`
  one way and merging one junction at a time (`exists_W_of_coarser`) the other.  Charts of `⋁1ᴺ` in
  `□N` are the runs of the cube (`onesChartEquiv`).
  A chart *is* an ordered partition of `Fin N` (`beadOf`), and `flatten` sorts the coordinates by
  it: bead first, ties by the cube's own order.  `flatten` and the shape pin the chart
  (`chain_ext_of_flatten`), a coordinate's bead is the block its rank falls in
  (`beadOf_eq_index`, against `dimComp`'s `Composition.index`), and every order rising inside each
  block occurs (`exists_chart_flatten`).  `stdChart` is the chart flattening to the identity, so
  an arrow between two of them crosses nothing (`exists_crossPerm_eq_one`).  `crossPerm_flatten`
  reads `crossPerm` off the chart, which is what `hom_ext_of_crossPerm` and
  `exists_crossPerm_of_blocks` run on.
- `BlockDecomp.lean` — block decomposition of a serial-wedge map (`faceEmb`/`blockIdx`/`blockFace`),
  and its numerics from the serial wedge's own altitude: a source bead sits inside its target block
  (`serialWedge_beadStart_blockIdx`), so `blockIdx` is monotone and `∑ ad = ∑ cd`.
  Shared by `Salvetti/`.
- `TopBead.lean` — **the coarsest chain on `n` events (`topDims`: one bead, or none), and the
  arrows into it**. `eq_of_W`: a merge moves no event, and a wedge map *is* its coordinate
  bijection, so a merge is pinned by its endpoints. One bead coarsens every shape and the run of
  edges refines every shape, so `exists_W_to_top` (the total merge out of every chain) and
  `exists_W_from_ones` (the run of `N` edges merges *onto* every shape of strand count `N`) are
  the two extreme coarsenings; between the two extremes nothing is constrained, so `onesTopEquiv`
  identifies that hom-set with `Sₙ` — every permutation is realised out of the run.
- `Degree.lean` — the grading `degree = Σ (dim − 1)` on `Ch K` and the **codimension** of a
  refinement (beads lost).  `codimNat : chFunctor ⟶ gradeFunctor` is a *monoidal* transformation, so
  codimension is additive along the tensorator.  `splitTarget` — the tensorator read backwards —
  splits the source at every junction of the target, which is `boundaries_subset_of_hom`; the
  species of a refinement are then `Concurrency/Grading/Boundaries` applied to that.
  `codimOneWedge`/`CutData` locate the single merge, and `codim_eq_two_iff` says codimension two
  has exactly two species — one bead cut in three, or two distinct beads each cut in two.
- `Boundaries.lean` — a dimension list *is* a `Composition` of its total (`dimComp`), so `boundaries
  d` is mathlib's `Composition.boundaries` read in `ℕ` — that is where `card_boundaries` and
  `boundaries_injective` come from. `cutAt` cuts at a boundary the shape lacks, `cut_unique` says
  the boundary pins the cut, and `cutOfLengthSucc` / `exists_cuts_of_length_add_two` classify one
  and two deleted boundaries.  The **bead relation** lives here too, on the junction set alone:
  `beadAt d p` counts the junctions at or below `p`, so `beadAt_lt_iff` (a junction in `(p, q]`),
  `beadAt_succ_eq_iff` (a junction is where the bead changes at a step) and
  `boundaries_subset_of_beadAt` (the beads pin the junctions) carry no total and no `Fin`;
  `ChartHom`'s `index_lt_iff_beadAt` is the only bridge to `Composition.index`.
- `Coarser.lean` — the converse of `boundaries_subset_of_hom`: a coarsening is realised by merging
  one junction at a time. Hence `nonempty_hom_iff` — `a ⟶ b` exists exactly when
  `boundaries b ⊆ boundaries a`, i.e. exactly at a coarsening — and then
  (`exists_crossPerm_eq_one`) it holds the merge. Also unique factorisation through an intermediate
  shape (`exists_factor`, `factor_ext`) and the interpolation `exists_crossPerm_mid` it gives.

*The bead merges, and what inverting them means (`Concurrency/Merge/`).*
- `MergeClass.lean` — `merge`, the cuts whose middle map is the comparison `cubeMerge`, and
  `W K := (merge K).multiplicativeClosure`, the **bead merges**.  `W_le_iff` is the induction
  principle, `merge_cutRefine_iff` says the square's other cut, `cubeReorder`, is not a merge.  A
  cut is data on the wedge map alone, so `merge` is an inverse image from `Ch Zbp`.
- `MergeBraid.lean` — the staircase `cubeMerge` sends a cut's two beads to consecutive coordinate
  blocks in order, so a generator crosses nothing; crossings multiply, so `crossPerm_eq_one_of_W`.
- `MergeGenerate.lean` — the **converse**, `W_iff_crossPerm_eq_one`.  Crossings *add*
  (`permLen_crossPerm_comp`), so a crossing-free refinement splits into crossing-free pieces:
  cut at any junction the target does not separate and factor (`exists_factor`), and induction on
  the bead count exhausts it.  At codimension one the middle map is forced, a chain morphism being
  its crossing permutation (`merge_of_crossPerm_of_codim_one`), whence `merge_iff_of_codim_one`.
  `crossPerm` being blind to the target, `W_eq_inverseImage_toChZ`.
- `TotalMerge.lean` — `zObj`/`zHom` (an object of `Ch Zbp` *is* its dimension list), the two
  spliced comparisons `mergeHom l r p q` and `atomHom l r`, and the splice
  `𝟙 ∨ w ∨ 𝟙` read as a **double concatenation** (`splicePhi_eq_concat`, `spliceNil_eq_concat`), so
  `coordMap_inclL`/`_inclR` reduce its coordinate map to the middle staircase `pairMerge p q w`
  alone: `pos_coordMap_splicePhi` says a splice moves only the beads it merges, by whatever
  permutation of `[0, p+q)` the staircase performs.
- `AtomPair.lean` — the atom relations of `Machinery/Braid/PosGerm`, realised in `Ch Zbp`:
  `exists_atom_pair` factors every length-additive
  `β * adjT i` through `atomComp n i = 1ⁱ 2 1^{n-2-i}`. The first step is *geometric*: the atom
  `atomHom` — the other wedge-to-tensor comparison of a square, `cubeReorder 1 1`, spliced at the
  cut — exchanges exactly the two strands there (`crossPerm_atomHom`), which is `adjT i` and
  is why it is not a merge (`not_W_atomHom`); the second step sorts across the double bead.
  `boundaries_atomComp` says the `k`-th atom's shape drops exactly the junction `k+1`, so
  `exists_atomPair_of_codim_two` reads the two junctions a codimension-two refinement of the run
  drops as the two atom indices below it — the count `artin_of_codim_two` consumes.
- `Factorisation.lean` — the two-step factorisations of `f : a ⟶ b` **are** the shapes between the
  two ends' junctions (`factorisationEquiv`), `exists_factor` and `factor_ext` packaged so that
  counting factorisations is counting an interval of the junction lattice.
- `SegalCondition.lean` — **for `K` the wedge is the tensor** [RESULT].  `IsLocal K w` (restriction
  along `w` is a bijection on maps into `K`) is mathlib's left Bousfield `ObjectProperty.isLocal`
  at `{K}`, so `isLocal_congr` / `IsLocal.of_isIso` / `IsLocal.of_iso` are its `RespectsIso`,
  `isLocal_of_isIso` and `isoClosure_isLocal`, and `IsMultiplicative` in `w` is free.  `IsSegal K`
  is locality at `wedgeToTensor (□p) (□q)`.  Project-specific: closure under whiskering
  (`IsLocal.tensor_id`/`id_tensor`, from `wedge2Desc` + `wedge2_hom_ext`) and the base points, free
  in both directions (`isLocal_iff_bijective_repoint`).  A unit bead is an isomorphism
  (`wedgeToTensorPsh_unit_left`/`_right`), so the positive blocks are the whole condition:
  `isSegal_iff_isLocal_cubeMerge_pos`.  `wedgeCubeHomEquiv` reads the target on cells, giving
  `faceComparison` and the `∃!` form.  Nothing here mentions a chain: the file sits below
  `ElementsFibration.lean`, which is where the merges meet it.
- `WedgeSlice.lean` — **a slice of `Ch Zbp` is the chains of a wedge**: `overToWedgeChains d` is
  bijective on objects and fully faithful (`serialWedgeFullyFaithful`: the triangle over a terminal
  object is free), and `over_W_eq_inverseImage` carries `W/d` to `W`.
- `WedgeSplit.lean` — `chConcat_isEquivalence : Ch X × Ch Y ≌ Ch (X ∨ Y)` and
  `W_prod_eq_inverseImage_chConcat`: `crossPerm` is block-diagonal over a concatenation, and a
  block-diagonal permutation is trivial only when both blocks are.  Importing
  `Localization.Prod` is all that `Functor.IsLocalization.prod` needs — there is no wrapper.
- `WedgeLocalize.lean` — …localized: `locChConcatEquiv`, the hypothesis-free cons step
  `locChConsEquiv n rest` (`serialWedge_cons` is `rfl`, so the wedge splitting already *is* the
  recursion on a dimension list), and `locOverEquivWedge` reading it on the base's slice.
- `CubeCrossing.lean` — `cross c`, the crossing permutation of the unique refinement of the one-bead
  chain: an invariant of a chain of `□n` that `W` leaves alone and every other refinement strictly
  shortens (`crossLen_lt`).
- `CubeWeakOrder.lean` — `crossLen_eq_add` says a refinement drops the Coxeter length by exactly its
  own crossing length, which *is* the right weak (Bruhat) order.  `WeakOrder n` is `Perm (Fin n)`
  under that order as a **type synonym** — the order is not an instance on `Perm` itself — needing
  only subadditivity of `permLen` and that only the identity has length zero.

*Presentations of the chains and of their localization (`Concurrency/Presentation/`).*  The chapter
reads in the order of the through-line: the base, then the slices, then the colimit, then what it
looks like at named targets.  `CubeChains.lean`'s import comments say the same thing in one line
each.

*The base.*
- `BaseComponent.lean` — `strandComponentGarside N` / `strandComponentArtin N`: each strand
  component of `Ch Zbp[W⁻¹]` is **one object** carrying `PosBraid N`, in either naming.
- `BaseDecomposition.lean` — `strandDecomposition`: an object of the localization is a chain on the
  nose (`objEquiv`) so it has a strand count, `isEmpty_loc_hom` says no arrow changes it, and
  `ObjectProperty.sigmaEquiv` makes the base their disjoint union.
- `BasePresentation.lean` — **`BraidPresentation`**, the input: `P N` presenting
  `SingleObj (PosBraid N)` with `vertex : Unique (P N).V`, whence `p.base` presents the localized
  base.  `ofMonoids` builds one from monoid presentations; `germBP` and `artinBP` are the two
  values; `BySimples` says each generator names a *simple*, which the lift needs because the action
  on runs is length-additive.  `zLocComponent` runs the other way, restricting an arbitrary base
  presentation to one component.
- `Retraction.lean` — the loops at the run **are** `PosBraid N` (`runBraidEquiv`, `runArtinEquiv`),
  and `homEquivPosBraid` reads every hom-set of the localized base as one — multiplicatively
  (`_comp`), blind to isomorphisms (`_sandwich`), and computing a codimension-one step off its two
  legs (`homEquivPosBraid_of_merge`: undoing a merge performs nothing).
- `ChBraid.lean` — the same reading pulled up to `Ch(K)[W⁻¹]` along the projection to the base:
  `chBraid` is the braid an arrow performs, `faithful_chLocBase` / `eq_of_chBraid_eq` make it
  decisive, and `chBraid_equiv_map` reads it through **any** equivalence modelling the
  localization — which is what each route below applies to its own model.

*The slices, and the colimit over them.*
- `SliceRuns.lean` — the runs over a chain, and the **exchange**: `exists_runOver_mul_adjT` says
  every descent of the weak order is realised by an arrow, and `RunOver.eq_of_locIso` says two runs
  isomorphic in the localized slice are *equal* — the weak order is a grading the localization
  keeps, and an iso pins it from both sides.
- `SliceExchange.lean` — the assembly: the localized slice **is** the weak order wherever the runs
  over `d` realise every permutation; `exists_not_isRun_over` is the witness that it is never
  *skeletal*.
- `ChartFibre.lean` — a partial action per strand count is a presheaf on the localized base
  (`chartFibre`), glued by `strandDecomposition`.  The fibre family is a parameter, and everything a
  caller needs of the opaque decomposition lives here: `runChartFibre_hom_invariant` says the
  transport to the component fixes any invariant a defined step raises, so an instance never unfolds
  it.  `SliceFibre` and `CubeChartAction` are the two instances.
- `SliceFibre.lean` — `ChartFibre` at the runs over `d`: they are a **downward-closed** set, so
  `weakActionOn` acts on them partially; `sliceFibre d` is the presheaf that gives, and
  `definedSliceLoc` says its defined part *is* the localized slice, reversed.
- `SliceInherit.lean` — **the slice family is the base's cells, lifted**: `slicePolyFunctor p`,
  `slicePresentationOf p`, `slicePoly_hP`, and hence `presentsChainsSliceColimit`,
  `BraidPresentation.Br` / `.presentsBr`, `presentsChainsGarsideColimit` /
  `presentsChainsArtinColimit`.  There is no condition on the base: `hP` is the whole input.
- `SlicePresentation.lean` — `Ch(K)[W⁻¹]` is the localized elements of `wedgeHoms K`
  (`locEquivElements`), `locOverEquivBase` says a chain's slice is its *shape's* slice
  unconditionally in `K`, and `glueV`/`glueE`/`at_glueV`/`arrow_glueE` read the colimit's cells on a
  leg.  `presentsChainsColimit` is the theorem with the family still abstract.
- `GlueRun.lean` — every 0-cell of `Br p K` is a **run's**, read in the copy indexed by the run's own
  chain (`exists_glueRunV`); nothing here is Garside- or Artin-specific.

*What the presentation looks like at named targets.*
- `BrBase.lean` — `Br p Zbp` is `p`'s own polygraph, generator to generator: `brZMap_cells` (the
  spelling is a single letter) and `bijective_brZPt` (the 0-cells are the strand counts) are what
  say so, `brZMap` / `brZEquiv` being the packaging that any two presentations of one category
  already admit. Under `BySimples`; the 1-cells are not claimed to biject.
- `BrCube.lean` — `presentsBrCube` (the weak Bruhat order), `presentsBrAction` / `endBrAction` (the
  positive braid action, whose loops at *every* object are `PosPureBraid n`), and `germBr_gen` /
  `artinBr_gen`, which say what a generator does to a run.
- `BrFunctor.lean` — `brFunctor : BPSet ⥤ Polygraph`; `brElt` is strictly functorial, so both
  functor laws are the colimit's, and `brMap_glueRunV` says the functor does `Ch f` on the runs.
- `BrMap.lean` — a **map** of braid presentations spells a generator of `p` by a *word* of `q`
  performing the same braid (`BraidPresentation.Map.braid_word`), and above a chain that word lifts
  once and for all, the projection to the base being a covering and `bot` absorbing.
- `CubeChartAction.lean` / `CubeChartWeakOrder.lean` — the cube's atoms are an `IsArtinFamily`, so
  `PosBraid n` acts partially on the charts over the run, and `chartWeakEquiv` says those charts are
  the weak order — a second, independent route to the order.
- `CubePresentation.lean` — `Ch(□n)[W⁻¹]` presented by `Presents.ofThin`: 0-cells the runs,
  generators the atom steps, relations all of them, because it is a poset.
- `HAction.lean` — the Segal/descent route: `chLocEquivElements`, `hLocEquiv`, `hLocArtinEquiv`, and
  the presentations `hLocPresentation` / `hLocActionPresentation` they carry.  This is the **special
  case**, not the main road.
- `PartialAtom.lean` — the atoms acting partially on the runs of `K`: flip the square at a cut, if
  `K` has one.
- `GlueVsFibration.lean` / `GlueArtin.lean` — what each route's generators perform, and hence the
  two routes compared.  Each route is an equivalence onto its own model whose reading of the base
  lifts the projection, so one call to `chBraid_equiv_map` (`ChBraid.lean`) answers it; faithfulness
  then makes the answer decisive, and `bijective_genQuiver` says the two polygraphs share their
  generating data in **both** dimensions.  What is *not* true is an isomorphism of polygraphs — the
  2-cells genuinely differ.
  `chBraid_runGen` is what every generator dictionary is checked against: a 1-cell of `Br p K`
  whose source run is uncrossed performs that generator's own permutation, the merge leg
  performing nothing.
- `CutPresentation.lean` — the presentation that `exists_factor` / `factor_ext`
  (`Concurrency/Grading/Coarser.lean`) feed.
  `cutsOf f = boundaries a \ boundaries b`, and `boundaries` is injective on shapes,
  so `mid_eq_of_cuts_eq` pins a one-cut step by the boundary it removes.  Two such steps out of one
  shape close a diamond whose apex has the two targets' boundaries in common (`exists_diamond`),
  and `Cut.exists_front` brings a named first step to the front of a generating path — no order on
  the cuts anywhere.  The relation is just "two paths of length two with the same value".
- `LocPresentation.lean` — the geometry at a run.  Out of `1ᴺ` a codimension-one refinement is the
  merge or the atom at one cut (`eq_mergeOnes_or_atomOnes`, `Cut.exists_eq_atom`), so the non-merge
  generators there are the `N−1` coordinate flips; `runMerge` is the merge into a shape and
  `existsUnique_W_ones`/`eq_runMerge` say it is the only one.  `conj` reads a refinement as a loop
  at the run, and it sees only the crossing permutation (`conj_congr`); `atomLoop_comm` and
  `atomLoop_braid` are then the two Artin relations, read off the codimension-two cell two atoms
  share (`exists_pairCell`, `exists_leg`).  Generation is `exists_atomWord`: since `conj_eq_runLoop`
  sends every refinement's loop to `runLoop` of its crossing permutation, and `runLoop_mul_adjT`
  appends one atom across an ascent, induction on `permLen` spells the loop as a word of that
  length.
- `ElementsFibration.lean` — `toChZ : Ch K ⥤ Ch Zbp` presented as a category of elements:
  `wedgeHoms K = ⋁- ⟶ K` on `(Ch Zbp)ᵒᵖ` and `chEquivElements : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ`
  (the `ᵒᵖ` is mathlib's opfibration convention).  `W_eq_inverseImage_toElements` puts the
  merges on the base, so `Machinery/Localization/FibrationLocalize` gives
  `isLocalization_chDescent`: all of the `K`-dependence of the localization sits in `wedgeHoms K`. 
  Its hypothesis is `IsSegal`; the sharp form `InvertsMerges K` — the same condition with `K`'s
  base points fixed (`isSegal_iff_invertsMerges_repoint`) — lives here too, since a merge *is*
  `𝟙 ∨ cubeMerge ∨ 𝟙` up to isomorphism (`CutData`) and hence a `mergeHom` (`eq_splicePhi_of_sq`),
  so no bead computation for `splicePhi` is needed.  Only one direction is proved —
  `bijective_merge11_of_invertsMerges` — not the converse.  The refutations state it, because
  pinning the base points is stronger than `¬ IsSegal`.
- `LiftPresentation.lean` — a presentation of `Ch Zbp` **lifts to `Ch K`** through `chEquivElements`
  (generators the base generators acting on a chain), and survives inverting the merges under
  `IsSegal K`.  `wedgeHomsDescend_obj_Q` names the chain a generator sits at: `Construction.fac` is
  an equality, so the descended fibre over `Q(op a)` is literally `⋁a ⟶ K`.
  The **vertex monoids do not follow**: `End` at a chain is a stabilizer
  (`endEquivStabilizer`), and `PosBraidAction` shows a stabilizer need not be generated by the
  generators sitting at its object — there the only generator that is a loop is the identity, while
  the loops are `PosPureBraid n`.

*Runs and executions (`Concurrency/Executions/`).*
- `Runs.lean` — the **run presheaf** `Lines K : (Ch K)ᵒᵖ ⥤ Type`, `a ↦ Run a.dims`. A *run* is an
  all-edges cube chain: `Run K` is the full subcategory of `Ch K` cut out by `IsRun`, and it is
  discrete. Runs of a cube assemble into `runPresheaf : Boxᵒᵖ ⥤ Type`, so by
  `Precubical/Segal/PshExtMonoidal` a run of `⋁a` *is* a map `(⋁a).toPsh ⟶ runPresheaf`
  (`runPshEquiv`), and `runRestrict` along a wedge map is transpose–precompose–assemble.
  `runFunctor : BPSet ⥤ Cat` is lax monoidal, by restricting `chFunctor`'s structure to runs.
- `RunSegal.lean` — **the Segal decomposition of a linearization**: a run performs bead `i` at
  exactly the prefix-sum interval, in that bead's own order (`coordMap_fst_run_iff` as an *iff*,
  `coordFlip_run_concat`), so `runProj` gets a computational characterization and the sealed
  `runSplit`/`runSegalProd` stay sealed.
- `RunRestrict.lean` — **face restriction preserves the run order**: `EdgeChain.restrict` is a
  `List.filterMap`, which keeps survivors in order (`exists_strictMono_filterMap`), hence
  `flatten_restrict{,_lt_iff,_rank}`.
- `RunPerm.lean` — **a run of `□ⁿ` is a permutation of its axes**: `runPermEquiv : Run (□ⁿ) ≃
  Perm (Fin n)`, whose `toFun` is `flatten` at the run, on the nose and whose inverse `runOfPerm` is the
  singleton-bead `blockChain`. Restriction along a face is *sorting*: `runPermEquiv_restrict`
  reads `runPresheaf.map g.op` as the inverse of `Tuple.sort (flatten r.chain ∘ faceEmb g)` — the
  permutation form of `flatten_restrict_rank`.
- `RunWord.lean` — the **run word** `runWord x : Perm (Fin n)` (which direction fires at each step),
  `stepPerm_eq` [RESULT], and the **arrow rule** `runWord_group` / `runWord_within`: across beads
  the finer execution runs in its own bead order, inside a bead it inherits the coarser one's. The
  route factors `permOf` through `coordFlip` of the *total* run map, so it needs neither the Segal
  decomposition nor `coordMapEquiv`'s inverse.
- `ChStarProduct.lean` — `Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ`, an **isomorphism** of categories: `runBp`
  (in `Runs.lean`) is `runPresheaf` bi-pointed at its unique vertex, and a run is the second leg of
  `prodLift`.  Both round trips are `rfl` — the cone's universal property is definitional.
  Side-condition-free — the wedge never has to be split.
- `ExecData.lean` — `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` [RESULT], a chain plus a linearization
  refining it. `ofWord` builds one from `reflectHom`, so it computes; `ext_runWord` (thinness of
  `Ch (□ⁿ)`) is what makes an enumeration of words complete.
- `Elements.lean` — thinness for `Ch⋆ K = (Lines K).Elements`: `Functor.elements_isThin` and the
  thinness of `Ch (□ⁿ)`.

*`H`, the complexification (`Concurrency/Complexification/`).*
- `SymRun.lean` — **`H Z ≅ runPresheaf`** (`HZIsoRun`): a cell of the symmetric round trip of the
  terminal precubical set at `▫n` is an order on its axes, hence a run of `□ⁿ` (`symRunEquiv`), and
  both sides restrict by `Tuple.sort`.
- `SymOverRun.lean` — the **asymmetry of `H`**: `HOverRun`/`HbpOverRun` send `H K` to `runBp`
  naturally (`H` of the terminal map, then `HZIsoRun`), while `H(□²) ⟶ □²` and hence
  `H(□²) ⟶ □² × runBp` are empty. `□ⁿ × runBp` lies over both factors, `H(□ⁿ)` over `runBp` only,
  and the missing `prodFst` is the room `H` has for a reorientation.
- `ChStarSym.lean` — **`Ch (Hbp K) ≌ Ch (K.prod runBp) ≌ (Ch⋆ K)ᵒᵖ`** [RESULT], for every `K`, with
  no side condition. There is no map `Hbp K ⟶ K`, so this is not a pushforward: a symmetry fixes a
  cube's extremal vertices (`Hbp_vertex₀/₁`), so bead-wise symmetries glue (`symOf`), every
  decorated chain factors uniquely as one followed by an ordinary chain (`symOf_chainOf`), and a
  morphism is carried across by the *twist* `φ ↦ chainOf (φ ≫ symOf ρ)`, whose functoriality is
  associativity plus that uniqueness. The run and the order are inverse to each other
  (`symCell`); `SHom.sortPerm_sortFace_inv` is what makes that consistent, and it is the only
  place blocks are looked at.  Both legs restrict bead by bead through *any* factorization of a
  source bead through a target bead (`bead_of_factor`, `bead_comp_of_factor`), of which
  `blockIdx`/`blockFace` is the canonical one; that is what
  `runPermEquiv_bead_comp`/`runPermEquiv_bead_twistRun` are stated at.
- `SymReorient.lean` — **the symmetry the equivalence above cannot see, and what it is**:
  `reorientBp : Sₙ →* Aut (Hbp □ⁿ)` is faithful, and across
  `hbpBraidSalEquiv : Ch (Hbp □ⁿ) ≌ (Sal (braidCOM n))ᵒᵖ` it *is* `salReorientFunctor`
  (`reorientCh_comp_hbpBraidSalEquiv`) [RESULT]. The engine is `beadDir`, the direction bead `i`
  performs at step `j`: `σ` relabels every step, which moves the Salvetti face (`chFace` of the
  chain) and the tope (`chFace` of `runLine`, the chain the run performs) together —
  `coordFlip_runLine` is `coordFlip_run_concat` with the local run order cancelled against the
  decoration. Whereas `□ⁿ` is rigid (`cube_endo_eq_id`, `Subsingleton (Aut □ⁿ)`), so an
  endomorphism of `□ⁿ × runBp` over the base leaves underlying chains alone and induces no
  reorientation (`not_reorientCh_of_over_base`).
- `RunClassifier.lean` — **the run object, and why `Hbp` is not a product** [RESULT].
  `HbpZIsoRun : Hbp Zbp ≅ runBp` is the runs classifier; over a one-vertex target a wedge map *is*
  its beads (`ofCells`/`oneBeadEquivCell`), so `Hom(⋁[2], runBp)` has two elements and
  `Hom(⋁[1,1], runBp)` one — `not_invertsMerges_runBp`.  The undecorated `□²` fails the same
  condition the other way round — one 2-cell, two runs to hit (`not_invertsMerges_cube_two`) —
  which is why `H` is in the picture at all.  Hence any *natural* splitting
  `Hom(⋁d, Hbp K) ≃ Hom(⋁d, K) × Hom(⋁d, runBp)` would refute `InvertsMerges (Hbp K)`
  (`not_invertsMerges_of_splitting`), and `desym` is not one: `not_desym_natural`, from the
  explicit merge `⋁[2,1] ⟶ ⋁[3]` and the cyclic run, where the twisted restriction sorts the
  *inverse* order and inverts (`runPermEquiv_bead_twistRun`) while the plain one sorts the order
  (`runPermEquiv_bead_comp`) — and sorting does not commute with inverting.  The tower
  `Ch (Hbp K) ⥤ Ch (Hbp Zbp) ⥤ Ch Zbp` (`forgetLabels`/`forgetRun`) is what survives.
  `onesHomEquivRunClassifier` — the maps out of the all-edges chain are the runs of the target,
  so the simples are the cells of `Hbp Zbp` (`simplesEquivCells`), with no `Perm` in the
  description; the two sides have opposite variance, so it is a bijection of fibres only.
  Then the **collapse and its failure** [RESULT]: an edge of `Hbp Zbp` carries no order, so
  `subsingleton_homHbpZbp_of_ones` makes `Hom(⋁𝟙ⁿ, Hbp Zbp)` a point; the base merge out of the
  all-edges chain therefore lifts with nothing to check (`exists_W_from_onesH` — the
  compatibility condition lives in that one-element hom-set, so the twist above is never
  consulted), and `run_HbpZbp_eq` says that chain is the only one in its degree.  For the cube the
  contrast is exact: `runHbpEquiv : Run (Hbp K) ≃ Run K` (the order on an edge is no data), so
  `Run (Hbp □ⁿ) ≃ Perm (Fin n)`, and `isRun_of_hom_to_run` plus discreteness of `Run` give
  `not_exists_hom_to_all_cube` — for `n ≥ 2` nothing maps to every all-edges chain.
- `HSegal.lean` — **`H` makes the wedge the tensor** [RESULT].  An `SBox` map is a
  `coord : Fin n → Bool ⊕ Fin m`, so composability of `f : ▪p ⟶ ▪n` with `g : ▪q ⟶ ▪n` reads off
  coordinatewise (disjoint images; `g ≡ 1` on `f`'s image, `f ≡ 0` on `g`'s, signs agreeing off
  both) and `SHom.merge` is the unique filler: `▪(p+q)` is the wedge `▪p ∨ ▪q`.  Through
  `symFreeCube`/`HCube` this is `isSegal_H_cube`.  The contrast is
  the same map failing the other way at `H Z` (`not_injective_faceComparison_H_Z`).
- `HPosAction.lean` — the action written down.  A decorated chain of `□ⁿ` has `dimSum = n`
  (`hbpCubeStrands`).  What the fibre *is*: `cellDir` reads an `H`-cell as an
  `SBox` map and restriction along a face is precomposition there (`cellDir_Hbp_map`), so
  `eventDirEquiv` — each bead's order followed by `coordFlip` — is a bijection between the events
  of a decorated chain and the axes, natural in the shape (`eventDirEquiv_comp`).  Inverting it
  against the lexicographic `strand` gives `fibrePerm`, the step at which each axis is performed,
  and `fibrePerm_comp` says a refinement shifts it by its crossing permutation.  On the run of
  edges `fibrePerm` *is* `runHbpCubeEquivPerm`, so the merge out of the run (invertible on the
  fibre, crossing nothing) makes it bijective everywhere (`bijective_fibrePerm`, `fibreEquiv`).
  `chToAction` is that data as a functor to `PosBraidAction n`, and `chToAction_obj_surjective`
  says the runs exhaust the orderings.
- `HPresentation.lean` — `wallCrossLoc`, the wall span read in the localization with its far leg
  inverted: a codimension-one chain lies *below* both chambers it separates.

*The Salvetti comparison (`Concurrency/Salvetti/`).*
- `ChainBraidFace.lean` — the **base comparison** `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)` and
  `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face`. `beadOf b q` is the bead flipping coordinate `q`;
  `ofBlockMap` rebuilds a chain from its block map; `reflectHom` is the **computable** converse
  (`chFace b ⊑ chFace a` reconstructs `a ⟶ b`).
- `EventPerm.lean` — the event relabelling `eventEquiv f = coordMapEquiv (wedgeMap f)`, and
  `eventEquiv_mk` (its `blockIdx` / `blockFace` form) — the computational handle on everything
  downstream.
- `EventBraid.lean` — the **run order** `runOrd`, the crossing permutation `permOf`, and
  `permOf_noDoubleCross` [RESULT]. Events are ordered by the run linearizing the execution, *not*
  by the run-free `pos` — ordering by `pos` makes `permOf` a function of the chain morphism alone,
  which collapses the label. The two leaves are `runOrd_within_flatten` (from `RunSegal`) and
  `flatten_restrict_lt_iff` (from `RunRestrict`). Then `braidFunctor` and
  `ConcPos K = proj K ⋙ braidFunctor`.
- `SalExec.lean` — the two halves `salCompare` is fed at `□ⁿ`, giving
  `Ch⋆ (□ⁿ) ≌ Sal (braidCOM n)` [RESULT]. `wordTopeEquiv` reads topes as run words (a tope's chain has injective `beadOf`, hence one
  direction per bead); `linesTopeIso` bundles that fibrewise, and its naturality square is
  `wordTope_runWord` — the wall crossing `T' = X' ⊙ T`, whose two branches are the arrow rule's
  two clauses.
- `SalCompare.lean` — `salCompare : ((Ch K)ᵒᵖ ≌ Face L) → (Lines K ≅ e.functor ⋙ salFunctor L) →
  (Ch⋆ K ≌ Sal L)` [RESULT]: both sides are categories of elements, so the comparison is one of
  bases plus one of presheaves; `hbpSalEquiv` chains it with `chSymChStarEquiv` for
  `Ch (Hbp K) ≌ (Sal L)ᵒᵖ` — "`H` is the complexification".
- `SalBraid.lean` — `topePerm_eq`: a cell's permutation is its run word inverted, because `topeRank`
  counts predecessors and a run word's predecessor count at `p` is the step at which `p` fires
  (`topeRank_wordTope`).
- `SalvettiConstruction.lean` — the **computable** reading of a tope as a linear order
  (`topeRank`, `topePerm`) and the crossing cocycle `topeCross`.
- `WallCrossing.lean` — the presentation said in **arrangement** language. A chamber is a run of the
  decorated cube; its `n-1` walls are its adjacent rank pairs, each carrying two codimension-one
  cells — `wallStay` (crossing permutation `1`: a merge) and `wallCross` (crossing permutation
  `adjT k`: an atom). `card_wallsThrough` says codimension *counts* walls, so a codimension-two cell
  lies on exactly two: consecutive (braid) or separated (commutation). An atom is **not** an arrow
  between chambers — a wall cell lies below both chambers it separates, so `σₖ` appears only after
  inverting one leg of the span.
- `CrossCompare.lean` — **the two crossing permutations of a decorated chain morphism agree**:
  `topePerm_hbpBraidSalEquiv` says the Salvetti tope records `fibrePerm`, the step at which each
  axis is performed, so `crossPerm_eq_topeCross` — both `ChainCat.crossPerm` (the flattening
  order) and `topeCross` (the arrangement's) are that function's coboundary.  Hence
  `W_wallLegFlip`: the leg of a wall span that crosses no wall is a bead merge.

### `Testing/` — the fast execution model, and computing `π₁`

Strictly downstream: nothing outside `Testing/` imports it, and it is the only part of the tree
`lake build CubeChains` does not build.

An execution of `□ⁿ` is a **linear order on the `n` directions plus a composition of `n`** — the run
linearizes each bead, and beads are consecutive blocks of that word. So `Ch⋆(□ⁿ)` has `n!·2^{n−1}`
objects (192 for `n = 4`), enumerable in output-linear time.

*Enumeration — the fast model, and the by-definition oracle it is checked against
(`Testing/Enumerate/`).*
- `Cells.lean` — cells of `□ⁿ` as sign vectors; `SubCube n` (a face-closed `Bool` predicate),
  `full`/`boundary`/`skeleton`, `beadCell`. `(cube n).init` is `some false`, so `some false` = a
  direction not yet performed.
- `Boundary.lean` — `∂□ⁿ ↪ □ⁿ` as a genuine subfunctor (cells of dimension `< n`), so `Ch⋆(∂□ⁿ)`
  is `ChStar` of an actual `BPSet`.
- `Enumerate.lean` — the **slow oracle**: `Ch (□n)` enumerated by definition, bottom-up from the
  decidable finite `Cell N k` through cube Yoneda, with a completeness proof.
- `Morphisms.lean` — the same for the *morphisms* of `Ch⋆(□n)`: `Ch (□n)` is thin, and
  `equivWedgeCat` presents a hom as the finite datum `ChainRefine`, so `Fintype (a ⟶ b)`.
- `FastExec.lean` — `FExec n` (nonempty blocks whose concatenation is a permutation), `Refines`
  (decidable), `fperm`, the DFS `execs` with `mem_execs_iff` (sound **and** complete), `buildPoset`.
- `FastEquiv.lean` — the bridge `fexecChStarEquiv : FExec n ≃ Ch⋆ (□ⁿ)` between the enumerable
  block-list model and `Concurrency/Executions/ExecData`, plus `fperm_eq_stepPerm`.

*The presentation and the braid words it carries (`Testing/Pi1/`).*  `Enumerate`/`Morphisms` are the
**slow oracle** — the by-definition route through the `Glue` quotients, kept to check the fast model
against.
- `GlueCount.lean` — **the size of `Br p (Hbp □ⁿ)`, measured** in an independent model (a chain is a
  permutation word cut into blocks, `W` is `isMono`, `crossPerm` is `flatWedge`).  The colimit is
  computed over the *maximal* chains, since every chain maps into one.  0-cells `n!`; Artin 1-cells
  `n!(n−1)` and 2-cells `n!(n−1)(n−2)/2` — a square or a hexagon per run and per unordered pair of
  cuts; germ cells different from Artin at both dimensions, which is what says the cells are
  inherited.  A thin family would give `(4, 54, 9888)` at every `p` and does not.
- `Parabolic.lean` — `outLabels_eq_parabolic`, `dims_eq_of_outLabels_eq`, `outLabels_eq_top_iff`.
- `Merges.lean` — is the monotone class generated by the bead merges?  The wedge map recorded as a
  per-target-bead list of source faces, given a composition, with the merges generated and compared
  against `W`.
- `WedgeBraid.lean` — `crossPerm` evaluated on hom-sets: at `⋁[1,1] ⟶ ⋁[2]` the two staircases of
  the square give the two elements of `S₂`, and at `n = 3` the homs out of a run exhaust `S₃`.

*The complexification, evaluated (`Testing/H/`).*
- `HTwo.lean` — `Ch (H² K)` and its localization at the bead merges.  In the sheared coordinates
  `(σ ∘ τ, τ)` the two factors move independently, i.e. `H² K ≅ H K × H 1`; the graded hom-sets are
  the sharp instrument for what `π₁` cannot see.
- `HBar.lean` — the natural maps between powers of `H`.  `Hmul_unique`: the monad multiplication is
  the *only* `H² ⟶ H`, while degree `2` carries two and `HmulOuter_ne_HmulInner` separates them.
- `HTwoDeep.lean` — the degree-`5`/`6` end of `HTwo`, reached because relabelling acts transitively
  on components, so one component determines all `24`.  Minutes per `#eval`.
- `HWedge.lean` — is the crossing permutation a function of the `Ch (Hbp □n)` wedge map?  Twisted by
  the coarse object's run it is; untwisted the datum is the plain `Ch (□n)` refinement and forgets
  the run.

## Where do I find…?

- **the box / precubical-set definition** → `Machinery/Cube/Box.lean`
- **cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n`** → `Precubical/Basic/Representable.lean` (`cubeRepr`)
- **`vertex₀/₁`, `BPSet.Hom`, `cubeMap`/`faceMap`** → `Precubical/Basic/Bipointed.lean`
- **the wedge / serial wedge / `wedge2` pushout** → `Precubical/Wedge/Wedge.lean` (+
  `Precubical/Chains/WedgeMap.lean`)
- **`NonSelfLinked` / `AdmitsAltitude` / altitude lemmas** → `Precubical/Basic/Altitude.lean`
- **the geometric tensor `⊗ᵍ`, computably** → `Precubical/Wedge/GeoTensor/` (`BP.lean` for the
  `BPSet` version and `cubeTensorIsoBP`); the Day-convolution version is `Machinery/DayTensor.lean`
- **the wedge as the default monoidal product on `BPSet`** → `Precubical/Wedge/WedgeMonoidal.lean`
- **`⋁` as a strong monoidal functor (`serialWedgeAppend` as tensorator)** →
  `Precubical/Segal/Segal.lean` (`serialWedgeFunctor : DimList ⥤ BPSet`)
- **the concrete↔topos model bridge (`realize`/`Nerve`)** → `Precubical/Basic/Nerve.lean`
- **the chain category `Ch` / the lift `liftToCh`** → `Precubical/Chains/Category.lean`
- **chains-are-wedge-maps** → `Precubical/Chains/Correspondence.lean` (`equivWedgeCat`)
- **concatenation `chConcat` and its inverse** → `Precubical/Segal/Segal.lean` /
  `Precubical/Segal/Split.lean`
- **`chFunctor` lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`** → `Precubical/Segal/WedgeLaxMonoidal.lean`
- **generic monoidal helpers (transport, associativity juggling)** →
  `Machinery/MonoidalTransport.lean`
- **the braid arrangement `braidCOM n` / COMs** → `Machinery/Arrangement/Braid.lean`,
  `Machinery/Arrangement/COM.lean`
- **runs, the run presheaf `Lines`, `runPresheaf`, `runRestrict`** →
  `Concurrency/Executions/Runs.lean`; the wedge-map split it rests on is `splitWedgeMorphism` in
  `Precubical/Segal/Split.lean`
- **`runBp`, `K.prod runBp`, and `Ch⋆` as a chain category** →
  `Concurrency/Executions/ChStarProduct.lean` (`chStarProdIso`/`chStarProdEquiv`); products of
  `BPSet` → `Precubical/Basic/BipointedProd.lean`
- **a chain of `□ⁿ` as an ordered set partition (`beadOf`, `ofBlockMap`)** →
  `Concurrency/Salvetti/ChainBraidFace.lean` (`chFaceEquiv`, `chFaceCatEquiv`, `reflectHom`)
- **the run order `runOrd`, `permOf`, no-double-crossing** →
  `Concurrency/Salvetti/EventBraid.lean`; its two inputs are `Concurrency/Executions/RunSegal.lean`
  (Segal) and `Concurrency/Executions/RunRestrict.lean` (face restriction)
- **`ConcPos` itself** → `Concurrency/Salvetti/EventBraid.lean`
- **the run-free crossing permutation of `Ch K` (wedge maps only)** →
  `Concurrency/Grading/WedgeBraid.lean` (`crossPerm`, `permLen_crossPerm_comp`,
  `crossPerm_chConcat`), read off the chart in `Concurrency/Grading/ChartHom.lean`
  (`flatten`, `crossPerm_flatten`)
- **the two staircases `□m ∨ □n ⟶ □(m+n)` and their coordinate blocks** →
  `Precubical/Wedge/WedgeTensor.lean` (`cubeMerge`/`cubeReorder`, `faceEmb_cubeMerge_*`,
  `faceEmb_cubeReorder_*`)
- **which permutations a hom-set of `Ch Zbp` realises** → `Concurrency/Grading/ChartHom.lean`
  (`exists_chart_flatten`, `exists_crossPerm_of_blocks`), and
  `Concurrency/Merge/AtomPair.lean` (`exists_crossPerm_ones`, `exists_crossPerm_single`)
- **when a refinement is a bead merge** → `Concurrency/Merge/MergeClass.lean` (`merge`, `W`,
  `W_le_iff`), `Concurrency/Merge/MergeBraid.lean` (`crossPerm_eq_one_of_W`),
  `Concurrency/Merge/MergeGenerate.lean` (`W_iff_crossPerm_eq_one`, `merge_iff`, `Coarser`)
- **when `K` inverts the bead merges, as a condition on cells** →
  `Concurrency/Merge/SegalCondition.lean` (`IsSegal`, `faceComparison`,
  `isSegal_iff_existsUnique`), read on chains in `Concurrency/Presentation/ElementsFibration.lean`
  (`InvertsMerges`, `isSegal_iff_invertsMerges_repoint`); for `Hbp □ⁿ` →
  `Concurrency/Complexification/HSegal.lean` (`sbox_existsUnique`, `isSegal_H_cube`)
- **when a hom-set of `Ch Zbp` is nonempty, and how a refinement factors** →
  `Concurrency/Grading/Boundaries.lean` (`boundaries`), `Concurrency/Grading/Coarser.lean`
  (`nonempty_hom_iff`, `exists_factor`, `factor_ext`, `exists_crossPerm_mid`)
- **the Salvetti comparison** → `Concurrency/Salvetti/SalCompare.lean` (`salCompare`), fed at `□ⁿ`
  from `SalExec.lean` (`chFaceCatEquiv`, `linesTopeIso`)
- **an execution as a word + composition, and enumerating them** → `Testing/Enumerate/FastExec.lean`
  (`FExec`, `execs`, `mem_execs_iff`), identified with `Ch⋆` in `Testing/Enumerate/FastEquiv.lean`
- **restricting a chain along a face / `EdgeChain`** → `Precubical/Chains/ChainRestrictions.lean`
- **hom functors and opposites, monoidally** → `Machinery/HomMonoidal.lean`
- **the braid group itself (Garside germ), `permHom`, `PureBraid`** → `Machinery/Braid/Germ.lean`
- **the Artin presentation** → `Machinery/Braid/Artin.lean`; **Matsumoto's theorem** →
  `Machinery/Braid/Matsumoto.lean`
- **the braid groupoid `FullBraid` (the target of `ConcPos`)** → `Machinery/Graded.lean`
- **what a presentation *is* (`Polygraph`, `Presents`, `ofDesc`, `ofThin`)** →
  `Machinery/Presentation/Basic.lean`; comparing two of them → `.../Comparison.lean`; crossing a
  variance → `.../Opposite.lean`
- **the input `BraidPresentation`, `germBP` / `artinBP`** →
  `Concurrency/Presentation/BasePresentation.lean`
- **`Br p K` and `presentsBr K` — the presentation of `Ch(K)[W⁻¹]`** →
  `Concurrency/Presentation/SliceInherit.lean`; read at named targets in `.../BrBase.lean`,
  `.../BrCube.lean`, `.../BrFunctor.lean`, `.../BrMap.lean`
- **the gluing theorem behind it, for an arbitrary `∫X`** → `Machinery/Presentation/Glue.lean`
  (`presentsSliceColimit`, `sliceRet`), with both sides a colimit in `.../SliceColimit.lean`
- **the Segal/descent route (the special case)** → `Concurrency/Presentation/HAction.lean`
  (`chLocEquivElements`, `hLocPresentation`, `hLocActionPresentation`), compared with the colimit
  route in `.../GlueVsFibration.lean` and `.../GlueArtin.lean`

## Build & conventions

- `lake build CubeChains` builds the results and the retained infrastructure — everything except
  `Testing/`. To gate the whole tree including `Testing/`, sweep every module:
  `lake build $(find CubeChains -name '*.lean' | sed 's#/#.#g; s#\.lean$##')`.
  **No file sets `maxHeartbeats`**; if you find yourself needing one, you have hit a spelling
  mismatch (see below), not a hard proof.
- The tree is **`sorry`-free and declares no `axiom`**: every result reduces to
  `[propext, Classical.choice, Quot.sound]`.  An unproved input enters as a *hypothesis* on the
  declaration that needs it — the one such input is Garside's theorem, injectivity of
  `posToBraid n`, carried by `posPureToPure_injective`.
- **`End`/`Aut`/`SingleObj` multiply flipped** (`u * v = v ≫ u`). `End` is the one that pairs with
  `SingleObj`, which is why braid words compose with the *later* arrow first: a path word is
  `w_last ++ … ++ w_first`. Getting it backwards leaves every group count unchanged and shows up
  only as loops failing to be pure braids.
- **A presentation of `C` is not a presentation of `Cᵒᵖ`.** A word composes source-first, so the
  `ᵒᵖ`s in the presentation chain are the composition order, not a choice; `Machinery/Presentation/Opposite.lean`
  is where a comparison crosses a variance.
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
  `RefineObj ⟷ Ch` bridge imports both while the statement *looks* unconditional.
  `Precubical/Segal/Segal.lean`'s `chConcat` / `wedgeInclL/R` are the unconditional replacements.
- Prefer reusing a mathlib construction (Over/comma cats, `FullSubcategory`, Kan extensions,
  `Quiver.IsThin`, `Localization`, adhesive/pushout API) over hand-rolling.

## Other docs

- `SlicePresentation.md` — the executed brief for the slice-colimit route: the repo dictionary for
  the gluing machinery, and the landmines it hit.
- `DESIGN.md` — the conventions/decisions log (precubical identities, universe policy, the
  topos+concrete architecture), with PZ/Z paper references.
- Per-area: `Machinery/Arrangement/README.md`, `Concurrency/README.md` + `Concurrency/BRAID.md`
  (why braids).
- `/orient` skill — fast session bootstrap (build, mathlib-reuse table, gotchas).
- Papers: PZ = arXiv:2103.05336, Z = arXiv:1901.05206.
