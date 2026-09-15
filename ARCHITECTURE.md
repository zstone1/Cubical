# ARCHITECTURE.md — the map

A Lean 4 + mathlib (`v4.30.0`) formalization of the **concurrency braid groupoid** of a precubical
set: the executions of a cube chain, the braid monoid that grades their refinements, and a
presentation of `Ch(K)[W⁻¹]` by the runs and the objects of degree one and two. **Read this first to
find the right file**, then open that one file (+ its module docstring) — you should never need the
whole tree in context.

This file is a **description of the tree, not a specification of it.** Where it records how a result
is currently reached, that is reportage; `CLAUDE.md` holds what is actually required, and a
derivation that deletes a link here beats one that adds a lemma to it.

Two models of precubical sets coexist: the **concrete/computable** one
(`Precubical/Basic/`, graded cells + face maps) and the **topos** one
(`PrecubicalSet := Boxᵒᵖ ⥤ Type`), bridged by the cube Yoneda lemma
(`Precubical/Basic/Representable.lean`). The topos model is the default everywhere downstream.

**Why braids.** `(GeoBP, ⊗ᵍ)` is monoidal but has **no swap** — `Box` is rigid (`Aut ▫k = {id}`,
the symmetry-free convention), so no block transposition `▫(m+n) ⟶ ▫(n+m)` exists. The braiding
is *created* by the passage to executions, not inherited: two interleavings of independent events
are isomorphic, not equal, and the iso has a winding number. Independent actions do not commute —
they braid.

## Three layers, and what is cited

The construction separates cleanly, and the separation is a fact about the code rather than an
aspiration: **no file in `Machinery/Presentation/` mentions `Ch`, `Zbp`, `BPSet` or anything
precubical.**

| layer | mentions chains? | where | related literature |
|---|---|---|---|
| presentations: colimits, the tensor, rigidity | **no** | `Machinery/Presentation/` | polygraphs and rewriting (Ara–Burroni–Guiraud–Malbos–Mimram–Ruiz, arXiv:2312.00429); free objects are cofibrant in the folk model structure (Lafont–Métayer–Worytkiewicz, *Adv. Math.* 2010) |
| braid theory: germs, the weak order, Matsumoto | **no** | `Machinery/Braid/`, `Machinery/Graded.lean` | Garside germs and the presentation they carry (Dehornoy–Digne–Michel, *Garside families and Garside germs*, J. Algebra 2013); coherent presentations of Artin monoids and Deligne's theorem on their actions on categories (Gaussent–Guiraud–Malbos, *Compositio Math.* 2015) |
| the geometry | **all of it** | `Concurrency/`, `Precubical/` | this development |

The geometric input is small and identifiable. Three facts carry it:

1. `Ch K` is the category of elements of `wedgeHoms K` over `Ch Zbp`, and `W K` is `W Zbp` pulled
   back (`chEquivElements`, `merge_iff`) — so `K` enters *only* through the index category;
2. the loops at the run of `N` events are `PosBraid N` (`runBraidEquiv`), the crossing permutations
   being a length-additive cocycle — which is what lets a *monoid* presentation of each braid
   monoid be read on the base;
3. the runs over a chain are the **block sums** of its beads' own runs (`runSet_append`,
   `runSet_single`), and an arrow permutes each block of its target and no more
   (`index_crossPerm`), so at a descent the shortened crossing permutation is realised too
   (`exists_run_mul_adjT`) — the exchange property, and the only place a chain meets the germ.

Everything from (3) onwards is a statement about the right weak order on permutations, readable by a
Garside theorist with no knowledge of cube chains.

## The goal statements

**A presentation of the braid monoid goes in; a presentation of `Ch(K)[W⁻¹]` comes out, for every
`K`, with no hypothesis on `K`.** Everything in *The supporting results* below is in service of that
— infrastructure, comparisons, and the refutations that pin the definitions down.

`K` ranges over **all** of `BPSet`, and that is the whole quantifier: `Paper.paperPresents` takes
`K` and nothing else — no instance argument, no decidability, no smallness side-condition. Two narrowings
are built into the *types* rather than into the theorems, and are stated here rather than left to be
discovered: `PrecubicalSet.cells` is fixed at `Type 0` (see `DESIGN.md`), and the polygraphs are
`Polygraph.{0,0,0}`. The universe **diagonal** is intrinsic rather than an artefact of any one
construction: polygraphs are the presheaves on `PolyShape`
(`Foundations/Polygraph/Presheaf.lean`), and a `Type u`-valued presheaf sees 0-cells, 1-cells and
2-cells in one universe, so `Polygraph.{u,u,u}` is where the (co)limits live — for every `u`. The
remaining `0` is `PrecubicalSet.cells`'s alone.

Every row of the **goal-statement tables** below is stated as an `example` in
`CubeChains.lean`, so `lake build CubeChains` checks
those statements as well as their proofs. *The
supporting results* table names declarations rather than restating them; many are reached only as
inputs to an anchored claim. The steps still open are **not** restated here; the board
(`bd ready`) is the status.

### The input

**`BraidData`** (`Concurrency/Presentation/BasePresentation.lean`) is generators and relations at
each strand count, and a **`BraidPresentation`** extends it by the fact that they present each
`SingleObj (PosBraid N)` as a *one-object* category:

```
Gen, Rel : ℕ → Type                                                   -- BraidData
src, tgt : ∀ N, Rel N → Quiver.Path (loopPt (Gen N)) (loopPt (Gen N))
part     : ∀ N, Presents (P N) ((SingleObj (PosBraid N))ᵒᵖ)             -- BraidPresentation
```

The single 0-cell is built into the types rather than hypothesised: `P N` is `loopPoly`, so
`(P N).V` is `Unit` and `p.v` replaces a `Unique` instance. `p.poly` is the coproduct over
the strand counts and `p.pt` names its 0-cell at `N` bijectively (`pt_injective`, `exists_pt`),
which is what makes `braids_at'` — the strand-`N` 0-cell names the strand count — an `rfl`, so
nothing a generator names carries a transport. `ofMonoids rels e` builds one from a monoid presentation of
each braid monoid; `germBP` and `artinBraids` are its two values, `artinBP` is Artin's data alone
(`artinBraids.toBraidData = artinBP` by `rfl`), and `BySimples` says each generator names a
*simple*, which the lift needs because the action on runs is length-additive.

| # | Claim | Declaration | Lives in |
|---|---|---|---|
| 1 | the run of `N` events is **one object** of the localized base, carrying `PosBraid N` | `runBase N : (SingleObj (PosBraid N))ᵒᵖ ⥤ ((W Zbp).op).Localization`, full and faithful | `Concurrency/Presentation/BaseComponent.lean` |
| 2 | a `BraidPresentation` presents `FullPosBraidᵒᵖ`, and hence — *through the paper polygraph* — the localized base | `p.braids : Presents p.poly FullPosBraidᵒᵖ`; `fullBaseEquiv` from `paperPresents Zbp` + `paperArtinIso` + `artinBraids.braids` | `.../BasePresentation.lean`, `.../PaperArtin.lean` |
| 3 | the loops at the run of `N` events **are** the positive braid monoid, in either naming | `runBraidEquiv N : PosBraid N ≃* RunLoops N`, `runArtinEquiv N` | `Concurrency/Presentation/Retraction.lean` |

### …and where that input comes from

A `BraidPresentation` need not be postulated: `fullBaseEquiv` reads one off `paperPresents Zbp`
through `paperArtinIso`. The paper's polygraph is itself reached in **three moves**, all about the
runs over a chain:

| move | machinery | at the runs |
|---|---|---|
| 1. the runs over a chain are a lower set of the right weak order, and an ascent is a degree-one object; over a degree-two object they are a polygon, whose two maximal climbs are the 2-cell's words | `WeakOrder.Lower`, `RankTwo` | `shapeLower`, `ascGen`, `riseClimb`, `Paper.poly` |
| 2. the pair chain placed under a polygon's foot carries its object's 2-cell onto every chain, so the runs over every chain satisfy Artin's relation | `Web.eval_mapPath`, `exists_pairLeg` | `chWeb`, `chPush`, `isArtin_chWeb` |
| 3. a refinement reads as Matsumoto's arrow over its target, inversely to the cells' interpretation | `Web.arrow`, `Localization.Construction` | `thetaAt`, `Theta` against `paperE` |

Over `Zbp` a run is its strand count, the `N−1` 1-cells there are `artinBP.S N` on the nose, and a
2-cell's two climbs are its pair's alternating words: `Paper.genArtinEquiv` and
`Paper.relArtinEquiv`, assembled into `Paper.paperArtinIso`.

**Matsumoto supplies faithfulness and nothing else.** The generators are the geometry's (an ascent
between two runs is an atom, `ascLeg`) and so are the relations (a degree-two object's polygon).
Category-valued Matsumoto (`Web.arrow`, `Machinery/Braid/MatsumotoCat.lean`) enters through
`isArtin_chWeb` alone, and a refinement being a map of webs (`Web.arrow_map`) is both the Artin
check and the functoriality of `Theta`.

### The output

| # | Claim | Declaration | Lives in |
|---|---|---|---|
| **0** | **`Ch(K)[W⁻¹]` is presented by the runs and the objects of degree one and two, for every `K` and with no hypothesis on `K`** — the headline, and the statement every other result here is measured against | `Paper.paperPresents K : Presents (Paper.poly K) (((W K).op).Localization)` | `Concurrency/Presentation/DirectPresents.lean` |
| **0′** | …and that polygraph is a functor of `K`, the presentation natural up to the isomorphism a localization functor is pinned to and no more | `Paper.polyFunctor : BPSet ⥤ Polygraph`, `Paper.paperPresentationIso`, `Paper.paperPresentationIso_id` | `Concurrency/Presentation/PaperFunctor.lean` |
| **0″** | …and at `K = Zbp` that polygraph **is Artin's generators and relations**, cell for cell and word for word: a 2-cell's source climbs through the lower junction first, as Artin's relation starts at the lower generator | `Paper.paperArtinIso : Paper.poly Zbp ≅ artinBP.poly`, on `Paper.src_eq_artinWords` | `Concurrency/Presentation/PaperArtin.lean` |
| 7 | the localized base is a **functor** on `BPSet`, which is what a presentation is read against | `chLocMap` / `chLocOpMap` / `chLocOpFunctor`, equalities on `id` and `comp` because they are `Construction.lift`s | `Concurrency/Presentation/LocFunctor.lean` |
| 9 | …and a **functor on `BPSet`** presents it a second way, by adjoining a formal inverse to each merge generator of the cut presentation | `chCutLocPresentation K : Presents (chCutLocFunctor.obj K) (((W K).op).Localization)` | `Concurrency/Presentation/LiftLocalize.lean` |

1–3 are the base `Ch(Z)`, twice over: as a category (1–2) and as the monoid of loops at the run (3),
each in both the Garside and the Artin naming. 7 is the functoriality in the space. 9 reaches the
same category from the other end, presenting the chains first and inverting the merges afterwards.

Further readings of that one polygraph live on the board rather than in the tree: the base read
generator to generator (`Cubical-g7z6`) and the positive braid action at the decorated cube
(`Cubical-zlli`).

### The special case

`chLocEquivElements` / `hLocEquiv` / `hLocArtinEquiv` (`Concurrency/Presentation/HAction.lean`) run
the lift by **pulling back along the discrete fibration** instead, and `hLocPresentation` /
`hLocActionPresentation` are the presentations that route gives. It asks the fibration to survive
localization (`IsSegal`), which buys a smaller presentation where it holds — `Ch(H□ⁿ)[W⁻¹]` is
`PosBraid n` acting on the `n!` orderings of the axes — but it is a special case, not the main road.

## The supporting results

`Ch K = ChainCat.Obj K`, `□n = BPSet.cube n`, `⋁d = BPSet.serialWedge d`,
`Ch⋆ K = (Lines K).Elements`, `Run K` = the all-edges full subcategory of `Ch K`,
`RunWedge` = a wedge with a chosen run.

| Result | Statement | Lives in |
|---|---|---|
| **Salvetti = executions** | `(braidModels n).salEquiv : Ch⋆ (□ⁿ) ≌ Sal (braidCOM n)` — a cell is a face below a tope, i.e. a chain plus a word linearizing it; the wall crossing `T' = X' ⊙ T` is the arrow rule.  Both sides are categories of elements, so the comparison is one `Models` datum: a base (`chFaceCatEquiv`) and a presheaf over it (`linesTopeIso`, whose fibres are `linesTopeEquiv`); `hbpBraidSalEquiv` is the same assembly on `Ch (Hbp □ⁿ)` | `Concurrency/Salvetti/SalExec.lean`, `Concurrency/Salvetti/SalCompare.lean` |
| **The reorientation lives on `H`, not on the product** | `reorientCh_comp_hbpBraidSalEquiv` — across `hbpBraidSalEquiv : Ch (Hbp □ⁿ) ≌ (Sal (braidCOM n))ᵒᵖ` the `Sₙ`-action on the decorated cube *is* `salReorientFunctor`; `not_reorientCh_of_over_base` — no endomorphism of `□ⁿ × run` over the base induces it, `□ⁿ` being rigid | `Concurrency/Complexification/SymReorient.lean` |
| **`H` lies over the runs and over nothing else** | `HOverRun : H ⟶ const runPresheaf` from `H` of the terminal map; `isEmpty_cubeHom` — for `n ≥ 2` there is no map `H(□ⁿ) ⟶ □ⁿ`, hence none `H(□²) ⟶ □² × runBp`, so the product model's `prodFst` has no counterpart on `H` | `Concurrency/Complexification/SymOverRun.lean` |
| **`H` is a twist, not a product** | `not_desym_natural` — the `desym` bijection `(⋁d ⟶ Hbp K) ≃ (⋁d ⟶ K) × (⋁d ⟶ runBp)` does not commute with restriction along the merge `⋁[2,1] ⟶ ⋁[3]`; `not_invertsMerges_runBp`/`not_invertsMerges_Hbp_Zbp` — the run factor takes the square's two orders to its edges' one order, so any natural product splitting would refute `InvertsMerges (Hbp K)` (`not_invertsMerges_of_splitting`) | `Concurrency/Complexification/RunClassifier.lean` |
| **The merges act bijectively exactly when the wedge is the tensor** | `IsSegal K` — `K` inverts the comparison `wedgeToTensor : X ∨ Y ⟶ X ⊗ᵍ Y` at every pair of cubes, i.e. (`isSegal_iff_existsUnique`) a `p`-cell and a `q`-cell meeting at a vertex are the front and back faces of exactly one `(p+q)`-cell.  `isSegal_iff_invertsMerges_repoint` (in `Concurrency/Presentation/ElementsFibration.lean`) — it *is* `InvertsMerges` at every choice of base points, a unit bead contributing nothing (`IsLocal.of_isIso`).  The one comparison map fails in two opposite ways: `□²` has too few cells and the missing filler is the reordering staircase (`not_surjective_faceComparison_cube_two`, from `cubeMerge_ne_cubeReorder`), `H Z` has too many (`not_injective_faceComparison_H_Z`) | `Concurrency/Merge/SegalCondition.lean` |
| **`H` closes the gap** | `sbox_existsUnique` — `▪(p+q)` **is** the wedge `▪p ∨ ▪q` in the symmetric box category, so `isSegal_H_of_symFree_repr`: `H K` is Segal as soon as `symFree K` is representable.  Hence `isSegal_H_cube : IsSegal (H □ⁿ)` | `Concurrency/Complexification/HSegal.lean` |
| **`H` supplies the arrows, the cube supplies the objects** | `run_HbpZbp_eq` — `Hbp Zbp` has one all-edges chain per degree, and `exists_W_from_ones` merges it into every chain of that degree; whereas `runHbpCubeEquivPerm : Run (Hbp □ⁿ) ≃ Perm (Fin n)` gives `n!` rigid all-edges chains, so `not_exists_hom_to_all_cube` — for `n ≥ 2` no decorated chain of `□ⁿ` maps to every one | `Concurrency/Complexification/RunClassifier.lean` |
| **`ConcPos` is well defined** | `permOf_noDoubleCross` — crossing permutations are length-additive, hence `braidFunctor : RunWedge ⥤ FullBraid` and `ConcPos K = proj K ⋙ braidFunctor`, a chain's refinement graded by the *positive* braid of its crossing permutation, before anything is inverted | `Concurrency/Salvetti/EventBraid.lean` |
| **Germ = Artin** | `garside_equiv_artin n : GarsideBraid n ≃* ArtinBraid n` and `posBraid_equiv_artinPos n : PosBraid n ≃* ArtinPosBraid n`, group and monoid.  The positive lift `σ ↦ σ̂` is `matsuLift`, the arrow category-valued Matsumoto (`Web.functor`) names from `1` to `σ` on all of `Sₙ` — **Matsumoto's theorem for `Sₙ`**, which mathlib lacks | `Machinery/Braid/Matsumoto.lean`, `.../MatsumotoCat.lean`, `.../RankTwo.lean` |
| **Two atoms determine the chain they meet in** | A codimension-one refinement erases exactly its own junction, so a chain receiving both atoms has lost both and nothing else (`boundaries_pairApex`, `eq_pairChain`): `pairChain` is the shape of the square (`i + 1 < j`) or of the hexagon (`j = i + 1`), and `exists_pairLeg` puts it below every chain where the two atoms act.  The Artin presentation of `Ch(H□ⁿ)[W⁻¹]` written directly in chains, matching the colimit cell for cell in all three dimensions, is `Cubical-xdhf` | `Concurrency/Presentation/PairChain.lean` |
| **Chains are braid faces** | `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)`, `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face` — a chain of `□ⁿ` is an ordered set partition of `Fin n` (`eq_of_beadOf`, `blockChain`), with no arrangement in the statement; `reflectHom` is the computable converse | `Concurrency/Grading/OrderedPartition.lean`, `Concurrency/Salvetti/ChainBraidFace.lean` |
| **Executions are word + composition** | `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n` — a chain together with a run word refining it; `fexecChStarEquiv` is the enumerable model | `Concurrency/Executions/ExecData.lean`, `Testing/Enumerate/FastEquiv.lean` |
| **The crossing permutation is the word change** | `stepPerm_eq : stepPerm f = (runWord x).trans (runWord y).symm` — `ConcPos`'s label is "position in the source's run word ↦ position in the target's" | `Concurrency/Executions/RunWord.lean` |
| **The arrangement's order and the flattening order label the same arrow** | `crossPerm_eq_topeCross` — on `Ch (Hbp □ⁿ)` both `ChainCat.crossPerm` and `topeCross` are the coboundary of `fibrePerm`, the cell's `cellWord` being that order (`cellWord_hbpBraidSalEquiv`); hence `W_wallLegFlip`, the far leg of a wall span is a bead merge.  A chamber *is* the word it spells (`wordTopeEquiv`), which is what makes `cellWord` readable at all, and `cellWord_of_tope` pins it by the tope | `Concurrency/Salvetti/CrossCompare.lean`, `Concurrency/Salvetti/SalBraid.lean` |
| **Chains are wedge maps** | `equivWedgeCat : RefineObj K ≌ Ch K` (under `NonSelfLinked` + `AdmitsAltitude`) — a refinement of a chain is the same as a bi-pointed map out of a serial wedge.  The forward direction is `homOfBeads`: into a chain whose structure map is a monomorphism (`descent_mono`), bead data assembles into a refinement | `Precubical/Chains/Correspondence.lean`, `Precubical/Chains/Embedding.lean` |
| **A wedge map is a chain refining a chain** | every serial wedge maps into the cube of its own total dimension (`nonempty_toCube`), the structure map of a chain of the cube is a monomorphism (`chain_mono`), and `Ch (□N)` is a poset — so a wedge map is pinned by the chain it induces (`wedgeHom_ext_chain`).  Hom-sets are then read off `boundaries` alone: `nonempty_wedgeHom_iff_coarser` — a hom exists exactly at a coarsening, realised by merging one junction at a time (`exists_crossPerm_eq_one_of_coarser`) | `Precubical/Wedge/CubeMerge.lean`, `Precubical/Chains/Embedding.lean`, `Concurrency/Grading/ChainHom.lean` |
| **A chain of `□ⁿ` has `n` events** | `wedgeDimSum_eq` — a chain climbs the cube's grading (coordinates fixed at `1`) from `0` to `n`; so a map of serial wedges keeps the event count (`serialWedge_dimSum_eq`), both being chains of the cube the target merges into, and every serial wedge is graded by pulling that grading back along the merge (`serialWedge_admitsAltitude`) | `Precubical/Chains/Altitude.lean` |
| **The merges are the flat refinements** | `W K := (merge K).multiplicativeClosure` — one bead merge at a time, a merge being a cut whose middle map is the comparison `cubeMerge`.  `W_iff_flat`: that is exactly the refinements carrying the target's standard chain of the cube back to the source's.  A composite is flat exactly when both legs are (`flat_comp_iff`), so a flat refinement that loses a bead factors through the canonical merge at any junction its target does not separate, and peeling merges off terminates; `merge_iff` says the generators are the codimension-one members.  `Flat` is an equation of wedge maps and nothing else, so `W` transports between any two chains carrying it | `Concurrency/Merge/MergeClass.lean`, `Concurrency/Merge/Flat.lean`, `Concurrency/Merge/MergeGenerate.lean` |
| **The two comparisons are the merge and the atom** | `cubeMerge`/`cubeReorder` run the two beads of `□m ∨ □n` on the head and tail block faces of the cube, in the two orders; they are the two maps `□m ∨ □n ⟶ ⊗` (`cubeMerge_eq`, `cubeReorder_eq`), `⊗ᵍ` having no swap.  Spliced at a cut they are `mergeHom` (`W_mergeHom`) and `atomHom`, which crosses the two strands at the cut (`crossPerm_atomHom`) and so is not a merge | `Precubical/Wedge/CubeMerge.lean`, `Precubical/Wedge/WedgeTensor.lean`, `Concurrency/Merge/TotalMerge.lean` |
| **A hom-set is pinned by the two extreme ones** | `exists_crossPerm_mid` — for `o ⟶ a ⟶ b ⟶ z` whose outer legs cross nothing, a permutation realised `o ⟶ b` and `a ⟶ z` is realised `a ⟶ b`.  Uniqueness of factorisation (`factor_ext`) forces the leg out of `b` to be the merge, so the middle arrow carries the permutation the extremes already do.  With `exists_crossPerm_of_blocks` (rise inside each source bead, land inside the target's) and `exists_crossPerm_single` (into one bead, the Young-coset representatives) as the only coordinate input, this answers "which permutations does `a ⟶ b` realise" with no coordinates | `Concurrency/Grading/Coarser.lean`, `Concurrency/Grading/ChainHom.lean`, `Concurrency/Merge/Atom.lean` |
| **A chain morphism is its permutation** | `hom_ext_of_crossPerm` — merges into the coarsest chain exist out of every chain (`exists_W_to_top`) and are pinned by their endpoints (`eq_of_W`), and out of the run every permutation is realised exactly once: `⋁(topDims n)` *is* `□n`, so `onesTopEquiv` counts the arrows `1ⁿ ⟶ [n]` as the runs of the cube (`onesChainEquiv`, `runPermEquiv`) | `Concurrency/Grading/Coarser.lean`, `Concurrency/Grading/TopBead.lean` |
| **Into the group it is not full** | `not_surjective_posToBraid` — a positive braid's writhe never goes negative, so no `σᵢ⁻¹` is in the image of `PosBraid n →* Braid n` | `Machinery/Braid/PosGerm.lean` |
| **The atoms out of a run satisfy the Artin relations** | `atomLoop N k` is the `k`-th coordinate flip `1ᴺ ⟶ [1,…,2,…,1]` read as a loop once the merges are inverted; `atomLoop_comm` for far-apart cuts and `atomLoop_braid` for adjacent ones, both off the codimension-two cell the two atoms share (`exists_pairCell`) — the second leg of each is the other atom, a leg being pinned by its crossing permutation (`exists_leg`, `conj_congr`).  `Cut.exists_atomComp` says those `N−1` flips are the only codimension-one generators out of the run that are not merges | `Concurrency/Presentation/LocPresentation.lean` |
| **…and they generate** | `exists_atomWord` — a loop at the run is the word its crossing permutation spells: `runLoop N σ` factors as `permLen σ` atoms, one per inversion, built by peeling an adjacent descent (`exists_adjacent_descent`) and appending across the ascent (`runLoop_comp`).  `conj_eq_runLoop` says every refinement's loop is one of these — its source merged back to the run, its target coarsened to one bead — so `exists_atomWord_conj` factors *every* `⋁a ⟶ ⋁b` as a word in atoms conjugated by the two merges | `Concurrency/Presentation/LocPresentation.lean` |
| **The degree-zero cells out of a run are Artin's** | `degree` vanishes exactly at a run (`degree_eq_zero_iff_eq_run`), so a degree-zero codimension-`k` refinement is a `k`-fold cut out of the basepoint, and `AtomPair`/`artinWords` index the pairs and the relation each imposes.  Which cells those are is read once, on the paper's own: `Paper.genArtinEquiv` at `k = 1` and `Paper.cellAtomPairEquiv` at `k = 2`, the latter on `PairChain`'s classification of the shape two cuts meet in.  What the cells *present* is `artinBraids.part`, and nothing geometric | `Concurrency/Presentation/ArtinDegreeZero.lean`, `Concurrency/Presentation/PairChain.lean`, `Concurrency/Presentation/PaperArtin.lean` |
| **A factorisation is its middle shape** | `Factorisation.ext_dims` — a two-step factorisation of `f` is pinned by the shape of its middle, `exists_factor` for existence and `factor_ext` for the legs.  Counting factorisations is then counting an interval of the junction lattice: `exists_atomPair_of_codim_two` says a codimension-two refinement of the run has **exactly two** atoms below it, the two junctions it drops read as indices (`boundaries_atomComp`), and `artin_of_codim_two` splits them by species — adjacent cuts give the hexagon, apart cuts the square | `Concurrency/Merge/Factorisation.lean`, `Concurrency/Merge/Atom.lean`, `Concurrency/Presentation/LocPresentation.lean` |
| **Only adjacent cuts need a 3-cell** | `wedge2Map_isPushout` — the **interchange square of the wedge is a pushout**, so two refinements re-shaping opposite halves of a wedge descend to one, uniquely, with nothing assumed of the four sets — so cuts **separated by a junction** join, for *every* `K`.  Of the three species of a codimension-two join the third is empty — cuts at the same junction are the same cut, and at equal target shapes `eq_of_join_of_dims_eq` says there is no join at all, a factorisation being its middle shape | `Precubical/Wedge/WedgeMonoidal.lean`, `Concurrency/Grading/Degree.lean`, `Concurrency/Grading/Coarser.lean` |
| **A discrete fibration localizes fibrewise** | `isLocalization_elementsDescent : ∫P` localized at the cartesian lifts of `W` is `∫P̄` over `B[W⁻¹]`, for any `W`-inverting `P : B ⥤ Type` — proved by turning the (presentation-free) universal property of `∫P̄` into that of `B[W⁻¹]`, a functor `∫G ⥤ E` being the same as a functor `D ⥤ Fam E` lifting `G` | `Machinery/Localization/FibrationLocalize.lean` |
| **A chain is its dimension sequence plus its classifying map** | `chEquivElements : Ch K ≌ ((wedgeHoms K).Elements)ᵒᵖ` for `wedgeHoms K = ⋁- ⟶ K` on `(Ch Zbp)ᵒᵖ`, and `W K` is its `W Zbp`; hence `isLocalization_chDescent` — once `wedgeHoms K` inverts the merges, localizing `Ch K` only localizes the base | `Concurrency/Presentation/ElementsFibration.lean` |
| **`C ≌ ⟨generators \| relations⟩`** | A `Polygraph` is combinatorial data alone — 0-cells `V`, 1-cells `Gen`, 2-cells `rel` on the words they spell — presenting `presented = Quotient rel` on `Paths (GenObj Gen)`, naming no category.  `Polygraph.Hom` sends a cell to a cell in *every* dimension, so polygraphs form a category and `Hom.functor` is functorial; `Polygraph.Spelling` is the weaker gadget that lets a 1-cell spell a whole *word*, which is what a comparison of two presentations needs and a `Hom` cannot give.  `Polygraph.comap` reads `P`'s 2-cells on a quiver over `P`'s, which is what `elements` is.  `Presents P C` is the *theorem* that `P` presents `C`: a functor `P.presented ⥤ C` with `IsEquivalence`.  So `transport` along an equivalence is a composition, and spanning / completeness / covering are `p.eval.map_surjective`, `p.E.map_injective` and `p.eval` being `EssSurj` — mathlib's, not a bespoke four axioms.  `ofDesc` is the constructor that takes those obligations; `presentedMonoidPresentation` turns a `PresentedMonoid` into one on `(SingleObj M)ᵒᵖ`, the `ᵒᵖ` being the composition order and not a choice | `Machinery/Presentation/Basic.lean`, `Machinery/Presentation/Monoid.lean` |
| **A presented base presents the total category** | `Presents.elements p F : Presents (p.elementsPoly F) ∫F` for `F : C ⥤ Type` — generators the base's acting on an element, relations the base's on projected words.  Words lift uniquely because the projection of generating quivers is a covering (`exists_lift`), and a relation downstairs imposes exactly its lifts upstairs (`gen_onElements`).  `ActionCategory M A` *is* `∫(actionAsFunctor M A)`, so a presented monoid presents its action category with nothing further to prove | `Machinery/Presentation/Elements.lean` |
| **`Ch Zbp` is presented by its bead cuts** | `zCutPresentation : Presents Cut.poly ((Ch Zbp)ᵒᵖ)` — generators the codimension-one refinements, relations the codimension-two ones (two paths of length two with the same value).  The engine is `exists_factor` / `factor_ext` (`Concurrency/Grading/Coarser.lean`): read through the target's wedge map, a factorisation *is* an intermediate chain of the cube, and there is exactly one of each shape — `exists_mid_chain` sends a coordinate to the block of the shape in which its own bead starts, `chain_ext_of_dims` pins it because down-sets of the source's bead order are linearly ordered by inclusion.  `boundaries d` (mathlib's `Composition.boundaries` for the dimension list) turns the shapes into a lattice — `nonempty_hom_iff` says `a ⟶ b` exists exactly when `boundaries b ⊆ boundaries a`, one way by splitting the source at each junction of the target, the other by merging one junction at a time — and `boundaries` is injective, so a one-cut step is pinned by the boundary it removes (`dims_eq_of_cuts_eq`), and two steps out of one shape close a diamond over any common coarsening (`exists_diamond`), which `exists_front` runs down a generating path | `Concurrency/Presentation/CutPresentation.lean`, `Concurrency/Grading/Coarser.lean`, `Concurrency/Grading/ChainHom.lean`, `Concurrency/Grading/Boundaries.lean` |
| **No additive invariant orients a 2-cell of the cut presentation** | A 2-cell of `Cut.poly` is two two-step factorisations of *one* codimension-two refinement, so every additive invariant takes the same value on the two sides: the letter count (`src_length` / `tgt_length`), the codimension (`codim_ev`), and the crossing count (`permLen_crossPerm_comp`) are all constant on it, and so is the multiset of the two legs' crossing counts — the merge/atom square has legs `(1,0)` and `(0,1)`.  So the cut presentation is **not** a rewriting system: the only orientation left on cut words is by which junction is dropped first, i.e. sort-by-position.  Nor does the reduction to the atoms supply one — Tietze elimination is not locally confluent, a deletion being free to consume the witness another deletion needs.  `Machinery/Rewriting/` is therefore generic, reached only from `Testing/`; `ofShortening` states the shape a terminating orientation would have to take (length-graded, two letters to one), and the tree builds none | `Concurrency/Presentation/CutPresentation.lean`, `Machinery/Rewriting/Presentation.lean` |
| **A thin category is presented by any spanning quiver** | `Presents.ofThin` — relating *every* parallel pair of words leaves no word problem, so a presentation of a preorder is a spanning family of generators on a covering family of 0-cells and nothing else (`Polygraph.thin`; soundness, completeness and faithfulness are all free) | `Machinery/Presentation/Basic.lean` |
| **The polygraph tensor is a Day convolution** | `PolyShape` is not monoidal — `cell m n ⊗ cell m' n'` would want a 3-cell — but it is **promonoidal**, and that is all a convolution needs.  A `Split c` says which of two factors carries each direction of the shape `c`; `Split.res` restricts one along a face, with a leg into each factor, and that is the whole structure.  The profunctor `Pro c a b = Σ s : Split c, (s.fst ⟶ a) × (s.snd ⟶ b)` (in `Day.lean`, with `Pro.push`/`Pro.pull`) is a coproduct of representables, so the coend collapses by co-Yoneda to `(F ⊛ G) c = Σ s : Split c, F s.fst × G s.snd` — `dayObj`, functorial in both arguments by `dayFunctor`, and a genuine `Limits.Cowedge` with its `IsColimit` in `DayCoend.lean`.  **`dayIso : dayObj (cellsPsh P) (cellsPsh Q) ≅ cellsPsh (prod P Q)`** is the theorem: read through `polyToPsh`, the tensor of polygraphs *is* that convolution.  So `ProdRel.interchange` is not an axiom — it is the `Split.square` component (`cell_ofDayCells_square`), and `Split.square` is the one splitting of a bigon that puts an edge in each factor, which exists only at `cell 2 2` because a `(g,1)·(1,h)` boundary has two letters on each side.  Functoriality (`prodMap`, `prodMap_id`, `prodMap_comp`) and the coherence (`MonoidalCategory Polygraph.{u,u,u}`) come with it, and `dayIso_naturality` says `prodMap` *is* `dayMap` | `Foundations/Polygraph/Day.lean`, `Foundations/Polygraph/DayCoend.lean`, `Foundations/Polygraph/Tensor.lean`, `Foundations/Polygraph/Monoidal.lean` |
| **An arrow permutes each block of its target and no more** | `index_crossPerm` — read the target in its own standard chain, where the source's firing order inverts `crossPerm` (`crossPerm_flatten`) and a coarsening's beads are the target's blocks read in that order (`beadOf_of_hom`).  So a descent at `k` puts `k` and `k+1` in one block (`index_adj_eq_of_descent`), which *is* the arrow `zObj (atomComp N k) ⟶ d` (`nonempty_hom_of_index`); and `exists_crossPerm_of_blocks` then realises `σ * adjT k`, because the only pair `adjT k` reorders is that one — the **exchange**, `exists_run_mul_adjT` | `Concurrency/Presentation/SliceRuns.lean`, `Concurrency/Presentation/SliceRunSet.lean`, `Concurrency/Grading/ChainHom.lean` |
| **…and a run over a shape is one permutation per bead** | `wedgeOrder d.dims` is one right weak order per bead, and `blockSum` reads a tuple as a single permutation of the events; every run over the shape is one (`exists_blockSum`, on `runSet_append` and `runSet_single`), and the chain a tuple names is the beads' own runs concatenated (`wedgeRunChain`, `crossPerm_wedgeRunChain`).  `crossCap` bounds the block sum and only the reversal in every bead attains it (`permLen_blockSum_le`, `eq_blockTop_of_permLen`), so a shape has exactly one greatest run and it is the least one's complement (`compl_tupleRun_blockBot`).  The event count is carried as a parameter with its equation (`RunAt.strands`, `RunOver.perm`), never transported: a merge preserves it only propositionally | `Concurrency/Presentation/BeadOrder.lean`, `Concurrency/Presentation/BeadRuns.lean`, `Concurrency/Presentation/SliceRunSet.lean` |
| **A presentation of `Ch Zbp` lifts to `Ch K`, but not to its vertex monoids** | `chPresentation : Presents (p.elementsPoly (wedgeHoms K)) ((Ch K)ᵒᵖ)` pulls a presentation of `(Ch Zbp)ᵒᵖ` back along the fibration, and `chCutPresentation` is it with the base presentation supplied — unconditionally.  Under `IsSegal` the fibration survives the localization, and `hLocPresentation` is the same pullback there; `hLocActionPresentation = (hLocPresentation n).transport (hLocEquiv n).op` is *that same 2-polygraph*, read on the action category. `End` does **not** follow: `endEquivStabilizer` says it is a stabilizer, and `end_not_generated_by_simples` — in `PosBraidAction n` the only generator that is a loop is the identity, while the loops are `PosPureBraid n` — says a stabilizer is not spanned by the generators sitting at it | `Concurrency/Presentation/LiftPresentation.lean` |
| **The decorated chains act on the orderings** | `chToAction : Ch (Hbp □ⁿ) ⥤ PosBraidAction n` — a chain goes to the order its events perform the axes in (`fibrePerm`, the step at which each axis is performed), a refinement to the simple of its crossing permutation, `fibrePerm_comp` being the action condition; `chToAction_obj_surjective` says the runs exhaust the orderings | `Concurrency/Complexification/HPosAction.lean`, `Machinery/Braid/PosAction.lean` |
| **Crossing a wall** | A codimension-one chain lies *below* both chambers it separates, so `wallCross w k` is the apex of a span whose legs are `wallLeg` (crossing `adjT k`) and `wallLegFlip` (a merge, `W_wallLegFlip`); `wallCrossLoc` inverts the second and turns the span into an arrow of chambers | `Concurrency/Complexification/HPresentation.lean`, `Concurrency/Salvetti/CrossCompare.lean` |

**Retained infrastructure** not on the results' path but kept as finished mathematics:
- the **geometric tensor** `⊗ᵍ` — a computable `MonoidalCategory` on `PrecubicalSet` and on the
  alias `GeoBP := BPSet` (`Precubical/Wedge/GeoTensor/`);
- the **nerve bridge** `nerveRealizeIso : Nerve (realize X) ≅ X` between the concrete and topos
  models (`Precubical/Basic/Nerve.lean`, `Reachability.lean`) — a natural iso, not an adjunction.

## Layered layout — three provenance tiers

`Machinery/` → `Precubical/` → `Concurrency/` is the spine, and it is a **provenance** order as much
as a dependency one: tier 1 is what a paper would cite, tier 2 what it would recall from the
precubical literature, tier 3 the contribution. `Machinery/Arrangement/` (COMs, the braid
arrangement) is a **second root** — nothing precubical reaches it, its only in-tree imports being
`Machinery/Skeletal` and `Machinery/StrictInverse` — and feeds
`Machinery/Braid/`; the two join the spine at `Concurrency/Salvetti/ChainBraidFace` and
`Concurrency/Salvetti/EventBraid`. `CubeChains.lean` imports the results and the retained
infrastructure; `Testing/` sits outside its cone.

A module holding a single comment line is a **retirement note** — nothing imports it and nothing
below lists it. Find them with `find CubeChains -name '*.lean' -size -2` and do not read them.

### `Machinery/` — tier 1: generic mathematics, cited rather than proved

*The cube category (`Machinery/Cube/`).*
- `Box.lean` — the box category `Box` and the topos `PrecubicalSet := Boxᵒᵖ ⥤ Type` (`HasPushouts`
  free).  **A morphism *is* a sign vector**: `Hom a b := StdCube.Cell b.dim a.dim`, identity
  `topCell`, composition `subst`.  So `cubeRepr` is the identity equivalence and
  `Box.sign`/`ofSign`/`hom_ext` are `rfl`.  Landmine: `id_comp`/`comp_id` are **not** `rfl` (they are
  `subst_topCell`/`topCell_subst`), and `sign`/`ofSign` must stay plain `def`s — as `abbrev`s,
  `rw [Box.sign_ofSign]` stops matching.
- `BoxMonoidal.lean` — the **parallel tensor** on `Box`: `▫m ⊗ ▫n = ▫(m+n)`, morphisms concatenate
  sign vectors; `MonoidalCategory Box`. **`Box` is NOT braided** — no block swap exists.
- `SymBox.lean` — the **symmetric box category** `SBox` (`▪n`): the injections `Fin m ↪ Fin n` plus
  signs, so `Aut ▪n = Perm (Fin n)`.  `J : Box ⥤ SBox` is the monotone wide subcategory, and
  `sHomEquiv : (▪m ⟶ ▪n) ≃ Perm (Fin m) × (▫m ⟶ ▫n)` is the sorting factorization.
- `Reversal.lean` — `flipCell` reverses a sign vector (`0 ↔ 1`, `∗` fixed); it commutes with
  substitution (`flipCell_subst`), and that single fact is the functoriality of `Box.rev : Box ⥤
  Box`, an involution on every hom-set. The engine of the complement.
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
- `HMonad.lean` — the natural maps between powers of `H`.  `natOrd` reads a candidate `H² ⟶ H` as a
  rule combining two orders, whence `Hmul_unique`: the monad multiplication is the *only* `H² ⟶ H`.
  Forgetting either order is not natural (`natOrd_forget`), and at degree `2` the two composites are
  separated by `HmulOuter_ne_HmulInner`.

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
- `HomInduction.lean` — `hom_induction`: `morphismProperty_eq_top` with the `objEquiv` bookkeeping
  paid once, so a caller gets a predicate on `W.Q.obj c ⟶ W.Q.obj c'` with no transport in sight.

*The braid group itself (`Machinery/Braid/`).*
- `Germ.lean` — `Braid n` as a `PresentedGroup` by its Garside germ: one generator `[σ]` per
  permutation, one relation per **length-additive** product; `permHom : Bₙ ↠ Sₙ`, `PureBraid n`.
- `PosGerm.lean` — `PosBraid n`, the same germ presentation read as a **monoid** (`[1] = 1` must be
  imposed: without it every generator may go to one idempotent). `germ_of_atom` cuts the relations
  down to those whose right factor is an adjacent transposition — the only shape the geometry
  realises — and `map_eq_of_atom` is its uniqueness half, a hom being pinned on the simples by the
  atoms (`posBraid_hom_ext`). `posToBraid` is not surjective (`writhe_nonneg`). `posPermHom` is `permHom` read on the
  monoid, `PosPureBraid n = mker (posPermHom n)` its positive pure braids, and `posPureToPure`
  compares them with `PureBraid n ≤ Braid n` — injective exactly as far as `posToBraid n` is,
  Garside's theorem, carried as a hypothesis.  `posPerm_ne_adjT_sq` — the square of a generator is
  no simple, crossing twice while performing nothing — is what separates a refinement's class from
  the loops the localization adds.
- `PosAction.lean` — `PosBraidAction n = ActionCategory (PosBraid n) (Perm (Fin n))`: the orderings
  of the strands, with the positive braids realising the changes of ordering.  The action must be
  **left** multiplication through `posPermHom` (`x * posPermHom β` is a right action); the
  endomorphism monoid at every ordering is `PosPureBraid n`.  `eq_one_of_mul_eq_one` — the writhe
  is additive and non-negative, so there are no non-trivial units — makes `val_eq_one_of_isIso` and
  `eq_of_isIso`: a category, not a groupoid.
- `Artin.lean` — the adjacent transpositions `adjT k`, the Coxeter matrix
  `cox i k = orderOf (adjT i * adjT k)`, and the alternating words `altProd`/`altWord`.
  `IsArtinFamily g` is **one** clause — the two alternating words of length `cox` agree — and
  `isArtinFamily_iff` reads it as the two oriented relations of `ArtinRel`; the Coxeter section is
  the one place the two species are told apart.  The two words differ by `(sᵢsₖ)^t`
  (`altWord_mul_inv`), so `altWord_cox` is `orderOf` alone.  `artinRels` reads `ArtinRel` in the
  free group for `ArtinBraid n`, and `Machinery/Braid/Matsumoto`'s `ArtinPosBraid n` reads it as a
  monoid presentation.  `adjT_injective` reads the value at the low endpoint, which is what lets a
  cell be pinned by the transposition it performs.
- `WeakOrder.lean` — the right weak order on `Sₙ` (the synonym `WeakOrder n`), `Fin.revPerm` its
  top.  A cover is one adjacent crossing undone (`covBy_iff`), and `≤` is reachability by covers
  (`le_iff_reflTransGen`, mathlib's `le_iff_reflTransGen_covBy`).
- `RankTwo.lean` — **the polygon two crossings span**, uniform in the pair.  A double descent
  inverts every pair the two crossings reach, so it absorbs every alternating word in them
  (`permLen_mul_altWord`); the word is reduced up to `cox` (`permLen_altWord_of_le`: a first failure
  would give `sᵢsₖ` a shorter period).  Hence `descent_altWord`, `eq_altProd_of_descents`, the foot
  `polyFoot` and its place in the order, and `isArtinFamily_of_atom` — every germ carries an Artin
  family, multiplicativity across an ascent being the only input.
- `MatsumotoCat.lean` — **category-valued Matsumoto**.  The covers (`Ascent`) of a lower set of the
  weak order (`WeakOrder.Lower`) quiver it, a reduced word is a `Climb`, and a labelling (`Web`)
  satisfying `Web.IsArtin` — two covers close over their polygon's foot — names one arrow per
  comparison (`Web.eval_eq`, the layer's one confluence argument): it extends uniquely to a functor
  on the poset (`Web.functor`, `Web.functor_unique`).
- `Matsumoto.lean` — **Matsumoto's theorem for `Sₙ`** [RESULT].  All of `Sₙ` is a web in
  `SingleObj Mᵐᵒᵖ` (`permWeb`), for which `Web.IsArtin` is `IsArtinFamily` (`isArtin_permWeb`), and
  `matsuLift g σ` is the arrow it names from `1` to `σ`.  Hence `PosBraid.liftArtin`,
  `posBraid_equiv_artinPos` and `garside_equiv_artin` (over `garsideOfArtin`, the easy direction),
  with no hypothesis, and `length_of_word_eq_posPerm`.
- `Generated.lean` — peeling an adjacent descent: only the identity has none, and the length alone
  decides which way a swap goes.
- `Sum.lean` — the block-diagonal `permSum : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m+n))`; the
  crossing count adds because the blocks never interact.

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

*The polygraph itself (`Foundations/Polygraph/`).*
- `Basic.lean` — the `Polygraph` structure and its morphisms, and `cellCongr`, the one transport a
  cell fibred over its boundary ever carries.
- `PathCoords.lean` — **a path is its length and its letters**: `ofCoords` lays `m` letters end to
  end, `ext_of_coords` says nothing else is left.  Coordinates are `ℕ`-indexed and clamped, so a
  path equation may be checked coordinatewise across a change of endpoints.
- `Presheaf.lean` — **2-polygraphs are a presheaf topos** (Schanuel, by Carboni–Johnstone's route):
  `polyEquivPresheaf : Polygraph.{u,u,u} ≌ (PolyShapeᵒᵖ ⥤ Type u)`, the site being one point, one
  edge, and one bigon `cell m n` per pair of boundary lengths.  Hence every limit and colimit, and
  `cellsAt s` preserving both — **(co)limits are cellwise**.
- `Day.lean` — **`PolyShape` is promonoidal**.  It is not monoidal (`cell m n ⊗ cell m' n'` would be
  a 3-cell), but a `Split` — which of two factors carries each direction of a shape — is all a
  convolution needs.  The profunctor `Pro c a b = Σ s : Split c, (s.fst ⟶ a) × (s.snd ⟶ b)` lives
  here beside `Split`, with `Pro.push`/`Pro.pull` its functoriality; it is a coproduct of
  representables, so the coend collapses by co-Yoneda to
  `(F ⊛ G) c = Σ s : Split c, F s.fst × G s.snd` (`dayObj`, `dayFunctor`).  `Split.square`, the only
  splitting that puts an edge in each factor, exists only at `cell 2 2`.
- `DayCoend.lean` — that `dayObj` really *is* the coend of `Pro`, not merely the same formula:
  `dayProfunctor`, `dayIntegrand`, and `dayIsCoend : IsColimit (dayCowedge F G c)`, with
  `dayObjIsoCoend` naming mathlib's `Limits.coend`.  Both halves of the universal property are
  co-Yoneda — the identity-legged splitting `⟨s, 𝟙, 𝟙⟩` generates, and dinaturality slides a pair of
  legs off the profunctor onto the cells.
- `Tensor.lean` — `Polygraph.prod`, its functoriality `prodMap`, and **`dayIso`**: read through
  `polyToPsh`, the tensor *is* the convolution, and `ProdRel.interchange` is its `Split.square`
  component (`cell_ofDayCells_square`).  So the interchange square is not an axiom of the tensor.
- `Monoidal.lean` — `MonoidalCategory Polygraph.{u,u,u}` with `⊗ = prod` on the nose
  (`tensorObj_eq` is `rfl`): `unitPoly` (one 0-cell and nothing else), `assoc`, `unitorLeft`,
  `unitorRight`.  Re-bracketing is a bijection on cells in every dimension, so `prod_pentagon` and
  `prod_triangle` are `rintro` case bashes closing by `rfl` — 4 shapes of 1-cell and 10 of 2-cell
  in a 4-fold tensor.  The unitors' inverses are literally `prodInl`/`prodInr`.

*Generators and relations (`Machinery/Presentation/`).*
- `Basic.lean` — what a polygraph presents: `presented`, the words on `Gen` modulo the congruence
  `homRel` the 2-cells generate.  `Hom.functor : P.presented ⥤ Q.presented` is functorial;
  `Spelling` is the weaker gadget that lets a 1-cell spell a whole *word*, which a `Hom` cannot;
  `comap` reads `P`'s 2-cells on a quiver over `P`'s.
  Separately, `Presents P C` is the *theorem* that `P` presents `C` — a functor `P.presented ⥤ C`
  that is an equivalence — so `transport` is a composition and `ofDesc` is the only place the
  classical obligations appear.  `Polygraph.thin` + `Presents.ofThin` are the thin case, where
  there is no word problem at all.
  It also owns the **congruence a `HomRel` generates**, which names no polygraph: `HomRel.Gen`,
  killed by any functor killing the relation (`map_eq_of_gen`), monotone in it (`Gen.mono`),
  reversing (`HomRel.op`, `Gen.op`), and **reflected along a fully faithful functor**
  (`gen_pullbackRel`) whenever every object factoring an arrow between images is an image.  That
  last one is the engine of every completeness proof that is not a normal-form argument, `Presents.elements` among them.
- `Coproduct.lean` — the coproduct `coprod P`: the disjoint union in every dimension, with the
  leg constraint carried by indexed inductives (`CoprodGen`, `CoprodRel`), and `coprodIsColimit`
  saying that this *is* the categorical coproduct.  `coprodDesc` descends a family of prefunctors
  into any quiver at all — cells, a category, another polygraph's words — and `coprodDescHom` does
  the same for morphisms of polygraphs; `coprod_pre_ext`/`coprod_hom_ext` are the uniqueness, and
  `Presents.coproduct` is the payoff.  The construction is by hand rather than `∐` for one reason:
  `HasColimit` is a `Prop`, so an abstract leg is `Classical.choice`-opaque, whereas here a leg's
  0-cell *is* a pair, `coprodDesc` restricts to its family by `rfl`, and `coproduct_at` — hence
  `braids_at'` and everything a generator names — carries no transport.
- `ColimitCells.lean` — **every cell of a colimit is a leg's**, one statement at every `PolyShape`
  at once (`exists_colimit_ι_cell`, from `cellsAt` preserving colimits), with
  `exists_colimit_ι_obj` its `pt` case.  Nothing is ever unfolded.
- `Elements.lean` — `Presents.elements`: a presented base presents `∫F`, on the `comap` of the
  base along the projection of generating quivers.
- `ElementsLocalize.lean` — the **picked 1-cells, lifted along the fibration**: a 1-cell of `∫F` is
  picked when its base 1-cell is (`elementsPicked`), and the projection being a discrete covering, a
  word of picked arrows lifts letter by letter.  `multiplicativeClosure_pickedArrows_elements` is
  what `presentsLocalization` then asks for, transported.
- `Localize.lean` — **formal inverses for some of the generators**: `invPoly P S` adjoins one
  inverse 1-cell per picked 1-cell with the two cancellation 2-cells, and `presentsLocalization`
  says it presents the localization at the class those cells generate.  The proof is a comparison of
  *universal properties* — a functor out of `(invPoly P S).presented` is a functor out of
  `P.presented` sending each picked cell to an isomorphism (`invDesc`, `invIncl_comp_injective`) —
  so `Localization.Construction`'s strict property closes it.  Everything is spelled on
  `GenObj (InvGen P S)` and never on `GenObj (invPoly P S).Gen`: the two differ by a projection, and
  mixing them blocks `rw` on the `Paths.lift` lemmas.  `invPolyMap`/`invFunctor` carry a map of
  polygraphs along the extension, `invFunctor` being what makes `chCutLocFunctor` a functor.
- `Monoid.lean` — `presentedMonoidPresentation`: a `PresentedMonoid` presents `(SingleObj M)ᵒᵖ`.
  `loopPoly` is the shape before any monoid is named, and is what `BraidPresentation.part` takes.
- `Comparison.lean` — `Presents.Map p q`: a `Spelling` whose induced functor commutes with the two
  comparisons, automatically an equivalence (`isEquivalence`).  A mere *choice* of word makes the
  statement vacuous; `refl` and `trans` are the two ways one is built.
*Abstract rewriting (`Machinery/Rewriting/`).*  Nothing here names a chain, a cube or a braid, and
only `Testing/` imports it: the presentation of `Ch(Z)[W⁻¹]` the tree builds carries no
convergent orientation (see *The supporting results*), so what is here is the generic theorems.
- `Newman.lean` — rewriting at the `Relation` level: `LocallyConfluent`, `Confluent`,
  `Terminating`, `Convergent`.  Mathlib stops at `Relation.church_rosser`, which wants *strong*
  confluence, so **Newman's lemma** (`LocallyConfluent.confluent`), unique normal forms
  (`Confluent.existsUnique_normal`), the decision procedure `eq_iff_eqvGen` and
  **Hindley–Rosen** (`Confluent.union`, through `confluent_of_diamond`) are all here.  Termination is
  a *parameter*: `terminating_of_measure` takes any well-founded relation on any type, so a
  lexicographic refinement of a length is as admissible as a length (`terminating_of_natMeasure`).
- `Presentation.lean` — **a convergent orientation presents**.  `Polygraph.step` is a rule inside a
  context, which is mathlib's `HomRel.CompClosure`; an `Orientation` is a rule set that the 2-cells
  imply, that implies them back, and that converges, with two entry points — `ofCells` takes any
  `Relation.Convergent`, and `ofShortening` is the length-graded one, backed by
  `terminating_of_length`.  Convergence decides the word problem (`quot_eq_iff_eqvGen`,
  `quot_eq_iff_normal_eq`), and `Orientation.complete` → `Presents.ofOrientation` discharges
  `Presents.ofDesc`'s completeness obligation from it plus a separation hypothesis at normal words.

*Loose at `Machinery/` — small generic facts belonging to no chapter.*
- `Slice.lean` — `Functor.IsDiscreteFibration F`: `Over.post F : Over c ⥤ Over (F.obj c)` is an
  equivalence for every `c`, said without choice.  `π_leftOp_isDiscreteFibration` is the example —
  mathlib's `Elements` is the opfibration convention, so the fibration over `C` is `(π X).leftOp`,
  and **that bookkeeping lives here and nowhere else**.
- `SigmaComponents.lean` — `ObjectProperty.sigmaEquiv`: a family of object properties covering every
  object with no morphism between different members exhibits the category as the disjoint union of
  the corresponding full subcategories.  Mathlib's `ConnectedComponents.decomposedEquiv` is the case
  where the index is the set of components; here it is supplied.
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
  `sort_inv_lt_iff` — `(sort f)⁻¹` is the **rank map**, comparing indices as `f` does;
  `sort_congr` — sorting sees only a tuple's **order type**, so a rank map may stand in for the
  tuple it ranks (this is what makes rank transitive, hence `runPresheaf` functorial);
  `sort_comp_strictAnti` — reading `f` through an antitone map reverses the sort by `Fin.revPerm`.
- `MonoidalTransport.lean` — transporting `⊗ₘ` along a tensorator `μ : A ⊗ B ≅ P`, stated in an
  arbitrary monoidal category so that `rw`/`simp`/`monoidal` behave where they would not at `BPSet`.
- `Graded.lean` — `Graded M`, the total category of a family of monoids indexed by `ℕ`: degrees as
  objects, `End n = M n`, the degree transport living once in composition.  `FullBraid` is it at
  `Braid` — the groupoid `braidFunctor` maps into, hence the receptacle of `ConcPos`; `Graded.Germ` is
  what a target must supply for a permutation cocycle to compose, and `Germ.hom_comp` discharges
  that law once for every germ family.  `hom_congrDeg` is the escape hatch: a family of
  homomorphisms into a *fixed* monoid cannot see the degree transport, so a grading read through
  one needs no strand count named.
- `Composition.lean` — mathlib's `Composition.index` (the block a position falls in) read off the
  prefix sums: `index_lt_iff` is the sandwich with no side condition, and everything about blocks
  follows — monotonicity (`index_monotone`) and which block a junction starts
  (`index_eq_of_bracket` + `sizeUpTo_eq_card`).  That a composition is determined by the partition it
  cuts is mathlib's, the injectivity half of `compositionEquiv`.

### `Precubical/` — tier 2: the precubical literature's cube chains

*Precubical sets, two models (`Precubical/Basic/`).*
- `Basic.lean` — the concrete/computable model: graded cells, `face ε i`,
  the precubical identity, the `Category` instance.
- `StandardCube.lean` — `□ⁿ` concretely (sign-vector cells `Fin N → Option
  Bool`, `none = ∗`), `faceCell`, `nones`.
- `StandardCube.lean` — the single home of sign-vector algebra, in three layers: faces (`nones`,
  `faceCell`, `face_face`), peeling (`fixedSet`, `minFixed`, `freeMin`, `Cell.peelRec`), and
  **substitution** (`substFun`, `subst`, `subst_assoc`, `subst_faceCell`, `subst_injective`).  It
  imports only mathlib, which is what lets `Box` be defined on it.
- `Representable.lean` — **cube Yoneda**: `cubeRepr : (□ⁿ ⟶ K) ≃ K.cells n`, now the identity
  equivalence, plus what refers to composition — `Box.sign_comp`, `Box.ofSign_peel`, `Box.mono`,
  `Box.endo_eq_id`, `boxHom_dim_le`.
- `Bipointed.lean` — `BPSet` (a presheaf with two chosen `0`-cells) + `Hom` + category; `cells`,
  `vertex₀/₁`, `faceMap`/`cubeMap`, `IsAltitude`, and `comp_app_cell` (the `ConcreteCategory`
  bundling that defeats `rfl` on a composite application).
- `BipointedProd.lean` — the levelwise product with paired base points, as the binary product:
  `BPSet.prod` with `prodFst`/`prodSnd`/`prodLift` (computable, both legs `rfl`), shown to be the
  binary product by `prodFanIsLimit`, so `instance : HasBinaryProducts BPSet` and mathlib's `⨯`
  API apply.  Downstream spells `X.prod Y`; mathlib's chosen `X ⨯ Y` is `noncomputable`.
- `Nerve.lean` — `realize : PrecubicalSet ⥤ PrecubicalConstructions`, the nerve
  `Nerve : PrecubicalConstructions ⥤ PrecubicalSet`, and both round trips `realizeNerveIso`,
  `nerveRealizeIso`.  It also owns the **concrete** model's cube Yoneda (`stdPre`, `act`,
  `concreteRepr`, `cubeι`, `substMap`): `act` is the iterated-face construction, needed because
  `nerveRealizeIso` is cube Yoneda for an arbitrary `PrecubicalConstructions` rather than for `□ⁿ`.
  The only consumer of `Basic/Basic.lean`, and with it the only other file naming
  `PrecubicalConstructions`.
- `Reachability.lean` — `PrecubicalSet`-level reachability and connected components `π₀`.
- `Terminal.lean` — the terminal precubical set `Z` (one cell per dimension), `Zbp`.
- `Altitude.lean` — the side conditions `NonSelfLinked` / `AdmitsAltitude`,
  all `PrecubicalSet`-level, + the `alt_*` lemmas; an altitude pulls back along any map
  (`IsAltitude.comp`, `AdmitsAltitude.of_hom`).

*Wedges, and the geometric tensor (`Precubical/Wedge/`).*
- `Wedge.lean` — `cube n` (representable, bi-pointed), `wedge2 X Y` = `X ∨ Y` (pushout of a point),
  `vertexMap`, `serialWedge` = `⋁d` (the fold `List.foldr (□· ∨ ·) (□0)`).
- `WedgeMonoidal.lean` — the wedge as the **default** `instance : MonoidalCategory BPSet`
  (tensor `∨`, unit `□0`, associator `wedge2Assoc`, unitors, pentagon + triangle).
- `GluePushout.lean` — a **computable** pushout of presheaves (mathlib's is
  `Classical.choice`-opaque).
- `GeoTensor.lean` + `GeoTensor/Hom.lean`, `GeoTensor/Monoidal.lean` — the **computable** geometric
  tensor on `PrecubicalSet`, from the closed form of the Day coend:
  `(X ⊗ Y)(▫n) = Σ p q, (p + q = n) × X(▫p) × Y(▫q)`, restriction = split the cell and restrict
  each half. `GeoTensor/Cube.lean` is `□m ⊗ □n ≅ □(m+n)` at the representable level.
- `GeoTensor/Unit.lean` — the unit and both unitors.  `tensorUnit` is the representable at dimension
  `0`, so a unit cell's sign vector lives on `Fin 0`: its degree is forced (`unitCell_dim_zero`) and
  it is unique (`unitCell_unique`), which makes a unit half of a product cell redundant and the
  surviving half carry the whole degree (`leftUnitorEquiv`, `leftUnitor`).  `Box` has no symmetry,
  but a unit half occupies no coordinates, so swapping the two halves *is* natural once one of them
  is the unit (`unitSwap`) — and the right unitor is the left one conjugated by that swap, so every
  right-hand statement follows rather than being proved again.
- `GeoTensor/Assoc.lean` — the associator.  Both sides of `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` are the same
  triple split, so the components reassociate nested `tensorCells` along `(p+q)+r = p+(q+r)`
  (`assocFwd`/`assocBwd`, `associator`) and naturality is associativity of the triple coordinate
  split of a sign vector.  `tensorCells_heq` is the one structural `HEq` a cell crosses when its
  total dimension moves.
- `GeoTensor/BP.lean` — the same on bi-pointed sets, written `X ⊗ᵍ Y`, carried by the alias
  `GeoBP := BPSet`; `cubeTensorIsoBP`. It lives on its own alias because bare `⊗` on `BPSet` is
  the **wedge**. Unit is `□0` on the nose.
- `CubeMerge.lean` — the **two staircases** out of `□m ∨ □n`: `Box.headFace ε p q` and
  `Box.tailFace ε p q` are the block faces of `□(p+q)` (first `p`, resp. last `q`, axes free, the
  rest at `ε`), meeting at a vertex (`endVertexMap_headFace`); `cubeMerge` descends the wedge onto
  head-then-tail, `cubeReorder` onto the blocks exchanged (`cubeMerge_ne_cubeReorder`).  Also
  `nonempty_toCube`: every serial wedge merges into the cube of its own total dimension.  No tensor
  appears.
- `WedgeTensor.lean` — the **two wedge-to-tensor comparisons** `wedgeToTensor : X ∨ Y ⟶ X ⊗ᵍ Y`
  and `wedgeSwapTensor : X ∨ Y ⟶ Y ⊗ᵍ X`, descended from the two slices meeting at the glued
  vertex (`slice_corner`).  There are two because `⊗ᵍ` has no swap; at cubes they are the two
  staircases (`cubeMerge_eq`, `cubeReorder_eq`).

*The cube-chain category (`Precubical/Chains/`).*
- `Basic.lean` — `Beads K d` (cube data at a *given* shape `d`) with its flat view
  `Beads.toList`/`Beads.ofList` (injective, `toList_injective`); `CubeChain` (a cube list satisfying
  the folded `IsCubeChain`; the junction vertices are forced, not stored), `ofIsCubeChain`.
- `WedgeMap.lean` — bi-pointed maps out of a serial wedge ↔ shape-indexed cube data; `wedgeDesc
  (c : Beads K.toPsh d) … : ⋁d ⟶ K.repoint a b` (re-pointing the target is what makes the endpoint
  conditions the morphism's own `app_init`/`app_final`), `beadCell`, `serialWedge_hom_ext`,
  `bpset_hom_ext_of_beadCell`, the `glue0_*` pushout/mono cores.
- `Altitude.lean` — the cube's grading (`cubeAlt`, coordinates fixed at `1`), the chain arithmetic
  `beadStart`/`isCubeChain_alt_final`/`isCubeChain_alt_get`, and the count: a chain of `□m` has
  `m` events (`wedgeDimSum_eq`), a map of serial wedges keeps it (`serialWedge_dimSum_eq`), and a
  serial wedge is graded by pulling the cube's grading back along `nonempty_toCube`.
- `Embedding.lean` — under `NonSelfLinked` + an altitude a chain's structure map is a
  monomorphism (`descent_mono`, with the two landmine counterexamples), so `Ch K` is thin
  (`chainCat_hom_subsingleton`) and bead data assembles into a refinement (`homOfBeads`, the chain
  condition reflected from `K`).  At the cube: `chain_mono`, `wedgeHom_ext_chain`.
- `Correspondence.lean` — **`equivWedgeCat`**; forward by `homOfBeads`, backward by block
  decomposition.
- `Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category. The face inclusion is
  carried as *data*, not as a `Prop`.
- `Category.lean` — `ChainCat`, `chFunctor : BPSet ⥤ Cat`, `Aut.liftToCh`.
- `CubeVtx.lean` — vertices of cube faces: `cubeVtxOfCell` is an `OrderHom`, so the monotonicity the
  coordinate coend needs is in its type rather than a lemma; `cubeVtx` is its `Box`-hom spelling.
  Also the endpoint rules `vertexEnd_cube` (on a representable, `vertexEnd` is precomposition) and
  `sign_vertexEnd`.
- `CubeNonSelfLinked.lean` — `cube_nonSelfLinked`, on `cubeMap_cube_app` reading the Yoneda
  canonical map of a cube cell as a substitution.
- `ChainSkeletal.lean` — `Ch(K)` is acyclic and skeletal for **every** `K` (only identity
  endomorphisms): a refinement keeps its target's junctions, so equal bead counts force equal
  shapes (`boundaries_injective`), and on one shape each bead lies in the bead of its own index
  (`blockIdx_endo`), which `Box` rigidity makes the identity.
- `Reversal.lean` — a chain run backwards: the cubes in reverse order, each flipped by `Box.rev`.
  Reversal exchanges a cube's two extremal vertices, so the reversed list is again a chain, and it
  only permutes the dimension list, so `EdgeChain.rev` restricts it to the all-edges chains — the
  geometry `Run.rev` reaches through. Restriction along a face travels with `runPresheaf`, not with
  the cube lists: on a run it is a rank map (`runFace`, `Executions/Runs.lean`), and reversal's
  naturality for it is `revRunPsh` (`Executions/Complement.lean`).

*Concatenation, splitting, and the lifts along a wedge (`Precubical/Segal/`).*
- `Segal.lean` — the append iso `serialWedgeAppend : ⋁x ∨ ⋁y ≅ ⋁(x ++ y)`, built **structurally**
  from `λ_`/`α_`/whiskering (so its coherence is monoidal, not a pushout chase); `⋁` as a **strong
  monoidal** functor `serialWedgeFunctor : DimList ⥤ BPSet` where `abbrev DimList := Discrete
  (FreeMonoid ℕ+)`; the concatenation `chConcat X Y : Ch X × Ch Y ⥤ Ch (X ∨ Y)` and its
  faithfulness.
- `Split.lean` — the **choice-free** inverse of `chConcat`, in three layers: `Split Z A B` ("`Z` is
  `A ∨ B`" as data, on the computable `Glue.cellSide`), `Split.chainSplit` (the *order* — the only
  place altitude is used), and the interface `chObjEquiv : Ch Z ≃ Ch A × Ch B`. Also
  `splitWedgeMorphism`, the same split for a bare map `⋁as ⟶ X ∨ Y`, which is the form
  `Concurrency/Executions/Runs.lean` consumes, and `AdmitsAlt`, the monoidal subcategory where the
  splitting applies (`wedge2_admitsAltitude` glues the two altitudes).
- `WedgeLaxMonoidal.lean` — `chFunctor` is lax monoidal `(BPSet, ∨) ⥤ (Cat, ×)`; each coherence
  square is the matching `MonoidalTransport` lemma fed the append iso's own coherence.
- `WedgeExtend.lean` — lifting a presheaf on `Box` to serial wedges: `F↑ X = (X.toPsh ⟶ F)` is
  precomposition, so it turns the wedge colimit into a limit — `pshExtWedge2` binary,
  `pshExtProd` iterated, both under single-vertexness of `F ▫0`.
- `PshExtMonoidal.lean` — `pshExtFunctor F = BPSet.toPshFunctor.op ⋙ yoneda.obj F` is oplax
  monoidal, strong under single-vertexness — so `Lines K a = (⋁a.dims).toPsh ⟶ runPresheaf`
  literally, with its splitting for free.

### `Concurrency/` — tier 3: the concurrency braid groupoid

See `Concurrency/README.md` and `Concurrency/BRAID.md`.

*The two gradings on `Ch K` — crossings, and codimension (`Concurrency/Grading/`).*
- `CoordFunctor.lean` — the **coordinates of a serial wedge**, by bead data alone: `coordMap φ
  ⟨i,k⟩ = ⟨blockIdx φ i, faceEmb (blockFace φ i) k⟩` on the nose, `coordFlip χ : beadEvent a ≃
  Fin m` for `χ : ⋁a ⟶ □m`, and functoriality from `ι_comp_blockFace` (bead data composes, `yoneda`
  faithful) rather than from a coend.  `coordMap_of_factor` cancels `serialWedge_ι_mono`, so a
  caller with its own factorization never computes `blockFace`.  Also `coordFlip_comp` (the engine
  behind the label theorem), the run-free **lexicographic event flattening** `pos =
  finSigmaFinEquiv`, and the **monoidality of `coordMap` over `++`**: `eventInl`/`eventInr` split `beadEvent (a ++ b)` (`eventAppendCases`), and
  `coordMap_inclL`/`coordMap_inclR` say a wedge map restricting along the half-inclusions moves each
  block by its own restriction — the coordinate content of `chConcat`'s tensorator.
- `WedgeBraid.lean` — the **braid grading of `Ch K` from the wedge map alone**: `crossPerm h g` is
  `coordMap g.φ` read through `pos` at a strand count `h : dimSum a.dims = N` the source meets,
  **monoidal over the wedge** (`crossPerm_chConcat`: on the tensorator it is the block sum `permSum`, so crossings
  add).  Carrying the count rather than transporting afterwards is what
  makes the cocycle law a plain anti-homomorphism (`crossPerm_comp`): the target numbering of `g`
  and the source numbering of the next map are proofs of the same equation, hence the same term.
  `crossPerm_recount` is the only transport left, and it is `rfl`.  Everything geometric about
  `crossPerm` goes through `ChainHom`'s `crossPerm_flatten` instead of this definition.
- `ChainHom.lean` — **a wedge map is a chain refining a chain**: a serial wedge maps into the cube
  of its own total dimension and a chain of that cube is a mono, so a wedge map is pinned by the
  chain it induces (`wedgeHom_ext_chain`).  `Coarser d d'` is then the
  boundary inclusion itself, and `nonempty_wedgeHom_iff_coarser` is `boundaries_subset_of_wedgeHom`
  one way and merging one junction at a time (`exists_crossPerm_eq_one_of_coarser`) the other.  Chains of `⋁1ᴺ` in
  `□N` are the runs of the cube (`onesChainEquiv`).
  Against the ordered partition of `OrderedPartition`, `flatten` and the shape pin the chain
  (`chain_ext_of_flatten`), a coordinate's bead is the block its rank falls in
  (`beadOf_eq_index`, against `dimComp`'s `Composition.index`), and every order rising inside each
  block occurs (`exists_chain_flatten`).  `stdChain` is the chain flattening to the identity, so
  an arrow between two of them crosses nothing (`exists_crossPerm_eq_one`).  `crossPerm_flatten`
  reads `crossPerm` off the chain, which is what `hom_ext_of_crossPerm` and
  `exists_crossPerm_of_blocks` run on.
- `BlockDecomp.lean` — block decomposition of a serial-wedge map (`faceEmb`/`blockIdx`/`blockFace`),
  and its numerics from the grading every serial wedge carries: a source bead lies inside its
  target block (`serialWedge_bead_sub_block`), so `blockIdx` is monotone and the target's blocks are
  unions of the source's — every junction of the target is one of the source's
  (`boundaries_subset_of_wedgeHom`, `boundaries_subset_of_hom`).
- `OrderedPartition.lean` — **a chain of `□n` is an ordered partition of `Fin n`**: `beadOf b q`
  is the bead flipping `q` (the bead component of `coordFlip`'s inverse, `flatten` being the rank
  component, and `flatten_lt_iff` sorting by bead then by the cube's order).  Bead `i`'s face is
  `blockSign (beadOf b) i` (`ev_beadFace_eq_blockSign`, the reading pinned along the spine), so a
  chain is pinned by its partition (`eq_of_beadOf`) and `blockChain` realises every partition; a
  refinement coarsens the partition (`beadRefines_of_hom`) and `reflectHom` realises every
  coarsening, by `homOfBeads` into the monomorphism `chain_mono`.
- `TopBead.lean` — **the coarsest chain on `n` events (`topDims`: one bead, or none), and the
  arrows into it**. `eq_of_W`: a merge moves no event, and a wedge map *is* its coordinate
  bijection, so a merge is pinned by its endpoints. One bead coarsens every shape and the run of
  edges refines every shape, so `exists_W_to_top` (the total merge out of every chain) and
  `exists_W_from_ones` (the run of `N` edges merges *onto* every shape of strand count `N`) are
  the two extreme coarsenings; between the two extremes nothing is constrained, so `onesTopEquiv`
  identifies that hom-set with `Sₙ` — every permutation is realised out of the run.
- `Degree.lean` — the grading `degree = Σ (dim − 1)` on `Ch K` and the **codimension** of a
  refinement (beads lost); `grading` makes it a functor to the delooping of `(ℕ, +)`.  A
  refinement keeps its target's junctions (`boundaries_subset_of_hom`), so the codimension counts
  the junctions it drops and the species of a refinement are `Concurrency/Grading/Boundaries`
  applied to that.  `CutData` is the single merge a codimension-one refinement is
  (`codim_eq_one_iff`), and it is unique.
- `Boundaries.lean` — a dimension list *is* a `Composition` of its total (`dimComp`), so `boundaries
  d` is mathlib's `Composition.boundaries` read in `ℕ` — that is where `card_boundaries` and
  `boundaries_injective` come from. `cutAt` cuts at a boundary the shape lacks and
  `cutOfLengthSucc` classifies one deleted boundary.  The **bead
  relation** lives here too, on the junction set alone:
  `beadAt d p` counts the junctions at or below `p`, so `beadAt_lt_iff` (a junction in `(p, q]`),
  `beadAt_succ_eq_iff` (a junction is where the bead changes at a step) and
  `boundaries_subset_of_beadAt` (the beads pin the junctions) carry no total and no `Fin`.
  `ChainHom`'s `beadAt_eq_index_succ` — `beadAt d ↑p = index p + 1`, the junction at `0` being the
  offset — identifies it with `Composition.index` outright, so every comparison of the two
  spellings is `omega`.
- `Coarser.lean` — **factoring through an intermediate shape**: between a chain and a coarsening of
  it, a shape is realised by exactly one chain, read off the source's firing order both ways — a
  coarsening's beads are down-sets for it (`beadOf_of_hom`), and a shape whose junctions the source
  has is realised by sending a coordinate to the block its own rank falls in (`exists_mid_chain`).
  Through the target's wedge map that is a bijection: `factor_ext` its injectivity, `exists_factor`
  its surjectivity, and the interpolation `exists_crossPerm_mid` what it gives.
  `inversions_flatten_subset` — **a coarsening only ever removes an out-of-order pair**, since its
  beads are the blocks of the source's firing order and blocks are ordered by their members — is
  "a crossing is never undone" with no pair crossed twice in it, and gives
  `permLen_crossPerm_comp`: along a composite the two crossing permutations are read in *one* chart,
  the target's standard chain, so they are the firing orders of a chain of a cube and a coarsening
  of it.
- `CodimTwo.lean` — **the capacity of a shape**, and the two codimension-two shapes.  `crossCap` is
  the reversal inside each bead — the pairs of events the shape makes concurrent, and so the bound
  on every run over it (`permLen_le_crossCap`, in `BeadOrder.lean`, where the runs over a shape are
  already resolved into their beads).  Below degree three one bead carries everything, so the
  capacity is read off the degree (`crossCap_eq_one_of_degree`, `crossCap_of_degree_eq_two`) — except
  at degree two, where the two species part.  The two codimension-two species are two *shapes*,
  `𝟙^p ++ 3 :: 𝟙^q` and `𝟙^p ++ 2 :: (𝟙^m ++ 2 :: 𝟙^q)`, told apart by which pair of junctions they
  drop (`boundaries_three_bead`, `boundaries_two_two_bead`); their capacities (`crossCap_three_bead`,
  `crossCap_two_two_bead`) are then computed from the shape, never used to discriminate.
  Factoring is orthogonal to all of it — a factorisation whose first leg is a single cut *is*
  that cut (`oneCutEquivCuts`), so at codimension two there are exactly two, indexed by `Bool`
  (`oneCutEquivBool`).

*The bead merges, and what inverting them means (`Concurrency/Merge/`).*
- `MergeClass.lean` — `merge`, the cuts whose middle map is the comparison `cubeMerge`, and
  `W K := (merge K).multiplicativeClosure`, the **bead merges**.  `W_le_iff` is the induction
  principle.  A cut is data on the wedge map alone, so `merge` is an inverse image from `Ch Zbp`.
- `MergeBraid.lean` — a splice `𝟙 ∨ w ∨ 𝟙` keeps every strand before and after its cut and moves
  the merged block by the staircase alone (`crossPerm_splicePhi_out`/`_mid`, read off the splice's
  events): at `w = cubeReorder` that is the Garside atom, the one place a permutation is named, and
  at `w = cubeMerge` it is nothing (`crossPerm_eq_one_of_merge`, `crossPerm_eq_one_of_W`).
  `crossPerm_concat` reads the tensorator law `crossPerm_chConcat` on a bare concatenation.
- `Flat.lean` — `Flat u`, the refinements carrying the **standard chain** of the target back to the
  standard chain of the source (`stdChain`, the reading that fires the coordinates in their own
  order).  On coordinates that is "every event keeps its rank" (`flat_iff_pos_coordMap`), so flatness
  is monoidal over the wedge (`flat_concatHomφ`) and a splice is flat as soon as its middle map is —
  which `cubeMerge` is, whence `flat_of_merge` / `flat_of_W` with no permutation on the route.
  `flat_comp_iff` — a composite is flat exactly when both legs are — is the geometric "a crossing is
  never undone": the middle chain of a flat composite is a coarsening of the source's standard chain,
  and a coarsening is pinned by its shape (`chain_ext_of_dims`).  Quantifying the strand count keeps
  `Flat` a bare equation of wedge maps, which is why it transports along a relabelling of either
  classifying map.  `crossPerm_eq_one_iff_flat` is the one bridge to the crossing permutation, and
  `crossPerm_eq_one_of_W` / `pos_coordMap_of_W` are its corollaries.
- `MergeGenerate.lean` — the **converse**, `W_iff_flat`.  Flatness is inherited by factors, so a
  flat refinement splits into flat pieces: cut at any junction the target does not separate and
  factor (`exists_factor`), and induction on the bead count exhausts it.  At codimension one the
  middle map is forced, a chain morphism being its crossing permutation
  (`merge_of_flat_of_codim_one`) — the one step here that reads coordinates — whence `merge_iff`.
  `Flat` being an equation of wedge maps, `W_eq_inverseImage_toChZ`.
- `TotalMerge.lean` — `zObj`/`zHom` (an object of `Ch Zbp` *is* its dimension list), the two
  spliced comparisons `mergeHom l r p q` and `atomHom l r`, and the splice `𝟙 ∨ w ∨ 𝟙` read as a
  **double concatenation** (`splicePhi_eq_concat`, `spliceNil_eq_concat`), so on events a splice is
  the identity before and after its cut and the staircase on the merged block
  (`pos_coordMap_splicePhi_left`/`_mid`/`_right`).
- `Atom.lean` — the atom relations of `Machinery/Braid/PosGerm`, realised in `Ch Zbp`.
  `atomComp n i = 1ⁱ 2 1^{n-2-i}` is the run with the junction `i+1` undone, so `i, i+1` is the only
  pair of strands it lets share a bead (`eq_adj_of_index_eq`), and which atoms lie below a refinement
  of the run is a question about its cut set (`nonempty_hom_atomComp_iff`).  The atom itself is
  *geometric*: `atomOnes` is the other wedge-to-tensor comparison of a square, `cubeReorder 1 1`,
  spliced at the cut — it exchanges exactly the two strands there (`crossPerm_atomOnes`), which is
  `adjT i` and is why it is not a merge.
  `boundaries_atomComp` says the `k`-th atom's shape drops exactly the junction `k+1`, so
  `exists_atomPair_of_codim_two` reads the two junctions a codimension-two refinement of the run
  drops as the two atom indices below it — the count `artin_of_codim_two` consumes.
- `Factorisation.lean` — a two-step factorisation of `f : a ⟶ b` **is** its middle shape
  (`Factorisation.ext_dims`), `factor_ext` forcing the legs and the chain over a shape being the
  cartesian lift of the second leg.
- `SegalCondition.lean` — **for `K` the wedge is the tensor** [RESULT].  `IsLocal K w` (restriction
  along `w` is a bijection on maps into `K`) is mathlib's left Bousfield `ObjectProperty.isLocal`
  at `{K}`, so `IsLocal.of_isIso` / `IsLocal.of_iso` are its `ObjectProperty.isLocal_of_isIso` and
  `isoClosure_isLocal`, and `IsMultiplicative` in `w` is free.  `IsSegal K` is locality at
  `wedgeToTensor (□p) (□q)`.  `IsLocal K` is a `MorphismProperty BPSet`, so its `RespectsIso` and
  **`IsMonoidal`** are instances — the latter registered from `IsLocal.tensor`, which is the one
  project-specific input (`wedge2Desc` + `wedge2_hom_ext`); the whiskerings are then mathlib's
  `whiskerLeft_mem`/`whiskerRight_mem`.  The base points are free in both directions
  (`isLocal_iff_bijective_repoint`).  A unit bead is an isomorphism
  (`wedgeToTensorPsh_unit_left`/`_right`), so the positive blocks are the whole condition:
  `isSegal_iff_isLocal_cubeMerge_pos`.  `wedgeCubeHomEquiv` reads the target on cells, giving
  `faceComparison` and the `∃!` form.  Nothing here mentions a chain: the file sits below
  `ElementsFibration.lean`, which is where the merges meet it.
- `CubeCrossing.lean` — `cross c`, the crossing permutation of the unique refinement of the one-bead
  chain `cubeTop n`: an invariant of a chain of `□n`.  It is the **word** a chain fires, the firing
  order `flatten` inverted (`cross_eq_flatten_inv`) — inverse because a refinement factors the
  crossing on the right and the firing order on the left, and `Machinery/Braid/WeakOrder` is the
  right weak order.  On a run it is the run's own word (`cross_wordRun`); no other file of
  `Concurrency/Merge/` names `flatten`.
- `CubeFaces.lean` — a shape on `n` events *is* its junction set, so there is a coarsening for
  every subset of a chain's junctions (`exists_coarsening`), two coarsenings meet in the
  intersection (`exists_meet`), and two distinct codimension-one steps close a square
  (`exists_join`).

*Presentations of the chains and of their localization (`Concurrency/Presentation/`).*  The chapter
reads in the order of the through-line: the base, then the runs over a chain, then the other route
and what separates the two generating sets, then the two runs a chain spans and the polygon of a
degree-two shape, and last the paper's polygraph and its Artin reading.  `CubeChains.lean`'s import comments say the same thing
in one line each.

*The base.*
- `BaseComponent.lean` — `runBase N`, the run of `N` events as a one-object piece of
  `Ch Zbp[W⁻¹]`.  Full faithfulness *is* bijectivity of `runBraid N`, which is what
  `CategoryOfElements.isEquivalence_pre` asks of the functor a fibre is pulled back along.
- `BasePresentation.lean` — **`BraidData`** and **`BraidPresentation`**, the input, and *pure braid
  theory*: `P N` is `loopPoly` of the generators and relations at strand count `N`, and a
  `BraidPresentation` adds `part N`, that they present `SingleObj (PosBraid N)` there; `p.braids`
  presents `FullPosBraidᵒᵖ` as the coproduct over the counts — so there is no vertex to declare
  unique, and `braids_at'` (the strand-`N` 0-cell names `N`) is `rfl`.  `BraidData.ofRels` is
  generators and relations alone and `ofMonoids` adds the monoid presentations; `artinBP` is Artin's
  data, `germBP` and `artinBraids` the two presentations; `BySimples` says each generator names a
  *simple*, which the lift needs because the action on runs is length-additive.  Nothing here
  mentions a chain, which is why `PaperArtin` can name `artinBP`'s cells without importing the base
  route.
- `Retraction.lean` — the loops at the run **are** `PosBraid N` (`runBraidEquiv`, `runArtinEquiv`):
  `posGrade` sends a refinement to the simple of its crossing permutation, the merges are inverted,
  and `runLoop` generates, so the descent retracts it.

*The runs over a chain.*
- `SliceRuns.lean` — the **exchange**: an arrow permutes each block of its target and no more
  (`index_crossPerm`), so at a descent the shortened crossing permutation is realised too
  (`exists_run_mul_adjT`).
- `SliceRunSet.lean` — the runs over `d` (`RunAt`, `RunAt.perm`, `RunSet`), and
  `exists_not_isRun_over` — a slice has an object that is not a run.  The fibre is the runs and not
  their permutations, because postcomposition leaves a run's source untouched and so keeps the
  strand count on the nose.
- `BeadRuns.lean` — **the runs over a concatenation are the block sums of the runs over the halves**
  (`runSet_append`), and a single cube admits every permutation of its axes (`runSet_single`).  A run
  is a wedge map out of an all-edges wedge (`runSet_iff_exists_wedgeHom`), such a map splits at a
  junction (`splitTarget`), and `crossPerm` is monoidal there (`crossPerm_chConcat`).  Leaving the
  *source* shape free is what keeps the equation free of `Fin` transports.
- `BeadOrder.lean` — **the beads' permutations, and the run they name**: `wedgeOrder l` is one right
  weak order per bead, `blockSum` reads a tuple as one permutation of the events, and the chain a
  tuple names is its beads' own runs concatenated (`wedgeRunChain`, `crossPerm_wedgeRunChain`).
  `crossCap` bounds the block sum bead by bead (`permLen_blockSum_le`) and only the reversal in
  every bead attains it (`eq_blockTop_of_permLen`); every run over the shape is a tuple's
  (`exists_blockSum`), so the same two facts bound every run (`permLen_le_crossCap`) and pin the
  greatest one.  The tuple's chain read as a run (`tupleRun`) has two descriptions — the
  tuple, and the beads' own runs (`runProj`) — and they are compared exactly once, in
  `compl_tupleRun_blockBot`: `Run.compl` carries the least tuple's run (`blockBot`) to the greatest
  tuple's (`blockTop`), bead by bead.  `run_eq_of_runProj` is the extensionality that makes that a
  one-liner.
- `LocFunctor.lean` — `chLocMap` / `chLocOpMap` / `chLocOpFunctor`: `Ch f` localized, as a functor
  of `K`, with `chLocMap_id` / `chLocMap_comp` equalities because it is a `Construction.lift`.
  `chLocOpMap` is the side `Paper.paperPresentationIso` reads.

*The other route, and the geometry that separates the two generating sets.*
- `HAction.lean` — the Segal/descent route: `chLocEquivElements`, `hLocEquiv`, `hLocArtinEquiv`, and
  the presentations `hLocPresentation` / `hLocActionPresentation` they carry.  This is the **special
  case**, not the main road.
- `PairChain.lean` — the codimension-two chain of two cuts.  A codimension-one refinement erases
  exactly its own junction, so a chain receiving both atoms has lost both and nothing else
  (`boundaries_pairApex`, `eq_pairChain`); `pairChain` is the square's shape (`i + 1 < j`) or the
  hexagon's (`j = i + 1`), and `exists_pairLeg` puts it below every chain where the two atoms act.
  Its boundaries pin which (`dims_pairChain_of_adj` / `_of_apart`).
- `CutPresentation.lean` — the presentation that `exists_factor` / `factor_ext`
  (`Concurrency/Grading/Coarser.lean`) feed.
  `cutsOf f = boundaries a \ boundaries b`, and `boundaries` is injective on shapes,
  so `dims_eq_of_cuts_eq` pins a one-cut step by the boundary it removes.  Two such steps out of one
  shape close a diamond whose apex has the two targets' boundaries in common (`exists_diamond`),
  and `exists_front` brings a named first step to the front of a generating path — no order on
  the cuts anywhere.  The relation is just "two paths of length two with the same value", and that is
  also why no additive invariant orients it (see *The supporting results*).
- `LocPresentation.lean` — the geometry at a run.  Out of `1ᴺ` a codimension-one refinement is the
  merge or the atom at one cut (`eq_mergeOnes_or_atomOnes`, `Cut.exists_atomComp`), so the non-merge
  generators there are the `N−1` coordinate flips; `runMerge` is the merge into a shape and
  `existsUnique_W_ones`/`eq_runMerge` say it is the only one.  `conj` reads a refinement as a loop
  at the run, and it sees only the crossing permutation (`conj_congr`); `atomLoop_comm` and
  `atomLoop_braid` are then the two Artin relations, read off the codimension-two cell two atoms
  share (`exists_pairCell`, `exists_leg`).  Generation is `exists_atomWord`: since `conj_eq_runLoop`
  sends every refinement's loop to `runLoop` of its crossing permutation, and `runLoop_comp`
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
  `IsSegal K`.  `chPresentation_arrow` names the arrow a generator is: `Construction.fac` is an
  equality, so the descended fibre (`wedgeHomsDescend`) over `Q(op a)` is literally `⋁a ⟶ K`.
  The **vertex monoids do not follow**: `End` at a chain is a stabilizer
  (`endEquivStabilizer`), and `PosBraidAction` shows a stabilizer need not be generated by the
  generators sitting at its object — there the only generator that is a loop is the identity, while
  the loops are `PosPureBraid n`.
- `LiftLocalize.lean` — the same lift **with the merges inverted, over every `K`**.  A presentation of
  `(Ch Zbp)ᵒᵖ` whose picked 1-cells generate `(W Zbp).op` lifts to one of `(Ch K)ᵒᵖ` whose lifted
  picked 1-cells generate `(W K).op` (`chPicked`, `multiplicativeClosure_chPicked`): the class sees
  only the wedge map, and the fibration lifts a word of picked arrows letter by letter.  Adjoining a
  formal inverse to each is then a functor of `K` — `chLiftFunctor` / `chLocFunctor`, and at the bead
  cuts `chCutLocFunctor` with `chCutLocPresentation` — because a map of `K` re-indexes the elements
  and moves no base 1-cell (`mapElements_comp_chOfElements`, `chPresentation_E_naturality`).

*The two runs a chain spans, and the polygon of a degree-two shape.*
- `TopRefinement.lean` — **the two runs a chain spans**.  A refinement out of a run *is* a run of
  the target's wedge (`wedgeRun` / `ofWedgeRun`, inverse by `ofWedgeRun_wedgeRun`), and both runs are
  read off that bijection.  The least is the base merge out of the run on the chain's own events
  (`runMerge`), carried up by `W_iff_of_φ`: `bottomOf a := ofWedgeRun a ⟨𝟙^(dimSum a.dims), …⟩`, with
  `bottomRun`/`bottomHom` its two components and `bottomOf_eq_of_W` — any merge out of a run *is*
  that pair — the single source of `bottomRun_self`, `bottomRun_eq_of_W` and `eq_bottomRun_of_W`.
  The greatest is that merge's **complement** — `topOf e := ofWedgeRun e (wedgeRun (bottomHom e)).compl`.  That the
  greatest refinement never merges is then `Run.compl_ne`, not a length count (`not_W_topOf`).
  `IsTop` is stated the same way — an equation of pairs, equivalently `wedgeRun f = (wedgeRun
  (bottomHom e)).compl` (`isTop_iff_wedgeRun`).  The capacity enters only afterwards, as a theorem:
  the merge's wedge run crosses nothing (`cross_wedgeRun_bottomHom`), so the complement crosses the
  whole capacity (`permLen_runCross_topOf`), and the weak order being graded bead by bead makes that
  the *only* refinement of that length (`isTop_iff_permLen`) — the bridge by which a polygon's
  climb to its top is recognised as the greatest refinement.
- `RunAtoms.lean` — **the runs over a shape, and the polygon of a degree-two one**.  The run-arrows
  into a shape of `Ch Zbp` are a lower set of the right weak order (`ShapePerm`, `shapeLower`) with
  least element `shapeBot`, the merge; an ascent between two of them is an atom over the shape
  (`ascLeg`), and a refinement of shapes carries runs over its source to runs over its target by
  left translation (`pushPerm`, `pushPre`), length-additively.  Over a degree-two shape the runs are
  a polygon: `riseClimb` climbs it from the bottom alternately through its two junctions
  (`shapePair`), reading `RankTwo`'s alternating word as ascents, and the climbs through either
  junction first meet at the top (`riseElem_cox`).

*The paper's polygraph, at every `K` — the end of the through-line.*
- `PaperPoly.lean` — the polygraph **defined directly**, with no `∫F` vocabulary: 0-cells the runs,
  1-cells the degree-one **objects**, 2-cells the degree-two ones, a cell running from the run below
  its object (`bottomHom`) to the run its greatest refinement comes out of (`topOf`).  A run over a
  chain is a run-arrow into its shape (`ChPerm`, `shapeRun`), and an ascent between two of them is a
  degree-one object (`ascObj`, `ascGen`), so a climb spells a word (`ascPre`).  A 2-cell's two words
  are its polygon's two maximal climbs (`riseWord`): the source through the lower junction first
  (`loWord`), the target through the higher (`hiWord`), both ending at the greatest refinement
  (`topOf_fst_eq_riseElem`) — nothing chosen and no orientation to fix.
- `ChainWeb.lean` — **the runs over a chain carry Matsumoto's functor**.  The runs over `e` with
  their ascents read as `ascGen` are a web on the paper's cells (`chWeb`), and a refinement `q` is a
  map of webs by left translation (`chPush`), along which a climb evaluates to its image
  (`Web.eval_mapPath`, `Web.arrow_map`).  The pair chain placed under a polygon's foot
  (`exists_pairLeg`) pushes its own 2-cell onto that polygon, so every chain's web is Artin
  (`isArtin_chWeb`) — the hypothesis naming only the Coxeter order of the pair, never the species.
  `thetaAt u` is then the web arrow over the target from its bottom run up to the run the source is
  merged from (`cutTop`, the source's bottom run pushed along `u`), and `thetaAt_comp` is
  `Web.arrow_comp` read across a push.
- `DirectPresents.lean` — **`Ch(K)[W⁻¹]` is presented by the paper's cells, for every `K` and with
  no hypothesis on `K`** [RESULT]: `Paper.paperPresents`.  `Rconj u` conjugates a refinement by the
  two merges the localization inverts, built out of `Q` alone with no model of `Ch(K)[W⁻¹]` in
  between, and `lift_climb` is the geometric input — a climb telescopes into the conjugate of the
  refinement it performs (`runAt_climb`).  `paperE` interprets the cells, `Theta` reads a
  refinement as `thetaAt`, and the two are inverse, so `Theta` is a localization functor
  (`isLocalization_Theta`) and `paperE` the presentation.
- `PaperFunctor.lean` — **that polygraph is a functor of `K`, and its presentation is natural in
  `K`** [RESULT]: `Paper.polyFunctor` (with `polyFunctor.obj K = Paper.poly K`) and
  `Paper.paperPresentationIso`, the unit checked by `paperPresentationIso_id`. A map of `K` moves the
  object a cell carries and no shape, so a climb is the same term over `K'` and only each letter's
  classifying map moves (`mapPath_ascPre`, `riseWord_pushforward`).  The square `paperSquare` is
  then an *equality* of functors, and the isomorphism its `eqToIso`.

*…and at `Zbp` it is Artin's.*
- `ArtinDegreeZero.lean` — **the pairs of cuts, and Artin's relations.**  `AtomPair` (in `RunAtoms`)
  is the ordered pair a degree-two shape carries, `AtomPair.adj_or_apart` the two species, and
  `artinWords p` the two alternating words `artinRise lo hi (cox lo hi)` and
  `artinRise hi lo (cox hi lo)` — `RankTwo`'s `altProd` in the free monoid.  The species is read
  once (`artinWords_eq`: two letters apart, three adjacent), which makes them Artin's relation
  (`artinRel_artinWords`); `artinRelEquiv` matches the pairs to `artinBP.Rel N`.  Which cells carry the pairs is read once, in `PaperArtin`.
- `PaperArtin.lean` — **at `Zbp` the paper's polygraph is Artin's generators and relations, cell for
  cell and word for word** [RESULT].  `Paper.genArtinEquiv` matches the degree-one objects to
  `artinBP.S N` and `Paper.cellAtomPairEquiv` the degree-two ones to the pairs, while
  `Paper.src_eq_artinWords` / `tgt_eq_artinWords` say a 2-cell's two climbs read letter for letter as
  its pair's two words (`readAt_riseClimb`) — assembled into `Paper.paperArtinIso` against the data
  `artinBP`.  `fullBaseEquiv` is the localized base read off it with `artinBraids.braids`.
- `PaperAtoms.lean` — **what a presentation of `Ch(K)[W⁻¹]` cannot choose**.  A 2-cell's two words
  are as long as the Coxeter order of its pair (`length_src`, `length_tgt`) and differ in their last
  letter (`src_ne_tgt`), so word length is a grading vanishing only on the isomorphisms and read off
  no presentation; such a grading pins the cells below dimension two, and in dimension two makes
  every 2-cell a **critical pair** — two different words of at most three letters naming one arrow —
  which is `critPresents`.

*Runs and executions (`Concurrency/Executions/`).*
- `Runs.lean` — the **run presheaf** `Lines K : (Ch K)ᵒᵖ ⥤ Type`, `a ↦ Run a.dims`. A *run* is an
  all-edges cube chain: `Run K` is the full subcategory of `Ch K` cut out by `IsRun`, and it is
  discrete. Runs of a cube assemble into `runPresheaf : Boxᵒᵖ ⥤ Type`, so by
  `Precubical/Segal/PshExtMonoidal` a run of `⋁a` *is* a map `(⋁a).toPsh ⟶ runPresheaf`
  (`runPshEquiv`), and `runRestrict` along a wedge map is transpose–precompose–assemble.
  `chConcat` and its splitting restrict to runs (`runConcat`/`runSplit`), `isRun_chConcat` being
  the only content.  A run of `□ⁿ` *is* a permutation of its axes (`runPermEquiv`, firing order, `toFun` is `flatten`
  on the nose; `runWordEquiv` the step-to-axis reading; `wordRun`/`wordChain` the inverse map, the
  singleton-bead `blockChain`), and **restriction along a `Box` face is the rank map** of that
  order: `runFace g r = (runPermEquiv k).symm (Tuple.sort (runPermEquiv m r ∘ faceEmb g))⁻¹`, whose
  two functor laws are `Tuple.sort_perm` and `Tuple.sort_congr`. `Run.equivEdgeChain` is the
  all-edges cut of `chCubes`, sealed `irreducible` — the route a geometric statement about a run
  takes to reach `Run K`.
- `RunSegal.lean` — **the Segal decomposition of a linearization**: a run performs bead `i` at
  exactly the prefix-sum interval, in that bead's own order (`coordMap_fst` as an *iff*,
  `coordFlip_run_concat`), so `runProj` gets a computational characterization and the sealed
  `runSplit`/`runSegalProd` stay sealed.
- `RunPerm.lean` — **running a run backwards**. `Run.rev` is the geometric reversal (`Box.rev` on
  every bead, beads in reverse order, through `Run.equivEdgeChain`), and what it does to the
  bijection is a theorem: `runPermEquiv n ρ.rev = Fin.revPerm * runPermEquiv n ρ`
  (`runPermEquiv_rev`; `runWordEquiv_rev` and `rev_wordRun` are the same on the other readings). `Box.rev` leaves a cube free exactly where it was, so a bead keeps the **axis**
  it flips and only the **step** changes — `beadOf_rev`, chased on the flat cube list, where
  `(Box.sign c.2).val q` does not depend on `c.1` and no shape transport appears. Reversal survives
  restriction (`Run.rev_restrict`) because restriction is a rank map and `Fin.rev` is antitone.
- `Complement.lean` — **the complementary run**: `Run.compl` reverses a run of `⋁d` inside every
  bead, by post-composing its classifier with `revRunPsh : runPresheaf ⟶ runPresheaf`.
  An involution on the nose, so it pins the **greatest**
  refinement of a chain out of a run as the complement of that chain's merge — no maximality
  argument, no choice. On a bead cut into `k` pieces it is the longest element of `Sₖ`.
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
  cube's extremal vertices (`Hbp_vertexEnd`), so bead-wise symmetries glue (`symOf`), every
  decorated chain factors uniquely as one followed by an ordinary chain (`symOf_chainOf`), and a
  morphism is carried across by the *twist* `φ ↦ chainOf (φ ≫ symOf ρ)`, whose functoriality is
  associativity plus that uniqueness. The run and the order are inverse to each other
  (`symCell`); `SHom.sortPerm_sortFace_inv` is what makes that consistent, and it is the only
  place blocks are looked at.  Both legs restrict bead by bead through *any* factorization of a
  source bead through a target bead (`beadCell_of_factor`, `beadCell_comp_of_factor`), of which
  `blockIdx`/`blockFace` is the canonical one; that is what
  `runPermEquiv_beadCell_comp`/`runPermEquiv_beadCell_twistRun` are stated at.
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
  *inverse* order and inverts (`runPermEquiv_beadCell_twistRun`) while the plain one sorts the order
  (`runPermEquiv_beadCell_comp`) — and sorting does not commute with inverting.  The tower
  `Ch (Hbp K) ⥤ Ch (Hbp Zbp) ⥤ Ch Zbp` — `pushforward` along `Hbp.map (isTerminalZbp.from K)`,
  then `toChZ` — is what survives.
  `onesHomEquivRunClassifier` — the maps out of the all-edges chain are the runs of the target,
  so the simples are the cells of `Hbp Zbp`, with no `Perm` in the
  description; the two sides have opposite variance, so it is a bijection of fibres only.
  Then the **collapse and its failure** [RESULT]: an edge of `Hbp Zbp` carries no order, so
  `subsingleton_homHbpZbp_of_ones` makes `Hom(⋁𝟙ⁿ, Hbp Zbp)` a point; the base merge out of the
  all-edges chain therefore lifts with nothing to check (`exists_W_from_ones` — the
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
  fibre, crossing nothing) makes it bijective everywhere (`bijective_fibrePerm`).
  `chToAction` is that data as a functor to `PosBraidAction n`, and `chToAction_obj_surjective`
  says the runs exhaust the orderings.
- `HPresentation.lean` — `wallCrossLoc`, the wall span read in the localization with its far leg
  inverted: a codimension-one chain lies *below* both chambers it separates.

*The Salvetti comparison (`Concurrency/Salvetti/`).*
- `ChainBraidFace.lean` — the **base comparison** `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)` and
  `chFaceCatEquiv : (Ch □ⁿ)ᵒᵖ ≌ Face`: a chain's face is the covector of its ordered partition
  (`chFace`), and the face order is the coarsening of partitions (`chFace_faceLE_iff`), so
  `Grading/OrderedPartition`'s `blockChain` and `reflectHom` are the **computable** converse.
- `EventBraid.lean` — the **run order** `runOrd`, the crossing permutation `permOf`, and
  `permOf_noDoubleCross` [RESULT]. Events are ordered by the run linearizing the execution, *not*
  by the run-free `pos` — ordering by `pos` makes `permOf` a function of the chain morphism alone,
  which collapses the label. The two leaves are `runOrd_within_flatten` (from `RunSegal`) and
  `flatten_restrict_lt_iff` (from `Runs`). Then `braidFunctor` and
  `ConcPos K = proj K ⋙ braidFunctor`.
- `SalExec.lean` — the two halves `salEquiv`/`hbpEquiv` is fed at `□ⁿ`, giving
  `Ch⋆ (□ⁿ) ≌ Sal (braidCOM n)` [RESULT]. `wordTopeEquiv` reads topes as run words (a tope's chain has injective `beadOf`, hence one
  direction per bead); `linesTopeIso` bundles that fibrewise, and its naturality square is
  `wordTope_runWord` — the wall crossing `T' = X' ⊙ T`, whose two branches are the arrow rule's
  two clauses.
- `SalCompare.lean` — **`L` models `K`** [RESULT]: a `Models L K` is an equivalence of *bases*
  `(Ch K)ᵒᵖ ≌ Face L` together with `Lines K ≅ base.functor ⋙ salFunctor L`, and that one datum gives
  `salEquiv : Ch⋆ K ≌ Sal L`, both sides being categories of elements (`salElementsEquiv`).
  `hbpEquiv` chains it with `chSymChStarEquiv` for `Ch (Hbp K) ≌ (Sal L)ᵒᵖ` — "`H` is the
  complexification".
- `SalBraid.lean` — a cell's tope *is* a chamber, so a cell names the word that chamber spells
  (`cellWord`, pinned by the tope at `cellWord_of_tope`), and a Salvetti edge names the reordering
  between two words — the crossing cocycle `topeCross`.
- `WallCrossing.lean` — the presentation said in **arrangement** language. A chamber is a run of the
  decorated cube; its `n-1` walls are its adjacent rank pairs, each carrying two codimension-one
  cells — `wallStay` (crossing permutation `1`: a merge) and `wallCross` (crossing permutation
  `adjT k`: an atom). `card_wallsThrough` says codimension *counts* walls, so a codimension-two cell
  lies on exactly two: consecutive (braid) or separated (commutation). An atom is **not** an arrow
  between chambers — a wall cell lies below both chambers it separates, so `σₖ` appears only after
  inverting one leg of the span.
- `CrossCompare.lean` — **the two crossing permutations of a decorated chain morphism agree**:
  `cellWord_hbpBraidSalEquiv` says the Salvetti tope records `fibrePerm`, the step at which each
  axis is performed, so `crossPerm_eq_topeCross` — both `ChainCat.crossPerm` (the flattening
  order) and `topeCross` (the arrangement's) are that function's coboundary.  Hence
  `W_wallLegFlip`: the leg of a wall span that crosses no wall is a bead merge.

### `Testing/` — the fast execution model, and computing `π₁`

Strictly downstream: nothing outside `Testing/` imports it, and it is the only part of the tree
`lake build CubeChains` does not build.

An execution of `□ⁿ` is a **linear order on the `n` directions plus a composition of `n`** — the run
linearizes each bead, and beads are consecutive blocks of that word. So `Ch⋆(□ⁿ)` has `n!·2^{n−1}`
objects (192 for `n = 4`), enumerable in output-linear time.

One model and one engine, deliberately: a harness earns its keep by being fast, not by being
general, and a second model of `Ch⋆` here is a model with no equivalence proved to either of the two
that exist.

- `Cells.lean` — cells of `□ⁿ` as sign vectors; `SubCube n` (a face-closed `Bool` predicate),
  `full`/`boundary`/`skeleton`, `beadCell`. `(cube n).init` is `some false`, so `some false` = a
  direction not yet performed.
- `FastExec.lean` — `FExec n` (nonempty blocks whose concatenation is a permutation), `Refines`
  (decidable), `fperm`, the DFS `execs` with `mem_execs_iff` (sound **and** complete), `buildPoset`.
- `FastEquiv.lean` — the bridge `fexecChStarEquiv : FExec n ≃ Ch⋆ (□ⁿ)` between the enumerable
  block-list model and `Concurrency/Executions/ExecData`, plus `fperm_eq_stepPerm`.

## Where do I find…?

- **the box / precubical-set definition** → `Machinery/Cube/Box.lean`
- **cube Yoneda `(□ⁿ ⟶ K) ≃ K.cells n`** → `Precubical/Basic/Representable.lean` (`cubeRepr`)
- **`vertex₀/₁`, `BPSet.Hom`, `cubeMap`/`faceMap`** → `Precubical/Basic/Bipointed.lean`
- **the wedge / serial wedge / `wedge2` pushout** → `Precubical/Wedge/Wedge.lean` (+
  `Precubical/Chains/WedgeMap.lean`)
- **`NonSelfLinked` / `AdmitsAltitude` / altitude lemmas** → `Precubical/Basic/Altitude.lean`;
  the cube's grading and chain arithmetic → `Precubical/Chains/Altitude.lean`
- **a chain is a monomorphism / bead data as a refinement** → `Precubical/Chains/Embedding.lean`
  (`descent_mono`, `chain_mono`, `homOfBeads`)
- **the geometric tensor `⊗ᵍ`, computably** → `Precubical/Wedge/GeoTensor/` (`BP.lean` for the
  `BPSet` version and `cubeTensorIsoBP`)
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
- **a chain of `□ⁿ` as an ordered set partition (`beadOf`, `blockChain`, `reflectHom`)** →
  `Concurrency/Grading/OrderedPartition.lean`; as a braid face →
  `Concurrency/Salvetti/ChainBraidFace.lean` (`chFaceEquiv`, `chFaceCatEquiv`)
- **the run order `runOrd`, `permOf`, no-double-crossing** →
  `Concurrency/Salvetti/EventBraid.lean`; its two inputs are `Concurrency/Executions/RunSegal.lean`
  (Segal) and `Concurrency/Executions/Runs.lean` (face restriction)
- **`ConcPos` itself** → `Concurrency/Salvetti/EventBraid.lean`
- **the run-free crossing permutation of `Ch K` (wedge maps only)** →
  `Concurrency/Grading/WedgeBraid.lean` (`crossPerm`, `crossPerm_chConcat`), read off the chain in
  `Concurrency/Grading/ChainHom.lean` (`flatten`, `crossPerm_flatten`); its additivity
  (`permLen_crossPerm_comp`) in `Concurrency/Grading/Coarser.lean`
- **the two staircases `□m ∨ □n ⟶ □(m+n)` and their coordinate blocks** →
  `Precubical/Wedge/CubeMerge.lean` (`cubeMerge`/`cubeReorder`, `Box.headFace`/`Box.tailFace`,
  `faceEmb_cubeMerge_*`, `faceEmb_cubeReorder_*`); as the wedge-to-tensor comparisons →
  `Precubical/Wedge/WedgeTensor.lean` (`cubeMerge_eq`)
- **which permutations a hom-set of `Ch Zbp` realises** → `Concurrency/Grading/ChainHom.lean`
  (`exists_chain_flatten`, `exists_crossPerm_of_blocks`), and
  `Concurrency/Merge/Atom.lean` (`exists_crossPerm_single`)
- **when a refinement is a bead merge** → `Concurrency/Merge/MergeClass.lean` (`merge`, `W`,
  `W_le_iff`), `Concurrency/Merge/MergeBraid.lean` (`crossPerm_eq_one_of_W`),
  `Concurrency/Merge/MergeGenerate.lean` (`W_iff_crossPerm_eq_one`, `merge_iff`, `Coarser`)
- **when `K` inverts the bead merges, as a condition on cells** →
  `Concurrency/Merge/SegalCondition.lean` (`IsSegal`, `faceComparison`,
  `isSegal_iff_existsUnique`), read on chains in `Concurrency/Presentation/ElementsFibration.lean`
  (`InvertsMerges`, `isSegal_iff_invertsMerges_repoint`); for `Hbp □ⁿ` →
  `Concurrency/Complexification/HSegal.lean` (`sbox_existsUnique`, `isSegal_H_cube`)
- **when a hom-set of `Ch Zbp` is nonempty, and how a refinement factors** →
  `Concurrency/Grading/Boundaries.lean` (`boundaries`), `Concurrency/Grading/ChainHom.lean`
  (`nonempty_hom_iff`), `Concurrency/Grading/Coarser.lean`
  (`exists_factor`, `factor_ext`, `exists_crossPerm_mid`)
- **the Salvetti comparison** → `Concurrency/Salvetti/SalCompare.lean` (`salEquiv`/`hbpEquiv`), fed at `□ⁿ`
  from `SalExec.lean` (`chFaceCatEquiv`, `linesTopeIso`)
- **an execution as a word + composition, and enumerating them** → `Testing/Enumerate/FastExec.lean`
  (`FExec`, `execs`, `mem_execs_iff`), identified with `Ch⋆` in `Testing/Enumerate/FastEquiv.lean`
- **restricting a run along a face** → `Concurrency/Executions/Runs.lean` (`runFace`, `runPresheaf`)
- **running a chain or a run backwards (the complement)** → `Machinery/Cube/Reversal.lean`
  (`flipCell`, `Box.rev`), `Precubical/Chains/Reversal.lean` (`revCubeChain`, `EdgeChain.rev`),
  `Concurrency/Executions/Complement.lean` (`Run.compl`); the greatest refinement of a chain out of
  a run *is* the complement of the merge below it
  (`Concurrency/Presentation/TopRefinement.lean`, `topOf`)
- **the braid group itself (Garside germ), `permHom`, `PureBraid`** → `Machinery/Braid/Germ.lean`
- **the Artin presentation** → `Machinery/Braid/Artin.lean`; **Matsumoto's theorem** →
  `Machinery/Braid/Matsumoto.lean`
- **the braid groupoid `FullBraid` (the target of `ConcPos`)** → `Machinery/Graded.lean`
- **what a presentation *is* (`Polygraph`, `Presents`, `ofDesc`, `Presents.ofThin`)** →
  `Machinery/Presentation/Basic.lean`; comparing two of them → `.../Comparison.lean`
- **the input `BraidData` / `BraidPresentation`, `artinBP`, `germBP` / `artinBraids`** →
  `Concurrency/Presentation/BasePresentation.lean`
- **the runs over a shape, as one permutation per bead** → `Concurrency/Presentation/BeadOrder.lean`
  (`wedgeOrder`, `blockSum`, `tupleRun`); the presentation's functoriality in `K` →
  `.../LocFunctor.lean` (`chLocMap`)
- **the same category presented from the cut presentation instead, by inverting the merges** →
  `Concurrency/Presentation/LiftLocalize.lean` (`chCutLocFunctor`, `chCutLocPresentation`), on
  `Machinery/Presentation/Localize.lean` (`invPoly`, `presentsLocalization`) read at the bead cuts
  in `.../CutPresentation.lean` (`Cut.mergeGen`, `zCutLocPresentation`)
- **the runs over a chain, their polygons, and Matsumoto's functor on them** →
  `Concurrency/Presentation/RunAtoms.lean` (`shapeLower`, `ascLeg`, `pushPerm`, `riseClimb`),
  `.../PaperPoly.lean` (`ascGen`, `riseWord`, `Paper.poly`) and `.../ChainWeb.lean` (`chWeb`,
  `isArtin_chWeb`, `thetaAt`); the degree-zero cells read against Artin's →
  `.../ArtinDegreeZero.lean` (`artinWords`, `artinRelEquiv`) and `.../PaperArtin.lean`
  (`Paper.genArtinEquiv`, `Paper.relArtinEquiv`, `Paper.paperArtinIso`)
- **abstract rewriting — Newman, normal forms, and when an orientation presents** →
  `Machinery/Rewriting/Newman.lean`, `.../Presentation.lean`
- **the Segal/descent route (the special case)** → `Concurrency/Presentation/HAction.lean`
  (`chLocEquivElements`, `hLocPresentation`, `hLocActionPresentation`)

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
  `ᵒᵖ`s in the presentation chain are the composition order, not a choice.
- **Trust `lake build`, not the IDE** (cross-file diagnostics are stale).
- **Foundational machinery proves the strongest `BPSet`-level statement available.** Never weaken a
  definition or lemma to the presheaf level (`.toPsh ⟶ .toPsh`) so a tactic will fire; callers
  project with `.hom`. `BPSet.Hom` bundles `app_init`/`app_final`, so `BPSet`-level statements carry
  the endpoint conditions for free and keep `⊗`/`▷`/`◁`/`α_`/`λ_`/`ρ_` and `monoidal` applicable.
  When a proof wants to track endpoint data beside a map, **re-point the target** (`repoint`)
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

- `DESIGN.md` — the conventions/decisions log (precubical identities, universe policy, the
  topos+concrete architecture), with PZ/Z paper references.
- Per-area: `Machinery/Arrangement/README.md`, `Concurrency/README.md` + `Concurrency/BRAID.md`
  (why braids).
- `/orient` skill — fast session bootstrap (build, mathlib-reuse table, gotchas).
- Papers: PZ = arXiv:2103.05336, Z = arXiv:1901.05206.
