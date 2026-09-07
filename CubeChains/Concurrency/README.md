# Concurrency — executions, and `Sal(braidCOM n) ≌ Ch⋆(□ⁿ)`

The executions of a cube chain, the braid they grade, and the identification of the execution
category of `□ⁿ` with the Salvetti poset of the braid arrangement. Builds on `Machinery/Arrangement/`
and `Precubical/Chains/`; `Concurrency/BRAID.md` says why braids are here at all.

## What an execution is

A **run** is a cube chain every bead of which is an edge — a linearization. `Run K` is the full
subcategory of `Ch K` cut out by `IsRun`, and it is **discrete**: `Ch K` is skeletal and an
all-edges chain's bead count *is* its `dimSum`, which every chain map preserves.

Runs of a cube assemble into a presheaf `runPresheaf : Boxᵒᵖ ⥤ Type`, so a run of `⋁a` *is* a map
`(⋁a).toPsh ⟶ runPresheaf` (`runPshEquiv`) — the contravariant lift of `Precubical/Segal/PshExtMonoidal`.
That is what makes the run presheaf

> `Lines K : (Ch K)ᵒᵖ ⥤ Type`,  `a ↦ Run a.dims`

functorial without a bespoke restriction: `runRestrict` is transpose–precompose–assemble, and its
`_id`/`_comp` laws are the lift's. An **execution** is an element of it:

> `Ch⋆ K := (Lines K).Elements` — a chain together with a run linearizing it.

`RunWedge` is the `K`-free version (a wedge with a chosen run); `proj K : Ch⋆ K ⥤ RunWedge` forgets
the map to `K`.

## The three theorems

```
   Ch (□ⁿ)  ──── chFaceEquiv ────≃──→  Face (braidCOM n)         (ChainBraidFace)
      ▲                                       ▲
      │ chain of an execution                 │ face of a cell
      │                                       │
  Ch⋆ (□ⁿ)  ──── salCompare ──────≌──→  Sal (braidCOM n)          (SalExec, SalCompare)
      │
      │ ConcPos = proj ⋙ braidFunctor
      ▼
  FullBraid
```

1. **The base.** `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)` — a chain of `□ⁿ` *is* an ordered set
   partition of `Fin n`, namely `beadOf : Fin n → Fin L`, the bead each coordinate flips. Both
   halves are explicit: `coordFlip` (`Concurrency/Grading/CoordFunctor`) gives the bijection, `blockMap`
   (`Machinery/Arrangement/BraidCovector`) the covector round trip, and `reflectHom` reconstructs the
   morphism `a ⟶ b` from `chFace b ⊑ chFace a`.
2. **The cells.** `salCompare chFaceCatEquiv linesTopeIso : Ch⋆ (□ⁿ) ≌ Sal (braidCOM n)` — both
   sides are categories of elements, so the comparison splits into a base and a presheaf over it.
   A Salvetti cell is a face below a
   tope; a tope's chain has injective `beadOf`, hence one direction per bead, hence *is* a run word.
   So `X ⊑ T` is exactly `ExecData`'s condition, and the wall crossing `T' = X' ⊙ T` is the **arrow
   rule** of `RunWord`: across beads the finer execution runs in its own bead order
   (`runWord_group`), inside a bead it inherits the coarser one's (`runWord_within`).
3. **The grading.** `permOf_noDoubleCross` — crossing permutations are length-additive, so
   `braidFunctor : RunWedge ⥤ FullBraid` is a functor and `ConcPos K = proj K ⋙ braidFunctor` is
   well defined. The Salvetti side has its own crossing cocycle, `topeCross` with `topeCross_comp`,
   but length-additivity of `topeCross` is not proved, so there is no second grading on `Ch⋆` and
   nothing compares the two there. What *is* proved is one step up: `crossPerm_eq_topeCross`
   identifies the two orders on `Ch (Hbp □ⁿ)`.

⚠ **`permOf` must order events by the run.** Ordering them by the run-free flattening
`pos = finSigmaFinEquiv` makes `permOf` a function of the chain morphism alone, and a label that
depends on the morphism alone cannot see a braid, the loops being moves of the run. The run order
is `runOrd`.

That is a statement about `Ch⋆`, where the run is the datum a loop moves. `Concurrency/Grading/WedgeBraid` grades
`Ch K` — which carries no run — by `pos`, and there depending on the wedge map alone is the point.

## Files

- `Runs.lean` — `Run`, `IsRun`, `runPresheaf`, `runPshEquiv`, `runRestrict`, `Lines`, `RunWedge`;
  `runFunctor` lax monoidal by restricting `chFunctor`'s structure (`isRun_chConcat`).
- `Elements.lean` — the `Elements` scaffolding for `Ch⋆`, plus the thinness of `Ch (□ⁿ)`.
- `RunPerm.lean` — a run of `□ⁿ` *is* a permutation of its axes: `runPermEquiv`, with `flatten` at the run
  as its forward map, so downstream still computes.
- `ChStarProduct.lean` — `chStarProdEquiv : Ch⋆ K ≌ (Ch (K.prod runBp))ᵒᵖ`; a complexified chain
  is a chain in a product.
- `EventPerm.lean` — the event relabelling `eventEquiv f = coordMapEquiv (wedgeMap f)` and
  `beadEvent`/`pos` live in `Concurrency/Grading/CoordFunctor`.
- `RunSegal.lean` — the Segal decomposition of a linearization: a run performs bead `i` at the
  prefix-sum interval, in that bead's own order.
- `RunRestrict.lean` — restricting a run along a face is a `List.filterMap`, which preserves the
  step order; `flatten_restrict{,_lt_iff,_rank}`.
- `EventBraid.lean` — `runOrd`, `permOf`, `permOf_noDoubleCross`, `braidFunctor`, `ConcPos`.
- `ChainBraidFace.lean` — `chFaceEquiv`, `chFaceCatEquiv`, `beadOf`, `ofBlockMap`, `reflectHom`.
- `RunWord.lean` — `runWord`, `stepPerm_eq`, and the arrow rule `runWord_group`/`runWord_within`.
- `ExecData.lean` — `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n`; `ofWord` computes, `ext_runWord` is
  completeness.
- `SalExec.lean` — the two halves `salCompare` is fed at `□ⁿ`: `wordTope`, the tope of a run word,
  and `linesTopeIso`, the runs of a chain as the topes above its face.
- `SalCompare.lean` — `salCompare`, the base-plus-presheaf comparison, and `hbpSalEquiv`.
- `SalvettiConstruction.lean` — `topeRank`, `topePerm` (a tope read as a linear order) and
  `topeCross` with its cocycle law `topeCross_comp`.
- `SalBraid.lean` — `topePerm_eq`: a cell's permutation is its run word inverted, `topeRank`
  counting predecessors (`topeRank_wordTope`).
- `WallCrossing.lean` — the dictionary across `hbpBraidSalEquiv`: `wallStay`/`wallCross` are the two
  cells over a wall, of crossing permutation `1` and `adjT k`; `card_wallsThrough` says codimension
  counts walls, so codimension two is two walls — consecutive (braid) or separated (commutation).
- `CrossCompare.lean` — `crossPerm_eq_topeCross`: the arrangement's order and the flattening order
  label a decorated chain morphism alike, both being `fibrePerm`'s coboundary. Hence
  `W_wallLegFlip` — the far leg of a wall span is a bead merge.

## References
- Bandelt–Chepoi–Knauer, *COMs: Complexes of Oriented Matroids* (arXiv:1507.06111).
- Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional OMs* (arXiv:2507.06365) — the
  source of the `Sal` definition.
