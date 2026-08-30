# Salvetti — executions, and `Sal(braidCOM n) ≌ Ch⋆(□ⁿ)`

The executions of a cube chain, the braid they grade, and the identification of the execution
category of `□ⁿ` with the Salvetti poset of the braid arrangement. Builds on `Arrangements/`
and `Chains/`; `Salvetti/BRAID.md` says why braids are here at all.

## What an execution is

A **run** is a cube chain every bead of which is an edge — a linearization. `Run K` is the full
subcategory of `Ch K` cut out by `IsRun`, and it is **discrete**: `Ch K` is skeletal and an
all-edges chain's bead count *is* its `dimSum`, which every chain map preserves.

Runs of a cube assemble into a presheaf `runPresheaf : Boxᵒᵖ ⥤ Type`, so a run of `⋁a` *is* a map
`(⋁a).toPsh ⟶ runPresheaf` (`runPshEquiv`) — the contravariant lift of `Chains/PshExtMonoidal`.
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
  Ch⋆ (□ⁿ)  ←─── braidSalEquiv ───≌───  Sal (braidCOM n)          (SalExec)
      │                                       │
      │ ConcPos = proj ⋙ braidFunctor         │ salvettiGrading
      ▼                                       ▼
  FullBraid  ←──── topeCross_eq_stepPerm ────→ SingleObj (Braid n) (SalBraid)
```

1. **The base.** `chFaceEquiv : Ch (□ⁿ) ≃ Face (braidCOM n)` — a chain of `□ⁿ` *is* an ordered set
   partition of `Fin n`, namely `beadOf : Fin n → Fin L`, the bead each coordinate flips. Both
   halves are explicit: `coordFlip` (`Chains/CoordFunctor`) gives the bijection, `blockMap`
   (`Arrangements/BraidCovector`) the covector round trip, and `reflectHom` reconstructs the
   morphism `a ⟶ b` from `chFace b ⊑ chFace a`.
2. **The cells.** `braidSalEquiv : Sal (braidCOM n) ≌ Ch⋆ (□ⁿ)`. A Salvetti cell is a face below a
   tope; a tope's chain has injective `beadOf`, hence one direction per bead, hence *is* a run word.
   So `X ⊑ T` is exactly `ExecData`'s condition, and the wall crossing `T' = X' ⊙ T` is the **arrow
   rule** of `RunWord`: across beads the finer execution runs in its own bead order
   (`runWord_group`), inside a bead it inherits the coarser one's (`runWord_within`).
3. **The grading.** `permOf_noDoubleCross` — crossing permutations are length-additive, so
   `braidFunctor : RunWedge ⥤ FullBraid` is a functor and `Conc K = FreeGroupoid.lift (ConcPos K)`
   is well defined. `topeCross_eq_stepPerm` transports it to the Salvetti side, so
   `salvettiGrading` is not a second proof.

⚠ **`permOf` must order events by the run.** Ordering them by the run-free flattening
`pos = finSigmaFinEquiv` makes `permOf` a function of the chain morphism alone, and
`subsingleton_hom_freeGroupoid_chOp` (`NoMonodromy`) says the base of `Ch⋆ (□ⁿ)` has no loops at
all — so such a label sees no braid. The run order is `runOrd`.

That is a statement about `Ch⋆`, where the run is the datum a loop moves. `Chains/WedgeBraid` grades
`Ch K` — which carries no run — by `pos`, and there depending on the wedge map alone is the point.

## Files

- `Runs.lean` — `Run`, `IsRun`, `runPresheaf`, `runPshEquiv`, `runRestrict`, `Lines`, `RunWedge`;
  `runFunctor` lax monoidal by restricting `chFunctor`'s structure (`isRun_chConcat`).
- `Elements.lean` — the `Elements` scaffolding for `Ch⋆`, plus the thinness of `Ch (□ⁿ)`.
- `Covering.lean` — `proj` and `π` are **discrete opfibrations**: a `Ch⋆` morphism is forced by a
  base morphism. Neither is a covering (the fibres vary).
- `EventPerm.lean` — the event relabelling `eventEquiv f = coordMapEquiv (wedgeMap f)` and
  `eventCore : RunWedge ⥤ Core Type`; `beadEvent`/`pos` live in `Chains/CoordFunctor`.
- `RunSegal.lean` — the Segal decomposition of a linearization: a run performs bead `i` at the
  prefix-sum interval, in that bead's own order.
- `RunRestrict.lean` — restricting a run along a face is a `List.filterMap`, which preserves the
  step order; `localStep_restrict{,_lt_iff,_rank}`.
- `EventBraid.lean` — `runOrd`, `permOf`, `permOf_noDoubleCross`, `braidFunctor`, `ConcPos`, `Conc`.
- `NoMonodromy.lean` — the coarsest chain is terminal in `Ch (□ⁿ)`, so both it and its opposite have
  codiscrete free groupoids: a run-blind grading has nothing to grade.
- `ChainBraidFace.lean` — `chFaceEquiv`, `chFaceCatEquiv`, `beadOf`, `ofBlockMap`, `reflectHom`.
- `RunWord.lean` — `runWord`, `stepPerm_eq`, and the arrow rule `runWord_group`/`runWord_within`.
- `ExecData.lean` — `execEquiv : Ch⋆ (□ⁿ) ≃ ExecData n`; `ofWord` computes, `ext_runWord` is
  completeness.
- `SalExec.lean` — `braidSalEquiv` as `salCompare` at `□ⁿ`; `wordTope`, the tope of a run word,
  and `linesTopeIso`, the runs of a chain as the topes above its face.
- `SalBraid.lean` — `topeCross_eq_stepPerm`, `stepPerm_noDoubleCross`, `salvettiGrading`,
  `salvettiConstruction`.
- `RunWedgeZ.lean` — `Ch⋆ Zbp ≌ RunWedge`: at the terminal object nothing labels the events, so the
  braid is the full one, not the pure part. Also `toChainZ`, decomplexification.
- `WallCrossing.lean` — the dictionary across `hbpBraidSalEquiv`: `wallStay`/`wallCross` are the two
  cells over a wall, of crossing permutation `1` and `adjT k`; `card_wallsThrough` says codimension
  counts walls, so codimension two is two walls — consecutive (braid) or separated (commutation).
- `CrossCompare.lean` — `crossPermAt_eq_topeCross`: the arrangement's order and the flattening order
  label a decorated chain morphism alike, both being `fibrePerm`'s coboundary. Hence
  `W_wallLegFlip` — the far leg of a wall span is a bead merge.

## References
- Bandelt–Chepoi–Knauer, *COMs: Complexes of Oriented Matroids* (arXiv:1507.06111).
- Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional OMs* (arXiv:2507.06365) — the
  source of the `Sal` definition.
