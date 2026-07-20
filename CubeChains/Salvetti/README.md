# Salvetti — `Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`

Identifies the Salvetti complex of the braid arrangement with the intrinsic cube-chain execution
model, where `Int(Lines K) := (Lines K).Elements`. Builds on `Arrangements/` and `Chains/`.

## Headline theorem
`BraidIso.braidSalEquiv n : Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`.

Both sides are categories of elements, so nothing is matched cell by cell. The comparison factors
into a **base** and a **presheaf** half, and the assembly is three `trans`es:

```
      (Ch □ⁿ)ᵒᵖ  ──── chFaceEquiv ────≌──→  Face(braidCOM n)
          │                                        │
    Lines(□ⁿ)  ────── salLinesIso ────≅──→  salFunctor(braidCOM n)
```

## Executions

An **execution** of a chain is a *run*: `Run k = (runObj (dimSum k) ⟶ ⋁k)`, a bi-pointed map out
of the all-edges wedge of the right total length — an interleaving of the beads' edges.

- `Runs.lean` — runs, their concatenation, their restriction, and the presheaf they assemble into.
  * `RunF : DimList ⥤ Type` — runs as a functor of the shape, lax monoidal *by inheritance*
    (`Foundations/HomMonoidal`), so `runAppend = μ RunF` arrives with all three coherence laws
    already stated in terms of the associator and unitors rather than `List.append` transports.
  * `Run.splitEquiv c rest : Run (c :: rest) ≃ Run [c] × Run rest` — **Segal for runs**: every run
    of a cons-shaped wedge *is* an append. This is what licenses bead-local reasoning; it rests on
    `splitWedgeMorphism` (`Chains/WedgeSplitHom`).
  * `runRestrict : (⋁a ⟶ ⋁b) → Run b → Run a`, in three layers — `runRestrictFace` (cube to cube,
    via `EdgeChain.restrict`), `runRestrictWedge` (recursion on the source list), `runRestrict`
    (recursion on the target list). The enabling law is `runRestrict_tensor`: restriction commutes
    with concatenation. `runRestrict_id` and `runRestrict_comp` fall out of it, and they are
    exactly what makes `Lines` a functor.
  * `Lines K : (Ch K)ᵒᵖ ⥤ Type`, `a ↦ Run a.dims` — the run presheaf. The variance is already
    right: a chain map `f : a ⟶ b` carries `f.φ : ⋁a.dims ⟶ ⋁b.dims`.
- `Elements.lean` — category-of-elements bookkeeping (`Functor.elements_isThin`, `mapEquivalence`,
  `pre`/`preInv`/`preEquivalenceComp`) plus the thinness of `Ch (□ⁿ)` that feeds it.

## The comparison

- `BraidPartition.lean` — a cube chain of `□ⁿ` **is** an ordered set partition of `Fin n`: bead
  `i`'s block is the coordinates it flips. Blocks are disjoint (a coordinate never un-flips) and
  cover (sizes sum to `n`, by altitude), giving `blockIndex` and `covectorHeight`; a refinement
  induces `⊑` on the `braidSign` covectors (`faceLE_of_chainRefine`).
- `BraidFace.lean` — the base half, `chFaceEquiv n : (Ch □ⁿ)ᵒᵖ ≌ Face(braidCOM n)`. Choice-free:
  `signHeight` computes a height function *from* a covector instead of extracting a `braidSign`
  witness out of a `Prop`-truncated membership, and `faceToCh` is written out rather than inverted
  through `EssSurj`.
- `SalLines.lean` — the objectwise bijection `runTopeEquiv a : Run a.dims ≃ TopeOver a`. A run of
  `a` traces out an all-edges chain (`runChain`) whose partition is a *linear* order on `Fin n`,
  hence a tope, lying above `a`'s covector because the run is a chain morphism onto `a`. The two
  round trips are mono-cancellation against `a.map`.
- `RunOrderFace.lean` — the bead-local half of naturality: restricting along a face is
  `List.filterMap`, which drops cubes but never reorders them, so block indices travel by `fmIdx`
  and a height comparison survives `runRestrictFace`.
- `WallCrossing.lean` — naturality itself (the Salvetti wall crossing), and `salLinesIso`, the
  presheaf half of the comparison. Gluing the bead-local half to the concatenation needs a height
  on *raw* cube lists rather than on chains, since the halves a junction cuts out are not chains:
  `flipIdx` is that total replacement and `flipIdx_eq_blockIndex` the bridge.
- `BraidIso.lean` — the assembly.

## References
- Bandelt–Chepoi–Knauer, *COMs: Complexes of Oriented Matroids* (arXiv:1507.06111).
- Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional OMs* (arXiv:2507.06365) — the
  source of the `Sal` definition.
