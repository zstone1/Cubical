# FinalBraid — the braid Salvetti complex from cube chains

**Goal.** Build the braid Salvetti complex intrinsically from cube chains as
`Sal n := (Lines (□ⁿ)).Elements`, the category of elements of a chamber presheaf, and show
it splits over wedges.

Everything here depends **only** on `Chains/`, `Foundations/`, and mathlib.
⛔ **Never read/import `CubeChains/FinalPrecubical/`** — it is deprecated and off-limits
(blocked by a settings `deny` + `.ignore`).

## The objects

- `□ⁿ := BPSet.cube n`, `Ch(□ⁿ) := ChainCat.Obj (cube n)`, the (unconditional) cube-chain
  category: a morphism `x ⟶ y` means `x` subdivides `y`.
- A **chamber** of `□ᵈ` (`Chamber d`) is a finest chain of the Boolean lattice `{0,1}ᵈ`,
  encoded as a strict total order on the `d` coordinate directions (the order they flip
  `0 → 1`); there are `d!` of them.
- **Lines** (the chamber presheaf) `Lines K : (ChainCat.Obj K)ᵒᵖ ⥤ Type`,
  `Lines x = ∏_{beads b of x} Cham(□^{dim b})`; on `f : x ⟶ y` (`x` finer) it restricts each
  `y`-bead's chamber to the `x`-sub-beads by pulling back along the block data of `f`.
- **Sal** `n := (Lines (□ⁿ)).Elements`: objects `(x, C)` = a chain with a chamber refining it;
  the induced order is the Salvetti/Paris order. It is a poset (thin).

## What the folder contains

- `Lines.lean` — `Chamber` and the `Lines` presheaf (chambers + restriction along
  `blockIdx`/`blockFace`).
- `Elements.lean` — reuse/scaffolding: `cubeChainRefineEquiv n` (`Ch(□ⁿ) ≌ RefineObj(□ⁿ)` via
  `equivWedgeCat`), thinness of the cube categories, and general `Elements`/Grothendieck API
  (`Functor.elements_isThin`, `mapEquivalence`, `pre`/`preEquivalence`).
- `Sal.lean` — the definition `Sal n` and its projection `salToChain`.
- `LinesWedge.lean` — the external product `extProd`/`extProdEquiv` and the wedge → product
  theorem `linesWedgeEquiv : (Lines (wedge2 P Q)).Elements ≌ (Lines P).Elements × (Lines Q).Elements`.

## Reused (not rebuilt)

`Ch(□ⁿ) ≌ RefineObj(□ⁿ)` = `CubeChain.equivWedgeCat` (`Chains/Correspondence.lean`) at
`cube_nonSelfLinked` + `cube_admitsAltitude`; the bead / cube-list decomposition =
`Chains/WedgeMap.lean`; the category of elements = mathlib `CategoryTheory.Elements`.
