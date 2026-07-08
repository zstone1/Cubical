# FinalBraid — the braid Salvetti complex from cube chains

**Goal.** Give the Salvetti complex `Sal` its authoritative definition (the face poset of a
complex of oriented matroids), assemble the braid arrangement as a COM, and compare it with the
intrinsic cube-chain model:

> `Sal (braidCOM n) ≌ Int(Lines(□ⁿ))`   where   `Int(Lines(□ⁿ)) := (Lines □ⁿ).Elements`.

Everything here depends **only** on `Chains/`, `Foundations/`, and mathlib.
⛔ **Never read/import `CubeChains/FinalPrecubical/`** — it is deprecated and off-limits
(blocked by a settings `deny` + `.ignore`).

## The definition of `Sal`

`Sal` is the **Salvetti face poset of a COM** (`Sal.lean`), following Dorpalen-Barry–Dugger–Proudfoot
(*Salvetti complexes for conditional oriented matroids*, arXiv:2507.06365):

- a **COM** `L : COM E` (`COM.lean`) is a covector set closed under face symmetry (FS) and strong
  elimination (SE); its **topes** are the maximal covectors.
- `Sal L` has cells `(X, T)` — a covector (face) `X` and a tope `T` with `X ⊑ T` — ordered by
  `(X, T) ≤ (X', T') ⟺ X ⊑ X' ∧ T' = comp X' T`.  This is a `PartialOrder`, so `Sal L` is a thin
  category and `salNerve L := nerve (Sal L)` is its Salvetti simplicial set.

## The intrinsic cube-chain model `Int(Lines)`

- `□ⁿ := BPSet.cube n`, `Ch(□ⁿ) := ChainCat.Obj (cube n)`, the (unconditional) cube-chain
  category: a morphism `x ⟶ y` means `x` subdivides `y`.
- A **chamber** of `□ᵈ` (`Chamber d`) is a finest chain of the Boolean lattice `{0,1}ᵈ`,
  encoded as a strict total order on the `d` coordinate directions (the order they flip
  `0 → 1`); there are `d!` of them.
- **Lines** (the chamber presheaf) `Lines K : (ChainCat.Obj K)ᵒᵖ ⥤ Type`,
  `Lines x = ∏_{beads b of x} Cham(□^{dim b})`; on `f : x ⟶ y` (`x` finer) it restricts each
  `y`-bead's chamber to the `x`-sub-beads by pulling back along the block data of `f`.
- `Int(Lines(□ⁿ)) := (Lines □ⁿ).Elements`: objects `(x, C)` = a chain with a chamber refining it,
  in the induced Salvetti/Paris order (a thin poset).

## What the folder contains

- `COM.lean` — sign vectors (`SignVec`, `comp`/`sep`/`faceLE`), the `COM` axioms, topes.
- `Sal.lean` — **the definition of `Sal`**: the Salvetti face poset of a COM + `salNerve`.
- `Braid.lean` — the braid arrangement `braidCOM n : COM (pairs of Fin n)` (an oriented matroid).
- `Lines.lean` — `Chamber` and the `Lines` presheaf (chambers + restriction along
  `blockIdx`/`blockFace`).
- `Elements.lean` — reuse/scaffolding: `cubeChainRefineEquiv n` (`Ch(□ⁿ) ≌ RefineObj(□ⁿ)` via
  `equivWedgeCat`), thinness of the cube categories, and general `Elements`/Grothendieck API
  (`Functor.elements_isThin`, `mapEquivalence`, `pre`/`preEquivalence`).
- `LinesWedge.lean` — the external product `extProd`/`extProdEquiv` and the wedge → product
  theorem `linesWedgeEquiv : (Lines (wedge2 P Q)).Elements ≌ (Lines P).Elements × (Lines Q).Elements`.

## Reused (not rebuilt)

`Ch(□ⁿ) ≌ RefineObj(□ⁿ)` = `CubeChain.equivWedgeCat` (`Chains/Correspondence.lean`) at
`cube_nonSelfLinked` + `cube_admitsAltitude`; the bead / cube-list decomposition =
`Chains/WedgeMap.lean`; the category of elements = mathlib `CategoryTheory.Elements`; the
Salvetti poset definition = Dorpalen-Barry–Dugger–Proudfoot (arXiv:2507.06365).
