# Salvetti — `Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`

Identifies the Salvetti complex of the braid arrangement with the intrinsic cube-chain model,
where `Int(Lines K) := (Lines K).Elements`. Builds on `Arrangements/` and `Chains/`.

## Headline theorems
- `BraidIso.braidSalEquiv n : Sal(braidCOM n) ≌ (Lines(cube n)).Elements`.
- `SalWedge.braidSerialSalEquiv` — the serial-wedge generalization
  `Sal(⊕ᵢ braidCOM dᵢ) ≌ Int(Lines(serialWedge dims))`, by recursion from `braidSalEquiv 0`
  and the wedge splitting `salWedgeEquiv`.

## The pieces
- `Lines.lean` — the chamber presheaf `Lines K : (ChainCat.Obj K)ᵒᵖ ⥤ Type`: a chain ↦ one
  chamber (strict total order on directions) per bead; a chain map ↦ restriction along the block
  data of `Chains/BlockDecomp`.
- `Elements.lean` — category-of-elements bookkeeping (`pre`/`preEquivalence`, thinness) and
  `Ch(□ⁿ) ≌ RefineObj(□ⁿ)`.
- `SalBraidPartition.lean`, `SalBraidChain.lean` — a cube chain of `□ⁿ` ⟺ an ordered set
  partition of `Fin n`.
- `SalBraidChamberRank.lean`, `SalBraidTope.lean` — chamber tuples on a chain ⟺ topes above its
  covector (via the lexicographic height `heightOf`).
- `BraidFaceEquiv.lean` — `Face(braidCOM n) ≌ (RefineObj □ⁿ)ᵒᵖ`.
- `WallCrossing.lean` — naturality of the tope ⟷ chamber correspondence (the Salvetti wall
  crossing).
- `LinesWedge.lean`, `SalWedge.lean` — the wedge / serial-wedge assembly.
