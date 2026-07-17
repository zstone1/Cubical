# Salvetti — `Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`

Identifies the Salvetti complex of the braid arrangement with the intrinsic cube-chain execution
model, where `Int(Lines K) := (Lines K).Elements`. Builds on `Arrangements/` and `Chains/`.

## Headline theorems
- `BraidIso.braidSalEquiv n : Sal(braidCOM n) ≌ Int(Lines(cube n))`.
- `SalWedge.braidSerialSalEquiv` — the serial-wedge generalization
  `Sal(⊕ᵢ braidCOM dᵢ) ≌ Int(Lines(serialWedge dims))`, by recursion from `braidSalEquiv 0` and the
  wedge splitting.

## The pieces

*Executions.*
- `Lines.lean` — the chamber presheaf `Lines K : (Ch K)ᵒᵖ ⥤ Type`: a chain ↦ one chamber (strict
  total order on directions) per bead; a chain map ↦ restriction along the block data of
  `Chains/BlockDecomp`.
- `Elements.lean` — category-of-elements bookkeeping (`pre`/`preEquivalence`, thinness) and
  `Ch(□ⁿ) ≌ RefineObj(□ⁿ)`.
- `ConcGroupoid.lean` — the concurrency braid groupoid `ConcGrpd K = FreeGroupoid (Int(Lines K))`
  and `PureBraid n`.
- `Normalize.lean` — normalization: `seqHom x : x ⟶ seqExec x` splits every bead into its edges in
  the order of the line, so `concGrpdRunEquiv : ConcGrpd K ≌ RunGrpd K` (the full subgroupoid on the
  runs). Unconditional in `K`.
- `LinesWedge.lean` — `linesWedgeEquiv : Int(Lines(P ∨ Q)) ≌ Int(Lines P) × Int(Lines Q)`.

*The comparison.*
- `SalBraidPartition.lean`, `SalBraidChain.lean` — a cube chain of `□ⁿ` ⟺ an ordered set partition
  of `Fin n`.
- `SalBraidChamberRank.lean`, `SalBraidTope.lean` — chamber tuples on a chain ⟺ topes above its
  covector (via the lexicographic height `heightOf`).
- `BraidFaceEquiv.lean` — `Face(braidCOM n) ≌ (RefineObj □ⁿ)ᵒᵖ`.
- `BraidSalObj.lean` — the object-map characterization of `braidSalEquiv`.
- `WallCrossing.lean` — naturality of the tope ⟷ chamber correspondence (the Salvetti wall crossing).
- `SalWedge.lean` — the serial-wedge assembly.
- `BraidReindex.lean` — the `Sₙ` reorientation action on the Salvetti category (`salReindex σ`).
- `FZSurj.lean` — essential surjectivity of `FZ = braidSalEquiv ⋙ concToZ` onto the `nEvents = n`
  stratum (feeds the terminal descent in `Braid/`).

## References
- Bandelt–Chepoi–Knauer, *COMs: Complexes of Oriented Matroids* (arXiv:1507.06111).
- Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional OMs* (arXiv:2507.06365) — the
  source of the `Sal` definition.
