# Arrangements — braid arrangements, COMs, and Salvetti posets

Foundational combinatorics with **no cube-chain content**, consumed by the `Ch(K)` execution model
in `Salvetti/`.

## Files
- `COM.lean` — sign vectors (`SignVec`, `comp`/`sep`/`faceLE`) and the COM axioms (face symmetry
  + strong elimination) of Bandelt–Chepoi–Knauer; `IsOM`, topes.
- `Sal.lean` — the Salvetti face poset `Sal L` of a COM: cells `(X, T)` with `X ⊑ T`, ordered by
  wall crossing `(X,T) ≤ (X',T') ⟺ X ⊑ X' ∧ T' = comp X' T`. `salNerve L := nerve (Sal L)`.
- `SalElements.lean` — presents `Sal L` as the category of elements of the "topes above" functor.
- `COMSum.lean` — direct sum of COMs and `Sal(L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`.
- `Braid.lean` — the braid arrangement `braidCOM n` (an OM); `braidSign x {i,j} = sign(xᵢ − xⱼ)`.
- `BraidPreorder.lean`, `BraidCovector.lean` — the `Fin n` dictionary: topes ⟺ injective heights,
  covectors ⟺ ordered set partitions (`blockMap`).
- `BraidGeometry.lean` — real realization: each covector's open convex star cone in `ℝⁿ`.
- `BraidCone.lean` — the bead cone: series timings realize `braidDirectSum dims = ⊕ᵢ A_{dᵢ−1}`.
- `BraidSymmetry.lean` — the `Sₙ` reorientation action `reorient σ` on `braidCOM n`.
- `ElementsProd.lean` — the external product `F ⊠ G` and `extProdEquiv` on categories of elements.

## References
- Bandelt–Chepoi–Knauer, *COMs: Complexes of Oriented Matroids* (arXiv:1507.06111).
- Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional OMs* (arXiv:2507.06365) —
  the source of the `Sal` definition.
