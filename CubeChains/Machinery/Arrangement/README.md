# Machinery/Arrangement — braid arrangements, COMs, and Salvetti posets

Foundational combinatorics with **no cube-chain content**, consumed by the `Ch(K)` execution model
in `Concurrency/`.

## Files
- `COM.lean` — sign vectors (`SignVec`, `comp`/`sep`/`faceLE`) and the COM axioms (face symmetry
  + strong elimination) of Bandelt–Chepoi–Knauer; `IsOM`, topes.
- `Sal.lean` — the Salvetti face poset `Sal L` of a COM: cells `(X, T)` with `X ⊑ T` (`SalCell`),
  ordered by wall crossing `(X,T) ≤ (X',T') ⟺ X ⊑ X' ∧ T' = comp X' T` (`le_iff`).
- `SalElements.lean` — presents `Sal L` as the category of elements of the "topes above" functor:
  the base `Face L` (covectors of `L`), the presheaf `salFunctor L : Face L ⥤ Type`, and
  `salElementsEquiv L : Sal L ≌ (salFunctor L).Elements`. This is the form `Concurrency/Salvetti/SalExec`
  compares against.
- `COMSum.lean` — direct sum of COMs and `Sal(L₁ ⊕ L₂) ≌ Sal L₁ × Sal L₂`.
- `Braid.lean` — the braid arrangement `braidCOM n` (an OM); `braidSign x {i,j} = sign(xᵢ − xⱼ)`.
- `BraidPreorder.lean`, `BraidCovector.lean` — the `Fin n` dictionary: topes ⟺ injective heights,
  covectors ⟺ ordered set partitions (`blockMap`).
- `BraidSymmetry.lean` — the `Sₙ` reorientation action `reorient σ` on `braidCOM n`.
- `SalSymmetry.lean` — the induced cellwise action on `Sal (braidCOM n)`; `reorient_comp` (it
  commutes with wall crossing) is what makes it order-preserving.

The external product `F ⊠ G` (`extProd`) lives in `Machinery/Localization/ElementsProd.lean` — it is
about categories of elements in general, not about arrangements.

## References
- Bandelt–Chepoi–Knauer, *COMs: Complexes of Oriented Matroids* (arXiv:1507.06111).
- Dorpalen-Barry–Dugger–Proudfoot, *Salvetti complexes for conditional OMs* (arXiv:2507.06365) —
  the source of the `Sal` definition.
