import CubeChains.Salvetti.TopeSal
import CubeChains.Salvetti.Elements

/-!
# Salvetti/BraidSal — `Ch⋆(□ⁿ) ≌ Sal(braidCOM n)`

The headline identification: the executions of the standard cube (`Ch⋆ (□n) = (Lines □n).Elements`,
a chain together with a run refining it) form the Salvetti face poset of the braid arrangement.

Both sides are categories of elements, so nothing is matched cell by cell — the equivalence is four
`trans`es of already-built pieces:

```
  (Lines □n).Elements
    ≌ (topeLines □n).Elements                     -- runs are topes           (topeLinesIsoLines)
    ≌ (chFaceFunctor ⋙ salFunctor).Elements       -- wall crossing            (topeSalIso)
    ≌ (salFunctor).Elements                        -- base change             (preEquivalenceComp)
    ≌ Sal (braidCOM n)                             -- Sal is ∫ salFunctor      (salElementsEquiv)
```
-/

open CategoryTheory Opposite CategoryOfElements

namespace CubeChains

/-- **The executions of a cube are the Salvetti poset of the braid arrangement.** -/
noncomputable def braidSalEquiv (n : ℕ) : Ch⋆ (□n) ≌ Sal (braidCOM n) :=
  (mapEquivalence (topeLinesIsoLines (□n))).symm.trans <|
    (mapEquivalence (topeSalIso n)).trans <|
      (preEquivalenceComp (COM.salFunctor (braidCOM n)) chFaceCatEquiv).trans
        (COM.salElementsEquiv (braidCOM n)).symm

end CubeChains
