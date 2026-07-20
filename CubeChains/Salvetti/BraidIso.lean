import CubeChains.Salvetti.WallCrossing
import CubeChains.Salvetti.ElementsComp

/-!
# Salvetti/BraidIso — `Sal(braidCOM n) ≌ Int(Lines(□ⁿ))`

Both sides are categories of elements, so nothing is matched cell by cell: the *bases* are compared
by `chFaceEquiv` and the *presheaves* by `salLinesIso`, and the assembly is three `trans`es.

Computable: `preEquivalenceComp` replaces `preEquivalence`, whose inverse comes from `EssSurj`
via choice.
-/

open CategoryTheory Opposite CubeChain StdCube ChainCat
open BPSet

namespace CubeChains

/-- **The Salvetti complex of the braid arrangement is the category of executions of the cube.** -/
def braidSalEquiv (n : ℕ) :
    Sal (braidCOM n) ≌ (Lines (□n)).Elements :=
  (COM.salElementsEquiv (braidCOM n)).trans <|
    (CategoryOfElements.preEquivalenceComp
        (COM.salFunctor (braidCOM n)) (chFaceEquiv n)).symm.trans
      (CategoryOfElements.mapEquivalence (salLinesIso n)).symm

end CubeChains
