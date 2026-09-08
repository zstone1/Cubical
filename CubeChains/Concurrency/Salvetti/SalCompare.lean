import CubeChains.Machinery.Arrangement.SalElements
import CubeChains.Concurrency.Executions.Elements
import CubeChains.Concurrency.Complexification.ChStarSym

/-!
# Concurrency/Salvetti/SalCompare — executions against Salvetti cells

Both sides are categories of elements: the executions of `K` are `(Lines K).Elements` by
definition, and `Sal L ≌ (salFunctor L).Elements` by `salElementsEquiv`.  So the comparison is one
datum — a `Models` — an equivalence of *bases* under which the runs refining a chain are the topes
above its face.
-/

open CategoryTheory

namespace CubeChains

variable {E : Type} {L : COM E} {K : BPSet}

/-- **`L` models `K`**: chains are faces, and the runs refining a chain are the topes above its
face. -/
structure Models (L : COM E) (K : BPSet) where
  /-- chains are faces -/
  base : (Ch K)ᵒᵖ ≌ COM.Face L
  /-- …and the runs refining a chain are the topes above its face -/
  fibre : Lines K ≅ base.functor ⋙ COM.salFunctor L

namespace Models

/-- **A COM that models `K` presents the executions of `K`** — a chain with a run refining it is a
face with a chamber above it. -/
def salEquiv (m : Models L K) : (Lines K).Elements ≌ Sal L :=
  (CategoryOfElements.mapEquivalence m.fibre).trans
    ((CategoryOfElements.preEquivalenceComp (COM.salFunctor L) m.base).trans
      (COM.salElementsEquiv L).symm)

/-- **`H K` is the complexification of a `K` that `L` models**: a chain of `H K` is a chain of `K`
with a run refining it (`chSymChStarEquiv`), so the decorated chains are the opposite of the
Salvetti poset. -/
def hbpEquiv (m : Models L K) : Ch (Hbp.obj K) ≌ (Sal L)ᵒᵖ :=
  (chSymChStarEquiv K).trans m.salEquiv.op

end Models

end CubeChains
