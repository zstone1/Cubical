import CubeChains.Machinery.Arrangement.SalElements
import CubeChains.Concurrency.Executions.Elements
import CubeChains.Concurrency.Complexification.ChStarSym

/-!
# Concurrency/Salvetti/SalCompare — executions against Salvetti cells

Both sides of `Ch⋆ K ≌ Sal L` are categories of elements: `Ch⋆ K = (Lines K).Elements` by
definition, and `Sal L ≌ (salFunctor L).Elements` by `salElementsEquiv`.  So the comparison
splits into a comparison of *bases* — an equivalence `(Ch K)ᵒᵖ ≌ Face L` — and a comparison of
*presheaves* over it — a natural iso `Lines K ≅ e.functor ⋙ salFunctor L`, i.e. "the runs
refining a chain are the topes above its face".
-/

open CategoryTheory

namespace CubeChains

variable {E : Type} {L : COM E} {K : BPSet}

/-- **A COM presents the executions of `K`**: faces are chains, and the topes above a face are
the runs refining it. -/
def salCompare (e : (Ch K)ᵒᵖ ≌ COM.Face L) (i : Lines K ≅ e.functor ⋙ COM.salFunctor L) :
    Ch⋆ K ≌ Sal L :=
  (CategoryOfElements.mapEquivalence i).trans
    ((CategoryOfElements.preEquivalenceComp (COM.salFunctor L) e).trans
      (COM.salElementsEquiv L).symm)

/-- **`H` is the complexification of a `K` carrying a COM**: the decorated chains of `K` are the
opposite of the Salvetti poset of `L`. -/
def hbpSalEquiv (e : (Ch K)ᵒᵖ ≌ COM.Face L) (i : Lines K ≅ e.functor ⋙ COM.salFunctor L) :
    Ch (Hbp.obj K) ≌ (Sal L)ᵒᵖ :=
  (chSymChStarEquiv K).trans (salCompare e i).op

end CubeChains
