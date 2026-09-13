import CubeChains.Machinery.Presentation.Basic
import CubeChains.Foundations.Polygraph.Presheaf

/-!
# Machinery/Presentation/ColimitCells — every cell of a colimit is a leg's

Joint surjectivity comes from the presheaf topos, at every shape at once
(`exists_colimit_ι_cell`): cells are computed **pointwise**, so `Types` supplies 0- and 1-cells
alike and no probe polygraph is needed.
-/

universe u

namespace CategoryTheory.Polygraph

open Limits

variable {J : Type u} [Category.{u} J] (D : J ⥤ Polygraph.{u, u, u})

/-- The comparison carries a leg's cell to that leg's cell downstairs. -/
theorem hom_preservesColimitIso_cellsApp (s : PolyShape) (k : J) (y : cellsObj (D.obj k) s) :
    (preservesColimitIso (cellsAt s) D).hom (cellsApp (colimit.ι D k) s y)
      = colimit.ι (D ⋙ cellsAt s) k y :=
  congrArg (fun g : (cellsAt s).obj (D.obj k) ⟶ colimit (D ⋙ cellsAt s) =>
      ConcreteCategory.hom g y)
    (ι_preservesColimitIso_hom (cellsAt s) D k)

/-- **Every cell of a colimit is a leg's cell** — cells are computed pointwise. -/
theorem exists_colimit_ι_cell (s : PolyShape) (A : cellsObj (colimit D) s) :
    ∃ (j : J) (x : cellsObj (D.obj j) s), cellsApp (colimit.ι D j) s x = A := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective' (F := D ⋙ cellsAt s)
    ((preservesColimitIso (cellsAt s) D).hom A)
  exact ⟨j, x, (preservesColimitIso (cellsAt s) D).toEquiv.injective
    ((hom_preservesColimitIso_cellsApp D s j x).trans hx)⟩

/-- **Every 0-cell of a colimit is a leg's 0-cell.** -/
theorem exists_colimit_ι_obj (A : GenObj (colimit D).Gen) :
    ∃ (j : J) (x : GenObj (D.obj j).Gen), (colimit.ι D j).pre.obj x = A :=
  exists_colimit_ι_cell D PolyShape.pt A

end CategoryTheory.Polygraph
