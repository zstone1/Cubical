import CubeChains.Machinery.Presentation.Basic
import CubeChains.Foundations.Polygraph.Presheaf

/-!
# Machinery/Presentation/ColimitCells — a colimit's cells are the colimit of the cells

A prefunctor out of `P`'s generating quiver *is* a morphism `P ⟶ thin Gen'` (`toThin`), and a
morphism into a thin polygraph *is* its prefunctor (`thin_hom_ext`): cells are a left adjoint, so
they carry colimits.  `colimitCells` descends a compatible family and `colimit_pre_ext` is the
uniqueness — the colimit's universal property alone, no 0-cell examined.

Joint surjectivity comes instead from the presheaf topos, at every shape at once
(`exists_colimit_ι_cell`): cells are computed **pointwise**, so `Types` supplies 0- and 1-cells
alike and no probe polygraph is needed.
-/

universe u

namespace CategoryTheory.Polygraph

open Limits

variable {J : Type u} [Category.{u} J] (D : J ⥤ Polygraph.{u, u, u})

section Cells

variable {V' : Type u} {Gen' : V' → V' → Type u}
  (ψ : ∀ j : J, GenObj (D.obj j).Gen ⥤q GenObj Gen')
  (hψ : ∀ {i j : J} (u : i ⟶ j), (D.map u).pre ⋙q ψ j = ψ i)

include hψ in
/-- A compatible family of prefunctors, as a cocone in the thin polygraph on `Gen'`. -/
def thinCocone : Cocone D where
  pt := thin Gen'
  ι :=
    { app := fun j => toThin (ψ j)
      naturality := fun _ _ u => by
        simpa only [Functor.const_obj_map, Category.comp_id] using thin_hom_ext (hψ u) }

include hψ in
/-- **A compatible family of prefunctors descends to the colimit's cells.** -/
noncomputable def colimitCells : GenObj (colimit D).Gen ⥤q GenObj Gen' :=
  (colimit.desc D (thinCocone D ψ hψ)).pre

/-- **…restricting to the family it came from.** -/
theorem ι_pre_comp_colimitCells (j : J) :
    (colimit.ι D j).pre ⋙q colimitCells D ψ hψ = ψ j :=
  congrArg (fun m : Hom (D.obj j) (thin Gen') => m.pre)
    (colimit.ι_desc (thinCocone D ψ hψ) j)

/-- **A prefunctor on a colimit's cells is pinned by its legs.**  This is what replaces induction
over 0-cells: a thin target sees a morphism only through its 1-cells, so `colimit.hom_ext` becomes
an extensionality principle for prefunctors. -/
theorem colimit_pre_ext {φ φ' : GenObj (colimit D).Gen ⥤q GenObj Gen'}
    (h : ∀ j : J, (colimit.ι D j).pre ⋙q φ = (colimit.ι D j).pre ⋙q φ') : φ = φ' := by
  have key : (toThin φ : colimit D ⟶ thin Gen') = toThin φ' :=
    colimit.hom_ext (F := D) (X := thin Gen') (f := toThin φ) (f' := toThin φ')
      fun j => thin_hom_ext (h j)
  exact congrArg Hom.pre key

end Cells

/-! ## The legs are jointly surjective on cells -/

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

/-- **Two cells of a colimit agree exactly when the diagram identifies them** — the injectivity
half of `exists_colimit_ι_cell`. -/
theorem colimit_cell_eq (s : PolyShape) {j j' : J} {x : cellsObj (D.obj j) s}
    {x' : cellsObj (D.obj j') s}
    (w : cellsApp (colimit.ι D j) s x = cellsApp (colimit.ι D j') s x') :
    Relation.EqvGen (D ⋙ cellsAt s).ColimitTypeRel ⟨j, x⟩ ⟨j', x'⟩ :=
  Types.colimit_eq (F := D ⋙ cellsAt s)
    (((hom_preservesColimitIso_cellsApp D s j x).symm.trans
        (congrArg (ConcreteCategory.hom (preservesColimitIso (cellsAt s) D).hom) w)).trans
      (hom_preservesColimitIso_cellsApp D s j' x'))

/-- **Every 1-cell of a colimit is a leg's 1-cell**, up to the transport its endpoints carry — the
`edge` shape of `exists_colimit_ι_cell`, a 1-cell being its two endpoints and itself. -/
theorem exists_colimit_ι_map {A B : GenObj (colimit D).Gen} (e : A ⟶ B) :
    ∃ (j : J) (x y : GenObj (D.obj j).Gen) (g : x ⟶ y)
      (hx : (colimit.ι D j).pre.obj x = A) (hy : (colimit.ι D j).pre.obj y = B),
      Quiver.homOfEq ((colimit.ι D j).pre.map g) hx hy = e := by
  obtain ⟨j, t, ht⟩ := exists_colimit_ι_cell D PolyShape.edge ⟨A, B, e⟩
  exact ⟨j, t.left, t.right, t.hom, congrArg Quiver.Total.left ht,
    congrArg Quiver.Total.right ht,
    eq_of_heq ((Quiver.homOfEq_heq _ _ _).trans (Quiver.Total.hom_heq ht))⟩

end CategoryTheory.Polygraph
