import CubeChains.Machinery.Presentation.Basic
import CubeChains.Foundations.Polygraph.Presheaf

/-!
# Machinery/Presentation/ColimitCells — a colimit's cells are the colimit of the cells

A prefunctor out of `P`'s generating quiver *is* a morphism `P ⟶ thin Gen'` (`toThin`), and a
morphism into a thin polygraph *is* its prefunctor (`thin_hom_ext`): cells are a left adjoint, so
they carry colimits.  `colimitCells` descends a compatible family of prefunctors and
`colimit_pre_ext` is the uniqueness — the colimit's universal property alone, no 0-cell examined.

Joint surjectivity and the identification of two legs' 0-cells come instead from the presheaf
topos: cells are computed **pointwise** (`cellsAt` preserves colimits), so `Types` supplies both.
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

/-- The comparison carries a leg's 0-cell to that leg's 0-cell downstairs. -/
theorem hom_preservesColimitIso_pre_obj (k : J) (y : GenObj (D.obj k).Gen) :
    (preservesColimitIso (cellsAt PolyShape.pt) D).hom ((colimit.ι D k).pre.obj y)
      = colimit.ι (D ⋙ cellsAt PolyShape.pt) k y := by
  have h := ι_preservesColimitIso_hom (cellsAt PolyShape.pt) D k
  exact congrArg (fun g : (cellsAt PolyShape.pt).obj (D.obj k) ⟶
    colimit (D ⋙ cellsAt PolyShape.pt) => ConcreteCategory.hom g y) h

/-- **Every 0-cell of a colimit is a leg's 0-cell** — cells are computed pointwise. -/
theorem exists_colimit_ι_obj (A : GenObj (colimit D).Gen) :
    ∃ (j : J) (x : GenObj (D.obj j).Gen), (colimit.ι D j).pre.obj x = A := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective' (F := D ⋙ cellsAt PolyShape.pt)
    ((preservesColimitIso (cellsAt PolyShape.pt) D).hom A)
  exact ⟨j, x, (preservesColimitIso (cellsAt PolyShape.pt) D).toEquiv.injective
    ((hom_preservesColimitIso_pre_obj D j x).trans hx)⟩

/-- **Two 0-cells of a colimit agree exactly when the diagram identifies them** — the injectivity
half of `exists_colimit_ι_obj`. -/
theorem colimit_pre_obj_eq {j j' : J} {x : GenObj (D.obj j).Gen} {x' : GenObj (D.obj j').Gen}
    (w : (colimit.ι D j).pre.obj x = (colimit.ι D j').pre.obj x') :
    Relation.EqvGen (D ⋙ cellsAt PolyShape.pt).ColimitTypeRel ⟨j, x⟩ ⟨j', x'⟩ := by
  refine Types.colimit_eq (F := D ⋙ cellsAt PolyShape.pt) ?_
  rw [← hom_preservesColimitIso_pre_obj D j x, ← hom_preservesColimitIso_pre_obj D j' x', w]

/-- The quiver whose 1-cells are propositions. -/
abbrev GenProp : PUnit.{u + 1} → PUnit.{u + 1} → Type u := fun _ _ => ULift.{u} Prop

/-- **A property of 1-cells holding on every leg holds on the colimit.**  Stated on a leg's 1-cell
rather than on a 1-cell of the colimit, so neither the property nor its proof carries a
transport. -/
theorem colimit_gen_induction (Φ : ∀ {A B : GenObj (colimit D).Gen}, (A ⟶ B) → Prop)
    (h : ∀ (j : J) {x y : GenObj (D.obj j).Gen} (g : x ⟶ y), Φ ((colimit.ι D j).pre.map g))
    {A B : GenObj (colimit D).Gen} (e : A ⟶ B) : Φ e := by
  have key : (⟨fun _ => ⟨PUnit.unit⟩, fun {_ _} f => ⟨Φ f⟩⟩ :
        GenObj (colimit D).Gen ⥤q GenObj GenProp.{u})
      = ⟨fun _ => ⟨PUnit.unit⟩, fun _ => ⟨True⟩⟩ :=
    colimit_pre_ext D fun j => Prefunctor.ext' (fun _ => rfl)
      (fun _ _ g => congrArg (fun p : Prop => (⟨p⟩ : ULift.{u} Prop))
        (propext ⟨fun _ => trivial, fun _ => h j g⟩))
  exact of_eq_true (congrArg
    (fun π : GenObj (colimit D).Gen ⥤q GenObj GenProp.{u} => (π.map e).down) key)

/-- **Every 1-cell of a colimit is a leg's 1-cell**, up to the transport its endpoints carry. -/
theorem exists_colimit_ι_map {A B : GenObj (colimit D).Gen} (e : A ⟶ B) :
    ∃ (j : J) (x y : GenObj (D.obj j).Gen) (g : x ⟶ y)
      (hx : (colimit.ι D j).pre.obj x = A) (hy : (colimit.ι D j).pre.obj y = B),
      Quiver.homOfEq ((colimit.ι D j).pre.map g) hx hy = e :=
  colimit_gen_induction D
    (Φ := fun {A B} f => ∃ (j : J) (x y : GenObj (D.obj j).Gen) (g : x ⟶ y)
      (hx : (colimit.ι D j).pre.obj x = A) (hy : (colimit.ι D j).pre.obj y = B),
      Quiver.homOfEq ((colimit.ι D j).pre.map g) hx hy = f)
    (fun j {x y} g => ⟨j, x, y, g, rfl, rfl, rfl⟩) e

end CategoryTheory.Polygraph
