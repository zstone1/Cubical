import CubeChains.Machinery.Presentation.Coequalizer

/-!
# Machinery/Presentation/ColimitCells — a colimit's cells are the colimit of the cells

A prefunctor out of `P`'s generating quiver *is* a morphism `P ⟶ thin Gen'` (`toThin`), and a
morphism into a thin polygraph *is* its prefunctor (`thin_hom_ext`): cells are a left adjoint, so
they carry colimits.  `colimitCells` descends a compatible family of prefunctors, `colimit_pre_ext`
is the uniqueness, and both are the colimit's universal property alone — no 0-cell is examined and
the construction is never unfolded.

Joint surjectivity of the legs is then one test against a quiver whose cells are *propositions*:
"true" and "reached by a leg" agree on every leg, hence agree.
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

/-! ## The legs are jointly surjective on cells

Each dimension is one test against a quiver whose cells in *that* dimension are propositions and
whose cells in the other are trivial, so neither test carries a transport. -/

/-- The quiver whose 0-cells are propositions. -/
abbrev PtProp : ULift.{u} Prop → ULift.{u} Prop → Type u := fun _ _ => PUnit

/-- The quiver whose 1-cells are propositions. -/
abbrev GenProp : PUnit.{u + 1} → PUnit.{u + 1} → Type u := fun _ _ => ULift.{u} Prop

/-- **Every 0-cell of a colimit is a leg's 0-cell.** -/
theorem exists_colimit_ι_obj (A : GenObj (colimit D).Gen) :
    ∃ (j : J) (x : GenObj (D.obj j).Gen), (colimit.ι D j).pre.obj x = A := by
  have key : (⟨fun B => ⟨⟨∃ (j : J) (x : GenObj (D.obj j).Gen),
        (colimit.ι D j).pre.obj x = B⟩⟩, fun _ => PUnit.unit⟩ :
        GenObj (colimit D).Gen ⥤q GenObj PtProp.{u})
      = ⟨fun _ => ⟨⟨True⟩⟩, fun _ => PUnit.unit⟩ :=
    colimit_pre_ext D fun j => Prefunctor.ext'
      (fun x => congrArg (fun p : Prop => (⟨⟨p⟩⟩ : GenObj PtProp.{u}))
        (propext ⟨fun _ => trivial, fun _ => ⟨j, x, rfl⟩⟩))
      (fun _ _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _)
  exact of_eq_true (congrArg
    (fun π : GenObj (colimit D).Gen ⥤q GenObj PtProp.{u} => (π.obj A).as.down) key)

/-- **Every 1-cell of a colimit is a leg's 1-cell**, up to the transport its endpoints carry. -/
theorem exists_colimit_ι_map {A B : GenObj (colimit D).Gen} (e : A ⟶ B) :
    ∃ (j : J) (x y : GenObj (D.obj j).Gen) (g : x ⟶ y)
      (hx : (colimit.ι D j).pre.obj x = A) (hy : (colimit.ι D j).pre.obj y = B),
      Quiver.homOfEq ((colimit.ι D j).pre.map g) hx hy = e := by
  have key : (⟨fun _ => ⟨PUnit.unit⟩, fun {X Y} f => ⟨∃ (j : J) (x y : GenObj (D.obj j).Gen)
        (g : x ⟶ y) (hx : (colimit.ι D j).pre.obj x = X)
        (hy : (colimit.ι D j).pre.obj y = Y),
        Quiver.homOfEq ((colimit.ι D j).pre.map g) hx hy = f⟩⟩ :
        GenObj (colimit D).Gen ⥤q GenObj GenProp.{u})
      = ⟨fun _ => ⟨PUnit.unit⟩, fun _ => ⟨True⟩⟩ :=
    colimit_pre_ext D fun j => Prefunctor.ext' (fun _ => rfl)
      (fun x y g => congrArg (fun p : Prop => (⟨p⟩ : ULift.{u} Prop))
        (propext ⟨fun _ => trivial, fun _ => ⟨j, x, y, g, rfl, rfl, rfl⟩⟩))
  exact of_eq_true (congrArg
    (fun π : GenObj (colimit D).Gen ⥤q GenObj GenProp.{u} => (π.map e).down) key)

end CategoryTheory.Polygraph
