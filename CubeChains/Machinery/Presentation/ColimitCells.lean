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

/-! ## …and so does a compatible family of *spellings*

A spelling out of `P` is a prefunctor `GenObj P.Gen ⥤q Q.Word`, so it is a prefunctor into a
generating quiver like any other: `wordGen` names that quiver, and descending a family of spellings
is `colimitCells` with nothing added. -/

section Spell

variable (Q : Polygraph.{u, u, u})

/-- The generating quiver whose 1-cells are `Q`'s words. -/
abbrev wordGen : Q.V → Q.V → Type u := fun x y => Quiver.Path (⟨x⟩ : GenObj Q.Gen) ⟨y⟩

/-- **`GenObj (wordGen Q)` is `Q.Word`** — the identity in both directions. -/
def ofWordGen : GenObj (wordGen Q) ⥤q Q.Word where
  obj x := ⟨x.as⟩
  map e := e

/-- …and back. -/
def toWordGen : Q.Word ⥤q GenObj (wordGen Q) where
  obj x := ⟨x.as⟩
  map e := e

variable (ψ : ∀ j : J, GenObj (D.obj j).Gen ⥤q Q.Word)
  (hψ : ∀ {i j : J} (u : i ⟶ j), (D.map u).pre ⋙q ψ j = ψ i)

include hψ in
/-- **A compatible family of spellings descends to the colimit's cells.** -/
noncomputable def colimitSpell : GenObj (colimit D).Gen ⥤q Q.Word :=
  colimitCells D (fun j => ψ j ⋙q toWordGen Q)
    (fun u => congrArg (fun π => π ⋙q toWordGen Q) (hψ u)) ⋙q ofWordGen Q

/-- **…restricting to the family it came from.** -/
theorem ι_pre_comp_colimitSpell (j : J) :
    (colimit.ι D j).pre ⋙q colimitSpell D Q ψ hψ = ψ j :=
  congrArg (fun π => π ⋙q ofWordGen Q)
    (ι_pre_comp_colimitCells D (fun j => ψ j ⋙q toWordGen Q)
      (fun u => congrArg (fun π => π ⋙q toWordGen Q) (hψ u)) j)

/-- **A spelling on a colimit's cells is pinned by its legs** — `colimit_pre_ext`, read through
`wordGen`. -/
theorem colimit_spell_ext {φ φ' : GenObj (colimit D).Gen ⥤q Q.Word}
    (h : ∀ j : J, (colimit.ι D j).pre ⋙q φ = (colimit.ι D j).pre ⋙q φ') : φ = φ' :=
  congrArg (fun π => π ⋙q ofWordGen Q)
    (colimit_pre_ext D (φ := φ ⋙q toWordGen Q) (φ' := φ' ⋙q toWordGen Q)
      fun j => congrArg (fun π => π ⋙q toWordGen Q) (h j))

end Spell

/-! ## The legs are jointly surjective on cells

Each dimension is one test against a quiver whose cells in *that* dimension are propositions and
whose cells in the other are trivial, so neither test carries a transport. -/

/-- The quiver whose 0-cells are propositions. -/
abbrev PtProp : ULift.{u} Prop → ULift.{u} Prop → Type u := fun _ _ => PUnit

/-- The quiver whose 1-cells are propositions. -/
abbrev GenProp : PUnit.{u + 1} → PUnit.{u + 1} → Type u := fun _ _ => ULift.{u} Prop

/-- **A property of 0-cells holding on every leg holds on the colimit** — the induction principle
the legs' joint surjectivity is; nothing about the construction is unfolded. -/
theorem colimit_obj_induction (Φ : GenObj (colimit D).Gen → Prop)
    (h : ∀ (j : J) (x : GenObj (D.obj j).Gen), Φ ((colimit.ι D j).pre.obj x))
    (A : GenObj (colimit D).Gen) : Φ A := by
  have key : (⟨fun B => ⟨⟨Φ B⟩⟩, fun _ => PUnit.unit⟩ :
        GenObj (colimit D).Gen ⥤q GenObj PtProp.{u})
      = ⟨fun _ => ⟨⟨True⟩⟩, fun _ => PUnit.unit⟩ :=
    colimit_pre_ext D fun j => Prefunctor.ext'
      (fun x => congrArg (fun p : Prop => (⟨⟨p⟩⟩ : GenObj PtProp.{u}))
        (propext ⟨fun _ => trivial, fun _ => h j x⟩))
      (fun _ _ _ => Subsingleton.elim (α := PUnit.{u + 1}) _ _)
  exact of_eq_true (congrArg
    (fun π : GenObj (colimit D).Gen ⥤q GenObj PtProp.{u} => (π.obj A).as.down) key)

/-- **…and the same in dimension one.**  Stated on a leg's 1-cell rather than on a 1-cell of the
colimit, so neither the property nor its proof carries a transport. -/
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

/-- **Every 0-cell of a colimit is a leg's 0-cell.** -/
theorem exists_colimit_ι_obj (A : GenObj (colimit D).Gen) :
    ∃ (j : J) (x : GenObj (D.obj j).Gen), (colimit.ι D j).pre.obj x = A :=
  colimit_obj_induction D
    (fun A => ∃ (j : J) (x : GenObj (D.obj j).Gen), (colimit.ι D j).pre.obj x = A)
    (fun j x => ⟨j, x, rfl⟩) A

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
