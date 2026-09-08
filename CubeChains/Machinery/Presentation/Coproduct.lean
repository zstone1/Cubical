import CubeChains.Machinery.Presentation.ColimitCells
import CubeChains.Machinery.Presentation.Adjunction
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sigma.Basic

/-!
# Machinery/Presentation/Coproduct — the coproduct of polygraphs

`∐ P` is the coproduct in `Polygraph`, and nothing here builds one: polygraphs are a presheaf
topos, so `cellsAt` preserves it, and a coproduct of *types* is its disjoint union.  That is the
whole content — a cell of `∐ P` lies in one leg and remembers which, in every dimension:

```
  Σ i, cellsAt s (P i)  ≃  cellsAt s (∐ P)         s = pt, edge, cell m n
```

`coprodCells` descends a family of prefunctors (`thin` is right adjoint to cells), `coprodInterp`
the same into a category, and `coprod_pre_ext` is the uniqueness.  Everything else —
star-bijectivity of a leg, a word lying in one leg, `boundaryDetermined_coprod` — is read off
`coprodCellsEquiv`.

A leg's 0-cell is *not* definitionally a pair, so a fact about a leg's cells is stated at
`(Sigma.ι P i).pre.obj x` with the endpoint equations quantified inside the conclusion, so that
`rintro … rfl rfl` substitutes them away and nothing transports.
-/

universe v u₂ u

namespace CategoryTheory

/-- **A lift along equal interpretations agrees**, up to the transport its endpoints carry. -/
theorem Paths.lift_map_of_eq {V : Type u} [Quiver.{u} V] {D : Type u₂} [Category.{v} D]
    {φ ψ : V ⥤q D} (h : φ = ψ) {x y : V} (u : Quiver.Path x y) :
    (Paths.lift φ).map u = Quiver.homOfEq ((Paths.lift ψ).map u)
      (congrArg (fun π : V ⥤q D => π.obj x) h).symm
      (congrArg (fun π : V ⥤q D => π.obj y) h).symm := by
  subst h; rfl

/-- **An arrow of a disjoint union is one leg's**, up to the transport its endpoints carry. -/
theorem Sigma.exists_incl_map {ι : Type*} {C : ι → Type*} [∀ i, Category (C i)]
    {X Y : Σ i, C i} (f : X ⟶ Y) :
    ∃ (i : ι) (a b : C i) (g : a ⟶ b) (hx : (⟨i, a⟩ : Σ i, C i) = X)
      (hy : (⟨i, b⟩ : Σ i, C i) = Y),
      Quiver.homOfEq ((Sigma.incl i).map g) hx hy = f := by
  cases f with
  | mk g => exact ⟨_, _, _, g, rfl, rfl, rfl⟩

namespace Polygraph

open Limits

variable {ι : Type u} (P : ι → Polygraph.{u, u, u})

/-! ## Descending a family of prefunctors

A prefunctor out of `P i` *is* a morphism `P i ⟶ thin Gen'` (`toThin`), and a morphism into a thin
polygraph *is* its prefunctor (`thin_hom_ext`): cells are a left adjoint, so `Sigma.desc` descends
a family with nothing to check. -/

section Cells

variable {V' : Type u} {Gen' : V' → V' → Type u} (ψ : ∀ i : ι, GenObj (P i).Gen ⥤q GenObj Gen')

/-- The descent of a family, as a morphism into the thin polygraph on `Gen'`. -/
noncomputable def coprodThin : (∐ P) ⟶ thin Gen' := Limits.Sigma.desc fun i => toThin (ψ i)

/-- **A family of prefunctors descends to the coproduct's cells.** -/
noncomputable def coprodCells : GenObj (∐ P).Gen ⥤q GenObj Gen' := (coprodThin P ψ).pre

/-- **…restricting to the family it came from.** -/
theorem ι_pre_comp_coprodCells (i : ι) :
    (Limits.Sigma.ι P i).pre ⋙q coprodCells P ψ = ψ i :=
  have h : Limits.Sigma.ι P i ≫ coprodThin P ψ = toThin (ψ i) := Limits.Sigma.ι_desc _ i
  congrArg (fun m : P i ⟶ thin Gen' => m.pre) h

/-- **A prefunctor on a coproduct's cells is pinned by its legs** — a thin target sees a morphism
only through its 1-cells, so `Sigma.hom_ext` becomes an extensionality principle for
prefunctors. -/
theorem coprod_pre_ext {φ φ' : GenObj (∐ P).Gen ⥤q GenObj Gen'}
    (h : ∀ i : ι, (Limits.Sigma.ι P i).pre ⋙q φ = (Limits.Sigma.ι P i).pre ⋙q φ') : φ = φ' :=
  congrArg (fun m : (∐ P) ⟶ thin Gen' => m.pre)
    (Limits.Sigma.hom_ext (toThin φ) (toThin φ') fun i => thin_hom_ext (by
      rw [comp_pre, comp_pre]; exact h i))

end Cells

/-! ## …and into a category

An interpretation of the cells in a category is a prefunctor like any other; `catGen` names the
generating quiver of a category's own arrows and `catPre` reads it back. -/

section Interp

/-- A category's own arrows, as 1-cells. -/
def toCatGen (D : Type u₂) [Category.{v} D] : D ⥤q GenObj (catGen D) where
  obj X := ⟨X⟩
  map f := f

variable {D : Type u} [Category.{u} D] (ψ : ∀ i : ι, GenObj (P i).Gen ⥤q D)

/-- **A family of interpretations descends to the coproduct's cells.** -/
noncomputable def coprodInterp : GenObj (∐ P).Gen ⥤q D :=
  coprodCells P (fun i => ψ i ⋙q toCatGen D) ⋙q catPre D

/-- **…restricting to the family it came from.** -/
theorem ι_pre_comp_coprodInterp (i : ι) :
    (Limits.Sigma.ι P i).pre ⋙q coprodInterp P ψ = ψ i :=
  congrArg (fun π : GenObj (P i).Gen ⥤q GenObj (catGen D) => π ⋙q catPre D)
    (ι_pre_comp_coprodCells P (fun i => ψ i ⋙q toCatGen D) i)

/-- **…on a 0-cell of one leg.** -/
theorem coprodInterp_obj (i : ι) (x : GenObj (P i).Gen) :
    (coprodInterp P ψ).obj ((Limits.Sigma.ι P i).pre.obj x) = (ψ i).obj x :=
  congrArg (fun π : GenObj (P i).Gen ⥤q D => π.obj x) (ι_pre_comp_coprodInterp P ψ i)

/-- **…and on a 1-cell**, up to the transport its endpoints carry. -/
theorem coprodInterp_map (i : ι) {x y : GenObj (P i).Gen} (g : x ⟶ y) :
    (coprodInterp P ψ).map ((Limits.Sigma.ι P i).pre.map g)
      = Quiver.homOfEq ((ψ i).map g) (coprodInterp_obj P ψ i x).symm
          (coprodInterp_obj P ψ i y).symm :=
  Prefunctor.map_of_eq (ι_pre_comp_coprodInterp P ψ i) g

end Interp

/-! ## …and a family of spellings

A spelling out of `P i` is a prefunctor into `Q.Word`, so it is an interpretation like any other. -/

section Spell

variable (Q : Polygraph.{u, u, u}) (ψ : ∀ i : ι, GenObj (P i).Gen ⥤q Q.Word)

/-- **A family of spellings descends to the coproduct's cells.** -/
noncomputable def coprodSpell : GenObj (∐ P).Gen ⥤q Q.Word := coprodInterp P ψ

/-- **…restricting to the family it came from.** -/
theorem ι_pre_comp_coprodSpell (i : ι) :
    (Limits.Sigma.ι P i).pre ⋙q coprodSpell P Q ψ = ψ i :=
  ι_pre_comp_coprodInterp P ψ i

/-- **A spelling on a coproduct's cells is pinned by its legs.** -/
theorem coprod_spell_ext {φ φ' : GenObj (∐ P).Gen ⥤q Q.Word}
    (h : ∀ i : ι, (Limits.Sigma.ι P i).pre ⋙q φ = (Limits.Sigma.ι P i).pre ⋙q φ') : φ = φ' :=
  congrArg (fun π => π ⋙q ofWordGen Q)
    (coprod_pre_ext P (φ := φ ⋙q toWordGen Q) (φ' := φ' ⋙q toWordGen Q)
      fun i => congrArg (fun π => π ⋙q toWordGen Q) (h i))

end Spell

/-! ## The cells of a coproduct are the coproduct of the cells

`cellsAt s` preserves colimits (`Foundations/Polygraph/Presheaf`), and a coproduct of types is its
disjoint union.  So the legs are jointly surjective *and* disjoint, in every dimension — the second
half being what a colimit alone does not give. -/

section CellsEquiv

variable (s : PolyShape)

/-- The cells at a shape, as a cofan over the legs. -/
noncomputable def coprodCellsCofan :
    IsColimit (Cofan.mk ((cellsAt s).obj (∐ P)) fun i => (cellsAt s).map (Limits.Sigma.ι P i)) :=
  isColimitOfHasCoproductOfPreservesColimit (cellsAt s) P

/-- The disjoint union of the legs' cells, as a cofan. -/
noncomputable def sigmaCellsCofan : Cofan fun i : ι => (cellsAt s).obj (P i) :=
  Cofan.mk (Σ i : ι, cellsObj (P i) s)
    fun i => ↾fun x => (⟨i, x⟩ : Σ j : ι, cellsObj (P j) s)

/-- The cells of the legs, gathered into the coproduct. -/
noncomputable def sigmaCellsGather : (Σ i : ι, cellsObj (P i) s) ⟶ (cellsAt s).obj (∐ P) :=
  ↾fun a => cellsApp (Limits.Sigma.ι P a.1) s a.2

/-- **A cell of a coproduct lies in one leg, and remembers which.** -/
noncomputable def coprodCellsEquiv : (Σ i : ι, cellsObj (P i) s) ≃ cellsObj (∐ P) s where
  toFun a := cellsApp (Limits.Sigma.ι P a.1) s a.2
  invFun c := (coprodCellsCofan P s).desc (sigmaCellsCofan P s) c
  left_inv a := by
    have h := ConcreteCategory.congr_hom
      ((coprodCellsCofan P s).fac (sigmaCellsCofan P s) ⟨a.1⟩) a.2
    simpa using h
  right_inv c := by
    have key : (coprodCellsCofan P s).desc (sigmaCellsCofan P s) ≫ sigmaCellsGather P s
        = 𝟙 ((cellsAt s).obj (∐ P)) :=
      (coprodCellsCofan P s).hom_ext fun j => by
        have h : (cellsAt s).map (Limits.Sigma.ι P j.as) ≫
            ((coprodCellsCofan P s).desc (sigmaCellsCofan P s) ≫ sigmaCellsGather P s)
            = (cellsAt s).map (Limits.Sigma.ι P j.as) :=
          IsColimit.fac_assoc (coprodCellsCofan P s) (sigmaCellsCofan P s) j
            (sigmaCellsGather P s)
        exact h.trans (Category.comp_id _).symm
    simpa [sigmaCellsGather] using ConcreteCategory.congr_hom key c

@[simp] theorem coprodCellsEquiv_apply (i : ι) (c : cellsObj (P i) s) :
    coprodCellsEquiv P s ⟨i, c⟩ = cellsApp (Limits.Sigma.ι P i) s c := rfl

end CellsEquiv

/-! ## The 0-cells -/

/-- **A 0-cell of a coproduct lies in one leg, and remembers which.** -/
theorem coprod_obj_inj {i j : ι} {x : GenObj (P i).Gen} {y : GenObj (P j).Gen}
    (h : (Limits.Sigma.ι P i).pre.obj x = (Limits.Sigma.ι P j).pre.obj y) :
    (⟨i, x⟩ : Σ i : ι, GenObj (P i).Gen) = ⟨j, y⟩ :=
  (coprodCellsEquiv P .pt).injective h

theorem coprod_pre_obj_injective (i : ι) :
    Function.Injective (Limits.Sigma.ι P i).pre.obj := fun _ _ h =>
  eq_of_heq (Sigma.mk.inj_iff.mp (coprod_obj_inj P h)).2

/-- **…and the leg it lies in is the one it names.** -/
theorem coprod_index_eq {i j : ι} {x : GenObj (P i).Gen} {y : GenObj (P j).Gen}
    (h : (Limits.Sigma.ι P i).pre.obj x = (Limits.Sigma.ι P j).pre.obj y) : i = j :=
  congrArg Sigma.fst (coprod_obj_inj P h)

/-- **Every 0-cell of a coproduct is a leg's.** -/
theorem exists_coprod_obj (A : GenObj (∐ P).Gen) :
    ∃ (i : ι) (x : GenObj (P i).Gen), (Limits.Sigma.ι P i).pre.obj x = A := by
  obtain ⟨⟨i, x⟩, hx⟩ := (coprodCellsEquiv P .pt).surjective A
  exact ⟨i, x, hx⟩

/-- The leg a 0-cell lies in. -/
noncomputable def coprodFibre (A : GenObj (∐ P).Gen) : ι := ((coprodCellsEquiv P .pt).symm A).1

@[simp] theorem coprodFibre_ι (i : ι) (x : GenObj (P i).Gen) :
    coprodFibre P ((Limits.Sigma.ι P i).pre.obj x) = i :=
  congrArg Sigma.fst ((coprodCellsEquiv P .pt).symm_apply_apply ⟨i, x⟩)

/-! ## The 1-cells -/

/-- **Every 1-cell of a coproduct is a leg's**, up to the transport its endpoints carry. -/
theorem exists_coprod_map {A B : GenObj (∐ P).Gen} (e : A ⟶ B) :
    ∃ (i : ι) (x y : GenObj (P i).Gen) (g : x ⟶ y)
      (hx : (Limits.Sigma.ι P i).pre.obj x = A) (hy : (Limits.Sigma.ι P i).pre.obj y = B),
      Quiver.homOfEq ((Limits.Sigma.ι P i).pre.map g) hx hy = e := by
  obtain ⟨⟨i, t⟩, ht⟩ :=
    (coprodCellsEquiv P .edge).surjective (⟨A, B, e⟩ : Quiver.Total (GenObj (∐ P).Gen))
  exact ⟨i, t.left, t.right, t.hom, congrArg Quiver.Total.left ht,
    congrArg Quiver.Total.right ht,
    eq_of_heq ((Quiver.homOfEq_heq _ _ _).trans (Quiver.Total.hom_heq ht))⟩

theorem coprod_pre_map_injective (i : ι) {x y : GenObj (P i).Gen} :
    Function.Injective fun g : x ⟶ y => (Limits.Sigma.ι P i).pre.map g := fun g g' h =>
  eq_of_heq (Quiver.Total.hom_heq (eq_of_heq (Sigma.mk.inj_iff.mp
    ((coprodCellsEquiv P .edge).injective
      (congrArg (Quiver.Total.mk ((Limits.Sigma.ι P i).pre.obj x)
        ((Limits.Sigma.ι P i).pre.obj y)) h) : (⟨i, ⟨x, y, g⟩⟩ :
          Σ i : ι, Quiver.Total (GenObj (P i).Gen)) = ⟨i, ⟨x, y, g'⟩⟩)).2))

theorem coprod_star_injective (i : ι) (x : GenObj (P i).Gen) :
    Function.Injective ((Limits.Sigma.ι P i).pre.star x) := by
  rintro ⟨y, g⟩ ⟨y', g'⟩ h
  obtain ⟨hy, hg⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : y = y' := coprod_pre_obj_injective P i hy
  exact Sigma.ext rfl (heq_of_eq (coprod_pre_map_injective P i (eq_of_heq hg)))

theorem coprod_star_surjective (i : ι) (x : GenObj (P i).Gen) :
    Function.Surjective ((Limits.Sigma.ι P i).pre.star x) := by
  rintro ⟨B, e⟩
  obtain ⟨j, y, z, g, hy, rfl, hg⟩ := exists_coprod_map P e
  obtain rfl : i = j := (coprod_index_eq P hy).symm
  obtain rfl : y = x := coprod_pre_obj_injective P i hy
  exact ⟨⟨z, g⟩, Sigma.ext rfl (heq_of_eq hg)⟩

instance coprod_pathsFunctor_faithful (i : ι) :
    (Limits.Sigma.ι P i).pre.pathsFunctor.Faithful :=
  Prefunctor.pathsFunctor_faithful _ (coprod_star_injective P i)

theorem coprod_pathsFunctor_full (i : ι) : (Limits.Sigma.ι P i).pre.pathsFunctor.Full :=
  Prefunctor.pathsFunctor_full _ (coprod_star_surjective P i) (coprod_pre_obj_injective P i)

theorem coprodFibre_eq_of_hom {A B : GenObj (∐ P).Gen} (e : A ⟶ B) :
    coprodFibre P A = coprodFibre P B := by
  obtain ⟨i, x, y, -, rfl, rfl, -⟩ := exists_coprod_map P e
  rw [coprodFibre_ι, coprodFibre_ι]

/-- **A word of a coproduct stays in the leg it starts in.** -/
theorem coprodFibre_eq_of_path {A B : GenObj (∐ P).Gen} (u : Quiver.Path A B) :
    coprodFibre P A = coprodFibre P B := by
  induction u with
  | nil => rfl
  | cons _ e ih => exact ih.trans (coprodFibre_eq_of_hom P e)

/-- **Every word of a coproduct is a leg's**, up to the transport its endpoints carry. -/
theorem exists_coprod_mapPath {A B : GenObj (∐ P).Gen} (u : Quiver.Path A B) :
    ∃ (i : ι) (x y : GenObj (P i).Gen)
      (hx : (Limits.Sigma.ι P i).pre.obj x = A) (hy : (Limits.Sigma.ι P i).pre.obj y = B)
      (u' : Quiver.Path x y),
      cellCongr Quiver.Path hx hy ((Limits.Sigma.ι P i).pre.mapPath u') = u := by
  obtain ⟨i, x, rfl⟩ := exists_coprod_obj P A
  obtain ⟨j, y, rfl⟩ := exists_coprod_obj P B
  obtain rfl : i = j := by
    have := coprodFibre_eq_of_path P u
    rwa [coprodFibre_ι, coprodFibre_ι] at this
  obtain ⟨u', hu'⟩ := (coprod_pathsFunctor_full P i).map_surjective (X := x) (Y := y) u
  exact ⟨i, x, y, rfl, rfl, u', hu'⟩

/-! ## The 2-cells -/

/-- **Every 2-cell of a coproduct is a leg's**, up to the transport its boundary carries. -/
theorem exists_coprod_two {A B : GenObj (∐ P).Gen} (α : (∐ P).Rel A B) :
    ∃ (i : ι) (x y : GenObj (P i).Gen)
      (hx : (Limits.Sigma.ι P i).pre.obj x = A) (hy : (Limits.Sigma.ι P i).pre.obj y = B)
      (β : (P i).Rel x y),
      cellCongr (∐ P).Rel hx hy ((Limits.Sigma.ι P i).two β) = α := by
  suffices H : ∀ (m n : ℕ) (c : ShapedCell (∐ P) m n), ∃ (i : ι) (x y : GenObj (P i).Gen)
      (hx : (Limits.Sigma.ι P i).pre.obj x = c.x) (hy : (Limits.Sigma.ι P i).pre.obj y = c.y)
      (β : (P i).Rel x y),
      cellCongr (∐ P).Rel hx hy ((Limits.Sigma.ι P i).two β) = c.cell from
    H _ _ ⟨A, B, α, rfl, rfl⟩
  intro m n c
  obtain ⟨⟨i, d⟩, hd⟩ := (coprodCellsEquiv P (.cell m n)).surjective c
  exact ⟨i, d.x, d.y, congrArg ShapedCell.x hd, congrArg ShapedCell.y hd, d.cell,
    eq_of_heq ((cellCongr_heq _ _ _ _).trans (ShapedCell.cell_heq hd))⟩

/-- **A 2-cell over one leg's 0-cells is that leg's.** -/
theorem coprod_two_surjective (i : ι) {x y : GenObj (P i).Gen}
    (α : (∐ P).Rel ((Limits.Sigma.ι P i).pre.obj x) ((Limits.Sigma.ι P i).pre.obj y)) :
    ∃ β : (P i).Rel x y, (Limits.Sigma.ι P i).two β = α := by
  obtain ⟨j, x', y', hx, hy, β, hβ⟩ := exists_coprod_two P α
  obtain rfl : i = j := (coprod_index_eq P hx).symm
  obtain rfl : x' = x := coprod_pre_obj_injective P i hx
  obtain rfl : y' = y := coprod_pre_obj_injective P i hy
  exact ⟨β, by simpa using hβ⟩

/-- **A 2-cell of the coproduct is its leg's boundary**: a leg is a covering, so words determine
themselves, and a leg's own 2-cells are pinned by theirs. -/
theorem boundaryDetermined_coprod (hP : ∀ i, (P i).BoundaryDetermined) :
    (∐ P).BoundaryDetermined := by
  intro A B α β hs ht
  obtain ⟨i, x, y, rfl, rfl, α', rfl⟩ := exists_coprod_two P α
  obtain ⟨β', rfl⟩ := coprod_two_surjective P i β
  refine congrArg (Limits.Sigma.ι P i).two (hP i α' β' ?_ ?_)
  · exact (coprod_pathsFunctor_faithful P i).map_injective
      (((Limits.Sigma.ι P i).src_two α').symm.trans (hs.trans ((Limits.Sigma.ι P i).src_two β')))
  · exact (coprod_pathsFunctor_faithful P i).map_injective
      (((Limits.Sigma.ι P i).tgt_two α').symm.trans (ht.trans ((Limits.Sigma.ι P i).tgt_two β')))

end Polygraph

/-! ## What it presents

A family of presentations presents the disjoint union of the categories.  The interpretation of a
leg's cells is that leg's own, included (`coproductEval_ι`); everything below is that equation, read
in each of the four obligations of `ofDesc`. -/

namespace Presents

open Polygraph Limits

variable {ι : Type u} {P : ι → Polygraph.{u, u, u}} {C : ι → Type u} [∀ i, Category.{u} (C i)]
  (p : ∀ i, Presents (P i) (C i))

/-- The cells of the coproduct, interpreted in the disjoint union of the categories. -/
noncomputable def coproductEval : GenObj (∐ P).Gen ⥤q (Σ i, C i) :=
  Polygraph.coprodInterp P fun i => (p i).evalPre ⋙q (CategoryTheory.Sigma.incl i).toPrefunctor

/-- **A leg's cells are interpreted by that leg's own presentation, included.** -/
theorem coproductEval_ι (i : ι) :
    (Limits.Sigma.ι P i).pre ⋙q coproductEval p
      = (p i).evalPre ⋙q (CategoryTheory.Sigma.incl i).toPrefunctor :=
  Polygraph.ι_pre_comp_coprodInterp P _ i

/-- **A leg's 0-cell names its own object, included.**  Not `rfl`: a coproduct's 0-cells are
reached only through its universal property, so this is the transport everything below carries. -/
theorem coproduct_at (i : ι) (x : GenObj (P i).Gen) :
    (coproductEval p).obj ((Limits.Sigma.ι P i).pre.obj x) = ⟨i, (p i).at' x⟩ :=
  Polygraph.coprodInterp_obj P _ i x

/-- **A leg's word, evaluated in the coproduct** — that leg's own evaluation, included. -/
theorem lift_coproductEval_mapPath (i : ι) {x y : GenObj (P i).Gen} (u : Quiver.Path x y) :
    (Paths.lift (coproductEval p)).map ((Limits.Sigma.ι P i).pre.mapPath u)
      = Quiver.homOfEq ((CategoryTheory.Sigma.incl i).map ((p i).eval.map u))
          (coproduct_at p i x).symm (coproduct_at p i y).symm := by
  rw [Paths.lift_mapPath, Paths.lift_map_of_eq (coproductEval_ι p i) u]
  exact congrArg (fun t => Quiver.homOfEq t _ _) ((p i).lift_evalPre_comp _ u)

theorem coproduct_sound {A B : GenObj (∐ P).Gen} (α : (∐ P).Rel A B) :
    (Paths.lift (coproductEval p)).map ((∐ P).src α)
      = (Paths.lift (coproductEval p)).map ((∐ P).tgt α) := by
  obtain ⟨i, x, y, rfl, rfl, β, rfl⟩ := Polygraph.exists_coprod_two P α
  simp only [cellCongr_self]
  rw [(Limits.Sigma.ι P i).src_two, (Limits.Sigma.ι P i).tgt_two,
    lift_coproductEval_mapPath, lift_coproductEval_mapPath]
  exact congrArg (fun t => Quiver.homOfEq t _ _) (congrArg _ ((p i).sound β))

theorem coproduct_complete {A B : GenObj (∐ P).Gen} {u v : Quiver.Path A B}
    (h : (Paths.lift (coproductEval p)).map u = (Paths.lift (coproductEval p)).map v) :
    (∐ P).quot.map u = (∐ P).quot.map v := by
  obtain ⟨i, x, y, rfl, rfl, u', rfl⟩ := Polygraph.exists_coprod_mapPath P u
  obtain ⟨v', rfl⟩ := (Polygraph.coprod_pathsFunctor_full P i).map_surjective (X := x) (Y := y) v
  simp only [cellCongr_self, Prefunctor.pathsFunctor_map] at h ⊢
  rw [lift_coproductEval_mapPath, lift_coproductEval_mapPath] at h
  exact (Limits.Sigma.ι P i).quot_map_congr ((p i).E.map_injective
    ((CategoryTheory.Sigma.incl i).map_injective (Quiver.homOfEq_injective _ _ h)))

theorem coproduct_full : (Paths.lift (coproductEval p)).Full where
  map_surjective := by
    intro A B f
    obtain ⟨i, x, rfl⟩ := Polygraph.exists_coprod_obj P A
    obtain ⟨j, y, rfl⟩ := Polygraph.exists_coprod_obj P B
    obtain ⟨k, a, b, g, hxa, hyb, rfl⟩ := CategoryTheory.Sigma.exists_incl_map f
    obtain rfl : i = k := (Sigma.mk.inj_iff.mp (hxa.trans (coproduct_at p i x))).1.symm
    obtain rfl : i = j := (Sigma.mk.inj_iff.mp (hyb.trans (coproduct_at p j y))).1
    obtain rfl : a = (p i).at' x :=
      eq_of_heq (Sigma.mk.inj_iff.mp (hxa.trans (coproduct_at p i x))).2
    obtain rfl : b = (p i).at' y :=
      eq_of_heq (Sigma.mk.inj_iff.mp (hyb.trans (coproduct_at p i y))).2
    obtain ⟨w, rfl⟩ := (p i).eval.map_surjective g
    exact ⟨(Limits.Sigma.ι P i).pre.mapPath w, lift_coproductEval_mapPath p i w⟩

theorem coproduct_essSurj : (Paths.lift (coproductEval p)).EssSurj where
  mem_essImage := by
    rintro ⟨i, c⟩
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := (p i).eval) c
    exact ⟨(Limits.Sigma.ι P i).pre.obj x,
      ⟨eqToIso (coproduct_at p i x) ≪≫ (CategoryTheory.Sigma.incl i).mapIso e⟩⟩

/-- **A family of presentations presents the disjoint union.** -/
noncomputable def coproduct : Presents (∐ P) (Σ i, C i) :=
  Presents.ofDesc (coproductEval p) (coproduct_sound p) (coproduct_complete p) (coproduct_full p)
    (coproduct_essSurj p)

/-- **A leg's 1-cell names its own arrow, included.** -/
theorem coproduct_arrow (i : ι) {x y : GenObj (P i).Gen} (g : x ⟶ y) :
    (Presents.coproduct p).arrow ((Limits.Sigma.ι P i).pre.map g)
      = Quiver.homOfEq ((CategoryTheory.Sigma.incl i).map ((p i).arrow g))
          (coproduct_at p i x).symm (coproduct_at p i y).symm :=
  (Presents.ofDesc_arrow _ (coproduct_sound p) _).trans
    (Polygraph.coprodInterp_map P _ i g)

end Presents

end CategoryTheory
