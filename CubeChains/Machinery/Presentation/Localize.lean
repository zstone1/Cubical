import CubeChains.Machinery.Presentation.Basic
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Machinery/Presentation/Localize — formal inverses for some of the generators

`invPoly P S` adjoins to `P` one formal-inverse 1-cell per 1-cell `S` picks out, together with the
two cancellation 2-cells.  `presentsLocalization`: it presents the localization of what `P` presents
at the class the picked cells generate.

The proof is a comparison of universal properties, not a construction: a functor out of
`(invPoly P S).presented` is a functor out of `P.presented` sending each picked cell to an
*isomorphism* (`invDesc`, `invIncl_comp_injective`), which is `IsInvertedBy` once the class is the
multiplicative closure.  `Localization.Construction`'s strict property closes it, and
`IsLocalization.of_equivalence_source` carries it along `p.equiv`.

Everything is spelled on `GenObj (InvGen P S)`, never on `GenObj (invPoly P S).Gen`: the two differ
by a projection, so mixing them blocks `rw` on the `Paths.lift` lemmas.
-/

universe w u' w₂ v u

namespace CategoryTheory

/-! ## A multiplicative closure, reversed

A composite reverses, so the closure that composes on the right becomes the one that composes on the
left; mathlib's `multiplicativeClosure'` is the bridge. -/

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (G : MorphismProperty C)

private theorem op_mem_closure {X Y : C} {f : X ⟶ Y} (hf : G.multiplicativeClosure f) :
    G.op.multiplicativeClosure f.op := by
  rw [multiplicativeClosure_eq_multiplicativeClosure']
  induction hf with
  | of f hf => exact .of _ hf
  | id x => exact .id _
  | comp_of f g _ hg ih => exact .of_comp g.op f.op hg ih

private theorem unop_mem_closure {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : G.op.multiplicativeClosure f) :
    G.multiplicativeClosure f.unop := by
  rw [multiplicativeClosure_eq_multiplicativeClosure']
  induction hf with
  | of f hf => exact .of _ hf
  | id x => exact .id _
  | comp_of f g _ hg ih => exact .of_comp g.unop f.unop hg ih

/-- **Generating a class commutes with reversal.** -/
theorem multiplicativeClosure_op :
    G.multiplicativeClosure.op = G.op.multiplicativeClosure :=
  le_antisymm (fun _ _ _ hf => G.op_mem_closure hf) fun _ _ _ hf => G.unop_mem_closure hf

end MorphismProperty

namespace Polygraph

/-! ## The extension -/

section Invert

variable (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- **1-cells**: those of `P`, and a formal inverse for each the predicate picks out.  A `Sum` and
not an inductive: a constructor argument in `P.V` would raise the 1-cell universe. -/
abbrev InvGen (a b : P.V) : Type w := P.Gen a b ⊕ {e : P.Gen b a // S e}

/-- A 1-cell of `P`, in the extension. -/
def fwdCell {a b : P.V} (e : P.Gen a b) : (⟨a⟩ : GenObj (InvGen P S)) ⟶ ⟨b⟩ := .inl e

/-- …and the formal inverse of a picked one. -/
def bwdCell {a b : P.V} (e : P.Gen a b) (he : S e) :
    (⟨b⟩ : GenObj (InvGen P S)) ⟶ ⟨a⟩ := .inr ⟨e, he⟩

/-- `P`'s generating quiver, inside the extension's. -/
def fwdPre : GenObj P.Gen ⥤q GenObj (InvGen P S) where
  obj x := ⟨x.as⟩
  map e := .inl e

/-- **2-cells**: those of `P`, and the two cancellations. -/
inductive InvRel : GenObj (InvGen P S) → GenObj (InvGen P S) → Type (max u' w w₂)
  | keep {x y : GenObj P.Gen} (α : P.Rel x y) : InvRel ⟨x.as⟩ ⟨y.as⟩
  | cancel {a b : P.V} (e : P.Gen a b) (he : S e) : InvRel ⟨a⟩ ⟨a⟩
  | cancel' {a b : P.V} (e : P.Gen a b) (he : S e) : InvRel ⟨b⟩ ⟨b⟩

/-- The source word of a 2-cell. -/
def invSrc : ∀ {x y : GenObj (InvGen P S)}, InvRel P S x y → Quiver.Path x y
  | _, _, .keep α => (fwdPre P S).mapPath (P.src α)
  | _, _, .cancel e he => (fwdCell P S e).toPath.comp (bwdCell P S e he).toPath
  | _, _, .cancel' e he => (bwdCell P S e he).toPath.comp (fwdCell P S e).toPath

/-- …and the target word. -/
def invTgt : ∀ {x y : GenObj (InvGen P S)}, InvRel P S x y → Quiver.Path x y
  | _, _, .keep α => (fwdPre P S).mapPath (P.tgt α)
  | _, _, .cancel _ _ => Quiver.Path.nil
  | _, _, .cancel' _ _ => Quiver.Path.nil

/-- **`P` with a formal inverse adjoined for each picked 1-cell.** -/
def invPoly : Polygraph.{w, u', max u' w w₂} where
  V := P.V
  Gen := InvGen P S
  Rel := InvRel P S
  src := invSrc P S
  tgt := invTgt P S

/-- **The extension, as a morphism of polygraphs.** -/
def invIncl : Hom P (invPoly P S) where
  pre := fwdPre P S
  two α := .keep α
  src_two _ := rfl
  tgt_two _ := rfl

/-! ## The picked cells, and their inverses in the extension -/

/-- The arrow a 1-cell names in `P.presented`. -/
def genArrow {a b : P.V} (e : P.Gen a b) : (⟨⟨a⟩⟩ : P.presented) ⟶ ⟨⟨b⟩⟩ :=
  P.quot.map (cell e).toPath

/-- The arrow a 1-cell names in the extension. -/
def fwdArrow {a b : P.V} (e : P.Gen a b) :
    (⟨⟨a⟩⟩ : (invPoly P S).presented) ⟶ ⟨⟨b⟩⟩ :=
  (invPoly P S).quot.map (fwdCell P S e).toPath

/-- …and the one its formal inverse names. -/
def bwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) :
    (⟨⟨b⟩⟩ : (invPoly P S).presented) ⟶ ⟨⟨a⟩⟩ :=
  (invPoly P S).quot.map (bwdCell P S e he).toPath

theorem fwdArrow_bwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) :
    fwdArrow P S e ≫ bwdArrow P S e he = 𝟙 _ :=
  ((invPoly P S).quot.map_comp _ _).symm.trans
    ((invPoly P S).quot_src_tgt (InvRel.cancel e he))

theorem bwdArrow_fwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) :
    bwdArrow P S e he ≫ fwdArrow P S e = 𝟙 _ :=
  ((invPoly P S).quot.map_comp _ _).symm.trans
    ((invPoly P S).quot_src_tgt (InvRel.cancel' e he))

/-- **The cancellation 2-cells, as an isomorphism.** -/
def fwdIso {a b : P.V} (e : P.Gen a b) (he : S e) :
    (⟨⟨a⟩⟩ : (invPoly P S).presented) ≅ ⟨⟨b⟩⟩ where
  hom := fwdArrow P S e
  inv := bwdArrow P S e he
  hom_inv_id := fwdArrow_bwdArrow P S e he
  inv_hom_id := bwdArrow_fwdArrow P S e he

theorem isIso_fwdArrow {a b : P.V} (e : P.Gen a b) (he : S e) : IsIso (fwdArrow P S e) :=
  (fwdIso P S e he).isIso_hom

/-- **A functor reads a picked 1-cell as an isomorphism**, the formal inverse as its inverse. -/
def mapFwdIso {E : Type*} [Category E] (F : (invPoly P S).presented ⥤ E) {a b : P.V}
    (e : P.Gen a b) (he : S e) : F.obj ⟨⟨a⟩⟩ ≅ F.obj ⟨⟨b⟩⟩ :=
  F.mapIso (fwdIso P S e he)

/-- **The extension reads a 1-cell of `P` as that 1-cell.** -/
theorem invIncl_functor_genArrow {a b : P.V} (e : P.Gen a b) :
    (invIncl P S).functor.map (genArrow P e) = fwdArrow P S e := rfl

/-! ## The class to invert, read upstairs -/

/-- The arrow a picked 1-cell names.  The 0-cells are indices, so nothing is transported. -/
inductive PickedCell : ∀ {X Y : P.presented}, (X ⟶ Y) → Prop
  | mk {a b : P.V} (e : P.Gen a b) (he : S e) : PickedCell (genArrow P e)

/-- **The arrows the picked 1-cells name.** -/
def pickedCells : MorphismProperty P.presented := fun _ _ f => PickedCell P S f

/-- **…and the class they generate.** -/
def pickedClosure : MorphismProperty P.presented := (pickedCells P S).multiplicativeClosure

theorem pickedCells_le_pickedClosure : pickedCells P S ≤ pickedClosure P S :=
  MorphismProperty.le_multiplicativeClosure _

instance : (pickedClosure P S).IsMultiplicative :=
  inferInstanceAs (pickedCells P S).multiplicativeClosure.IsMultiplicative

/-- **The extension inverts the class** — the cancellation 2-cells do it one generator at a time. -/
theorem inverts_pickedClosure :
    (pickedClosure P S).IsInvertedBy (invIncl P S).functor := by
  have h : pickedClosure P S
      ≤ (MorphismProperty.isomorphisms _).inverseImage (invIncl P S).functor :=
    (MorphismProperty.multiplicativeClosure_le_iff _ _).mpr (by
      rintro X Y f ⟨e, he⟩
      exact isIso_fwdArrow P S e he)
  exact fun _ _ f hf => h f hf

/-! ## Reading the extension in a target

A functor out of `P.presented` inverting the picked cells is exactly a functor out of the extension:
the formal inverse has nowhere to go but the inverse. -/

section Desc

variable {E : Type*} [Category E] (F : P.presented ⥤ E)
  (hF : (pickedCells P S).IsInvertedBy F)

/-- The arrow a picked 1-cell names downstairs, as an isomorphism. -/
private noncomputable def descIso {a b : P.V} (e : P.Gen a b) (he : S e) :
    F.obj ⟨⟨a⟩⟩ ≅ F.obj ⟨⟨b⟩⟩ :=
  @asIso _ _ _ _ (F.map (genArrow P e)) (hF _ (PickedCell.mk e he))

private noncomputable def invMap :
    ∀ {a b : P.V}, InvGen P S a b → (F.obj ⟨⟨a⟩⟩ ⟶ F.obj ⟨⟨b⟩⟩)
  | _, _, .inl e => F.map (genArrow P e)
  | _, _, .inr ⟨e, he⟩ => (descIso P S F hF e he).inv

/-- The cells, read in `E`. -/
private noncomputable def invInterp : GenObj (InvGen P S) ⥤q E where
  obj x := F.obj ⟨⟨x.as⟩⟩
  map {x y} e := invMap P S F hF (e : InvGen P S x.as y.as)

/-- **A word of `P`, read through the extension.** -/
private theorem lift_invInterp_fwd {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (Paths.lift (invInterp P S F hF)).map ((fwdPre P S).mapPath u) = F.map (P.quot.map u) := by
  induction u with
  | nil =>
      rw [Prefunctor.mapPath_nil, Paths.lift_nil]
      exact ((congrArg F.map (P.quot.map_id _)).trans (F.map_id _)).symm
  | cons u e ih =>
      rw [Prefunctor.mapPath_cons, Paths.lift_cons, ih,
        show P.quot.map (u.cons e) = P.quot.map u ≫ P.quot.map (Quiver.Hom.toPath e) from
          P.quot.map_comp u (Quiver.Hom.toPath e),
        F.map_comp]
      rfl

private theorem invSound {x y : GenObj (InvGen P S)} (α : InvRel P S x y) :
    (Paths.lift (invInterp P S F hF)).map (invSrc P S α)
      = (Paths.lift (invInterp P S F hF)).map (invTgt P S α) := by
  cases α with
  | keep α =>
      exact (lift_invInterp_fwd P S F hF (P.src α)).trans
        ((congrArg F.map (P.quot_src_tgt α)).trans (lift_invInterp_fwd P S F hF (P.tgt α)).symm)
  | cancel e he =>
      change (Paths.lift (invInterp P S F hF)).map
            ((fwdCell P S e).toPath.comp (bwdCell P S e he).toPath)
          = (Paths.lift (invInterp P S F hF)).map Quiver.Path.nil
      rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath, Paths.lift_nil]
      exact (descIso P S F hF e he).hom_inv_id
  | cancel' e he =>
      change (Paths.lift (invInterp P S F hF)).map
            ((bwdCell P S e he).toPath.comp (fwdCell P S e).toPath)
          = (Paths.lift (invInterp P S F hF)).map Quiver.Path.nil
      rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath, Paths.lift_nil]
      exact (descIso P S F hF e he).inv_hom_id

/-- **The functor a reading of `P` with invertible picked cells descends to.** -/
noncomputable def invDesc : (invPoly P S).presented ⥤ E :=
  Polygraph.desc (P := invPoly P S) (invInterp P S F hF) (invSound P S F hF)

/-- **…and it restricts to the reading it came from.** -/
theorem invIncl_comp_invDesc : (invIncl P S).functor ⋙ invDesc P S F hF = F :=
  Quotient.lift_unique' P.homRel _ F
    (Functor.ext (fun _ => rfl) fun _ _ u =>
      (lift_invInterp_fwd P S F hF u).trans
        ((Category.comp_id _).symm.trans (Category.id_comp _).symm))

end Desc

/-- **A functor out of the extension is pinned by its restriction to `P`** — the formal inverse has
no choice but the inverse, and the 1-cells of `P` span the rest. -/
theorem invIncl_comp_injective {E : Type*} [Category E]
    {F₁ F₂ : (invPoly P S).presented ⥤ E}
    (h : (invIncl P S).functor ⋙ F₁ = (invIncl P S).functor ⋙ F₂) : F₁ = F₂ := by
  have hobj : ∀ x : GenObj (invPoly P S).Gen, F₁.obj ⟨x⟩ = F₂.obj ⟨x⟩ :=
    fun x => Functor.congr_obj h (⟨⟨x.as⟩⟩ : P.presented)
  have hφ : Paths.of (GenObj (invPoly P S).Gen) ⋙q ((invPoly P S).quot ⋙ F₁).toPrefunctor
      = Paths.of (GenObj (invPoly P S).Gen) ⋙q ((invPoly P S).quot ⋙ F₂).toPrefunctor := by
    refine Prefunctor.ext_homOfEq hobj fun x y e => ?_
    refine Eq.trans ?_ (homOfEq_eq_eqToHom_conj _ (hobj x) (hobj y)).symm
    rcases e with e' | ⟨e', he⟩
    · exact Functor.congr_hom h (genArrow P e')
    · have hfwd : F₁.map (fwdArrow P S e')
          = eqToHom (hobj y) ≫ F₂.map (fwdArrow P S e') ≫ eqToHom (hobj x).symm := by
        rw [← invIncl_functor_genArrow P S e']
        exact Functor.congr_hom h (genArrow P e')
      exact Iso.inv_eqToHom_conj (mapFwdIso P S F₁ e' he) (mapFwdIso P S F₂ e' he)
        (hobj y) (hobj x) hfwd
  exact Quotient.lift_unique' (invPoly P S).homRel F₁ F₂
    ((Paths.lift_unique _ ((invPoly P S).quot ⋙ F₁) rfl).trans
      ((congrArg Paths.lift hφ).trans
        (Paths.lift_unique _ ((invPoly P S).quot ⋙ F₂) rfl).symm))

/-! ## The extension is a localization -/

/-- **The strict universal property of the localization**, at every target. -/
noncomputable def invStrict (E : Type*) [Category E] :
    Localization.StrictUniversalPropertyFixedTarget (invIncl P S).functor
      (pickedClosure P S) E where
  inverts := inverts_pickedClosure P S
  lift F hF := invDesc P S F
    (MorphismProperty.IsInvertedBy.of_le _ _ F hF (pickedCells_le_pickedClosure P S))
  fac F _ := invIncl_comp_invDesc P S F _
  uniq _ _ h := invIncl_comp_injective P S h

/-- **The extension localizes at the class the picked 1-cells generate.** -/
theorem isLocalization_invIncl :
    (invIncl P S).functor.IsLocalization (pickedClosure P S) :=
  Functor.IsLocalization.mk' _ _ (invStrict P S _) (invStrict P S _)

end Invert

end Polygraph

/-! ## The presentation of a localization -/

namespace Presents

open Polygraph

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)
  (S : ∀ {a b : P.V}, P.Gen a b → Prop)

/-- The arrow of `C` a picked 1-cell evaluates to. -/
inductive Picked : ∀ {A B : C}, (A ⟶ B) → Prop
  | mk {a b : P.V} (e : P.Gen a b) (he : S e) : Picked (p.arrow (cell e))

/-- **The arrows the picked 1-cells evaluate to.** -/
def pickedArrows : MorphismProperty C := fun _ _ f => p.Picked S f

/-- **A picked arrow is the image of a picked cell.** -/
theorem arrow_eq_E_map_genArrow {a b : P.V} (e : P.Gen a b) :
    p.arrow (cell e) = p.E.map (genArrow P e) := rfl

variable {W : MorphismProperty C} (hW : W = (p.pickedArrows S).multiplicativeClosure)

/-- The extension, read in `C` through a chosen inverse of the presentation. -/
private noncomputable def locLeg : C ⥤ (invPoly P S).presented :=
  p.equiv.inverse ⋙ (invIncl P S).functor

/-- …and that reading agrees with the extension along the presentation. -/
private noncomputable def locLegIso :
    p.equiv.functor ⋙ p.locLeg S ≅ (invIncl P S).functor :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p.equiv.unitIso.symm _
    ≪≫ Functor.leftUnitor _

include hW in
private theorem inverts_locLeg : W.IsInvertedBy (p.locLeg S) := by
  have hiso : (pickedClosure P S).IsInvertedBy (p.equiv.functor ⋙ p.locLeg S) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _ (p.locLegIso S)).mpr
      (inverts_pickedClosure P S)
  have h : (p.pickedArrows S).multiplicativeClosure
      ≤ (MorphismProperty.isomorphisms _).inverseImage (p.locLeg S) :=
    (MorphismProperty.multiplicativeClosure_le_iff _ _).mpr (by
      rintro A B f ⟨e, he⟩
      rw [p.arrow_eq_E_map_genArrow e]
      exact hiso (genArrow P e) (pickedCells_le_pickedClosure P S _ (PickedCell.mk e he)))
  rw [hW]
  exact fun _ _ f hf => h f hf

include hW in
private theorem pickedClosure_le :
    pickedClosure P S ≤ W.isoClosure.inverseImage p.equiv.functor := by
  haveI : W.IsMultiplicative := by rw [hW]; infer_instance
  refine le_trans ((MorphismProperty.multiplicativeClosure_le_iff _ _).mpr ?_)
    (MorphismProperty.monotone_inverseImage _ (MorphismProperty.le_isoClosure W))
  rintro X Y f ⟨e, he⟩
  rw [hW]
  exact MorphismProperty.le_multiplicativeClosure _ _ (Picked.mk e he)

include hW in
/-- **Adjoining a formal inverse to some of the generators presents the localization** at the class
those generators evaluate to. -/
noncomputable def presentsLocalization : Presents (invPoly P S) W.Localization := by
  haveI : (invIncl P S).functor.IsLocalization (pickedClosure P S) :=
    isLocalization_invIncl P S
  haveI : (p.locLeg S).IsLocalization W :=
    Functor.IsLocalization.of_equivalence_source (invIncl P S).functor (pickedClosure P S)
      (p.locLeg S) W p.equiv (p.pickedClosure_le S hW) (p.inverts_locLeg S hW) (p.locLegIso S)
  exact ⟨(Localization.equivalenceFromModel (p.locLeg S) W).inverse, inferInstance⟩

end Presents

end CategoryTheory
