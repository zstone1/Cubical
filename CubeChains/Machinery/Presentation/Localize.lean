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

`invWord` inverts a word of picked 1-cells; `invPolyMap`/`invFunctor` and `invCells`/`invSpelling`
carry a map of polygraphs and a spelling along the extension.
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

/-! ## The formal inverse of a word -/

section InvWord

/-- **The formal inverse of a word all of whose letters are picked** — read backwards.
`termination_by structural` is load-bearing: the proof argument otherwise sends the equation
compiler to well-founded recursion, and then `invWord` stops unfolding. -/
def invWord (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    Quiver.Path ((fwdPre P S).obj y) ((fwdPre P S).obj x) :=
  match u, h with
  | .nil, _ => Quiver.Path.nil
  | .cons v e, h =>
      (bwdCell P S e ((Quiver.Path.all_cons_iff v e).mp h).2).toPath.comp
        (invWord P S v ((Quiver.Path.all_cons_iff v e).mp h).1)
termination_by structural u

@[simp] theorem invWord_nil (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x : GenObj P.Gen}
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) (Quiver.Path.nil : Quiver.Path x x)) :
    invWord P S (Quiver.Path.nil : Quiver.Path x x) h = Quiver.Path.nil := rfl

theorem invWord_cons (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y z : GenObj P.Gen} (u : Quiver.Path x y) (e : y ⟶ z) (he : S e)
    (h₀ : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) (u.cons e)) :
    invWord P S (u.cons e) h = (bwdCell P S e he).toPath.comp (invWord P S u h₀) := rfl

/-- **A formal inverse is spelled out of formal inverses** — the `All` predicate a contraction of
the adjoined cells needs. -/
theorem all_invWord (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {T : ∀ ⦃x y : GenObj (InvGen P S)⦄, (x ⟶ y) → Prop}
    (hT : ∀ {a b : P.V} (e : P.Gen a b) (he : S e), T (bwdCell P S e he)) :
    ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y)
      (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u), Quiver.Path.All T (invWord P S u h) := by
  intro x y u
  induction u with
  | nil => exact fun _ => Quiver.Path.all_nil _
  | cons u e ih =>
      intro h
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      rw [invWord_cons P S u e he h₀ h]
      exact (Quiver.Path.all_toPath.mpr (hT e he)).comp (ih h₀)

private theorem quot_invWord_aux (P : Polygraph.{w, u', w₂})
    (S : ∀ {a b : P.V}, P.Gen a b → Prop) :
    ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y)
      (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u),
      ((invPoly P S).quot.map ((fwdPre P S).mapPath u)
            ≫ (invPoly P S).quot.map (invWord P S u h)
          = 𝟙 ((invPoly P S).quot.obj ((fwdPre P S).obj x)))
        ∧ ((invPoly P S).quot.map (invWord P S u h)
            ≫ (invPoly P S).quot.map ((fwdPre P S).mapPath u)
          = 𝟙 ((invPoly P S).quot.obj ((fwdPre P S).obj y))) := by
  intro x y u
  induction u with
  | nil =>
      refine fun h => ⟨?_, ?_⟩ <;>
        exact ((invPoly P S).quot.map_comp _ _).symm.trans
          ((invPoly P S).quot.map_id ((fwdPre P S).obj x))
  | cons u e ih =>
      intro h
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      obtain ⟨ih₁, ih₂⟩ := ih h₀
      have hfw : (invPoly P S).quot.map ((fwdPre P S).mapPath u) ≫ fwdArrow P S e
          = (invPoly P S).quot.map ((fwdPre P S).mapPath (u.cons e)) :=
        ((invPoly P S).quot.map_comp ((fwdPre P S).mapPath u) (fwdCell P S e).toPath).symm
      have hbw : bwdArrow P S e he ≫ (invPoly P S).quot.map (invWord P S u h₀)
          = (invPoly P S).quot.map (invWord P S (u.cons e) h) :=
        ((invPoly P S).quot.map_comp (bwdCell P S e he).toPath (invWord P S u h₀)).symm
      rw [← hfw, ← hbw]
      let iso := Iso.mk ((invPoly P S).quot.map ((fwdPre P S).mapPath u))
        ((invPoly P S).quot.map (invWord P S u h₀)) ih₁ ih₂ ≪≫ fwdIso P S e he
      exact ⟨iso.hom_inv_id, iso.inv_hom_id⟩

/-- **A word of picked 1-cells cancels its formal inverse.** -/
theorem quot_fwd_invWord (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    (invPoly P S).quot.map ((fwdPre P S).mapPath u)
        ≫ (invPoly P S).quot.map (invWord P S u h) = 𝟙 _ :=
  (quot_invWord_aux P S u h).1

/-- **…and is cancelled by it.** -/
theorem quot_invWord_fwd (P : Polygraph.{w, u', w₂}) (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    (invPoly P S).quot.map (invWord P S u h)
        ≫ (invPoly P S).quot.map ((fwdPre P S).mapPath u) = 𝟙 _ :=
  (quot_invWord_aux P S u h).2

end InvWord

/-! ## The extension along a map of polygraphs -/

universe w' u'' w₂'

section Map

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}
  (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)
  (f : Hom P Q) (hf : ∀ {a b : P.V} (e : P.Gen a b), S e → T (f.pre.map (cell e)))

private def invPre : GenObj (InvGen P S) ⥤q GenObj (InvGen Q T) where
  obj x := ⟨(f.pre.obj ⟨x.as⟩).as⟩
  map {x y} e := match (e : InvGen P S x.as y.as) with
    | .inl e' => Sum.inl (f.pre.map (cell e'))
    | .inr ⟨e', he⟩ => Sum.inr ⟨f.pre.map (cell e'), hf e' he⟩

private theorem fwdPre_comp_invPre : fwdPre P S ⋙q invPre S T f hf = f.pre ⋙q fwdPre Q T := rfl

/-- **A map carrying picked 1-cells to picked 1-cells extends to the formal inverses.** -/
def invPolyMap : Hom (invPoly P S) (invPoly Q T) where
  pre := invPre S T f hf
  two {x y} α := match α with
    | .keep α => .keep (f.two α)
    | .cancel e he => .cancel (f.pre.map (cell e)) (hf e he)
    | .cancel' e he => .cancel' (f.pre.map (cell e)) (hf e he)
  src_two α := by
    cases α with
    | keep α =>
        change (fwdPre Q T).mapPath (Q.src (f.two α))
            = (invPre S T f hf).mapPath ((fwdPre P S).mapPath (P.src α))
        rw [f.src_two α, ← Prefunctor.mapPath_comp_apply f.pre (fwdPre Q T),
          ← Prefunctor.mapPath_comp_apply (fwdPre P S) (invPre S T f hf)]
        exact (eq_of_heq
          (Prefunctor.mapPath_heq_of_eq (fwdPre_comp_invPre S T f hf) (P.src α))).symm
    | cancel e he => rfl
    | cancel' e he => rfl
  tgt_two α := by
    cases α with
    | keep α =>
        change (fwdPre Q T).mapPath (Q.tgt (f.two α))
            = (invPre S T f hf).mapPath ((fwdPre P S).mapPath (P.tgt α))
        rw [f.tgt_two α, ← Prefunctor.mapPath_comp_apply f.pre (fwdPre Q T),
          ← Prefunctor.mapPath_comp_apply (fwdPre P S) (invPre S T f hf)]
        exact (eq_of_heq
          (Prefunctor.mapPath_heq_of_eq (fwdPre_comp_invPre S T f hf) (P.tgt α))).symm
    | cancel e he => rfl
    | cancel' e he => rfl

/-- **…carrying a word of picked 1-cells to the pushed-forward word.** -/
theorem invPolyMap_mapPath_fwd {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (invPolyMap S T f hf).pre.mapPath ((fwdPre P S).mapPath u)
      = (fwdPre Q T).mapPath (f.pre.mapPath u) :=
  (Prefunctor.mapPath_comp_apply (fwdPre P S) (invPolyMap S T f hf).pre u).symm.trans
    ((eq_of_heq (Prefunctor.mapPath_heq_of_eq (fwdPre_comp_invPre S T f hf) u)).trans
      (Prefunctor.mapPath_comp_apply f.pre (fwdPre Q T) u))

/-- **…and the formal inverse of a word to the formal inverse of the pushed-forward word.** -/
theorem invPolyMap_mapPath_invWord {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u)
    (h' : Quiver.Path.All (fun ⦃_ _⦄ e => T e) (f.pre.mapPath u)) :
    (invPolyMap S T f hf).pre.mapPath (invWord P S u h)
      = invWord Q T (f.pre.mapPath u) h' := by
  revert h h'
  induction u with
  | nil => intro h h'; rfl
  | cons u e ih =>
      intro h h'
      obtain ⟨h₀, he⟩ := (Quiver.Path.all_cons_iff u e).mp h
      obtain ⟨h₀', -⟩ := (Quiver.Path.all_cons_iff _ _).mp h'
      refine Eq.trans (congrArg (invPre S T f hf).mapPath
        (invWord_cons P S u e he h₀ h)) ?_
      refine Eq.trans (Prefunctor.mapPath_comp (invPre S T f hf)
        (bwdCell P S e he).toPath (invWord P S u h₀)) ?_
      refine Eq.trans ?_ (invWord_cons Q T (f.pre.mapPath u) (f.pre.map (cell e))
        (hf e he) h₀' h').symm
      exact congrArg (Quiver.Path.comp (bwdCell Q T (f.pre.map (cell e)) (hf e he)).toPath)
        (ih h₀ h₀')

end Map

section MapLaws

theorem invPolyMap_congr {P Q : Polygraph.{w, u', w₂}}
    (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)
    {f g : Hom P Q} (h : f = g)
    (hf : ∀ {a b : P.V} (e : P.Gen a b), S e → T (f.pre.map (cell e)))
    (hg : ∀ {a b : P.V} (e : P.Gen a b), S e → T (g.pre.map (cell e))) :
    invPolyMap S T f hf = invPolyMap S T g hg := by subst h; rfl

theorem invPolyMap_id {P : Polygraph.{w, u', w₂}} (S : ∀ {a b : P.V}, P.Gen a b → Prop)
    (hS : ∀ {a b : P.V} (e : P.Gen a b), S e → S ((𝟙 P : Hom P P).pre.map (cell e))) :
    invPolyMap S S (𝟙 P) hS = 𝟙 (invPoly P S) :=
  Hom.ext' (Prefunctor.ext' (fun _ => rfl) fun _ _ e => by rcases e with e | ⟨e, he⟩ <;> rfl)
    fun α => by cases α <;> rfl

theorem invPolyMap_comp {P Q R : Polygraph.{w, u', w₂}}
    (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)
    (U : ∀ {a b : R.V}, R.Gen a b → Prop) (f : P ⟶ Q) (g : Q ⟶ R)
    (hf : ∀ {a b : P.V} (e : P.Gen a b), S e → T (f.pre.map (cell e)))
    (hg : ∀ {a b : Q.V} (e : Q.Gen a b), T e → U (g.pre.map (cell e)))
    (hfg : ∀ {a b : P.V} (e : P.Gen a b), S e → U ((f ≫ g).pre.map (cell e))) :
    invPolyMap S U (f ≫ g) hfg
      = (invPolyMap S T f hf ≫ invPolyMap T U g hg : invPoly P S ⟶ invPoly R U) :=
  Hom.ext' (Prefunctor.ext' (fun _ => rfl) fun _ _ e => by rcases e with e | ⟨e, he⟩ <;> rfl)
    fun α => by cases α <;> rfl

end MapLaws

section Fun

variable {D : Type*} [Category D] (G : D ⥤ Polygraph.{w, u', w₂})
  (S : ∀ (d : D) {a b : (G.obj d).V}, (G.obj d).Gen a b → Prop)
  (hS : ∀ {d d' : D} (u : d ⟶ d') {a b : (G.obj d).V} (e : (G.obj d).Gen a b),
    S d e → S d' ((G.map u).pre.map (cell e)))

/-- **A functor into `Polygraph` whose picked 1-cells are carried along, with the picked 1-cells
formally inverted.** -/
def invFunctor : D ⥤ Polygraph.{w, u', max u' w w₂} where
  obj d := invPoly (G.obj d) (S d)
  map {d d'} u := invPolyMap (S d) (S d') (G.map u) (hS u)
  map_id d := (invPolyMap_congr (S d) (S d) (G.map_id d) (hS (𝟙 d)) fun _ he => he).trans
    (invPolyMap_id (S d) fun _ he => he)
  map_comp {d d' d''} u v :=
    (invPolyMap_congr (S d) (S d'') (G.map_comp u v) (hS (u ≫ v))
        fun e he => hS v _ (hS u e he)).trans
      (invPolyMap_comp (S d) (S d') (S d'') (G.map u) (G.map v) (hS u) (hS v)
        fun e he => hS v _ (hS u e he))

@[simp] theorem invFunctor_obj (d : D) : (invFunctor G S hS).obj d = invPoly (G.obj d) (S d) := rfl

@[simp] theorem invFunctor_map {d d' : D} (u : d ⟶ d') :
    (invFunctor G S hS).map u = invPolyMap (S d) (S d') (G.map u) (hS u) := rfl

end Fun

/-! ## A spelling, on the formal inverses -/

section Spell

variable {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}}
  (S : ∀ {a b : P.V}, P.Gen a b → Prop) (T : ∀ {a b : Q.V}, Q.Gen a b → Prop)

/-- **The words a picked-respecting spelling of the 1-cells spells, on the formal inverses.** -/
def invCells (X : GenObj P.Gen ⥤q Q.Word)
    (hX : ∀ {a b : P.V} (e : P.Gen a b), S e →
      Quiver.Path.All (fun ⦃_ _⦄ e' => T e') (X.map (cell e))) :
    GenObj (InvGen P S) ⥤q (invPoly Q T).Word where
  obj x := (fwdPre Q T).obj (X.obj ⟨x.as⟩)
  map {x y} e := match (e : InvGen P S x.as y.as) with
    | .inl e' => (fwdPre Q T).mapPath (X.map (cell e'))
    | .inr ⟨e', he⟩ => invWord Q T (X.map (cell e')) (hX e' he)

/-- **Equal spellings spell equally on the formal inverses** — proof irrelevance in `hX`. -/
theorem invCells_congr {X X' : GenObj P.Gen ⥤q Q.Word} (h : X = X')
    (hX : ∀ {a b : P.V} (e : P.Gen a b), S e →
      Quiver.Path.All (fun ⦃_ _⦄ e' => T e') (X.map (cell e)))
    (hX' : ∀ {a b : P.V} (e : P.Gen a b), S e →
      Quiver.Path.All (fun ⦃_ _⦄ e' => T e') (X'.map (cell e))) :
    invCells S T X hX = invCells S T X' hX' := by subst h; rfl

private theorem lift_invCells_fwd (X : GenObj P.Gen ⥤q Q.Word) (hX) {x y : GenObj P.Gen}
    (u : Quiver.Path x y) :
    (Paths.lift (invCells S T X hX)).map ((fwdPre P S).mapPath u)
      = (fwdPre Q T).mapPath ((Paths.lift X).map u) :=
  (Paths.lift_mapPath (fwdPre P S) (invCells S T X hX) u).trans
    (Paths.lift_comp_map X (fwdPre Q T).pathsFunctor u).symm

variable (ψ : Spelling P Q)
  (hψ : ∀ {a b : P.V} (e : P.Gen a b), S e →
    Quiver.Path.All (fun ⦃_ _⦄ e' => T e') (ψ.cells.map (cell e)))

/-- **A spelling whose picked 1-cells spell words of picked 1-cells extends to the formal
inverses** — the inverse of a word is the reversed word of inverses. -/
def invSpelling : Spelling (invPoly P S) (invPoly Q T) where
  cells := invCells S T ψ.cells hψ
  sound α := by
    cases α with
    | keep α =>
        change (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((fwdPre P S).mapPath (P.src α)))
            = (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((fwdPre P S).mapPath (P.tgt α)))
        rw [lift_invCells_fwd S T ψ.cells hψ, lift_invCells_fwd S T ψ.cells hψ]
        exact Hom.quot_map_congr (invIncl Q T) (ψ.sound α)
    | cancel e he =>
        change (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((fwdCell P S e).toPath.comp (bwdCell P S e he).toPath))
            = (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map Quiver.Path.nil)
        rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath]
        exact (((invPoly Q T).quot.map_comp _ _).trans
          (quot_fwd_invWord Q T (ψ.cells.map (cell e)) (hψ e he))).trans
          ((invPoly Q T).quot.map_id _).symm
    | cancel' e he =>
        change (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map
              ((bwdCell P S e he).toPath.comp (fwdCell P S e).toPath))
            = (invPoly Q T).quot.map ((Paths.lift (invCells S T ψ.cells hψ)).map Quiver.Path.nil)
        rw [Paths.lift_map_comp, Paths.lift_toPath, Paths.lift_toPath]
        exact (((invPoly Q T).quot.map_comp _ _).trans
          (quot_invWord_fwd Q T (ψ.cells.map (cell e)) (hψ e he))).trans
          ((invPoly Q T).quot.map_id _).symm

@[simp] theorem invSpelling_cells :
    (invSpelling S T ψ hψ).cells = invCells S T ψ.cells hψ := rfl

end Spell

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
private theorem isLocalization_locLeg : (p.locLeg S).IsLocalization W :=
  haveI : (invIncl P S).functor.IsLocalization (pickedClosure P S) :=
    isLocalization_invIncl P S
  Functor.IsLocalization.of_equivalence_source (invIncl P S).functor (pickedClosure P S)
    (p.locLeg S) W p.equiv (p.pickedClosure_le S hW) (p.inverts_locLeg S hW) (p.locLegIso S)

include hW in
/-- **Adjoining a formal inverse to some of the generators presents the localization** at the class
those generators evaluate to. -/
noncomputable def presentsLocalization : Presents (invPoly P S) W.Localization :=
  haveI := p.isLocalization_locLeg S hW
  ⟨(Localization.equivalenceFromModel (p.locLeg S) W).inverse, inferInstance⟩

/-! ### …compatibly with `Q`

What the extension presents is read through `Q`: a 1-cell of `P` names, in the localization, the
arrow `P` named, and a formal inverse names its inverse.  Nothing abstract gives this — two
localization functors with the same target differ by an automorphism — so it is proved where the
construction is. -/

include hW in
/-- **The comparison**: the extension, read in the localization, is `P`'s reading then `Q`. -/
noncomputable def locComparison :
    (invIncl P S).functor ⋙ (p.presentsLocalization S hW).E ≅ p.E ⋙ W.Q :=
  haveI := p.isLocalization_locLeg S hW
  Functor.isoWhiskerRight (p.locLegIso S).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft p.equiv.functor
      (Localization.compEquivalenceFromModelInverseIso (p.locLeg S) W)

include hW in
/-- **A word of `P`, read in the localization.** -/
theorem eval_fwd_mapPath {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (p.presentsLocalization S hW).eval.map ((fwdPre P S).mapPath u)
      = ((p.locComparison S hW).app ⟨x⟩).hom ≫ W.Q.map (p.eval.map u)
        ≫ ((p.locComparison S hW).app ⟨y⟩).inv :=
  have hnat : ((invIncl P S).functor ⋙ (p.presentsLocalization S hW).E).map (P.quot.map u)
      ≫ ((p.locComparison S hW).app ⟨y⟩).hom
    = ((p.locComparison S hW).app ⟨x⟩).hom ≫ (p.E ⋙ W.Q).map (P.quot.map u) :=
    (p.locComparison S hW).hom.naturality (P.quot.map u)
  ((Iso.eq_comp_inv ((p.locComparison S hW).app ⟨y⟩)).mpr hnat).trans (Category.assoc _ _ _)

include hW in
/-- **A word of picked 1-cells, read in the localization, is inverted by its formal inverse.** -/
theorem eval_fwd_comp_invWord {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    (p.presentsLocalization S hW).eval.map ((fwdPre P S).mapPath u)
        ≫ (p.presentsLocalization S hW).eval.map (invWord P S u h) = 𝟙 _ :=
  ((p.presentsLocalization S hW).E.map_comp _ _).symm.trans
    ((congrArg (p.presentsLocalization S hW).E.map (quot_fwd_invWord P S u h)).trans
      ((p.presentsLocalization S hW).E.map_id _))

include hW in
/-- …and inverts it. -/
theorem eval_invWord_comp_fwd {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => S e) u) :
    (p.presentsLocalization S hW).eval.map (invWord P S u h)
        ≫ (p.presentsLocalization S hW).eval.map ((fwdPre P S).mapPath u) = 𝟙 _ :=
  ((p.presentsLocalization S hW).E.map_comp _ _).symm.trans
    ((congrArg (p.presentsLocalization S hW).E.map (quot_invWord_fwd P S u h)).trans
      ((p.presentsLocalization S hW).E.map_id _))

end Presents

end CategoryTheory
