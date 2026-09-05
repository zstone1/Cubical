import CubeChains.Machinery.Presentation.Basic
import CubeChains.Machinery.Presentation.Adjunction
import CubeChains.Machinery.Presentation.Coequalizer
import CubeChains.Machinery.Localization.SliceFamily
import CubeChains.Machinery.Localization.HomInduction
import Mathlib.CategoryTheory.Elements

/-!
# Machinery/Presentation/Glue — one copy of `P d` for each element over `d`

`elementsPoly X P` is the **slice diagram**: `∫X ⟶ D` is a discrete fibration, so the copies of
`P d` are indexed by the elements over `d` and glue along the arrows of `(∫X)ᵒᵖ`.  Nothing but the
colimit's universal property is ever used — the comparison `Φ` is `colimit.desc`, the unit is
`colimit.hom_ext`, and no 0-cell is examined anywhere.

`presentsSliceColimit` says `colimit (elementsPoly X P)` presents `(∫X)[W⁻¹]`, given a family of
slice presentations (`p`, `hP`), thin localized slices (`hthin`), and one condition on the 0-cells:
they are a **skeleton** of each localized slice (`R : SliceSkeleton`).  Faithful comes from the
strict retraction, essential surjectivity from the skeleton, and fullness from an induction over
the words of `(∫X)[W⁻¹]` — every obligation a `Prop`.
-/

universe w w' v₁ u₁ u' w₂ u

namespace CategoryTheory

open Opposite

/-- **A sandwich is pinned by its filling up to `HEq`**: the crusts are forced by the endpoints,
so heterogeneously equal fillings give equal sandwiches. -/
theorem eqToHom_conj_eq_of_heq {E : Type*} [Category E] {A B A₁ B₁ A₂ B₂ : E}
    (h₁ : A = A₁) (k₁ : B₁ = B) (h₂ : A = A₂) (k₂ : B₂ = B)
    {m : A₁ ⟶ B₁} {n : A₂ ⟶ B₂} (h : m ≍ n) :
    eqToHom h₁ ≫ m ≫ eqToHom k₁ = eqToHom h₂ ≫ n ≫ eqToHom k₂ := by
  subst h₁; subst k₁; subst h₂; subst k₂; cases h; simp


namespace Polygraph

/-- **A polygraph's 0-cells *are* the objects of the category it presents** — `Quotient` and
`Paths` both leave the objects alone. -/
def presentedVEquiv (Q : Polygraph.{w', u', w₂}) : Q.V ≃ Q.presented where
  toFun a := ⟨⟨a⟩⟩
  invFun X := X.as.as
  left_inv _ := rfl
  right_inv _ := rfl

variable {D : Type u₁} [Category.{v₁} D] (X : Dᵒᵖ ⥤ Type w) (P : D ⥤ Polygraph.{w', u', w₂})

/-- The 0-cells of `P d` name objects of `Over d`, and `P.map f` acts on them by postcomposition. -/
structure SliceLabels where
  /-- the arrow into `d` that a 0-cell names -/
  ob (d : D) : (P.obj d).V → Over d
  /-- `P.map f` postcomposes with `f` -/
  map_ob {d' d : D} (f : d' ⟶ d) (a : GenObj (P.obj d').Gen) :
    ob d ((P.map f).pre.obj a).as = (Over.map f).obj (ob d' a.as)

variable {P} (L : SliceLabels P)

/-- The 0-cells of the glued polygraph: the objects of `∫X`. -/
abbrev GlueV : Type (max u₁ w) := Σ d : D, X.obj (op d)

/-- The object of `∫X` that a 0-cell of the copy at `x ∈ X d` names. -/
def gluePt (d : D) (x : X.obj (op d)) (a : (P.obj d).V) : GlueV X :=
  ⟨(L.ob d a).left, X.map ((L.ob d a).hom).op x⟩

/-- The overlap identification on 0-cells: the copy at `f* x` sits inside the copy at `x`. -/
theorem gluePt_map {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) (a : GenObj (P.obj d').Gen) :
    gluePt X L d x ((P.map f).pre.obj a).as = gluePt X L d' (X.map f.op x) a.as := by
  unfold gluePt
  rw [L.map_ob f a]
  exact congrArg (fun z => (⟨(L.ob d' a.as).left, z⟩ : GlueV X))
    (Functor.map_comp_apply X f.op ((L.ob d' a.as).hom).op x)


/-- **The objects of `∫X` a copy names.**  The 0-cells of the glued polygraph are the copies'
0-cells, so this is the image of the glued polygraph in `∫X`: an object is covered exactly when
some copy has a 0-cell labelled by an arrow into it. -/
def Covered : GlueV X → Prop :=
  fun v => ∃ (s : GlueV X) (a : (P.obj s.1).V), gluePt X L s.1 s.2 a = v

/-- …as a type. -/
abbrev CoveredV : Type (max u₁ w) := {v : GlueV X // Covered X L v}

/-! ## The labels a family of presentations supplies -/

section Labels

variable (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))

/-- `overMapLoc` on objects is `Over.map`. -/
theorem overMapLoc_obj {d' d : D} (f : d' ⟶ d) (Y : Over d') :
    (overMapLoc W f).obj (Localization.Construction.objEquiv (W.over (X := d')) Y) =
      Localization.Construction.objEquiv (W.over (X := d)) ((Over.map f).obj Y) :=
  Functor.congr_obj (overMapLocFac W f) Y

variable (hP : ∀ {d' d : D} (f : d' ⟶ d),
  (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f)

include hP in
/-- The labels a compatible family of presentations supplies. -/
noncomputable def labelsOf : SliceLabels P where
  ob d a := (Localization.Construction.objEquiv (W.over (X := d))).symm ((p d).at' ⟨a⟩)
  map_ob {d' d} f a := by
    apply (Localization.Construction.objEquiv (W.over (X := d))).symm_apply_eq.mpr
    rw [← overMapLoc_obj, Equiv.apply_symm_apply]
    exact Functor.congr_obj (hP f) ((P.obj d').quot.obj a)

/-- The labels of `labelsOf` are what the presentations say. -/
theorem labelsOf_ob (d : D) (a : (P.obj d).V) :
    (p d).at' ⟨a⟩ = Localization.Construction.objEquiv (W.over (X := d))
      ((labelsOf W p hP).ob d a) :=
  ((Localization.Construction.objEquiv (W.over (X := d))).apply_symm_apply _).symm

/-- **Labelling is bijective exactly when the presentation names each object of the slice once.**
`Presents` asks for an equivalence, which need be neither injective nor surjective on objects, so
this is a hypothesis on `p` and not a consequence of it — and
`Machinery/Presentation/GlueRefutation` is what happens without it. -/
theorem labelsOf_ob_bijective_iff (d : D) :
    Function.Bijective ((labelsOf W p hP).ob d) ↔ Function.Bijective (p d).E.obj := by
  rw [show (labelsOf W p hP).ob d
      = ((Localization.Construction.objEquiv (W.over (X := d))).symm ∘ (p d).E.obj) ∘
        presentedVEquiv (P.obj d) from rfl,
    Equiv.bijective_comp, Equiv.comp_bijective]

end Labels

/-! ## Interpreting the cells

`Presents.ofDesc` wants a prefunctor, so the comparison must be strict on objects.  The slice
equivalence of `Machinery/Slice` is an abstract `IsEquivalence`, so instead of inverting it we
write down its inverse: the cartesian lift, which is a genuine functor. -/

section Eval

variable (W : MorphismProperty D)

/-- The cartesian lift: an arrow into `d` is an arrow into `(d, x)` in `∫X`. -/
@[simps] def elementsLift (d : D) (x : X.obj (op d)) : Over d ⥤ (X.Elements)ᵒᵖ where
  obj u := op ⟨op u.left, X.map u.hom.op x⟩
  map {u u'} φ :=
    (CategoryOfElements.homMk _ _ φ.left.op (by
      rw [← Functor.map_comp_apply, ← op_comp, Over.w])).op
  map_id _ := rfl
  map_comp _ _ := rfl

theorem elementsLift_comp_π (d : D) (x : X.obj (op d)) :
    elementsLift X d x ⋙ (CategoryOfElements.π X).leftOp = Over.forget d := rfl

/-- An arrow of `∫X` pulls its target's element back to its source's. -/
theorem elements_snd_map {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    X.map ((CategoryOfElements.π X).leftOp.map u).op c.unop.2 = c'.unop.2 :=
  u.unop.property

@[simp] theorem elements_eqToHom_val {e₁ e₂ : X.Elements} (h : e₁ = e₂) :
    (eqToHom h : e₁ ⟶ e₂).val = eqToHom (congrArg Sigma.fst h) := by
  subst h; rfl

/-- **The lift is a section of the projection on slices**: going down to the base slice and
lifting back at `c`'s own element is doing nothing.  A strict equality, because
`elements_snd_map` is an equation between elements. -/
theorem elementsLift_post (c : (X.Elements)ᵒᵖ) :
    Over.post (CategoryOfElements.π X).leftOp ⋙
        elementsLift X ((CategoryOfElements.π X).leftOp.obj c) c.unop.2
      = Over.forget c := by
  refine Functor.ext (fun Y => ?_) (fun Y Y' φ => ?_)
  · exact congrArg (fun z => op (⟨Y.left.unop.1, z⟩ : X.Elements)) (elements_snd_map X Y.hom)
  · apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    simp


/-- The lift of a `W.over d`-arrow lies over `W`. -/
theorem elementsLift_inverts (d : D) (x : X.obj (op d)) :
    (W.over (X := d)).IsInvertedBy
      (elementsLift X d x ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q) := by
  intro _ _ φ hφ
  exact Localization.inverts (W.inverseImage (CategoryOfElements.π X).leftOp).Q
    (W.inverseImage (CategoryOfElements.π X).leftOp) ((elementsLift X d x).map φ) hφ

/-- The slice over `(d, x)`, localized, mapped into `(∫X)[W⁻¹]`. -/
noncomputable def glueSliceEval (d : D) (x : X.obj (op d)) :
    (W.over (X := d)).Localization ⥤
      (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  Localization.Construction.lift _ (elementsLift_inverts X W d x)

theorem glueSliceEval_fac (d : D) (x : X.obj (op d)) :
    (W.over (X := d)).Q ⋙ glueSliceEval X W d x =
      elementsLift X d x ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q :=
  Localization.Construction.fac _ _


/-- **The cartesian lift is functorial in the base**: lifting at `x` after postcomposing with `f`
is lifting at `f* x`.  This is what makes the overlap 2-cells sound. -/
theorem elementsLift_over_map {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) :
    Over.map f ⋙ elementsLift X d x = elementsLift X d' (X.map f.op x) := by
  refine Functor.ext (fun u => ?_) (fun u u' φ => ?_)
  · exact congrArg (fun y => op (⟨op u.left, y⟩ : X.Elements))
      (Functor.map_comp_apply X f.op u.hom.op x)
  · apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    simp

/-- …hence the localized comparison is too. -/
theorem overMapLoc_comp_glueSliceEval {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) :
    overMapLoc W f ⋙ glueSliceEval X W d x = glueSliceEval X W d' (X.map f.op x) :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, overMapLocFac, Functor.assoc, glueSliceEval_fac, glueSliceEval_fac,
      ← Functor.assoc, elementsLift_over_map])

end Eval

/-! ## The cartesian lift, on slices

`∫X ⟶ D` is a discrete fibration, so the slice of `(∫X)ᵒᵖ` over an element is the slice of `D` over
its base — strictly, which is what lets the retraction be a cocone. -/

section Slices
/-- For the elements projection, postcomposition and `Over.post` commute as a strict **equality**
rather than an iso: composition in `(X.Elements)ᵒᵖ` is `.val`-wise, so
`F.map (h ≫ u) = F.map h ≫ F.map u` holds definitionally. -/
theorem elementsPost_map {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Over.map u ⋙ Over.post (CategoryOfElements.π X).leftOp
      = Over.post (CategoryOfElements.π X).leftOp ⋙
        Over.map ((CategoryOfElements.π X).leftOp.map u) :=
  rfl

/-- **The cartesian lift, on slices**: an arrow into `F c` is an arrow into `c`.  This is the
strict inverse of `Over.post F`, which is what lets the slice over `c` be cancelled. -/
def elementsLiftOver (c : (X.Elements)ᵒᵖ) :
    Over ((CategoryOfElements.π X).leftOp.obj c) ⥤ Over c where
  obj Y := Over.mk (X := c)
    ((CategoryOfElements.homMk c.unop ⟨op Y.left, X.map Y.hom.op c.unop.2⟩ Y.hom.op rfl).op)
  map {Y Y'} φ :=
    Over.homMk ((elementsLift X ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).map φ) (by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      simp only [Functor.leftOp_obj, CategoryOfElements.π_obj, op_unop, Over.mk_left,
        elementsLift_map, Over.mk_hom, unop_comp, Quiver.Hom.unop_op,
        CategoryOfElements.comp_val, CategoryOfElements.homMk_coe]
      exact op_comp.symm.trans (congrArg Quiver.Hom.op (Over.w φ)))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem elementsLiftOver_forget (c : (X.Elements)ᵒᵖ) :
    elementsLiftOver X c ⋙ Over.forget c
      = elementsLift X ((CategoryOfElements.π X).leftOp.obj c) c.unop.2 := rfl

theorem elementsLiftOver_post (c : (X.Elements)ᵒᵖ) :
    elementsLiftOver X c ⋙ Over.post (CategoryOfElements.π X).leftOp
      = 𝟭 (Over ((CategoryOfElements.π X).leftOp.obj c)) := rfl

end Slices
/-! ## Inverting a slice presentation

A compact presentation is an equivalence, not an isomorphism of categories, and inverting one is a
choice.  What restores strictness is that the 0-cells are a **skeleton** of the localized slice:
every slice object is isomorphic there to the object of exactly one 0-cell. -/

section Skeleton

variable (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))

/-- **The 0-cells are a skeleton of the localized slice.**  One condition, and the entry, its
injectivity, its fixing of the 0-cells and its naturality in the base are all read off it — the
last from uniqueness, which is where naturality has to come from.

`Presents` asks only for an equivalence, and a localized slice is thin but never skeletal (a
`W`-arrow makes two distinct objects isomorphic), so this is a hypothesis on `p` and not a
consequence of it; `Machinery/Presentation/GlueRefutation` is what happens without it. -/
structure SliceSkeleton where
  /-- exactly one 0-cell names an object isomorphic to `y` -/
  entry {d : D} (y : Over d) :
    ∃! a : (P.obj d).V, Nonempty ((p d).at' ⟨a⟩ ≅ (W.over (X := d)).Q.obj y)

namespace SliceSkeleton

variable {W p} (R : SliceSkeleton W p)

/-- The 0-cell a slice object is entered from. -/
noncomputable def ret {d : D} (y : Over d) : (P.obj d).V := (R.entry y).choose

/-- **The entry, read in the localized slice.** -/
noncomputable def iso {d : D} (y : Over d) :
    (p d).at' ⟨R.ret y⟩ ≅ (W.over (X := d)).Q.obj y := (R.entry y).choose_spec.1.some

/-- **Nothing else enters `y`.** -/
theorem eq_ret {d : D} {a : (P.obj d).V} {y : Over d}
    (e : (p d).at' ⟨a⟩ ≅ (W.over (X := d)).Q.obj y) : a = R.ret y :=
  (R.entry y).choose_spec.2 a ⟨e⟩

/-- **A 0-cell's own slice object is entered from it.** -/
theorem fix {d : D} (a : (P.obj d).V) :
    R.ret ((Localization.Construction.objEquiv (W.over (X := d))).symm ((p d).at' ⟨a⟩)) = a :=
  (R.eq_ret (eqToIso ((Localization.Construction.objEquiv
    (W.over (X := d))).apply_symm_apply ((p d).at' ⟨a⟩)).symm)).symm

include R in
/-- **Distinct 0-cells name distinct slice objects** — the hypothesis `Presents` does not carry. -/
theorem at_injective (d : D) : Function.Injective fun a : (P.obj d).V => (p d).at' ⟨a⟩ :=
  fun a b h => (R.fix a).symm.trans
    ((congrArg (fun Z => R.ret ((Localization.Construction.objEquiv
      (W.over (X := d))).symm Z)) h).trans (R.fix b))

end SliceSkeleton

variable (hP : ∀ {d' d : D} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f)
  (hthin : ∀ d : D, Quiver.IsThin ((W.over (X := d)).Localization))
  (R : SliceSkeleton W p)

include p hthin in
/-- A poset is presented by a poset. -/
theorem presented_isThin (d : D) : Quiver.IsThin ((P.obj d).presented) :=
  haveI := hthin d
  isThin_of_equiv (p d).equiv.symm

include hP in
/-- **The entry is stable under pushing the base**: the pushed 0-cell enters the pushed object, and
nothing else does. -/
theorem ret_push {d' d : D} (f : d' ⟶ d) (y : Over d') :
    R.ret ((Over.map f).obj y) = ((P.map f).pre.obj ⟨R.ret y⟩).as :=
  (R.eq_ret (eqToIso (Functor.congr_obj (hP f) ⟨⟨R.ret y⟩⟩) ≪≫
    (overMapLoc W f).mapIso (R.iso y) ≪≫ eqToIso (overMapLoc_obj W f y))).symm

include hthin in
/-- **The slice presentation, inverted on the nose.**  Objects go to the 0-cell they are entered
from; morphisms are forced, the slice being a poset. -/
noncomputable def slInv (d : D) :
    (W.over (X := d)).Localization ⥤ (P.obj d).presented :=
  haveI := presented_isThin W p hthin d
  { obj := fun Y => ⟨⟨R.ret ((Localization.Construction.objEquiv (W.over (X := d))).symm Y)⟩⟩
    map := fun {Y Y'} g => (p d).E.preimage
      ((R.iso ((Localization.Construction.objEquiv (W.over (X := d))).symm Y)).hom ≫ g ≫
        (R.iso ((Localization.Construction.objEquiv (W.over (X := d))).symm Y')).inv)
    map_id := fun _ => Subsingleton.elim _ _
    map_comp := fun _ _ => Subsingleton.elim _ _ }

include hthin in
/-- **The inversion is a strict retraction of the presentation**: a 0-cell's own object is entered
from it, and a poset leaves the morphisms nothing to disagree about. -/
theorem comp_slInv (d : D) : (p d).E ⋙ slInv W p hthin R d = 𝟭 _ := by
  haveI := presented_isThin W p hthin d
  refine CategoryTheory.Functor.ext (fun Z => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  change (⟨⟨R.ret ((Localization.Construction.objEquiv (W.over (X := d))).symm
    ((p d).at' ⟨Z.as.as⟩))⟩⟩ : (P.obj d).presented) = Z
  rw [R.fix]
  rfl

include hP hthin in
/-- **A commuting square inverts to a commuting square** — `ret_push` and the poset in place of
bijectivity on objects. -/
theorem slInv_square {d' d : D} (f : d' ⟶ d) :
    overMapLoc W f ⋙ slInv W p hthin R d = slInv W p hthin R d' ⋙ (P.map f).functor := by
  haveI := presented_isThin W p hthin d
  refine CategoryTheory.Functor.ext (fun Y => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hy : (Localization.Construction.objEquiv (W.over (X := d))).symm ((overMapLoc W f).obj Y)
      = (Over.map f).obj ((Localization.Construction.objEquiv (W.over (X := d'))).symm Y) := by
    refine (Localization.Construction.objEquiv (W.over (X := d))).symm_apply_eq.mpr ?_
    rw [← overMapLoc_obj W f, Equiv.apply_symm_apply]
  change (⟨⟨R.ret ((Localization.Construction.objEquiv (W.over (X := d))).symm
      ((overMapLoc W f).obj Y))⟩⟩ : (P.obj d).presented)
    = ⟨(P.map f).pre.obj ⟨R.ret
        ((Localization.Construction.objEquiv (W.over (X := d'))).symm Y)⟩⟩
  rw [hy]
  exact congrArg (fun a => (⟨⟨a⟩⟩ : (P.obj d).presented)) (ret_push W p hP R f _)

end Skeleton

/-! ## The glued polygraph, as a colimit -/

section Colimit

open Limits

/-! ### Functors out of a colimit

`catHomEquiv` turns a functor out of `P.presented` into a morphism `P ⟶ catPoly C`, so a colimit
of polygraphs has the universal property of a colimit *on presented categories*: this is the whole
content of `presented ⊣ catPoly`, used in the only form the comparison needs. -/

variable {C : Type u} [Category.{u} C]

/-- **The transpose is natural in the polygraph.** -/
theorem homInvFun_comp {P Q : Polygraph.{u, u, u}} (f : P ⟶ Q) (F : Q.presented ⥤ C) :
    homInvFun (f.functor ⋙ F) = f ≫ homInvFun F :=
  catHom_ext rfl

/-- …and so is its inverse. -/
theorem homToFun_comp {P Q : Polygraph.{u, u, u}} (f : P ⟶ Q) (m : Hom Q (catPoly C)) :
    homToFun (f ≫ m) = f.functor ⋙ homToFun m :=
  ((catHomEquiv P C).symm_apply_eq.1
    (((homInvFun_comp f (homToFun m)).trans
      (congrArg (f ≫ ·) ((catHomEquiv Q C).symm_apply_apply m))))).symm

/-! ### The colimit of the slice diagram

The elements of `X` index the copies: `∫X ⟶ D` is a discrete fibration, so the slice of `(∫X)ᵒᵖ`
over an element is the slice of `D` over its base, and the copies glue along exactly the arrows of
`(∫X)ᵒᵖ`.  Everything below is the colimit's universal property and nothing else; in particular no
0-cell is ever examined. -/

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) (P : D ⥤ Polygraph.{u, u, u})

/-- The object of `D` an element lies over. -/
abbrev eltBase (c : (X.Elements)ᵒᵖ) : D := (CategoryOfElements.π X).leftOp.obj c

/-- **The slice diagram**: one copy of `P d` for each element over `d`. -/
def elementsPoly : (X.Elements)ᵒᵖ ⥤ Polygraph.{u, u, u} := (CategoryOfElements.π X).leftOp ⋙ P

/-- The colimit leg at an element, read on presented categories. -/
noncomputable def glueInclFun (c : (X.Elements)ᵒᵖ) :
    (P.obj (eltBase X c)).presented ⥤ (colimit (elementsPoly X P)).presented :=
  (colimit.ι (elementsPoly X P) c).functor

/-- **The copies are natural in the element** — a strict equality of functors. -/
theorem glueInclFun_naturality {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ glueInclFun X P c
      = glueInclFun X P c' :=
  (functor_comp _ _).symm.trans
    (congrArg Hom.functor (colimit.w (elementsPoly X P) u))

variable {X P}

/-- **A compatible family of functors out of the copies descends.** -/
noncomputable def glueLift (F : ∀ c : (X.Elements)ᵒᵖ, (P.obj (eltBase X c)).presented ⥤ C)
    (hF : ∀ {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c),
      (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ F c = F c') :
    (colimit (elementsPoly X P)).presented ⥤ C :=
  homToFun (colimit.desc (elementsPoly X P)
    { pt := catPoly C
      ι :=
        { app := fun c => homInvFun (F c)
          naturality := fun _ _ u => by
            refine Eq.trans ?_ (Category.comp_id _).symm
            exact (homInvFun_comp ((elementsPoly X P).map u) (F _)).symm.trans
              (congrArg homInvFun (hF u)) } })

/-- **…to the family it came from.** -/
theorem glueInclFun_lift (F : ∀ c : (X.Elements)ᵒᵖ, (P.obj (eltBase X c)).presented ⥤ C)
    (hF : ∀ {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c),
      (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ F c = F c')
    (c : (X.Elements)ᵒᵖ) :
    glueInclFun X P c ⋙ glueLift F hF = F c :=
  (homToFun_comp _ _).symm.trans
    ((congrArg homToFun (colimit.ι_desc _ c)).trans ((catHomEquiv _ C).right_inv (F c)))

/-- **A functor out of the glued polygraph is pinned by its copies.**  This is what replaces
induction over 0-cells: the comparison and the retraction are compared here and nowhere else. -/
theorem glue_functor_ext {F G : (colimit (elementsPoly X P)).presented ⥤ C}
    (h : ∀ c, glueInclFun X P c ⋙ F = glueInclFun X P c ⋙ G) : F = G :=
  ((catHomEquiv _ C).right_inv F).symm.trans
    ((congrArg homToFun (colimit.hom_ext fun c =>
      (homInvFun_comp (colimit.ι (elementsPoly X P) c) F).symm.trans
        ((congrArg homInvFun (h c)).trans
          (homInvFun_comp (colimit.ι (elementsPoly X P) c) G)))).trans
      ((catHomEquiv _ C).right_inv G))

end Colimit

/-! ### The comparison functor

Each copy carries its own slice presentation; pushing that along the cartesian lift gives a
compatible family, and `glueLift` descends it.  `hP` is the whole input. -/

section ColimCompare

open Limits

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
  (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))

/-- A copy, read in `(∫X)[W⁻¹]`: the slice presentation, pushed along the cartesian lift. -/
noncomputable def glueLeg (c : (X.Elements)ᵒᵖ) :
    (P.obj (eltBase X c)).presented ⥤
      (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (p (eltBase X c)).E ⋙ glueSliceEval X W (eltBase X c) c.unop.2

variable (hP : ∀ {d' d : D} (f : d' ⟶ d),
  (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f)

include hP in
/-- **The copies agree along an arrow of `∫X`** — `hP`, read through the cartesian lift. -/
theorem glueLeg_naturality {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ glueLeg X W p c
      = glueLeg X W p c' := by
  change (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ (p _).E ⋙ _
    = (p _).E ⋙ glueSliceEval X W _ c'.unop.2
  rw [← Functor.assoc, hP, Functor.assoc, overMapLoc_comp_glueSliceEval, elements_snd_map]
  rfl

include hP in
/-- **The comparison functor**: a word of the glued polygraph, read in `(∫X)[W⁻¹]`. -/
noncomputable def glueDesc :
    (colimit (elementsPoly X P)).presented ⥤
      (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  glueLift (glueLeg X W p) (glueLeg_naturality X W p hP)

include hP in
/-- **A copy, read by the comparison** — its own presentation, and nothing else. -/
theorem glueIncl_desc (c : (X.Elements)ᵒᵖ) :
    glueInclFun X P c ⋙ glueDesc X W p hP
      = (p (eltBase X c)).E ⋙ glueSliceEval X W (eltBase X c) c.unop.2 :=
  glueInclFun_lift (glueLeg X W p) (glueLeg_naturality X W p hP) c

/-! ### The retraction

Down to the base slice, the slice presentation inverted, and the copy at the element.  All three
steps are strictly natural in the element, so this is an honest cocone. -/

variable (hthin : ∀ d : D, Quiver.IsThin ((W.over (X := d)).Localization))
  (R : SliceSkeleton W p)

include hthin in
/-- The retraction, before localizing. -/
noncomputable def glueRetractPre (c : (X.Elements)ᵒᵖ) :
    Over c ⥤ (colimit (elementsPoly X P)).presented :=
  Over.post (CategoryOfElements.π X).leftOp ⋙
    (W.over (X := eltBase X c)).Q ⋙
    slInv W p hthin R (eltBase X c) ⋙
    glueInclFun X P c

include hP hthin in
/-- The comparison on the base slice: `slInv_square` followed by the copies' naturality. -/
theorem glueStep {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        slInv W p hthin R (eltBase X c) ⋙ glueInclFun X P c
      = slInv W p hthin R (eltBase X c') ⋙ glueInclFun X P c' := by
  rw [← Functor.assoc, slInv_square W p hP hthin R, Functor.assoc, glueInclFun_naturality]

include hP hthin in
/-- …and it is natural in the element on the nose. -/
theorem glueRetractPre_map {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Over.map u ⋙ glueRetractPre X W p hthin R c
      = glueRetractPre X W p hthin R c' := by
  unfold glueRetractPre
  rw [← Functor.assoc, elementsPost_map, Functor.assoc, ← Functor.assoc (Over.map _),
    ← overMapLocFac, Functor.assoc, glueStep X W p hP hthin R u]

include hthin in
theorem glueRetractPre_inverts (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).IsInvertedBy
      (glueRetractPre X W p hthin R c) := by
  intro Y Z φ hφ
  haveI : IsIso ((W.over (X := eltBase X c)).Q.map
      ((Over.post (CategoryOfElements.π X).leftOp).map φ)) :=
    Localization.inverts _ (W.over (X := eltBase X c)) _ hφ
  exact inferInstanceAs (IsIso
    ((slInv W p hthin R (eltBase X c) ⋙ glueInclFun X P c).map
      ((W.over (X := eltBase X c)).Q.map
        ((Over.post (CategoryOfElements.π X).leftOp).map φ))))

include hP hthin in
/-- The retraction, as a **strict** cocone on the slices. -/
noncomputable def glueRetractCocone :
    OverCocone ((X.Elements)ᵒᵖ) ((colimit (elementsPoly X P)).presented) where
  obj c := glueRetractPre X W p hthin R c
  w u := glueRetractPre_map X W p hP hthin R u

include hP hthin in
theorem glueRetractCocone_inverts :
    (W.inverseImage (CategoryOfElements.π X).leftOp).IsInvertedBy
      (glueRetractCocone X W p hP hthin R).desc := by
  rw [isInvertedBy_iff_over, OverCocone.ofFunctor_desc]
  exact glueRetractPre_inverts X W p hthin R

include hP hthin in
/-- **The retraction** `Ψ : (∫X)[W⁻¹] ⥤ colim`, descended from the slices. -/
noncomputable def glueRetract :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization ⥤
      (colimit (elementsPoly X P)).presented :=
  Localization.Construction.lift _ (glueRetractCocone_inverts X W p hP hthin R)

include hP hthin in
theorem glueRetract_fac :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙ glueRetract X W p hP hthin R
      = (glueRetractCocone X W p hP hthin R).desc :=
  Localization.Construction.fac _ _

include hP hthin in
theorem glueRetract_forget (c : (X.Elements)ᵒᵖ) :
    Over.forget c ⋙ (glueRetractCocone X W p hP hthin R).desc
      = glueRetractPre X W p hthin R c :=
  congrArg (fun G => OverCocone.obj G c) (OverCocone.ofFunctor_desc _)

include hP hthin in
/-- **A slice, read through the retraction, is the copy at that element** — the mirror of
`glueIncl_desc`. -/
theorem glueSliceEval_retract (c : (X.Elements)ᵒᵖ) :
    glueSliceEval X W (eltBase X c) c.unop.2 ⋙ glueRetract X W p hP hthin R
      = slInv W p hthin R (eltBase X c) ⋙ glueInclFun X P c := by
  refine Localization.Construction.uniq _ _ ?_
  rw [← Functor.assoc, glueSliceEval_fac, Functor.assoc, glueRetract_fac,
    ← elementsLiftOver_forget X c, Functor.assoc, glueRetract_forget]
  unfold glueRetractPre
  simp only [← Functor.assoc]
  rw [elementsLiftOver_post, Functor.id_comp]

include hP hthin in
/-- **The unit**: the comparison, read through the retraction, is the identity.  Checked one copy
at a time, which is all the colimit ever asks — `slInv` cancels `(p d).E` there. -/
theorem glueUnit :
    glueDesc X W p hP ⋙ glueRetract X W p hP hthin R = 𝟭 _ :=
  glue_functor_ext fun c => by
    rw [← Functor.assoc, glueIncl_desc, Functor.assoc, glueSliceEval_retract,
      ← Functor.assoc, comp_slInv, Functor.id_comp, Functor.comp_id]

/-! ### Fullness and essential surjectivity

`glueVtx c` is the 0-cell of the copy at `c` entering `c` itself, and it meets every isomorphism
class, so the comparison is essentially surjective; the unit makes it faithful.  Fullness is an
induction over the words of `(∫X)[W⁻¹]`, each generator landing inside a single copy, where
`(p d).E` is already full.  The one thing to check is that two copies read a shared 0-cell the
same way, and that is a `Subsingleton.elim` in the localized slice, which is a poset. -/

include hthin R in
/-- **The comparison is faithful** — the unit, and nothing else. -/
theorem glueDesc_faithful : (glueDesc X W p hP).Faithful :=
  Functor.Faithful.of_comp_eq (glueUnit X W p hP hthin R)

/-- The 0-cell of the copy at `c` that enters the slice object `Y`. -/
noncomputable def glueOb (c : (X.Elements)ᵒᵖ) (Y : Over (eltBase X c)) :
    (colimit (elementsPoly X P)).presented :=
  (glueInclFun X P c).obj ⟨⟨R.ret Y⟩⟩

/-- …read by the comparison: the copy's own presentation, then the cartesian lift. -/
noncomputable def glueObIso (c : (X.Elements)ᵒᵖ) (Y : Over (eltBase X c)) :
    (glueDesc X W p hP).obj (glueOb X W p R c Y)
      ≅ (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
          ((elementsLift X (eltBase X c) c.unop.2).obj Y) :=
  eqToIso (Functor.congr_obj (glueIncl_desc X W p hP c) _) ≪≫
    (glueSliceEval X W (eltBase X c) c.unop.2).mapIso (R.iso Y) ≪≫
    eqToIso (Functor.congr_obj (glueSliceEval_fac X W (eltBase X c) c.unop.2) Y)

/-- An isomorphism of one copy's slice, read at the elements the cartesian lift names. -/
noncomputable def glueSliceIso (c : (X.Elements)ᵒᵖ) {Y Y' : Over (eltBase X c)}
    (e : (W.over (X := eltBase X c)).Q.obj Y ≅ (W.over (X := eltBase X c)).Q.obj Y') :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        ((elementsLift X (eltBase X c) c.unop.2).obj Y) ≅
      (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        ((elementsLift X (eltBase X c) c.unop.2).obj Y') :=
  eqToIso (Functor.congr_obj (glueSliceEval_fac X W (eltBase X c) c.unop.2) Y).symm ≪≫
    (glueSliceEval X W (eltBase X c) c.unop.2).mapIso e ≪≫
    eqToIso (Functor.congr_obj (glueSliceEval_fac X W (eltBase X c) c.unop.2) Y')

/-- …and a bare morphism, likewise. -/
noncomputable def glueSliceHom (c : (X.Elements)ᵒᵖ) {Y Y' : Over (eltBase X c)}
    (h : (W.over (X := eltBase X c)).Q.obj Y ⟶ (W.over (X := eltBase X c)).Q.obj Y') :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        ((elementsLift X (eltBase X c) c.unop.2).obj Y) ⟶
      (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        ((elementsLift X (eltBase X c) c.unop.2).obj Y') :=
  eqToHom (Functor.congr_obj (glueSliceEval_fac X W (eltBase X c) c.unop.2) Y).symm ≫
    (glueSliceEval X W (eltBase X c) c.unop.2).map h ≫
    eqToHom (Functor.congr_obj (glueSliceEval_fac X W (eltBase X c) c.unop.2) Y')

theorem glueSliceIso_hom (c : (X.Elements)ᵒᵖ) {Y Y' : Over (eltBase X c)}
    (e : (W.over (X := eltBase X c)).Q.obj Y ≅ (W.over (X := eltBase X c)).Q.obj Y') :
    (glueSliceIso X W c e).hom = glueSliceHom X W c e.hom := rfl

theorem glueSliceIso_inv (c : (X.Elements)ᵒᵖ) {Y Y' : Over (eltBase X c)}
    (e : (W.over (X := eltBase X c)).Q.obj Y ≅ (W.over (X := eltBase X c)).Q.obj Y') :
    (glueSliceIso X W c e).inv = glueSliceHom X W c e.inv := by
  simp [glueSliceIso, glueSliceHom]

/-- **A morphism of one copy's slice is hit** — `(p d).E` is full, free from `Presents`. -/
theorem exists_glueObHom (c : (X.Elements)ᵒᵖ) {Y Y' : Over (eltBase X c)}
    (h : (W.over (X := eltBase X c)).Q.obj Y ⟶ (W.over (X := eltBase X c)).Q.obj Y') :
    ∃ g : glueOb X W p R c Y ⟶ glueOb X W p R c Y',
      (glueDesc X W p hP).map g
        = (glueObIso X W p hP R c Y).hom ≫ glueSliceHom X W c h ≫
          (glueObIso X W p hP R c Y').inv := by
  refine ⟨(glueInclFun X P c).map
    ((p (eltBase X c)).E.preimage ((R.iso Y).hom ≫ h ≫ (R.iso Y').inv)), ?_⟩
  have hc := Functor.congr_hom (glueIncl_desc X W p hP c)
    ((p (eltBase X c)).E.preimage ((R.iso Y).hom ≫ h ≫ (R.iso Y').inv))
  simp only [Functor.comp_map] at hc
  refine hc.trans ?_
  rw [Functor.map_preimage]
  simp [glueObIso, glueSliceHom]
  rfl

/-- The copy at `c` reads its own top object as `c`. -/
theorem elementsLift_top (c : (X.Elements)ᵒᵖ) :
    (elementsLift X (eltBase X c) c.unop.2).obj (Over.mk (𝟙 (eltBase X c))) = c :=
  Functor.congr_obj (elementsLift_post X c) (Over.mk (𝟙 c))

/-- The 0-cell of the copy at `c` that enters `c` itself. -/
noncomputable def glueVtx (c : (X.Elements)ᵒᵖ) : (colimit (elementsPoly X P)).presented :=
  glueOb X W p R c (Over.mk (𝟙 (eltBase X c)))

/-- **…and the comparison sends it to `c`.** -/
noncomputable def glueVtxIso (c : (X.Elements)ᵒᵖ) :
    (glueDesc X W p hP).obj (glueVtx X W p R c)
      ≅ (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj c :=
  glueObIso X W p hP R c (Over.mk (𝟙 (eltBase X c))) ≪≫
    eqToIso (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
      (elementsLift_top X c))

include hP R in
/-- **The comparison is essentially surjective** — every object of `(∫X)[W⁻¹]` is an object of
`∫X`, and `glueVtx` names a 0-cell entering it. -/
theorem glueDesc_essSurj : (glueDesc X W p hP).EssSurj where
  mem_essImage Z :=
    ⟨glueVtx X W p R ((Localization.Construction.objEquiv _).symm Z),
      ⟨glueVtxIso X W p hP R _⟩⟩

/-! #### One copy, read in another

An arrow `u : c' ⟶ c` of `∫X` puts the copy at `c'` inside the copy at `c`, at the slice object `u`
itself.  Both copies then read the shared 0-cell, and they agree — in the localized slice, which is
a poset, there is nothing for them to disagree about. -/

variable {c' c : (X.Elements)ᵒᵖ}

include hP in
/-- **The 0-cell entering an arrow of `∫X` is the source copy's own.** -/
theorem ret_arrow (u : c' ⟶ c) :
    (⟨⟨R.ret (Over.mk ((CategoryOfElements.π X).leftOp.map u))⟩⟩ :
        (P.obj (eltBase X c)).presented)
      = (P.map ((CategoryOfElements.π X).leftOp.map u)).functor.obj
          ⟨⟨R.ret (Over.mk (𝟙 (eltBase X c')))⟩⟩ := by
  have h := ret_push W p hP R ((CategoryOfElements.π X).leftOp.map u)
    (Over.mk (𝟙 (eltBase X c')))
  rw [OverCocone.map_obj_top] at h
  exact congrArg (fun a => (⟨⟨a⟩⟩ : (P.obj (eltBase X c)).presented)) h

include hP in
/-- …so the two copies name the same 0-cell of the colimit. -/
theorem glueOb_arrow (u : c' ⟶ c) :
    glueOb X W p R c (Over.mk ((CategoryOfElements.π X).leftOp.map u))
      = glueVtx X W p R c' := by
  rw [glueOb, ret_arrow X W p hP R u, ← Functor.comp_obj, glueInclFun_naturality]
  rfl

/-- The cartesian lift reads an arrow of `∫X` as its source. -/
theorem elementsLift_arrow (u : c' ⟶ c) :
    (elementsLift X (eltBase X c) c.unop.2).obj
        (Over.mk ((CategoryOfElements.π X).leftOp.map u)) = c' :=
  congrArg (fun z => op (⟨c'.unop.1, z⟩ : X.Elements)) (elements_snd_map X u)

/-- The cartesian lift at `c`, restricted along an arrow into `c`, is the one at its source. -/
theorem overMapLoc_comp_sliceEval (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        glueSliceEval X W (eltBase X c) c.unop.2
      = glueSliceEval X W (eltBase X c') c'.unop.2 := by
  rw [overMapLoc_comp_glueSliceEval, elements_snd_map]

include hP hthin in
/-- **Both copies read the shared 0-cell the same way** — the entries agree in the localized
slice, which is a poset, and the cartesian lifts agree along the arrow. -/
theorem sliceEval_iso_heq (u : c' ⟶ c) :
    (glueSliceEval X W (eltBase X c) c.unop.2).map
        (R.iso (Over.mk ((CategoryOfElements.π X).leftOp.map u))).hom
      ≍ (glueSliceEval X W (eltBase X c') c'.unop.2).map
        (R.iso (Over.mk (𝟙 (eltBase X c')))).hom := by
  have hsrc : (p (eltBase X c)).at' ⟨R.ret (Over.mk ((CategoryOfElements.π X).leftOp.map u))⟩
      = (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)).obj
        ((p (eltBase X c')).at' ⟨R.ret (Over.mk (𝟙 (eltBase X c')))⟩) := by
    rw [show (p (eltBase X c)).at'
        ⟨R.ret (Over.mk ((CategoryOfElements.π X).leftOp.map u))⟩
      = (p (eltBase X c)).E.obj
        ⟨⟨R.ret (Over.mk ((CategoryOfElements.π X).leftOp.map u))⟩⟩ from rfl,
      ret_arrow X W p hP R u]
    exact Functor.congr_obj (hP ((CategoryOfElements.π X).leftOp.map u))
      ⟨⟨R.ret (Over.mk (𝟙 (eltBase X c')))⟩⟩
  have htgt : (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)).obj
        ((W.over (X := eltBase X c')).Q.obj (Over.mk (𝟙 (eltBase X c'))))
      = (W.over (X := eltBase X c)).Q.obj
        (Over.mk ((CategoryOfElements.π X).leftOp.map u)) :=
    (overMapLoc_obj W ((CategoryOfElements.π X).leftOp.map u) (Over.mk (𝟙 (eltBase X c')))).trans
      (congrArg (Localization.Construction.objEquiv (W.over (X := eltBase X c)))
        (OverCocone.map_obj_top ((CategoryOfElements.π X).leftOp.map u)))
  have key : (R.iso (Over.mk ((CategoryOfElements.π X).leftOp.map u))).hom
      = eqToHom hsrc ≫ (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)).map
        (R.iso (Over.mk (𝟙 (eltBase X c')))).hom ≫ eqToHom htgt := by
    haveI := hthin (eltBase X c)
    exact Subsingleton.elim _ _
  refine HEq.trans (Prefunctor.map_heq_congr
    (glueSliceEval X W (eltBase X c) c.unop.2).toPrefunctor hsrc htgt.symm
    ((conj_eqToHom_iff_heq' _ _ hsrc htgt).1 key)) ?_
  exact Prefunctor.map_heq_of_eq
    (congrArg Functor.toPrefunctor (overMapLoc_comp_sliceEval X W u)) _

include hP hthin in
/-- **…so the two comparisons agree.** -/
theorem glueObIso_arrow (u : c' ⟶ c) :
    (glueObIso X W p hP R c (Over.mk ((CategoryOfElements.π X).leftOp.map u))).hom ≫
        eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
          (elementsLift_arrow X u))
      = eqToHom (congrArg (glueDesc X W p hP).obj (glueOb_arrow X W p hP R u)) ≫
        (glueVtxIso X W p hP R c').hom := by
  simp only [glueObIso, glueVtxIso, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
    Category.assoc, eqToHom_trans]
  refine eqToHom_conj_eq_of_heq _ _ _ _
    ((sliceEval_iso_heq X W p hP hthin R u).trans ((conj_eqToHom_iff_heq' _ _ _ _).1 rfl).symm)

include hP hthin in
/-- **A slice arrow from an arrow of `∫X` up to the copy's top object is hit.** -/
theorem exists_glueVtxHom_fwd (u : c' ⟶ c)
    (h : (W.over (X := eltBase X c)).Q.obj (Over.mk ((CategoryOfElements.π X).leftOp.map u)) ⟶
      (W.over (X := eltBase X c)).Q.obj (Over.mk (𝟙 (eltBase X c)))) :
    ∃ g : glueVtx X W p R c' ⟶ glueVtx X W p R c,
      (glueDesc X W p hP).map g
        = (glueVtxIso X W p hP R c').hom ≫
          (eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
            (elementsLift_arrow X u)).symm ≫ glueSliceHom X W c h ≫
            eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
              (elementsLift_top X c))) ≫ (glueVtxIso X W p hP R c).inv := by
  obtain ⟨g₀, hg₀⟩ := exists_glueObHom X W p hP R c h
  refine ⟨eqToHom (glueOb_arrow X W p hP R u).symm ≫ g₀, ?_⟩
  have h1 : eqToHom (congrArg (glueDesc X W p hP).obj (glueOb_arrow X W p hP R u).symm) ≫
      (glueObIso X W p hP R c (Over.mk ((CategoryOfElements.π X).leftOp.map u))).hom
      = (glueVtxIso X W p hP R c').hom ≫
        eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
          (elementsLift_arrow X u)).symm := by
    rw [eqToHom_comp_iff, ← Category.assoc, ← comp_eqToHom_iff]
    exact glueObIso_arrow X W p hP hthin R u
  have h2 : (glueObIso X W p hP R c (Over.mk (𝟙 (eltBase X c)))).inv
      = eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        (elementsLift_top X c)) ≫ (glueVtxIso X W p hP R c).inv := by
    simp [glueVtxIso]
  refine ((glueDesc X W p hP).map_comp _ _).trans ?_
  refine (congrArg (· ≫ (glueDesc X W p hP).map g₀)
    (eqToHom_map (glueDesc X W p hP) (glueOb_arrow X W p hP R u).symm)).trans ?_
  refine (congrArg (eqToHom (congrArg (glueDesc X W p hP).obj
    (glueOb_arrow X W p hP R u).symm) ≫ ·) hg₀).trans ?_
  rw [h2, ← Category.assoc, h1, Category.assoc, Category.assoc, Category.assoc]
  rfl

include hP hthin in
/-- **…and back down.** -/
theorem exists_glueVtxHom_bwd (u : c' ⟶ c)
    (h : (W.over (X := eltBase X c)).Q.obj (Over.mk (𝟙 (eltBase X c))) ⟶
      (W.over (X := eltBase X c)).Q.obj (Over.mk ((CategoryOfElements.π X).leftOp.map u))) :
    ∃ g : glueVtx X W p R c ⟶ glueVtx X W p R c',
      (glueDesc X W p hP).map g
        = (glueVtxIso X W p hP R c).hom ≫
          (eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
            (elementsLift_top X c)).symm ≫ glueSliceHom X W c h ≫
            eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
              (elementsLift_arrow X u))) ≫ (glueVtxIso X W p hP R c').inv := by
  obtain ⟨g₀, hg₀⟩ := exists_glueObHom X W p hP R c h
  refine ⟨g₀ ≫ eqToHom (glueOb_arrow X W p hP R u), ?_⟩
  have hiso : (eqToIso (congrArg (glueDesc X W p hP).obj
        (glueOb_arrow X W p hP R u).symm) ≪≫
      glueObIso X W p hP R c (Over.mk ((CategoryOfElements.π X).leftOp.map u)))
      = glueVtxIso X W p hP R c' ≪≫
        eqToIso (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
          (elementsLift_arrow X u)).symm := by
    refine Iso.ext ?_
    simp only [Iso.trans_hom, eqToIso.hom]
    rw [eqToHom_comp_iff, ← Category.assoc, ← comp_eqToHom_iff]
    exact glueObIso_arrow X W p hP hthin R u
  have h1 := congrArg Iso.inv hiso
  simp only [Iso.trans_inv, eqToIso.inv] at h1
  have h2 : (glueObIso X W p hP R c (Over.mk (𝟙 (eltBase X c)))).hom
      = (glueVtxIso X W p hP R c).hom ≫
        eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
          (elementsLift_top X c)).symm := by
    simp [glueVtxIso]
  refine ((glueDesc X W p hP).map_comp _ _).trans ?_
  refine (congrArg ((glueDesc X W p hP).map g₀ ≫ ·)
    (eqToHom_map (glueDesc X W p hP) (glueOb_arrow X W p hP R u))).trans ?_
  refine (congrArg (· ≫ eqToHom (congrArg (glueDesc X W p hP).obj
    (glueOb_arrow X W p hP R u))) hg₀).trans ?_
  rw [h2, Category.assoc, Category.assoc, Category.assoc, h1, Category.assoc]
  exact Category.assoc _ _ _

/-! #### The generators -/

/-- The arrow of the slice over `c` from an arrow of `∫X` up to the top object. -/
def glueToTop (u : c' ⟶ c) :
    (Over.mk ((CategoryOfElements.π X).leftOp.map u) : Over (eltBase X c))
      ⟶ Over.mk (𝟙 (eltBase X c)) :=
  Over.homMk ((CategoryOfElements.π X).leftOp.map u) (by simp)

theorem elementsLift_glueToTop (u : c' ⟶ c) :
    (elementsLift X (eltBase X c) c.unop.2).map (glueToTop X u)
      = eqToHom (elementsLift_arrow X u) ≫ u ≫ eqToHom (elementsLift_top X c).symm := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  simp [glueToTop]

/-- A morphism of one copy's slice, read between the elements the cartesian lift names. -/
theorem glueSliceHom_Q (c : (X.Elements)ᵒᵖ) {Y Y' : Over (eltBase X c)} (ψ : Y ⟶ Y') :
    glueSliceHom X W c ((W.over (X := eltBase X c)).Q.map ψ)
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map
        ((elementsLift X (eltBase X c) c.unop.2).map ψ) := by
  have h := Functor.congr_hom (glueSliceEval_fac X W (eltBase X c) c.unop.2) ψ
  simp only [Functor.comp_map] at h
  rw [glueSliceHom, h]
  simp

include hP hthin in
/-- **An arrow of `∫X` is hit.** -/
theorem exists_glueVtxHom_Q (u : c' ⟶ c) :
    ∃ g : glueVtx X W p R c' ⟶ glueVtx X W p R c,
      (glueDesc X W p hP).map g = (glueVtxIso X W p hP R c').hom ≫
        (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map u ≫
        (glueVtxIso X W p hP R c).inv := by
  obtain ⟨g, hg⟩ := exists_glueVtxHom_fwd X W p hP hthin R u
    ((W.over (X := eltBase X c)).Q.map (glueToTop X u))
  refine ⟨g, hg.trans ?_⟩
  have hm : eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        (elementsLift_arrow X u)).symm ≫
      glueSliceHom X W c ((W.over (X := eltBase X c)).Q.map (glueToTop X u)) ≫
      eqToHom (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
        (elementsLift_top X c))
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q.map u := by
    rw [glueSliceHom_Q, elementsLift_glueToTop, Functor.map_comp, Functor.map_comp,
      eqToHom_map, eqToHom_map]
    simp
  rw [hm]

include hP hthin in
/-- **…and so is its formal inverse**, the arrow being invertible in the copy's own slice. -/
theorem exists_glueVtxHom_wInv (u : c' ⟶ c)
    (hu : (W.inverseImage (CategoryOfElements.π X).leftOp) u) :
    ∃ g : glueVtx X W p R c ⟶ glueVtx X W p R c',
      (glueDesc X W p hP).map g = (glueVtxIso X W p hP R c).hom ≫
        Localization.Construction.wInv u hu ≫ (glueVtxIso X W p hP R c').inv := by
  have hw : (W.over (X := eltBase X c)) (glueToTop X u) := hu
  obtain ⟨g, hg⟩ := exists_glueVtxHom_bwd X W p hP hthin R u
    (Localization.Construction.wInv (glueToTop X u) hw)
  refine ⟨g, hg.trans ?_⟩
  have hiso : glueSliceIso X W c (Localization.Construction.wIso (glueToTop X u) hw)
      = eqToIso (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
          (elementsLift_arrow X u)) ≪≫ Localization.Construction.wIso u hu ≪≫
        eqToIso (congrArg (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj
          (elementsLift_top X c)).symm := by
    refine Iso.ext ?_
    rw [glueSliceIso_hom]
    change glueSliceHom X W c ((W.over (X := eltBase X c)).Q.map (glueToTop X u)) = _
    rw [glueSliceHom_Q, elementsLift_glueToTop, Functor.map_comp, Functor.map_comp,
      eqToHom_map, eqToHom_map]
    simp
    rfl
  have hinv := congrArg Iso.inv hiso
  rw [glueSliceIso_inv] at hinv
  simp only [Iso.trans_inv, eqToIso.inv, Category.assoc] at hinv
  change _ = (glueVtxIso X W p hP R c).hom ≫
    Localization.Construction.wInv u hu ≫ (glueVtxIso X W p hP R c').inv
  rw [hinv]
  simp

/-! #### Fullness -/

include hP hthin in
/-- **Every arrow between chosen 0-cells is hit** — an induction over the words of `(∫X)[W⁻¹]`. -/
theorem exists_glueVtxHom (a b : (X.Elements)ᵒᵖ)
    (f : (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj a ⟶
      (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj b) :
    ∃ g : glueVtx X W p R a ⟶ glueVtx X W p R b,
      (glueDesc X W p hP).map g
        = (glueVtxIso X W p hP R a).hom ≫ f ≫ (glueVtxIso X W p hP R b).inv := by
  refine Localization.Construction.hom_induction
    (W.inverseImage (CategoryOfElements.π X).leftOp)
    (fun x y v => ∃ g : glueVtx X W p R x ⟶ glueVtx X W p R y,
      (glueDesc X W p hP).map g
        = (glueVtxIso X W p hP R x).hom ≫ v ≫ (glueVtxIso X W p hP R y).inv)
    (fun _ _ _ _ _ hg hg' => ?_)
    (fun {_ _} v => exists_glueVtxHom_Q X W p hP hthin R v)
    (fun {_ _} v hv => exists_glueVtxHom_wInv X W p hP hthin R v hv) f
  obtain ⟨k, hk⟩ := hg
  obtain ⟨k', hk'⟩ := hg'
  exact ⟨k ≫ k', by rw [Functor.map_comp, hk, hk']; simp⟩

include hP hthin in
/-- **The comparison reflects isomorphy of 0-cells** — the retraction carries it back. -/
noncomputable def glueIsoOfImage {A B : (colimit (elementsPoly X P)).presented}
    (e : (glueDesc X W p hP).obj A ≅ (glueDesc X W p hP).obj B) : A ≅ B :=
  eqToIso (Functor.congr_obj (glueUnit X W p hP hthin R) A).symm ≪≫
    (glueRetract X W p hP hthin R).mapIso e ≪≫
    eqToIso (Functor.congr_obj (glueUnit X W p hP hthin R) B)

/-- The element a 0-cell's image names. -/
noncomputable def objRepr (A : (colimit (elementsPoly X P)).presented) : (X.Elements)ᵒᵖ :=
  (Localization.Construction.objEquiv
    (W.inverseImage (CategoryOfElements.π X).leftOp)).symm ((glueDesc X W p hP).obj A)

include hP hthin R in
/-- **The comparison is full** — every 0-cell is isomorphic to a chosen one. -/
theorem glueDesc_full : (glueDesc X W p hP).Full where
  map_surjective {A B} f := by
    have eA : (glueDesc X W p hP).obj (glueVtx X W p R (objRepr X W p hP A))
        ≅ (glueDesc X W p hP).obj A :=
      glueVtxIso X W p hP R _ ≪≫ eqToIso ((Localization.Construction.objEquiv
        (W.inverseImage (CategoryOfElements.π X).leftOp)).apply_symm_apply _)
    have eB : (glueDesc X W p hP).obj (glueVtx X W p R (objRepr X W p hP B))
        ≅ (glueDesc X W p hP).obj B :=
      glueVtxIso X W p hP R _ ≪≫ eqToIso ((Localization.Construction.objEquiv
        (W.inverseImage (CategoryOfElements.π X).leftOp)).apply_symm_apply _)
    have e := glueIsoOfImage X W p hP hthin R eA
    have e' := glueIsoOfImage X W p hP hthin R eB
    obtain ⟨g₀, hg₀⟩ := exists_glueVtxHom X W p hP hthin R _ _
      ((glueVtxIso X W p hP R (objRepr X W p hP A)).inv ≫
        ((glueDesc X W p hP).mapIso e).hom ≫ f ≫ ((glueDesc X W p hP).mapIso e').inv ≫
        (glueVtxIso X W p hP R (objRepr X W p hP B)).hom)
    refine ⟨e.inv ≫ g₀ ≫ e'.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, hg₀]
    simp

include hP hthin R in
/-- **The colimit of the slice presentations presents `(∫X)[W⁻¹]`.**  Faithful from the unit, full
from the induction, essentially surjective from the skeleton — every obligation a `Prop`. -/
noncomputable def presentsSliceColimit :
    Presents (colimit (elementsPoly X P))
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  haveI := glueDesc_faithful X W p hP hthin R
  haveI := glueDesc_full X W p hP hthin R
  haveI := glueDesc_essSurj X W p hP R
  ⟨glueDesc X W p hP, {}⟩
end ColimCompare

end Polygraph

end CategoryTheory
