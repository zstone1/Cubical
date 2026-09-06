import CubeChains.Machinery.Presentation.Basic
import CubeChains.Machinery.Presentation.Adjunction
import CubeChains.Machinery.Presentation.Coequalizer
import CubeChains.Machinery.Localization.SliceFamily
import Mathlib.CategoryTheory.Elements

/-!
# Machinery/Presentation/Glue — one copy of `P d` for each element over `d`

`elementsPoly X P` is the **slice diagram**: `∫X ⟶ D` is a discrete fibration, so the copies of
`P d` are indexed by the elements over `d` and glue along the arrows of `(∫X)ᵒᵖ`.  Nothing but the
colimit's universal property is ever used — the comparison `Φ` is `colimit.desc`, the unit is
`colimit.hom_ext`, and no 0-cell is examined anywhere.

`presentsSliceColimit` says `colimit (elementsPoly X P)` presents `(∫X)[W⁻¹]`, given a family of
slice presentations (`p`, `hP`), thin localized slices (`hthin`), and one condition on the 0-cells:
they are a **skeleton** of each localized slice (`R : SliceSkeleton`).  The unit is strict; the
counit is only an isomorphism, a skeleton meeting each isomorphism class without exhausting the
objects — and that isomorphism travels as a cocone valued in `Arrow`, so it descends by
`OverCocone.desc` like any 1-cell and no comparison is ever transported.
-/

universe w w' v₁ u₁ u' w₂ u

namespace CategoryTheory

open Opposite

namespace Polygraph

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

/-- **The objects of `∫X` a copy names.**  The 0-cells of the glued polygraph are the copies'
0-cells, so this is the image of the glued polygraph in `∫X`: an object is covered exactly when
some copy has a 0-cell labelled by an arrow into it. -/
def Covered : GlueV X → Prop :=
  fun v => ∃ (s : GlueV X) (a : (P.obj s.1).V), gluePt X L s.1 s.2 a = v

/-- …as a type. -/
abbrev CoveredV : Type (max u₁ w) := {v : GlueV X // Covered X L v}

/-- `overMapLoc` on objects is `Over.map`. -/
theorem overMapLoc_obj (W : MorphismProperty D) {d' d : D} (f : d' ⟶ d) (Y : Over d') :
    (overMapLoc W f).obj (Localization.Construction.objEquiv (W.over (X := d')) Y) =
      Localization.Construction.objEquiv (W.over (X := d)) ((Over.map f).obj Y) :=
  Functor.congr_obj (overMapLocFac W f) Y

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

include hthin in
/-- **…and the retraction is a section up to isomorphism.**  The other composite is only an iso —
the 0-cells name a skeleton, not every slice object — and the slice being a poset makes it natural
for free. -/
noncomputable def slInvIso (d : D) : slInv W p hthin R d ⋙ (p d).E ≅ 𝟭 _ :=
  haveI := hthin d
  NatIso.ofComponents
    (fun Y => R.iso ((Localization.Construction.objEquiv (W.over (X := d))).symm Y)
      ≪≫ eqToIso ((Localization.Construction.objEquiv (W.over (X := d))).apply_symm_apply Y))
    fun _ => Subsingleton.elim _ _

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

section Legs

variable {E : Type*} [Category E]
  (S : ∀ c : (X.Elements)ᵒᵖ, (W.over (X := eltBase X c)).Localization ⥤ E)

/-- A functor on the localized base slice, read on the slice of `∫X` above it. -/
noncomputable def sliceLeg (c : (X.Elements)ᵒᵖ) : Over c ⥤ E :=
  Over.post (CategoryOfElements.π X).leftOp ⋙ (W.over (X := eltBase X c)).Q ⋙ S c

/-- **A family on the localized base slices, compatible along `∫X`, is a cocone on the slices of
`∫X`** — the discrete fibration, read on slices.  The retraction and the counit are both this, at
different targets. -/
noncomputable def sliceCocone
    (hS : ∀ {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c),
      overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙ S c = S c') :
    OverCocone ((X.Elements)ᵒᵖ) E where
  obj := sliceLeg X W S
  w u := by
    unfold sliceLeg
    rw [← Functor.assoc, elementsPost_map, Functor.assoc, ← Functor.assoc (Over.map _),
      ← overMapLocFac, Functor.assoc, hS u]

end Legs

include hthin in
/-- The retraction, before localizing. -/
noncomputable def glueRetractPre (c : (X.Elements)ᵒᵖ) :
    Over c ⥤ (colimit (elementsPoly X P)).presented :=
  sliceLeg X W (fun c => slInv W p hthin R (eltBase X c) ⋙ glueInclFun X P c) c

include hP hthin in
/-- The comparison on the base slice: `slInv_square` followed by the copies' naturality. -/
theorem glueStep {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        slInv W p hthin R (eltBase X c) ⋙ glueInclFun X P c
      = slInv W p hthin R (eltBase X c') ⋙ glueInclFun X P c' := by
  rw [← Functor.assoc, slInv_square W p hP hthin R, Functor.assoc, glueInclFun_naturality]

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
    OverCocone ((X.Elements)ᵒᵖ) ((colimit (elementsPoly X P)).presented) :=
  sliceCocone X W _ (fun {_ _} u => glueStep X W p hP hthin R u)

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
  unfold glueRetractPre sliceLeg
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

include hthin R in
/-- **The comparison is faithful on the unit alone** — no counit, and so no skeleton hypothesis
beyond the one the retraction already used. -/
theorem glueDesc_faithful : (glueDesc X W p hP).Faithful :=
  Functor.Faithful.of_comp_eq (glueUnit X W p hP hthin R)

/-! ### The counit

The other composite is only an isomorphism: `slInv` sends a slice object to the 0-cell it is
isomorphic to, not to itself.  `NatTrans.toArrow` carries that isomorphism as a **1-cell** — a
cocone valued in `Arrow`, whose two projections are the composite and the identity — so the slices
are assembled by `OverCocone.desc` like any other cocone, and every compatibility stays an equality
of functors. -/

include hP hthin in
/-- **The retraction, followed by the presentation, is postcomposition** — `slInv_square` and `hP`
run together. -/
theorem slInvComp_square {d' d : D} (f : d' ⟶ d) :
    overMapLoc W f ⋙ slInv W p hthin R d ⋙ (p d).E
      = (slInv W p hthin R d' ⋙ (p d').E) ⋙ overMapLoc W f := by
  rw [← Functor.assoc, slInv_square W p hP hthin R, Functor.assoc, hP]
  rfl

include hthin in
/-- **The comparison isomorphism, as a 1-cell.** -/
noncomputable def slInvArrow (d : D) :
    (W.over (X := d)).Localization ⥤ Arrow ((W.over (X := d)).Localization) :=
  (slInvIso W p hthin R d).hom.toArrow

include hP hthin in
/-- **Neighbouring slices compare the same way** — an *equality* of functors, because an arrow of a
poset is pinned by its endpoints and `slInvComp_square` supplies those. -/
theorem slInvArrow_square {d' d : D} (f : d' ⟶ d) :
    overMapLoc W f ⋙ slInvArrow W p hthin R d
      = slInvArrow W p hthin R d' ⋙ (overMapLoc W f).mapArrow := by
  haveI := hthin d
  refine CategoryTheory.Functor.ext (fun Y => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  exact Arrow.mk_eq_mk_of_thin _ _
    (Functor.congr_obj (slInvComp_square W p hP hthin R f) Y) rfl

include hP hthin in
/-- The comparison on the base slice: `slInvArrow_square`, then the cartesian lift at `c`
restricted along `u`, which is the lift at `c'`. -/
theorem glueCounitStep {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        slInvArrow W p hthin R (eltBase X c) ⋙
          (glueSliceEval X W (eltBase X c) c.unop.2).mapArrow
      = slInvArrow W p hthin R (eltBase X c') ⋙
          (glueSliceEval X W (eltBase X c') c'.unop.2).mapArrow := by
  rw [← Functor.assoc, slInvArrow_square W p hP hthin R, Functor.assoc,
    ← Functor.mapArrow_comp, overMapLoc_comp_glueSliceEval, elements_snd_map]

include hP hthin in
/-- **The counit, as a strict cocone** — `glueRetractCocone` one dimension up.  Its legs project
along `Arrow.leftFunc` and `Arrow.rightFunc` to `glueRetractPre c ⋙ glueDesc` and
`Over.forget c ⋙ Q` **definitionally**, which is what `glueCounitCocone_left`/`_right` spend. -/
noncomputable def glueCounitCocone :
    OverCocone ((X.Elements)ᵒᵖ)
      (Arrow ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization)) :=
  sliceCocone X W _ (fun {_ _} u => glueCounitStep X W p hP hthin R u)

include hP hthin in
/-- The retraction of a slice, read by the comparison. -/
theorem glueRetractPre_desc_eq (c : (X.Elements)ᵒᵖ) :
    glueRetractPre X W p hthin R c ⋙ glueDesc X W p hP
      = (Over.post (CategoryOfElements.π X).leftOp ⋙ (W.over (X := eltBase X c)).Q) ⋙
        ((slInv W p hthin R (eltBase X c) ⋙ (p (eltBase X c)).E) ⋙
          glueSliceEval X W (eltBase X c) c.unop.2) := by
  change Over.post (CategoryOfElements.π X).leftOp ⋙ (W.over (X := eltBase X c)).Q ⋙
      slInv W p hthin R (eltBase X c) ⋙
        (glueInclFun X P c ⋙ glueDesc X W p hP) = _
  rw [glueIncl_desc]
  rfl

/-- …and the slice itself, read by the comparison, is the slice of `∫X`. -/
theorem glueSliceForget (c : (X.Elements)ᵒᵖ) :
    (Over.post (CategoryOfElements.π X).leftOp ⋙ (W.over (X := eltBase X c)).Q) ⋙
        ((𝟭 ((W.over (X := eltBase X c)).Localization)) ⋙
          glueSliceEval X W (eltBase X c) c.unop.2)
      = Over.forget c ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q := by
  rw [Functor.id_comp, Functor.assoc, glueSliceEval_fac, ← Functor.assoc, elementsLift_post]

include hP hthin in
/-- **The cocone's two projections are the two functors to be compared** — the left one. -/
theorem glueCounitCocone_left :
    (glueCounitCocone X W p hP hthin R).postcomp Arrow.leftFunc
      = (glueRetractCocone X W p hP hthin R).postcomp (glueDesc X W p hP) := by
  ext c
  exact (glueRetractPre_desc_eq X W p hP hthin R c).symm

include hP hthin in
/-- …and the right one. -/
theorem glueCounitCocone_right :
    (glueCounitCocone X W p hP hthin R).postcomp Arrow.rightFunc
      = OverCocone.ofFunctor (W.inverseImage (CategoryOfElements.π X).leftOp).Q := by
  ext c
  exact glueSliceForget X W c

include hP hthin in
/-- …so the descended arrow runs from the composite… -/
theorem glueCounitDesc_left :
    (glueCounitCocone X W p hP hthin R).desc ⋙ Arrow.leftFunc
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙
        (glueRetract X W p hP hthin R ⋙ glueDesc X W p hP) :=
  ((OverCocone.desc_postcomp _ _).symm.trans
      (congrArg OverCocone.desc (glueCounitCocone_left X W p hP hthin R))).trans
    ((OverCocone.desc_postcomp _ _).trans
      (congrArg (· ⋙ glueDesc X W p hP) (glueRetract_fac X W p hP hthin R).symm))

include hP hthin in
/-- …to the localization functor. -/
theorem glueCounitDesc_right :
    (glueCounitCocone X W p hP hthin R).desc ⋙ Arrow.rightFunc
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q :=
  ((OverCocone.desc_postcomp _ _).symm.trans
      (congrArg OverCocone.desc (glueCounitCocone_right X W p hP hthin R))).trans
    (OverCocone.desc_ofFunctor _)

include hP hthin in
/-- The descended arrow is an isomorphism, because `slInvIso`'s components are. -/
theorem glueCounitArrow_isIso :
    IsIso (Functor.whiskerLeft (glueCounitCocone X W p hP hthin R).desc Arrow.leftToRight) := by
  haveI : ∀ c : (X.Elements)ᵒᵖ,
      IsIso ((Functor.whiskerLeft (glueCounitCocone X W p hP hthin R).desc
        Arrow.leftToRight).app c) := fun c =>
    inferInstanceAs (IsIso ((glueSliceEval X W (eltBase X c) c.unop.2).map
      ((slInvIso W p hthin R (eltBase X c)).hom.app _)))
  exact NatIso.isIso_of_isIso_app _

include hP hthin in
/-- **The counit**: the retraction, read through the comparison, is the identity up to
isomorphism — the isomorphism being the arrow the cocone descends to. -/
noncomputable def glueCounit :
    glueRetract X W p hP hthin R ⋙ glueDesc X W p hP ≅ 𝟭 _ :=
  haveI := glueCounitArrow_isIso X W p hP hthin R
  Localization.liftNatIso (W.inverseImage (CategoryOfElements.π X).leftOp).Q
    (W.inverseImage (CategoryOfElements.π X).leftOp)
    ((W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙
      (glueRetract X W p hP hthin R ⋙ glueDesc X W p hP))
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q
    (glueRetract X W p hP hthin R ⋙ glueDesc X W p hP) (𝟭 _)
    (eqToIso (glueCounitDesc_left X W p hP hthin R).symm ≪≫
      asIso (Functor.whiskerLeft (glueCounitCocone X W p hP hthin R).desc Arrow.leftToRight) ≪≫
      eqToIso (glueCounitDesc_right X W p hP hthin R))

include hP hthin R in
/-- **The colimit of the slice presentations presents `(∫X)[W⁻¹]`.**  `Equivalence.mk`
adjointifies, so the unit and the counit are all that is asked. -/
noncomputable def presentsSliceColimit :
    Presents (colimit (elementsPoly X P))
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  ⟨glueDesc X W p hP,
    (CategoryTheory.Equivalence.mk (glueDesc X W p hP)
      (glueRetract X W p hP hthin R)
      (eqToIso (glueUnit X W p hP hthin R).symm)
      (glueCounit X W p hP hthin R)).isEquivalence_functor⟩

end ColimCompare

end Polygraph

end CategoryTheory
