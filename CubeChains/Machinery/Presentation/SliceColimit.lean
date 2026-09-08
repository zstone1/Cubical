import CubeChains.Machinery.Presentation.Basic
import CubeChains.Machinery.Presentation.ChosenInverse
import CubeChains.Machinery.Presentation.Adjunction
import CubeChains.Machinery.Presentation.ColimitCells
import CubeChains.Machinery.Localization.SliceFamily
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Category.Cat.Colimit

/-!
# Machinery/Presentation/SliceColimit — one copy of `P d` for each element over `d`

`elementsPoly X P` is the **slice diagram**: `∫X ⟶ D` is a discrete fibration, so the copies of
`P d` are indexed by the elements over `d`, and `presentsSliceColimit` says their colimit presents
`(∫X)[W⁻¹]`.  Nothing is asked of the 0-cells — several may name one slice object, so *neither*
the unit nor the counit is an equality; both are carried as functors into `Arrow` and read back as
2-cells only at the end, so no comparison is ever transported.

`C[W⁻¹]` is itself the colimit of its localized slices (`isColimitOverLocCocone`), so
`presentsColimitOfLocalizedSlices` is a corollary and not a transport: levelwise equivalent
diagrams need **not** have equivalent strict colimits (`1 ⇉ SingleObj ℤ` against `1 ⇉ 1`).  The
comparison escapes that only because its target is a *fixed* category.
-/

universe w w' v₁ u₁ u' w₂ u

namespace CategoryTheory

open Opposite

namespace Polygraph

variable {D : Type u₁} [Category.{v₁} D] (X : Dᵒᵖ ⥤ Type w) (P : D ⥤ Polygraph.{w', u', w₂})

variable {P}

/-- `overMapLoc` on objects is `Over.map`. -/
theorem overMapLoc_obj (W : MorphismProperty D) {d' d : D} (f : d' ⟶ d) (Y : Over d') :
    (overMapLoc W f).obj (Localization.Construction.objEquiv (W.over (X := d')) Y) =
      Localization.Construction.objEquiv (W.over (X := d)) ((Over.map f).obj Y) :=
  Functor.congr_obj (overMapLocFac W f) Y

/-- …and every object of the localized slice is `Over.map`'s target of one below. -/
theorem objEquiv_symm_overMapLoc (W : MorphismProperty D) {d' d : D} (f : d' ⟶ d)
    (Y : (W.over (X := d')).Localization) :
    (Localization.Construction.objEquiv (W.over (X := d))).symm ((overMapLoc W f).obj Y)
      = (Over.map f).obj ((Localization.Construction.objEquiv (W.over (X := d'))).symm Y) :=
  (Localization.Construction.objEquiv (W.over (X := d))).symm_apply_eq.mpr
    (by rw [← overMapLoc_obj W f, Equiv.apply_symm_apply])

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
noncomputable def colimSliceEval (d : D) (x : X.obj (op d)) :
    (W.over (X := d)).Localization ⥤
      (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  Localization.Construction.lift _ (elementsLift_inverts X W d x)

theorem colimSliceEval_fac (d : D) (x : X.obj (op d)) :
    (W.over (X := d)).Q ⋙ colimSliceEval X W d x =
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
theorem overMapLoc_comp_colimSliceEval {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) :
    overMapLoc W f ⋙ colimSliceEval X W d x = colimSliceEval X W d' (X.map f.op x) :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, overMapLocFac, Functor.assoc, colimSliceEval_fac, colimSliceEval_fac,
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
choice.  The choice made here is a 0-cell naming each slice's **identity**; every other object is
that one pushed along its own structure map, so the inverse is functorial in the base *on the
nose* and nothing at all is asked of the 0-cells.  What it is not is a section: two 0-cells may
name one slice object, and then `(p d).E` followed by the inverse is only isomorphic to `𝟭`
(`Machinery/Presentation/StrictUnitRefutation`). -/

section Retract

variable (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))
  (hP : ∀ {d' d : D} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f)

/-- **A 0-cell naming the slice's identity.**  A choice — `Presents` is an equivalence, so several
0-cells may name that object — but which one is never asked. -/
noncomputable def sliceTop (d : D) : (P.obj d).presented :=
  (p d).E.objPreimage ((W.over (X := d)).Q.obj (Over.mk (𝟙 d)))

/-- …and it does name it. -/
noncomputable def sliceTopIso (d : D) :
    (p d).E.obj (sliceTop W p d) ≅ (W.over (X := d)).Q.obj (Over.mk (𝟙 d)) :=
  (p d).E.objObjPreimageIso _

/-- **The 0-cell a slice object is entered from**: the identity of its own domain, pushed along it.
-/
noncomputable def sliceRetObj {d : D} (y : Over d) : (P.obj d).presented :=
  (P.map y.hom).functor.obj (sliceTop W p y.left)

/-- **The entry is stable under pushing the base**, strictly — `P`'s functoriality and
nothing else. -/
theorem sliceRetObj_push {d' d : D} (f : d' ⟶ d) (y : Over d') :
    sliceRetObj W p ((Over.map f).obj y) = (P.map f).functor.obj (sliceRetObj W p y) :=
  Functor.congr_obj
    (show (P.map (y.hom ≫ f)).functor
        = (P.map y.hom).functor ⋙ (P.map f).functor by rw [P.map_comp, functor_comp])
    (sliceTop W p y.left)

/-- `𝟙 y.left ≫ y.hom = y.hom`, read in the localized slice. -/
theorem overMapLoc_top {d : D} (y : Over d) :
    (overMapLoc W y.hom).obj ((W.over (X := y.left)).Q.obj (Over.mk (𝟙 y.left)))
      = (W.over (X := d)).Q.obj y :=
  (overMapLoc_obj W y.hom (Over.mk (𝟙 y.left))).trans
    (congrArg (W.over (X := d)).Q.obj (congrArg Over.mk (Category.id_comp y.hom)))

/-- **The chosen preimage**: an object of the localized slice, entered from its own domain. -/
noncomputable def sliceRetPre (d : D) (Y : (W.over (X := d)).Localization) :
    (P.obj d).presented :=
  sliceRetObj W p ((Localization.Construction.objEquiv (W.over (X := d))).symm Y)

/-- …stable under pushing the base, `overMapLoc` being `Over.map` on objects. -/
theorem sliceRetPre_push {d' d : D} (f : d' ⟶ d) (Y : (W.over (X := d')).Localization) :
    sliceRetPre W p d ((overMapLoc W f).obj Y)
      = (P.map f).functor.obj (sliceRetPre W p d' Y) := by
  change sliceRetObj W p ((Localization.Construction.objEquiv (W.over (X := d))).symm
      ((overMapLoc W f).obj Y))
    = (P.map f).functor.obj (sliceRetObj W p
        ((Localization.Construction.objEquiv (W.over (X := d'))).symm Y))
  rw [objEquiv_symm_overMapLoc W f Y]
  exact sliceRetObj_push W p f _

include hP in
/-- `hP`, read on objects: which slice object a pushed 0-cell names. -/
theorem hP_obj {d' d : D} (f : d' ⟶ d) (a : (P.obj d').presented) :
    (p d).E.obj ((P.map f).functor.obj a) = (overMapLoc W f).obj ((p d').E.obj a) :=
  Functor.congr_obj (hP f) a

include hP in
/-- **…and the entry names the object it was read off.** -/
noncomputable def sliceRetObjIso {d : D} (y : Over d) :
    (p d).E.obj (sliceRetObj W p y) ≅ (W.over (X := d)).Q.obj y :=
  eqToIso (hP_obj W p hP y.hom (sliceTop W p y.left)) ≪≫
    (overMapLoc W y.hom).mapIso (sliceTopIso W p y.left) ≪≫ eqToIso (overMapLoc_top W y)

include hP in
/-- …transported along an equality of slice objects. -/
theorem sliceRetObjIso_congr {d : D} {y y' : Over d} (h : y = y') :
    sliceRetObjIso W p hP y
      = eqToIso (congrArg (fun z : Over d => (p d).E.obj (sliceRetObj W p z)) h)
        ≪≫ sliceRetObjIso W p hP y' ≪≫ eqToIso (congrArg (W.over (X := d)).Q.obj h.symm) := by
  subst h; simp

include hP in
/-- **The naming is natural in the base.**  This is the whole coherence the retraction needs, and
the only place `overMapLoc_comp` is spent:

```
      E (P (y ≫ f) ⊤)  --hP-->  (y ≫ f)∗ (E ⊤)  --⊤-->  Q (y ≫ f)
            ‖                        ‖ overMapLoc_comp        ‖
      f∗ (E (P y ⊤))   --hP-->  f∗ (y∗ (E ⊤))   --⊤-->  f∗ (Q y)
```
-/
theorem sliceRetObjIso_push {d' d : D} (f : d' ⟶ d) (y : Over d') :
    sliceRetObjIso W p hP ((Over.map f).obj y)
      = eqToIso ((congrArg (p d).E.obj (sliceRetObj_push W p f y)).trans
          (hP_obj W p hP f (sliceRetObj W p y)))
        ≪≫ (overMapLoc W f).mapIso (sliceRetObjIso W p hP y)
        ≪≫ eqToIso (Functor.congr_obj (overMapLocFac W f) y) := by
  -- `((Over.map f).obj y).left` is `y.left` only up to `Over.map`, which no rewrite unfolds
  -- inside an instance argument: restate the left-hand side in the `y` spelling first.
  change eqToIso (hP_obj W p hP (y.hom ≫ f) (sliceTop W p y.left))
      ≪≫ (overMapLoc W (y.hom ≫ f)).mapIso (sliceTopIso W p y.left)
      ≪≫ eqToIso (overMapLoc_top W (Over.mk (y.hom ≫ f))) = _
  rw [Functor.congr_mapIso (overMapLoc_comp W y.hom f) (sliceTopIso W p y.left)]
  simp only [sliceRetObjIso, Functor.comp_mapIso, Functor.mapIso_trans, eqToIso_map]
  exact eqToIso_conj_ext _ _ _ _ _ _ _ _ _

include hP in
/-- The naming, at an object of the localized slice. -/
noncomputable def sliceRetIsoAt (d : D) (Y : (W.over (X := d)).Localization) :
    (p d).E.obj (sliceRetPre W p d Y) ≅ Y :=
  sliceRetObjIso W p hP ((Localization.Construction.objEquiv (W.over (X := d))).symm Y)
    ≪≫ eqToIso ((Localization.Construction.objEquiv (W.over (X := d))).apply_symm_apply Y)

include hP in
/-- The object comparison every square below runs on. -/
theorem sliceRetPre_obj_eq {d' d : D} (f : d' ⟶ d) (Y : (W.over (X := d')).Localization) :
    (p d).E.obj (sliceRetPre W p d ((overMapLoc W f).obj Y))
      = (overMapLoc W f).obj ((p d').E.obj (sliceRetPre W p d' Y)) :=
  (congrArg (p d).E.obj (sliceRetPre_push W p f Y)).trans
    (hP_obj W p hP f (sliceRetPre W p d' Y))

include hP in
/-- **…and the naming with it** — `sliceRetObjIso_push`, read at the localization. -/
theorem sliceRetIsoAt_push {d' d : D} (f : d' ⟶ d) (Y : (W.over (X := d')).Localization) :
    sliceRetIsoAt W p hP d ((overMapLoc W f).obj Y)
      = eqToIso (sliceRetPre_obj_eq W p hP f Y)
        ≪≫ (overMapLoc W f).mapIso (sliceRetIsoAt W p hP d' Y) := by
  simp only [sliceRetIsoAt, sliceRetObjIso_congr W p hP (objEquiv_symm_overMapLoc W f Y),
    sliceRetObjIso_push W p hP f, Functor.mapIso_trans, eqToIso_map]
  exact eqToIso_conj_collapse _ _ _ _ _ _ _ _

include hP in
/-- **The slice presentation, inverted on the nose**: the chosen inverse at the entry 0-cells, so
nothing at all is asked of them. -/
noncomputable def sliceRet (d : D) :
    (W.over (X := d)).Localization ⥤ (P.obj d).presented :=
  (p d).E.invOfPreimage (sliceRetPre W p d) (sliceRetIsoAt W p hP d)

include hP in
/-- **The inversion is a section of the presentation up to isomorphism.** -/
noncomputable def sliceRetIso (d : D) : sliceRet W p hP d ⋙ (p d).E ≅ 𝟭 _ :=
  (p d).E.invOfPreimageCounit (sliceRetPre W p d) (sliceRetIsoAt W p hP d)

include hP in
/-- **…and a retraction of it, again only up to isomorphism.**  Two 0-cells may name a single
slice object, and the retraction sends both to the same 0-cell, so an equality is too much to
ask. -/
noncomputable def sliceUnitIso (d : D) :
    𝟭 ((P.obj d).presented) ≅ (p d).E ⋙ sliceRet W p hP d :=
  (p d).E.invOfPreimageUnit (sliceRetPre W p d) (sliceRetIsoAt W p hP d)

include hP in
/-- **A commuting square inverts to a commuting square** — `sliceRetPre_push` on objects, and on
morphisms the faithfulness of `(p d).E`. -/
theorem sliceRet_square {d' d : D} (f : d' ⟶ d) :
    overMapLoc W f ⋙ sliceRet W p hP d
      = sliceRet W p hP d' ⋙ (P.map f).functor :=
  Functor.invOfPreimage_square (p d').E (sliceRetPre W p d') (sliceRetIsoAt W p hP d')
    (p d).E (sliceRetPre W p d) (sliceRetIsoAt W p hP d) (P.map f).functor (overMapLoc W f)
    (hP f) (sliceRetPre_push W p f) (sliceRetPre_obj_eq W p hP f) (sliceRetIsoAt_push W p hP f)

include hP in
/-- **The retraction, followed by the presentation, is postcomposition.** -/
theorem sliceRetComp_square {d' d : D} (f : d' ⟶ d) :
    overMapLoc W f ⋙ sliceRet W p hP d ⋙ (p d).E
      = (sliceRet W p hP d' ⋙ (p d').E) ⋙ overMapLoc W f :=
  Functor.invOfPreimage_comp_square (p d').E (sliceRetPre W p d') (sliceRetIsoAt W p hP d')
    (p d).E (sliceRetPre W p d) (sliceRetIsoAt W p hP d) (overMapLoc W f)
    (sliceRetPre_obj_eq W p hP f) (sliceRetIsoAt_push W p hP f)

include hP in
/-- **`sliceRetIso`, as a 1-cell**, so that it can travel through a colimit: a 2-cell out of a
category is a functor into `Arrow`, and *that* descends. -/
noncomputable def sliceRetArrow (d : D) :
    (W.over (X := d)).Localization ⥤ Arrow ((W.over (X := d)).Localization) :=
  (sliceRetIso W p hP d).hom.toArrow

include hP in
/-- **Neighbouring slices compare the same way** — an *equality* of functors, the components being
`sliceRetIsoAt_push`. -/
theorem sliceRetArrow_square {d' d : D} (f : d' ⟶ d) :
    overMapLoc W f ⋙ sliceRetArrow W p hP d
      = sliceRetArrow W p hP d' ⋙ (overMapLoc W f).mapArrow :=
  Functor.invOfPreimageCounit_arrow_square (p d').E (sliceRetPre W p d')
    (sliceRetIsoAt W p hP d') (p d).E (sliceRetPre W p d) (sliceRetIsoAt W p hP d)
    (overMapLoc W f) (sliceRetPre_obj_eq W p hP f) (sliceRetIsoAt_push W p hP f)

include hP in
/-- **The retraction's comparison, as a 1-cell**, so that it can travel through the colimit: a
2-cell out of `(P d).presented` is a functor into `Arrow`, and *that* descends. -/
noncomputable def sliceUnitArrow (d : D) :
    (P.obj d).presented ⥤ Arrow ((P.obj d).presented) :=
  (sliceUnitIso W p hP d).hom.toArrow

include hP in
/-- **Neighbouring copies compare the same way** — the same square, one level down. -/
theorem sliceUnitArrow_square {d' d : D} (f : d' ⟶ d) :
    (P.map f).functor ⋙ sliceUnitArrow W p hP d
      = sliceUnitArrow W p hP d' ⋙ (P.map f).functor.mapArrow :=
  Functor.invOfPreimageUnit_arrow_square (p d').E (sliceRetPre W p d')
    (sliceRetIsoAt W p hP d') (p d).E (sliceRetPre W p d) (sliceRetIsoAt W p hP d)
    (P.map f).functor (overMapLoc W f) (hP f) (sliceRetPre_push W p f)
    (sliceRetPre_obj_eq W p hP f) (sliceRetIsoAt_push W p hP f)

end Retract

/-! ## The colimit polygraph -/

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
over an element is the slice of `D` over its base, and the copies are joined along exactly the
arrows of `(∫X)ᵒᵖ`.  Everything below is the colimit's universal property and nothing else; no
0-cell is ever examined. -/

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) (P : D ⥤ Polygraph.{u, u, u})

/-- The object of `D` an element lies over. -/
abbrev eltBase (c : (X.Elements)ᵒᵖ) : D := (CategoryOfElements.π X).leftOp.obj c

/-- **The slice diagram**: one copy of `P d` for each element over `d`. -/
def elementsPoly : (X.Elements)ᵒᵖ ⥤ Polygraph.{u, u, u} := (CategoryOfElements.π X).leftOp ⋙ P

/-- The colimit leg at an element, read on presented categories. -/
noncomputable def colimInclFun (c : (X.Elements)ᵒᵖ) :
    (P.obj (eltBase X c)).presented ⥤ (colimit (elementsPoly X P)).presented :=
  (colimit.ι (elementsPoly X P) c).functor

/-- **The copies are natural in the element** — a strict equality of functors. -/
theorem colimInclFun_naturality {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ colimInclFun X P c
      = colimInclFun X P c' :=
  (functor_comp _ _).symm.trans
    (congrArg Hom.functor (colimit.w (elementsPoly X P) u))

variable {X P}

/-- **A compatible family of functors out of the copies descends.** -/
noncomputable def colimLift (F : ∀ c : (X.Elements)ᵒᵖ, (P.obj (eltBase X c)).presented ⥤ C)
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
theorem colimInclFun_lift (F : ∀ c : (X.Elements)ᵒᵖ, (P.obj (eltBase X c)).presented ⥤ C)
    (hF : ∀ {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c),
      (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ F c = F c')
    (c : (X.Elements)ᵒᵖ) :
    colimInclFun X P c ⋙ colimLift F hF = F c :=
  (homToFun_comp _ _).symm.trans
    ((congrArg homToFun (colimit.ι_desc _ c)).trans ((catHomEquiv _ C).right_inv (F c)))

/-- **A functor out of the colimit polygraph is pinned by its copies.**  This is what replaces
induction over 0-cells: the comparison and the retraction are compared here and nowhere else. -/
theorem colim_functor_ext {F G : (colimit (elementsPoly X P)).presented ⥤ C}
    (h : ∀ c, colimInclFun X P c ⋙ F = colimInclFun X P c ⋙ G) : F = G :=
  ((catHomEquiv _ C).right_inv F).symm.trans
    ((congrArg homToFun (colimit.hom_ext fun c =>
      (homInvFun_comp (colimit.ι (elementsPoly X P) c) F).symm.trans
        ((congrArg homInvFun (h c)).trans
          (homInvFun_comp (colimit.ι (elementsPoly X P) c) G)))).trans
      ((catHomEquiv _ C).right_inv G))

end Colimit

/-! ### The comparison functor

Each copy carries its own slice presentation; pushing that along the cartesian lift gives a
compatible family, and `colimLift` descends it.  `hP` is the whole input. -/

section ColimCompare

open Limits

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
  (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))

/-- A copy, read in `(∫X)[W⁻¹]`: the slice presentation, pushed along the cartesian lift. -/
noncomputable def colimLeg (c : (X.Elements)ᵒᵖ) :
    (P.obj (eltBase X c)).presented ⥤
      (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (p (eltBase X c)).E ⋙ colimSliceEval X W (eltBase X c) c.unop.2

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

variable (hP : ∀ {d' d : D} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f)

include hP in
/-- **The copies agree along an arrow of `∫X`** — `hP`, read through the cartesian lift. -/
theorem colimLeg_naturality {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ colimLeg X W p c
      = colimLeg X W p c' := by
  change (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ (p _).E ⋙ _
    = (p _).E ⋙ colimSliceEval X W _ c'.unop.2
  rw [← Functor.assoc, hP ((CategoryOfElements.π X).leftOp.map u), Functor.assoc,
    overMapLoc_comp_colimSliceEval, elements_snd_map]
  rfl

include hP in
/-- **The comparison functor**: a word of the colimit polygraph, read in `(∫X)[W⁻¹]`. -/
noncomputable def colimDesc :
    (colimit (elementsPoly X P)).presented ⥤
      (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  colimLift (colimLeg X W p) (colimLeg_naturality X W p hP)

include hP in
/-- **A copy, read by the comparison** — its own presentation, and nothing else. -/
theorem colimIncl_desc (c : (X.Elements)ᵒᵖ) :
    colimInclFun X P c ⋙ colimDesc X W p hP
      = (p (eltBase X c)).E ⋙ colimSliceEval X W (eltBase X c) c.unop.2 :=
  colimInclFun_lift (colimLeg X W p) (colimLeg_naturality X W p hP) c

/-! ### The retraction

Down to the base slice, the slice presentation inverted, and the copy at the element.  All three
steps are strictly natural in the element, so this is an honest cocone. -/

include hP in
/-- The retraction, before localizing. -/
noncomputable def colimRetractPre (c : (X.Elements)ᵒᵖ) :
    Over c ⥤ (colimit (elementsPoly X P)).presented :=
  sliceLeg X W (fun c => sliceRet W p hP (eltBase X c) ⋙ colimInclFun X P c) c

include hP in
/-- The comparison on the base slice: `sliceRet_square` followed by the copies' naturality. -/
theorem colimStep {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        sliceRet W p hP (eltBase X c) ⋙ colimInclFun X P c
      = sliceRet W p hP (eltBase X c') ⋙ colimInclFun X P c' := by
  rw [← Functor.assoc, sliceRet_square W p hP, Functor.assoc, colimInclFun_naturality]

include hP in
theorem colimRetractPre_inverts (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).IsInvertedBy
      (colimRetractPre X W p hP c) := by
  intro Y Z φ hφ
  haveI : IsIso ((W.over (X := eltBase X c)).Q.map
      ((Over.post (CategoryOfElements.π X).leftOp).map φ)) :=
    Localization.inverts _ (W.over (X := eltBase X c)) _ hφ
  exact inferInstanceAs (IsIso
    ((sliceRet W p hP (eltBase X c) ⋙ colimInclFun X P c).map
      ((W.over (X := eltBase X c)).Q.map
        ((Over.post (CategoryOfElements.π X).leftOp).map φ))))

include hP in
/-- The retraction, as a **strict** cocone on the slices. -/
noncomputable def colimRetractCocone :
    OverCocone ((X.Elements)ᵒᵖ) ((colimit (elementsPoly X P)).presented) :=
  sliceCocone X W _ (fun {_ _} u => colimStep X W p hP u)

include hP in
theorem colimRetractCocone_inverts :
    (W.inverseImage (CategoryOfElements.π X).leftOp).IsInvertedBy
      (colimRetractCocone X W p hP).desc := by
  rw [isInvertedBy_iff_over, OverCocone.ofFunctor_desc]
  exact colimRetractPre_inverts X W p hP

include hP in
/-- **The retraction** `Ψ : (∫X)[W⁻¹] ⥤ colim`, descended from the slices. -/
noncomputable def colimRetract :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization ⥤
      (colimit (elementsPoly X P)).presented :=
  Localization.Construction.lift _ (colimRetractCocone_inverts X W p hP)

include hP in
theorem colimRetract_fac :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙ colimRetract X W p hP
      = (colimRetractCocone X W p hP).desc :=
  Localization.Construction.fac _ _

include hP in
theorem colimRetract_forget (c : (X.Elements)ᵒᵖ) :
    Over.forget c ⋙ (colimRetractCocone X W p hP).desc
      = colimRetractPre X W p hP c :=
  congrArg (fun G => OverCocone.obj G c) (OverCocone.ofFunctor_desc _)

include hP in
/-- **A slice, read through the retraction, is the copy at that element** — the mirror of
`colimIncl_desc`. -/
theorem colimSliceEval_retract (c : (X.Elements)ᵒᵖ) :
    colimSliceEval X W (eltBase X c) c.unop.2 ⋙ colimRetract X W p hP
      = sliceRet W p hP (eltBase X c) ⋙ colimInclFun X P c := by
  refine Localization.Construction.uniq _ _ ?_
  rw [← Functor.assoc, colimSliceEval_fac, Functor.assoc, colimRetract_fac,
    ← elementsLiftOver_forget X c, Functor.assoc, colimRetract_forget]
  unfold colimRetractPre sliceLeg
  simp only [← Functor.assoc]
  rw [elementsLiftOver_post, Functor.id_comp]

/-! ### The unit

`sliceUnitArrow` compares `𝟭` with `Ψ ∘ Φ` on one copy, and it is a *functor*, so the colimit
descends it like any other 1-cell.  Only then is it read back as a 2-cell, by `Arrow.leftToRight`:
a natural transformation out of a colimit does not descend, but a functor into `Arrow` does. -/

include hP in
/-- The unit's copy at an element. -/
noncomputable def colimUnitLeg (c : (X.Elements)ᵒᵖ) :
    (P.obj (eltBase X c)).presented ⥤ Arrow ((colimit (elementsPoly X P)).presented) :=
  sliceUnitArrow W p hP (eltBase X c) ⋙ (colimInclFun X P c).mapArrow

include hP in
theorem colimUnitLeg_naturality {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙ colimUnitLeg X W p hP c
      = colimUnitLeg X W p hP c' := by
  unfold colimUnitLeg
  rw [← Functor.assoc, sliceUnitArrow_square W p hP, Functor.assoc,
    ← Functor.mapArrow_comp, colimInclFun_naturality]

include hP in
/-- **The unit, as a 1-cell of the colimit polygraph.** -/
noncomputable def colimUnitArrow :
    (colimit (elementsPoly X P)).presented ⥤
      Arrow ((colimit (elementsPoly X P)).presented) :=
  colimLift (colimUnitLeg X W p hP) (colimUnitLeg_naturality X W p hP)

include hP in
theorem colimInclFun_unitArrow (c : (X.Elements)ᵒᵖ) :
    colimInclFun X P c ⋙ colimUnitArrow X W p hP = colimUnitLeg X W p hP c :=
  colimInclFun_lift (colimUnitLeg X W p hP) (colimUnitLeg_naturality X W p hP) c

include hP in
/-- **The descended arrow runs from the identity…** -/
theorem colimUnitArrow_left :
    colimUnitArrow X W p hP ⋙ Arrow.leftFunc = 𝟭 _ :=
  colim_functor_ext fun c => by
    rw [← Functor.assoc, colimInclFun_unitArrow, Functor.comp_id]
    rfl

include hP in
/-- **…to the comparison read through the retraction** — `colimSliceEval_retract` on each copy. -/
theorem colimUnitArrow_right :
    colimUnitArrow X W p hP ⋙ Arrow.rightFunc
      = colimDesc X W p hP ⋙ colimRetract X W p hP :=
  colim_functor_ext fun c => by
    rw [← Functor.assoc, colimInclFun_unitArrow, ← Functor.assoc, colimIncl_desc, Functor.assoc,
      colimSliceEval_retract]
    rfl

include hP in
/-- The descended arrow is an isomorphism, because `sliceUnitIso`'s components are and every
0-cell of the colimit is a copy's (`exists_colimit_ι_obj`). -/
theorem colimUnitArrow_isIso :
    IsIso (Functor.whiskerLeft (colimUnitArrow X W p hP) Arrow.leftToRight) := by
  haveI : ∀ A : (colimit (elementsPoly X P)).presented,
      IsIso ((Functor.whiskerLeft (colimUnitArrow X W p hP) Arrow.leftToRight).app A) := by
    intro A
    obtain ⟨c, x, hx⟩ := exists_colimit_ι_obj (elementsPoly X P) A.as
    obtain rfl : (colimInclFun X P c).obj ⟨x⟩ = A :=
      congrArg (fun z : GenObj (colimit (elementsPoly X P)).Gen =>
        (⟨z⟩ : (colimit (elementsPoly X P)).presented)) hx
    have h : (colimUnitArrow X W p hP).obj ((colimInclFun X P c).obj ⟨x⟩)
        = (colimUnitLeg X W p hP c).obj ⟨x⟩ :=
      Functor.congr_obj (colimInclFun_unitArrow X W p hP c) ⟨x⟩
    change IsIso ((colimUnitArrow X W p hP).obj ((colimInclFun X P c).obj ⟨x⟩)).hom
    rw [h]
    exact inferInstanceAs (IsIso ((colimInclFun X P c).map
      ((sliceUnitIso W p hP (eltBase X c)).hom.app ⟨x⟩)))
  exact NatIso.isIso_of_isIso_app _

include hP in
/-- **The unit**: the comparison, read through the retraction, is the identity up to isomorphism.
Not an equality: two 0-cells may name one slice object (`Machinery/Presentation/StrictUnitRefutation`). -/
noncomputable def colimUnit :
    𝟭 ((colimit (elementsPoly X P)).presented)
      ≅ colimDesc X W p hP ⋙ colimRetract X W p hP :=
  haveI := colimUnitArrow_isIso X W p hP
  Functor.arrowNatIso (colimUnitArrow X W p hP)
    (colimUnitArrow_left X W p hP) (colimUnitArrow_right X W p hP)

include hP in
/-- The comparison on the base slice: `sliceRetArrow_square`, then the cartesian lift at `c`
restricted along `u`, which is the lift at `c'`. -/
theorem colimCounitStep {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        sliceRetArrow W p hP (eltBase X c) ⋙
          (colimSliceEval X W (eltBase X c) c.unop.2).mapArrow
      = sliceRetArrow W p hP (eltBase X c') ⋙
          (colimSliceEval X W (eltBase X c') c'.unop.2).mapArrow := by
  rw [← Functor.assoc, sliceRetArrow_square W p hP, Functor.assoc,
    ← Functor.mapArrow_comp, overMapLoc_comp_colimSliceEval, elements_snd_map]

include hP in
/-- **The counit, as a strict cocone** — `colimRetractCocone` one dimension up.  Its legs project
along `Arrow.leftFunc` and `Arrow.rightFunc` to `colimRetractPre c ⋙ colimDesc` and
`Over.forget c ⋙ Q` **definitionally**, which is what `colimCounitCocone_left`/`_right` spend. -/
noncomputable def colimCounitCocone :
    OverCocone ((X.Elements)ᵒᵖ)
      (Arrow ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization)) :=
  sliceCocone X W _ (fun {_ _} u => colimCounitStep X W p hP u)

include hP in
/-- The retraction of a slice, read by the comparison. -/
theorem colimRetractPre_desc_eq (c : (X.Elements)ᵒᵖ) :
    colimRetractPre X W p hP c ⋙ colimDesc X W p hP
      = (Over.post (CategoryOfElements.π X).leftOp ⋙ (W.over (X := eltBase X c)).Q) ⋙
        ((sliceRet W p hP (eltBase X c) ⋙ (p (eltBase X c)).E) ⋙
          colimSliceEval X W (eltBase X c) c.unop.2) := by
  change Over.post (CategoryOfElements.π X).leftOp ⋙ (W.over (X := eltBase X c)).Q ⋙
      sliceRet W p hP (eltBase X c) ⋙
        (colimInclFun X P c ⋙ colimDesc X W p hP) = _
  rw [colimIncl_desc]
  rfl

/-- …and the slice itself, read by the comparison, is the slice of `∫X`. -/
theorem colimSliceForget (c : (X.Elements)ᵒᵖ) :
    (Over.post (CategoryOfElements.π X).leftOp ⋙ (W.over (X := eltBase X c)).Q) ⋙
        ((𝟭 ((W.over (X := eltBase X c)).Localization)) ⋙
          colimSliceEval X W (eltBase X c) c.unop.2)
      = Over.forget c ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q := by
  rw [Functor.id_comp, Functor.assoc, colimSliceEval_fac, ← Functor.assoc, elementsLift_post]

include hP in
/-- **The cocone's two projections are the two functors to be compared** — the left one. -/
theorem colimCounitCocone_left :
    (colimCounitCocone X W p hP).postcomp Arrow.leftFunc
      = (colimRetractCocone X W p hP).postcomp (colimDesc X W p hP) := by
  ext c
  exact (colimRetractPre_desc_eq X W p hP c).symm

include hP in
/-- …and the right one. -/
theorem colimCounitCocone_right :
    (colimCounitCocone X W p hP).postcomp Arrow.rightFunc
      = OverCocone.ofFunctor (W.inverseImage (CategoryOfElements.π X).leftOp).Q := by
  ext c
  exact colimSliceForget X W c

include hP in
/-- …so the descended arrow runs from the composite… -/
theorem colimCounitDesc_left :
    (colimCounitCocone X W p hP).desc ⋙ Arrow.leftFunc
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙
        (colimRetract X W p hP ⋙ colimDesc X W p hP) :=
  ((OverCocone.desc_postcomp _ _).symm.trans
      (congrArg OverCocone.desc (colimCounitCocone_left X W p hP))).trans
    ((OverCocone.desc_postcomp _ _).trans
      (congrArg (· ⋙ colimDesc X W p hP) (colimRetract_fac X W p hP).symm))

include hP in
/-- …to the localization functor. -/
theorem colimCounitDesc_right :
    (colimCounitCocone X W p hP).desc ⋙ Arrow.rightFunc
      = (W.inverseImage (CategoryOfElements.π X).leftOp).Q :=
  ((OverCocone.desc_postcomp _ _).symm.trans
      (congrArg OverCocone.desc (colimCounitCocone_right X W p hP))).trans
    (OverCocone.desc_ofFunctor _)

include hP in
/-- The descended arrow is an isomorphism, because `sliceRetIso`'s components are. -/
theorem colimCounitArrow_isIso :
    IsIso (Functor.whiskerLeft (colimCounitCocone X W p hP).desc Arrow.leftToRight) := by
  haveI : ∀ c : (X.Elements)ᵒᵖ,
      IsIso ((Functor.whiskerLeft (colimCounitCocone X W p hP).desc
        Arrow.leftToRight).app c) := fun c =>
    inferInstanceAs (IsIso ((colimSliceEval X W (eltBase X c) c.unop.2).map
      ((sliceRetIso W p hP (eltBase X c)).hom.app _)))
  exact NatIso.isIso_of_isIso_app _

include hP in
/-- **The counit**: the retraction, read through the comparison, is the identity up to
isomorphism — the isomorphism being the arrow the cocone descends to. -/
noncomputable def colimCounit :
    colimRetract X W p hP ⋙ colimDesc X W p hP ≅ 𝟭 _ :=
  haveI := colimCounitArrow_isIso X W p hP
  Localization.liftNatIso (W.inverseImage (CategoryOfElements.π X).leftOp).Q
    (W.inverseImage (CategoryOfElements.π X).leftOp)
    ((W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙
      (colimRetract X W p hP ⋙ colimDesc X W p hP))
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q
    (colimRetract X W p hP ⋙ colimDesc X W p hP) (𝟭 _)
    (Functor.arrowNatIso (colimCounitCocone X W p hP).desc
      (colimCounitDesc_left X W p hP) (colimCounitDesc_right X W p hP))

include hP in
/-- **The colimit of the slice presentations presents `(∫X)[W⁻¹]`.**  `Equivalence.mk`
adjointifies, so the unit and the counit are all that is asked. -/
noncomputable def presentsSliceColimit :
    Presents (colimit (elementsPoly X P))
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  ⟨colimDesc X W p hP,
    (CategoryTheory.Equivalence.mk (colimDesc X W p hP)
      (colimRetract X W p hP)
      (colimUnit X W p hP)
      (colimCounit X W p hP)).isEquivalence_functor⟩

end ColimCompare

end Polygraph

end CategoryTheory

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

/-! ## `C[W⁻¹]` is the colimit of its localized slices -/

/-- The localized slices as a diagram of categories. -/
noncomputable def overLocFunctor : C ⥤ Cat.{u, u} where
  obj c := Cat.of ((W.over (X := c)).Localization)
  map u := (overMapLoc W u).toCatHom
  map_id c := Cat.ext (overMapLoc_id W c)
  map_comp u v := Cat.ext (overMapLoc_comp W u v)

/-- The localization functor, restricted to the slice over `c`. -/
noncomputable def overLocLeg (c : C) : (W.over (X := c)).Localization ⥤ W.Localization :=
  (overCoconeLocEquiv W (𝟭 W.Localization)).obj c

/-- **A functor on `C[W⁻¹]` postcomposes the legs** — `overCoconeLocEquiv` is natural in its
target, which is what makes the legs a *colimiting* cocone and not merely a cocone. -/
theorem overLocLeg_comp {E : Type u} [Category.{u} E] (Φ : W.Localization ⥤ E) (c : C) :
    overLocLeg W c ⋙ Φ = (overCoconeLocEquiv W Φ).obj c :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, overLocLeg, overCoconeLocEquiv_apply W (𝟭 W.Localization) c,
      overCoconeLocEquiv_apply W Φ c, Functor.comp_id, Functor.assoc])

/-- The legs, as a cocone on the localized slices. -/
noncomputable def overLocCocone : Cocone (overLocFunctor W) where
  pt := Cat.of W.Localization
  ι :=
    { app := fun c => (overLocLeg W c).toCatHom
      naturality := fun _ _ u =>
        Cat.ext (((overCoconeLocEquiv W (𝟭 W.Localization)).w u).trans
          (Functor.comp_id _).symm) }

/-- **`C[W⁻¹]` is the colimit of its localized slices.** -/
noncomputable def isColimitOverLocCocone : IsColimit (overLocCocone W) where
  desc s := Cat.Hom.ofFunctor ((overCoconeLocEquiv W).symm
    { obj := fun c => (s.ι.app c).toFunctor
      w := fun {_ _} u => congrArg Cat.Hom.toFunctor (s.w u) })
  fac s c := Cat.ext ((overLocLeg_comp W _ c).trans
    (congrArg (fun G : OverCoconeLoc W ↥s.pt => G.obj c)
      ((overCoconeLocEquiv W).apply_symm_apply _)))
  uniq _s m h := Cat.ext ((Equiv.eq_symm_apply _).2 (OverCoconeLoc.ext W fun c =>
    (overLocLeg_comp W m.toFunctor c).symm.trans (congrArg Cat.Hom.toFunctor (h c))))

/-! ## The colimit of the slice presentations, against the colimit of the localized slices -/

namespace Polygraph

variable {D : Type u} [Category.{u} D] (X : Dᵒᵖ ⥤ Type u) {P : D ⥤ Polygraph.{u, u, u}}
  (V : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((V.over (X := d)).Localization))
  (hP : ∀ {d' d : D} (f : d' ⟶ d),
    (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc V f)

include hP in
/-- **The colimit of the slice presentations presents the colimit of the localized slices** — a
corollary of `presentsSliceColimit`, read through `isColimitOverLocCocone`. -/
noncomputable def presentsColimitOfLocalizedSlices :
    Presents (colimit (elementsPoly X P))
      ↥(colimit (overLocFunctor (V.inverseImage (CategoryOfElements.π X).leftOp))) :=
  (presentsSliceColimit X V p hP).transport
    (Cat.equivOfIso ((isColimitOverLocCocone _).coconePointUniqueUpToIso (colimit.isColimit _)))

include hP in
/-- **…so the colimit of the presented slices is the colimit of the localized ones**, the same
statement with the presentation cancelled on the left by `presentsColimit`. -/
noncomputable def colimitPresentedEquivColimitLoc :
    ↥(colimit (elementsPoly X P ⋙ presentedFunctor.{u, u})) ≌
      ↥(colimit (overLocFunctor (V.inverseImage (CategoryOfElements.π X).leftOp))) :=
  (presentsColimit (elementsPoly X P)).equiv.symm.trans
    (presentsColimitOfLocalizedSlices X V p hP).equiv


/-- **Any presentation of the colimit names its 0-cells strictly naturally.**  A 0-cell of a copy
and its push-forward are *one* 0-cell of the colimit polygraph, so they name one object of whatever
category is presented: the strictness is a property of the colimit, not of the proof, and no
weakening of `hP` and no 2-cell datum removes it. -/
theorem Presents.colimNaming_natural {C : Type u} [Category.{u} C]
    (q : Presents (colimit (elementsPoly X P)) C)
    {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) (a : (P.obj (eltBase X c')).presented) :
    q.E.obj ((colimInclFun X P c).obj
        ((P.map ((CategoryOfElements.π X).leftOp.map u)).functor.obj a))
      = q.E.obj ((colimInclFun X P c').obj a) :=
  congrArg q.E.obj (Functor.congr_obj (colimInclFun_naturality X P u) a)
end Polygraph

end CategoryTheory
