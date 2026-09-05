import CubeChains.Machinery.Presentation.Basic
import CubeChains.Machinery.Localization.SliceFamily
import CubeChains.Machinery.StrictInverse
import Mathlib.CategoryTheory.Elements

/-!
# Machinery/Presentation/Glue — one copy of `P d` for each element over `d`

`glue X L`: the objects of `∫X` as 0-cells, a copy of `P d` over each `x ∈ X d`, an overlap 2-cell
per `f : d' ⟶ d`, and `L : SliceLabels P` naming the arrow of `Over d` a 0-cell stands for.

**Write the functor down; do not invert an abstract equivalence.**  Strictness is what makes this
file typecheck: `SliceLabels.map_ob` is an equality only because `overMapLoc` is a
`Construction.lift` (an iso there, and `GlueRel.overlap` would not typecheck), and `elementsLift`
is an explicit lift because `Localization.uniq` is opaque on objects.  Once the labels are
bijective `pInv` inverts each `(p d).E` on the nose too, so both comparisons are equalities.
-/

universe w w' v₁ u₁ u' w₂

namespace CategoryTheory

open Opposite

/-- Composing two sandwiches: the two facing crusts merge into one.

Everything in this file is an `eqToHom` sandwich, and `rw`/`simp` cannot reassociate one: the two
spellings of the middle object are defeq but `kabstract` matches at `instances` transparency, so
`Category.assoc` silently fails to fire.  Use this through `exact`, which elaborates at default
transparency. -/
theorem eqToHom_conj_comp {E : Type*} [Category E] {A B B' B'' C A' C' : E}
    (hA : A' = A) (hB : B = B') (hB' : B' = B'') (hC : C = C') (f : A ⟶ B) (g : B'' ⟶ C) :
    (eqToHom hA ≫ f ≫ eqToHom hB) ≫ (eqToHom hB' ≫ g ≫ eqToHom hC)
      = eqToHom hA ≫ (f ≫ eqToHom (hB.trans hB') ≫ g) ≫ eqToHom hC := by
  subst hA; subst hB; subst hB'; subst hC; simp

/-- A sandwich inside a sandwich is a sandwich. -/
theorem eqToHom_conj_conj {E : Type*} [Category E] {A B A' B' A'' B'' : E}
    (hA : A' = A) (hB : B = B') (hA' : A'' = A') (hB' : B' = B'') (f : A ⟶ B) :
    eqToHom hA' ≫ (eqToHom hA ≫ f ≫ eqToHom hB) ≫ eqToHom hB'
      = eqToHom (hA'.trans hA) ≫ f ≫ eqToHom (hB.trans hB') := by
  subst hA; subst hB; subst hA'; subst hB'; simp

/-- Sandwiches with equal fillings agree; the bread is proof-irrelevant, so the two sides may be
spelled with different proofs. -/
theorem eqToHom_conj_congr {E : Type*} [Category E] {A B A' B' : E} (hA : A' = A) (hB : B = B')
    {f g : A ⟶ B} (h : f = g) :
    eqToHom hA ≫ f ≫ eqToHom hB = eqToHom hA ≫ g ≫ eqToHom hB := by rw [h]

/-- A functor carries a sandwich to a sandwich.  Under a `Quotient` lift's `.map` no rewrite
matches, so reach this through `exact`. -/
theorem eqToHom_conj_map {C E : Type*} [Category C] [Category E] (F : C ⥤ E) {A B B' Z : C}
    (h₁ : A = B) (m : B ⟶ B') (h₂ : B' = Z) :
    F.map (eqToHom h₁ ≫ m ≫ eqToHom h₂)
      = eqToHom (congrArg F.obj h₁) ≫ F.map m ≫ eqToHom (congrArg F.obj h₂) := by
  subst h₁; subst h₂; simp

/-- A sandwich whose crusts are identities up to defeq.  `eqToHom_refl` cannot see them — the two
spellings of each object are equal, not syntactically equal — so reach this through `exact`. -/
theorem eqToHom_conj_id {E : Type*} [Category E] {A B : E} (h₁ : A = A) (h₂ : B = B)
    (f : A ⟶ B) : eqToHom h₁ ≫ f ≫ eqToHom h₂ = f := by simp

/-- Conjugating by isomorphisms is functorial: the two facing copies of `β` cancel. -/
theorem conj_comp_conj {E : Type*} [Category E] {A B C A' B' C' : E}
    (α : A' ≅ A) (β : B' ≅ B) (γ : C' ≅ C) (x : A ⟶ B) (y : B ⟶ C) :
    (α.hom ≫ x ≫ β.inv) ≫ (β.hom ≫ y ≫ γ.inv) = α.hom ≫ (x ≫ y) ≫ γ.inv := by simp


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

/-- 1-cells of the glued polygraph: a 1-cell of `P d`, in the copy at some `x ∈ X d`. -/
inductive GlueGen : GlueV X → GlueV X → Type (max u₁ w u' w')
  | mk {d : D} (x : X.obj (op d)) {a b : (P.obj d).V} (g : (P.obj d).Gen a b) :
      GlueGen (gluePt X L d x a) (gluePt X L d x b)

/-- The copy of `P d` sitting over `x ∈ X d`. -/
def gluePre (d : D) (x : X.obj (op d)) :
    GenObj (P.obj d).Gen ⥤q GenObj (GlueGen X L) where
  obj a := ⟨gluePt X L d x a.as⟩
  map g := GlueGen.mk x g

/-- The copy at `f* x`, as a 0-cell of the copy at `x`. -/
theorem gluePre_obj_map {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) (a : GenObj (P.obj d').Gen) :
    (gluePre X L d x).obj ((P.map f).pre.obj a) = (gluePre X L d' (X.map f.op x)).obj a :=
  congrArg (fun s => (⟨s⟩ : GenObj (GlueGen X L))) (gluePt_map X L f x a)

/-- 2-cells of the glued polygraph: each copy's own, plus the overlaps.  Indexed in the `Paths`
spelling, so that `src`/`tgt` may use `≫` and `eqToHom` there. -/
inductive GlueRel : Paths (GenObj (GlueGen X L)) → Paths (GenObj (GlueGen X L)) →
    Type (max u₁ v₁ w u' w' w₂)
  | copy {d : D} (x : X.obj (op d)) {a b : GenObj (P.obj d).Gen} :
      (P.obj d).Rel a b → GlueRel ((gluePre X L d x).obj a) ((gluePre X L d x).obj b)
  | overlap {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) :
      GlueRel ((gluePre X L d' (X.map f.op x)).obj a) ((gluePre X L d' (X.map f.op x)).obj b)

/-- A copy's 2-cell keeps its source; an overlap's source is the copy at `f* x`. -/
def GlueRel.src : ∀ {s t : Paths (GenObj (GlueGen X L))}, GlueRel X L s t → (s ⟶ t)
  | _, _, .copy (d := d) x α => (gluePre X L d x).mapPath ((P.obj d).src α)
  | _, _, .overlap f x g => (gluePre X L _ (X.map f.op x)).mapPath g.toPath

/-- …and an overlap's target is the same 1-cell read in the copy at `x`. -/
def GlueRel.tgt : ∀ {s t : Paths (GenObj (GlueGen X L))}, GlueRel X L s t → (s ⟶ t)
  | _, _, .copy (d := d) x α => (gluePre X L d x).mapPath ((P.obj d).tgt α)
  | _, _, .overlap (d := d) (a := a) (b := b) f x g =>
      eqToHom (gluePre_obj_map X L f x a).symm ≫
        (gluePre X L d x).mapPath ((P.map f).pre.map g).toPath ≫
        eqToHom (gluePre_obj_map X L f x b)

/-- **The glued polygraph.** -/
def glue : Polygraph.{max u₁ w u' w', max u₁ w, max u₁ v₁ w u' w' w₂} where
  V := GlueV X
  Gen := GlueGen X L
  Rel := GlueRel X L
  src := GlueRel.src X L
  tgt := GlueRel.tgt X L

/-- The inclusion of the copy of `P d` at `x ∈ X d`. -/
def glueIncl (d : D) (x : X.obj (op d)) : Hom (P.obj d) (glue X L) where
  pre := gluePre X L d x
  two α := GlueRel.copy x α
  src_two _ := rfl
  tgt_two _ := rfl

/-- **The copy inclusions are natural in the base**: the copy at `f* x` is the copy at `x` read
through `P.map f`.  This is `GlueRel.overlap` and nothing else; `Paths.ext_functor` does the
induction over words, so only singleton paths are ever touched.

Note this is a strict **equality** of functors, not merely an isomorphism. -/
theorem glueIncl_naturality {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) :
    (P.map f).functor ⋙ (glueIncl X L d x).functor
      = (glueIncl X L d' (X.map f.op x)).functor := by
  refine Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, Hom.quot_comp_functor, Functor.assoc, Hom.quot_comp_functor,
    Hom.quot_comp_functor]
  refine Paths.ext_functor
    (funext fun a => congrArg (glue X L).quot.obj (gluePre_obj_map X L f x a)) ?_
  intro a b e
  have hF : ((P.map f).words ⋙ (glueIncl X L d x).words ⋙ (glue X L).quot).map
      (Quiver.Hom.toPath e)
      = (glue X L).quot.map ((gluePre X L d x).mapPath ((P.map f).pre.map e).toPath) := rfl
  have hG : ((glueIncl X L d' (X.map f.op x)).words ⋙ (glue X L).quot).map (Quiver.Hom.toPath e)
      = (glue X L).quot.map ((gluePre X L d' (X.map f.op x)).mapPath (Quiver.Hom.toPath e)) := rfl
  have hs : (glue X L).quot.map ((gluePre X L d' (X.map f.op x)).mapPath (Quiver.Hom.toPath e))
      = (glue X L).quot.map (eqToHom (gluePre_obj_map X L f x a).symm ≫
          (gluePre X L d x).mapPath ((P.map f).pre.map e).toPath ≫
          eqToHom (gluePre_obj_map X L f x b)) :=
    (glue X L).quot_src_tgt (GlueRel.overlap f x e)
  rw [hF, hG, hs, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  refine Eq.trans ?_ (eqToHom_conj_conj _ _ _ _ _).symm
  exact ((Category.id_comp _).symm.trans
    (congrArg (· ≫ (glue X L).quot.map ((gluePre X L d x).mapPath ((P.map f).pre.map e).toPath))
      (eqToHom_refl _ _).symm)).trans
    (congrArg (eqToHom _ ≫ ·) ((Category.comp_id _).symm.trans
      (congrArg ((glue X L).quot.map
          ((gluePre X L d x).mapPath ((P.map f).pre.map e).toPath) ≫ ·)
        (eqToHom_refl _ _).symm)))

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

/-- …so the lift of the base slice's terminal object is `c` itself. -/
theorem elementsLift_id (c : (X.Elements)ᵒᵖ) :
    (elementsLift X ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).obj
      (Over.mk (𝟙 ((CategoryOfElements.π X).leftOp.obj c))) = c :=
  Functor.congr_obj (elementsLift_post X c) (Over.mk (𝟙 c))

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

theorem glueSliceEval_obj (d : D) (x : X.obj (op d)) (u : Over d) :
    (glueSliceEval X W d x).obj (Localization.Construction.objEquiv (W.over (X := d)) u) =
      (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj ((elementsLift X d x).obj u) :=
  Functor.congr_obj (glueSliceEval_fac X W d x) u

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

/-! ## The comparison functor -/

section Compare

variable (W : MorphismProperty D)
  (p : ∀ d : D, Presents (P.obj d) ((W.over (X := d)).Localization))
  (hL : ∀ (d : D) (a : (P.obj d).V),
    (p d).at' ⟨a⟩ = Localization.Construction.objEquiv (W.over (X := d)) (L.ob d a))

/-- The object of `(∫X)[W⁻¹]` a 0-cell names.  Reducible: `Category.assoc` will not match
across a composite whose middle object is spelled two ways. -/
@[reducible] def glueAt (s : GenObj (GlueGen X L)) :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (W.inverseImage (CategoryOfElements.π X).leftOp).Q.obj (op ⟨op s.as.1, s.as.2⟩)

include hL in
theorem glueAt_gluePt (d : D) (x : X.obj (op d)) (a : (P.obj d).V) :
    (glueSliceEval X W d x).obj ((p d).at' ⟨a⟩) = glueAt X L W ⟨gluePt X L d x a⟩ := by
  rw [hL d a]
  exact glueSliceEval_obj X W d x (L.ob d a)

include hL in
/-- The arrow a 1-cell names: the copy's own arrow, pushed along the cartesian lift. -/
noncomputable def glueArrow :
    ∀ {s t : GenObj (GlueGen X L)}, (s ⟶ t) → (glueAt X L W s ⟶ glueAt X L W t)
  | ⟨_⟩, ⟨_⟩, GlueGen.mk (d := d) x g =>
      eqToHom (glueAt_gluePt X L W p hL d x _).symm ≫
        (glueSliceEval X W d x).map ((p d).arrow g) ≫ eqToHom (glueAt_gluePt X L W p hL d x _)

include hL in
/-- The cells of the glued polygraph, interpreted. -/
noncomputable def glueEval : GenObj (GlueGen X L) ⥤q
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization where
  obj := glueAt X L W
  map := glueArrow X L W p hL

include hL in
theorem glueEval_map_gluePre (d : D) (x : X.obj (op d)) {a b : GenObj (P.obj d).Gen} (e : a ⟶ b) :
    (glueEval X L W p hL).map ((gluePre X L d x).map e) =
      eqToHom (glueAt_gluePt X L W p hL d x a.as).symm ≫
        (glueSliceEval X W d x).map ((p d).arrow e) ≫
        eqToHom (glueAt_gluePt X L W p hL d x b.as) :=
  rfl

include hL in
/-- **A copy's word, evaluated**: the copy's own evaluation, pushed along the cartesian lift. -/
theorem glueEval_mapPath (d : D) (x : X.obj (op d)) {a b : GenObj (P.obj d).Gen}
    (u : Quiver.Path a b) :
    (Paths.lift (glueEval X L W p hL)).map ((gluePre X L d x).mapPath u) =
      eqToHom (glueAt_gluePt X L W p hL d x a.as).symm ≫
        (glueSliceEval X W d x).map ((p d).eval.map u) ≫
        eqToHom (glueAt_gluePt X L W p hL d x b.as) := by
  induction u with
  | nil =>
      rw [show (Paths.lift (glueEval X L W p hL)).map
            ((gluePre X L d x).mapPath (Quiver.Path.nil : Quiver.Path a a)) = 𝟙 _ from
          (Paths.lift (glueEval X L W p hL)).map_id _,
        show (p d).eval.map (Quiver.Path.nil : Quiver.Path a a) = 𝟙 _ from (p d).eval.map_id _,
        Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
      rfl
  | cons u e ih =>
      rw [Prefunctor.mapPath_cons, Paths.lift_cons, ih, glueEval_map_gluePre, (p d).eval_cons,
        Functor.map_comp]
      -- the two crusts `eqToHom_conj_comp` merges cancel here; `simp` lands on a goal that prints
      -- as `X = X` and only default transparency closes it
      exact (eqToHom_conj_comp _ _ _ _ _ _).trans (by simp; rfl)

variable (hP : ∀ {d' d : D} (f : d' ⟶ d),
  (P.map f).functor ⋙ (p d).E = (p d').E ⋙ overMapLoc W f)

include hP in
/-- **The compatibility square, read on words**: `P.map f` followed by `p d` is `p d'` followed by
postcomposition. -/
theorem glueBridge {d' d : D} (f : d' ⟶ d) :
    (P.map f).words ⋙ (P.obj d).quot ⋙ (p d).E
      = (P.obj d').quot ⋙ (p d').E ⋙ overMapLoc W f := by
  rw [← Functor.assoc, ← Hom.quot_comp_functor, Functor.assoc, hP f]

include hP in
/-- …and evaluated, rather than read on words. -/
theorem glueBridge' {d' d : D} (f : d' ⟶ d) :
    (p d').eval ⋙ overMapLoc W f = (P.map f).words ⋙ (p d).eval := by
  change ((P.obj d').quot ⋙ (p d').E) ⋙ overMapLoc W f
      = (P.map f).words ⋙ (P.obj d).quot ⋙ (p d).E
  rw [Functor.assoc, ← glueBridge W p hP f]

include hP in
/-- **The whole overlap identification, as an equality of functors.**  Stated on functors, where
there are no implicit object arguments to diverge; the morphism form is one `Functor.congr_hom`
away. -/
theorem glueSliceEval_bridge {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) :
    (p d').eval ⋙ glueSliceEval X W d' (X.map f.op x)
      = (P.map f).words ⋙ (p d).eval ⋙ glueSliceEval X W d x := by
  rw [← overMapLoc_comp_glueSliceEval X W f x, ← Functor.assoc, glueBridge' W p hP f,
    Functor.assoc]

include hL in
/-- The copy 2-cells are sound: they are `p d`'s own, pushed forward. -/
theorem glue_sound_copy (d : D) (x : X.obj (op d)) {a b : GenObj (P.obj d).Gen}
    (α : (P.obj d).Rel a b) :
    (Paths.lift (glueEval X L W p hL)).map ((gluePre X L d x).mapPath ((P.obj d).src α)) =
      (Paths.lift (glueEval X L W p hL)).map ((gluePre X L d x).mapPath ((P.obj d).tgt α)) := by
  rw [glueEval_mapPath, glueEval_mapPath, (p d).sound α]

include hL hP in
/-- **The overlap 2-cells are sound**: the copy at `f* x` is the copy at `x` read through
`P.map f`, because the cartesian lifts compose. -/
theorem glue_sound_overlap {d' d : D} (f : d' ⟶ d) (x : X.obj (op d))
    {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) :
    (Paths.lift (glueEval X L W p hL)).map ((gluePre X L d' (X.map f.op x)).mapPath g.toPath)
      = (Paths.lift (glueEval X L W p hL)).map
          (eqToHom (gluePre_obj_map X L f x a).symm ≫
            (gluePre X L d x).mapPath ((P.map f).pre.map g).toPath ≫
            eqToHom (gluePre_obj_map X L f x b)) := by
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, glueEval_mapPath,
    glueEval_mapPath]
  refine (eqToHom_conj_congr _ _
      (Functor.congr_hom (glueSliceEval_bridge X W p hP f x) (Quiver.Hom.toPath g))).trans ?_
  exact (eqToHom_conj_conj _ _ _ _ _).trans (eqToHom_conj_conj _ _ _ _ _).symm

include hL hP in
/-- **The 2-cells of the glued polygraph are sound.** -/
theorem glue_sound {s t : GenObj (GlueGen X L)} (α : (glue X L).Rel s t) :
    (Paths.lift (glueEval X L W p hL)).map ((glue X L).src α)
      = (Paths.lift (glueEval X L W p hL)).map ((glue X L).tgt α) := by
  cases α with
  | copy x hr => exact glue_sound_copy X L W p hL _ x hr
  | overlap f x g => exact glue_sound_overlap X L W p hL hP f x g

include hL hP in
/-- **The comparison functor**: a word of the glued polygraph, read in `(∫X)[W⁻¹]`. -/
noncomputable def glueDesc : (glue X L).presented ⥤
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization :=
  (glue X L).desc (glueEval X L W p hL) (glue_sound X L W p hL hP)

include hL hP in
/-- **A copy, read by the comparison functor**: the copy's own presentation, pushed along the
cartesian lift.  A strict equality, because `glueAt_gluePt` is one. -/
theorem glueIncl_desc (d : D) (x : X.obj (op d)) :
    (glueIncl X L d x).functor ⋙ glueDesc X L W p hL hP
      = (p d).E ⋙ glueSliceEval X W d x := by
  refine Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, Hom.quot_comp_functor, Functor.assoc,
    show (glue X L).quot ⋙ glueDesc X L W p hL hP = Paths.lift (glueEval X L W p hL) from
      (glue X L).quot_comp_desc _ (glue_sound X L W p hL hP), ← Functor.assoc]
  refine Functor.ext (fun a => (glueAt_gluePt X L W p hL d x a.as).symm) ?_
  intro a b u
  exact glueEval_mapPath X L W p hL d x u

/-! ## The retraction -/

section Retract

/-- For the elements projection, postcomposition and `Over.post` commute as a strict **equality**
rather than an iso: composition in `(X.Elements)ᵒᵖ` is `.val`-wise, so
`F.map (h ≫ u) = F.map h ≫ F.map u` holds definitionally. -/
theorem elementsPost_map {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Over.map u ⋙ Over.post (CategoryOfElements.π X).leftOp
      = Over.post (CategoryOfElements.π X).leftOp ⋙
        Over.map ((CategoryOfElements.π X).leftOp.map u) :=
  rfl

/-- …and composition, for the same reason. -/
theorem elementsPost_map_comp {a b c : (X.Elements)ᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) :
    (CategoryOfElements.π X).leftOp.map (u ≫ v)
      = (CategoryOfElements.π X).leftOp.map u ≫ (CategoryOfElements.π X).leftOp.map v :=
  rfl

/-- …and for the same reason the projection preserves identities strictly. -/
theorem elementsPost_map_id (c : (X.Elements)ᵒᵖ) :
    (CategoryOfElements.π X).leftOp.map (𝟙 c) = 𝟙 ((CategoryOfElements.π X).leftOp.obj c) :=
  rfl

variable (hb : ∀ d : D, Function.Bijective (p d).E.obj)

/-! ### Inverting the slice presentations strictly

`hL` makes `L.ob d` the object map of `(p d).E` (`labelsOf_ob_bijective_iff`), so asking for the
labels to be bijective is asking `(p d).E` to be an isomorphism of categories.  It then has a
strict inverse, and the comparison below is an equality at every step. -/

/-- The presentation of the slice over `d`, inverted on the nose. -/
noncomputable def pInv (d : D) :
    (W.over (X := d)).Localization ⥤ (P.obj d).presented :=
  strictInv (p d).E (hb d)

/-- The 0-cell of `P d` that names the identity — the label being surjective is what gives it. -/
noncomputable def glueBase (d : D) : (P.obj d).presented :=
  (pInv W p hb d).obj ((W.over (X := d)).Q.obj (Over.mk (𝟙 d)))

include hL in
theorem glueBase_ob (d : D) : L.ob d (glueBase W p hb d).as.as = Over.mk (𝟙 d) := by
  refine (Localization.Construction.objEquiv (W.over (X := d))).injective ?_
  rw [← hL]
  exact Functor.congr_obj (strictInv_comp (p d).E (hb d)) _

include hL in
/-- **The base 0-cell of the copy at `(d, x)` is `(d, x)` itself** — the label being injective is
what makes this the *only* 0-cell there over `(d, x)`. -/
theorem gluePt_base (d : D) (x : X.obj (op d)) :
    gluePt X L d x (glueBase W p hb d).as.as = ⟨d, x⟩ := by
  refine Eq.trans
    (congrArg (fun Y : Over d => (⟨Y.left, X.map Y.hom.op x⟩ : GlueV X))
      (glueBase_ob L W p hL hb d)) ?_
  exact congrArg (fun z => (⟨d, z⟩ : GlueV X)) (by simp; rfl)

include hL in
theorem glueIncl_base (d : D) (x : X.obj (op d)) :
    (glueIncl X L d x).functor.obj (glueBase W p hb d)
      = (glue X L).quot.obj ⟨(⟨d, x⟩ : GlueV X)⟩ :=
  congrArg (fun v => (glue X L).quot.obj ⟨v⟩) (gluePt_base X L W p hL hb d x)

/-! ### The retraction -/

/-- The copy inclusion at `c'` is the one at `c` read through `P (F u)`. -/
theorem glueIncl_elements {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor
      = (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c') c'.unop.2).functor := by
  rw [glueIncl_naturality, elements_snd_map]

include hP in
/-- **The comparison on the base slice**: `hP`, inverted.  An equality, not a mate — that is the
whole gain from bijective labels. -/
theorem glueStep {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        pInv W p hb ((CategoryOfElements.π X).leftOp.obj c) ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor
      = pInv W p hb ((CategoryOfElements.π X).leftOp.obj c') ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c') c'.unop.2).functor := by
  have hsq : overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
      pInv W p hb ((CategoryOfElements.π X).leftOp.obj c)
        = pInv W p hb ((CategoryOfElements.π X).leftOp.obj c') ⋙
          (P.map ((CategoryOfElements.π X).leftOp.map u)).functor :=
    strictInv_square (hb _) (hb _) _ _ (hP _)
  rw [← Functor.assoc, hsq, Functor.assoc, glueIncl_elements]

/-- The retraction, before localizing: down to the base slice, then `P (F c)`'s presentation
inverted, then the copy inclusion at `c`'s own element. -/
noncomputable def glueRetractPre (c : (X.Elements)ᵒᵖ) : Over c ⥤ (glue X L).presented :=
  Over.post (CategoryOfElements.π X).leftOp ⋙
    (W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q ⋙
    pInv W p hb ((CategoryOfElements.π X).leftOp.obj c) ⋙
    (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor

include hP in
/-- …and it is natural in `c` on the nose. -/
theorem glueRetractPre_map {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Over.map u ⋙ glueRetractPre X L W p hb c = glueRetractPre X L W p hb c' := by
  unfold glueRetractPre
  rw [← Functor.assoc, elementsPost_map, Functor.assoc, ← Functor.assoc (Over.map _),
    ← overMapLocFac, Functor.assoc, glueStep X L W p hP hb u]

theorem glueRetractPre_inverts (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).IsInvertedBy
      (glueRetractPre X L W p hb c) := by
  intro Y Z φ hφ
  haveI : IsIso ((W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.map
      ((Over.post (CategoryOfElements.π X).leftOp).map φ)) :=
    Localization.inverts _ (W.over (X := (CategoryOfElements.π X).leftOp.obj c)) _ hφ
  exact inferInstanceAs (IsIso
    ((pInv W p hb ((CategoryOfElements.π X).leftOp.obj c) ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor).map
      ((W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.map
        ((Over.post (CategoryOfElements.π X).leftOp).map φ))))

include hP in
/-- The retraction, as a **strict** cocone on the slices. -/
noncomputable def glueRetractCocone :
    OverCocone ((X.Elements)ᵒᵖ) ((glue X L).presented) where
  obj c := glueRetractPre X L W p hb c
  w u := glueRetractPre_map X L W p hP hb u

include hP in
theorem glueRetractCocone_inverts :
    (W.inverseImage (CategoryOfElements.π X).leftOp).IsInvertedBy
      (glueRetractCocone X L W p hP hb).desc := by
  rw [isInvertedBy_iff_over, OverCocone.ofFunctor_desc]
  exact glueRetractPre_inverts X L W p hb

include hP in
/-- **The retraction** `Ψ : (∫X)[W⁻¹] ⥤ Glue`, descended from the slices. -/
noncomputable def glueRetractDesc :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization ⥤ (glue X L).presented :=
  Localization.Construction.lift _ (glueRetractCocone_inverts X L W p hP hb)

include hP in
theorem glueRetractDesc_fac :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙ glueRetractDesc X L W p hP hb
      = (glueRetractCocone X L W p hP hb).desc :=
  Localization.Construction.fac _ _

include hP in
theorem glueRetract_forget (c : (X.Elements)ᵒᵖ) :
    Over.forget c ⋙ (glueRetractCocone X L W p hP hb).desc = glueRetractPre X L W p hb c :=
  congrArg (fun G => OverCocone.obj G c) (OverCocone.ofFunctor_desc _)

/-! ### The two identities -/

include hL hP in
/-- **Ψ then Φ, one slice at a time** — an equality, because `pInv` cancels `(p d).E`. -/
theorem glueRetractPre_desc (c : (X.Elements)ᵒᵖ) :
    glueRetractPre X L W p hb c ⋙ glueDesc X L W p hL hP
      = Over.forget c ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q := by
  unfold glueRetractPre
  simp only [Functor.assoc]
  rw [glueIncl_desc, ← Functor.assoc (pInv W p hb _),
    show pInv W p hb ((CategoryOfElements.π X).leftOp.obj c) ⋙
        (p ((CategoryOfElements.π X).leftOp.obj c)).E = 𝟭 _ from strictInv_comp _ _,
    Functor.id_comp, glueSliceEval_fac, ← Functor.assoc, elementsLift_post]

include hL hP in
/-- **The counit**: the retraction, read through the comparison, is the identity. -/
theorem glueCounit :
    glueRetractDesc X L W p hP hb ⋙ glueDesc X L W p hL hP = 𝟭 _ :=
  Localization.Construction.uniq _ _ (by
    rw [← Functor.assoc, glueRetractDesc_fac, Functor.comp_id]
    refine OverCocone.functor_ext fun c => ?_
    rw [← Functor.assoc, glueRetract_forget, glueRetractPre_desc])

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

include hP in
/-- **A slice, read through the retraction, is the copy inclusion** — the mirror of
`glueIncl_desc`, and what makes the unit computable on generators. -/
theorem glueSliceEval_retract (c : (X.Elements)ᵒᵖ) :
    glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2 ⋙
        glueRetractDesc X L W p hP hb
      = pInv W p hb ((CategoryOfElements.π X).leftOp.obj c) ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor := by
  refine Localization.Construction.uniq _ _ ?_
  rw [← Functor.assoc, glueSliceEval_fac, Functor.assoc, glueRetractDesc_fac,
    ← elementsLiftOver_forget X c, Functor.assoc, glueRetract_forget]
  unfold glueRetractPre
  simp only [← Functor.assoc]
  rw [elementsLiftOver_post, Functor.id_comp]

include hL hP in
theorem glueRetract_glueAt (s : GenObj (GlueGen X L)) :
    (glueRetractDesc X L W p hP hb).obj (glueAt X L W s) = (glue X L).quot.obj s :=
  (Functor.congr_obj (glueRetractDesc_fac X L W p hP hb) _).trans
    (glueIncl_base X L W p hL hb _ _)

include hL hP in
/-- **The unit**: the comparison, read through the retraction, is the identity.  Checked on
generators, where `pInv` cancels `(p d).E` and the copy inclusion is `glueIncl_desc`. -/
theorem glueUnit :
    glueDesc X L W p hL hP ⋙ glueRetractDesc X L W p hP hb = 𝟭 _ := by
  refine Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, show (glue X L).quot ⋙ glueDesc X L W p hL hP
      = Paths.lift (glueEval X L W p hL) from
    (glue X L).quot_comp_desc _ (glue_sound X L W p hL hP), Functor.comp_id]
  refine Paths.ext_functor ?_ ?_
  · exact funext fun s => glueRetract_glueAt X L W p hL hP hb s
  · rintro ⟨a⟩ ⟨b⟩ (@⟨d, x, a', b', g⟩)
    refine Eq.trans (congrArg (glueRetractDesc X L W p hP hb).map
      ((Paths.lift_toPath _ _).trans (glueEval_map_gluePre X L W p hL d x g))) ?_
    -- no rewrite reaches under a `Quotient` lift's `.map`, so the chain runs through `exact`
    have m1 := Functor.congr_hom
      (glueSliceEval_retract X L W p hP hb (op (⟨op d, x⟩ : X.Elements))) ((p d).arrow g)
    have m2 := Functor.congr_hom (comp_strictInv (p d).E (hb d))
      ((P.obj d).quot.map (Quiver.Hom.toPath g))
    have m3 := (Functor.congr_hom (Hom.quot_comp_functor (glueIncl X L d x))
      (Quiver.Hom.toPath g)).trans (eqToHom_conj_congr _ _ (congrArg (glue X L).quot.map
        (Paths.lift_comp_of_map (gluePre X L d x) (Quiver.Hom.toPath g))))
    have inner := (congrArg (glueIncl X L d x).functor.map m2).trans
      ((eqToHom_conj_map (glueIncl X L d x).functor _ _ _).trans
        ((eqToHom_conj_congr _ _ m3).trans (eqToHom_conj_conj _ _ _ _ _)))
    have mid := m1.trans ((eqToHom_conj_congr _ _ inner).trans (eqToHom_conj_conj _ _ _ _ _))
    exact (eqToHom_conj_map (glueRetractDesc X L W p hP hb) _ _ _).trans
      ((eqToHom_conj_congr _ _ mid).trans (eqToHom_conj_conj _ _ _ _ _))

include hL hP hb in
/-- **`glue X L` presents `(∫X)[W⁻¹]`.**  `Equivalence.mk` adjointifies, so the two identities
are all that is asked. -/
noncomputable def presentsGlue :
    Presents (glue X L) ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  ⟨glueDesc X L W p hL hP,
    (CategoryTheory.Equivalence.mk (glueDesc X L W p hL hP) (glueRetractDesc X L W p hP hb)
      (eqToIso (glueUnit X L W p hL hP hb).symm)
      (eqToIso (glueCounit X L W p hL hP hb))).isEquivalence_functor⟩

include hP hb in
/-- …read with the labels the family itself supplies. -/
noncomputable def presentsGlueOf :
    Presents (glue X (labelsOf W p hP))
      ((W.inverseImage (CategoryOfElements.π X).leftOp).Localization) :=
  presentsGlue X (labelsOf W p hP) W p (labelsOf_ob W p hP) hP hb

end Retract

end Compare

end Polygraph

end CategoryTheory
