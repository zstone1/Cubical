import CubeChains.Machinery.Presentation.Basic
import CubeChains.Machinery.Localization.SliceFamily
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Machinery/Presentation/Glue — one copy of `P d` for each element over `d`

`glue X L`: the objects of `∫X` as 0-cells, a copy of `P d` over each `x ∈ X d`, an overlap 2-cell
per `f : d' ⟶ d`, and `L : SliceLabels P` naming the arrow of `Over d` a 0-cell stands for.

**Write the functor down; do not invert an abstract equivalence.**  Strictness is what makes this
file typecheck: `SliceLabels.map_ob` is an equality only because `overMapLoc` is a
`Construction.lift` (an iso there, and `GlueRel.overlap` would not typecheck), `elementsLift` and
`glueRetractPre` are explicit lifts because `Localization.uniq` is opaque on objects, and
`Over.mapPost` is an equality here — leaving `glueRetractStep` the only non-strict step.
-/

universe w w' v₁ u₁ u'

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

/-- A commuting square of functors, conjugated by two equivalences.  This is how a *strict*
compatibility square becomes a comparison for the equivalences' inverses — only an isomorphism,
because an inverse is a choice. -/
noncomputable def conjIso {A B A' B' : Type*} [Category A] [Category B] [Category A']
    [Category B'] (e₁ : A ≌ B) (e₂ : A' ≌ B') (G : A ⥤ A') (H : B ⥤ B')
    (h : G ⋙ e₂.functor = e₁.functor ⋙ H) :
    H ⋙ e₂.inverse ≅ e₁.inverse ⋙ G :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight e₁.counitIso.symm (H ⋙ e₂.inverse) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e₁.inverse
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (eqToIso h.symm) e₂.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft G e₂.unitIso.symm ≪≫ Functor.rightUnitor G)

/-- **`conjIso` is a mate.**  Its inverse is `mateEquiv` of the square along the two equivalences'
adjunctions, so `Mathlib.CategoryTheory.Adjunction.Mates` supplies its coherences —
`mateEquiv_vcomp` for composition — instead of triangle-identity manipulation by hand. -/
theorem conjIso_inv_eq_mate {A B A' B' : Type*} [Category A] [Category B] [Category A']
    [Category B'] (e₁ : A ≌ B) (e₂ : A' ≌ B') (G : A ⥤ A') (H : B ⥤ B')
    (h : G ⋙ e₂.functor = e₁.functor ⋙ H) :
    (conjIso e₁ e₂ G H h).inv =
      (mateEquiv e₁.toAdjunction e₂.toAdjunction
        (TwoSquare.mk _ _ _ _ (eqToHom h))).natTrans := by
  ext a
  simp [conjIso, mateEquiv, Equivalence.toAdjunction]

/-- **The mate/counit identity**: `conjIso` pushed back through `e₂.functor` and composed with
`e₁`'s counit is `e₂`'s counit.  This is what makes the comparison of `Ψ ⋙ Φ` with `𝟭` natural, and
it is evidence that `conjIso` is the right abstraction: it reduces to `e₁`'s own triangle identity
read through `H`, with nothing left over. -/
theorem conjIso_hom_comp_counit {A B A' B' : Type*} [Category A] [Category B] [Category A']
    [Category B'] (e₁ : A ≌ B) (e₂ : A' ≌ B') (G : A ⥤ A') (H : B ⥤ B')
    (h : G ⋙ e₂.functor = e₁.functor ⋙ H) (Z : B) :
    e₂.functor.map ((conjIso e₁ e₂ G H h).hom.app Z) ≫
        eqToHom (Functor.congr_obj h (e₁.inverse.obj Z)) ≫ H.map (e₁.counitIso.hom.app Z)
      = e₂.counitIso.hom.app (H.obj Z) := by
  simp [conjIso]
  simp [← Functor.map_comp]

section ConjComp

variable {A B A' B' A'' B'' : Type*} [Category A] [Category B] [Category A'] [Category B']
  [Category A''] [Category B''] (e₁ : A ≌ B) (e₂ : A' ≌ B') (e₃ : A'' ≌ B'')
  (G₁ : A ⥤ A') (G₂ : A' ⥤ A'') (H₁ : B ⥤ B') (H₂ : B' ⥤ B'')
  (h₁ : G₁ ⋙ e₂.functor = e₁.functor ⋙ H₁) (h₂ : G₂ ⋙ e₃.functor = e₂.functor ⋙ H₂)
  (h : (G₁ ⋙ G₂) ⋙ e₃.functor = e₁.functor ⋙ (H₁ ⋙ H₂))

include h₁ h₂ in
/-- Squares whose 2-cell is an `eqToHom` compose horizontally to the `eqToHom` square. -/
theorem twoSquare_eqToHom_hComp :
    TwoSquare.hComp (TwoSquare.mk _ _ _ _ (eqToHom h₁) : TwoSquare G₁ e₁.functor e₂.functor H₁)
        (TwoSquare.mk _ _ _ _ (eqToHom h₂) : TwoSquare G₂ e₂.functor e₃.functor H₂)
      = TwoSquare.mk _ _ _ _ (eqToHom h) := by
  ext a
  simp [eqToHom_map]

include h₁ h₂ in
/-- **`conjIso` respects composition**, by `mateEquiv_vcomp`.  Both outer composites are strict, so
the horizontal composite of the two squares is the square of the composite. -/
theorem conjIso_comp :
    (conjIso e₁ e₃ (G₁ ⋙ G₂) (H₁ ⋙ H₂) h).inv =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (conjIso e₁ e₂ G₁ H₁ h₁).inv G₂ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft H₁ (conjIso e₂ e₃ G₂ H₂ h₂).inv ≫
        (Functor.associator _ _ _).inv := by
  rw [conjIso_inv_eq_mate, conjIso_inv_eq_mate, conjIso_inv_eq_mate,
    ← twoSquare_eqToHom_hComp e₁ e₂ e₃ G₁ G₂ H₁ H₂ h₁ h₂ h, mateEquiv_vcomp]
  rfl

include h₁ h₂ in
/-- `conjIso_comp`, with the two outer functors given only up to equality. -/
theorem conjIso_comp_congr {G : A ⥤ A''} {H : B ⥤ B''} (hG : G = G₁ ⋙ G₂) (hH : H = H₁ ⋙ H₂)
    (h' : G ⋙ e₃.functor = e₁.functor ⋙ H) :
    (conjIso e₁ e₃ G H h').inv =
      eqToHom (by rw [hG]) ≫
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (conjIso e₁ e₂ G₁ H₁ h₁).inv G₂ ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft H₁ (conjIso e₂ e₃ G₂ H₂ h₂).inv ≫
          (Functor.associator _ _ _).inv) ≫ eqToHom (by rw [hH]) := by
  subst hG; subst hH
  simpa using conjIso_comp e₁ e₂ e₃ G₁ G₂ H₁ H₂ h₁ h₂ h'

/-- Whiskering an `eqToHom` of functors is an `eqToHom`. -/
theorem whiskerRight_eqToHom {A B E : Type*} [Category A] [Category B] [Category E]
    {F G : A ⥤ B} (h : F = G) (H : B ⥤ E) :
    Functor.whiskerRight (eqToHom h) H = eqToHom (congrArg (· ⋙ H) h) := by
  subst h; ext; simp

theorem whiskerLeft_eqToHom {A B E : Type*} [Category A] [Category B] [Category E]
    (F : A ⥤ B) {G H : B ⥤ E} (h : G = H) :
    Functor.whiskerLeft F (eqToHom h) = eqToHom (congrArg (F ⋙ ·) h) := by
  subst h; ext; simp

/-- `conjIso` transported along equalities of its two outer functors. -/
theorem conjIso_congr {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (e₁ : A ≌ B) (e₂ : A' ≌ B') {G G' : A ⥤ A'} {H H' : B ⥤ B'} (hG : G = G') (hH : H = H')
    (h : G ⋙ e₂.functor = e₁.functor ⋙ H) (h' : G' ⋙ e₂.functor = e₁.functor ⋙ H') :
    (conjIso e₁ e₂ G H h).inv =
      eqToHom (by rw [hG]) ≫ (conjIso e₁ e₂ G' H' h').inv ≫ eqToHom (by rw [hH]) := by
  subst hG; subst hH; simp

/-- **`conjIso` at the identity square is the identity**, up to unitors. -/
theorem conjIso_id {A B : Type*} [Category A] [Category B] (e : A ≌ B)
    (h : 𝟭 A ⋙ e.functor = e.functor ⋙ 𝟭 B) :
    (conjIso e e (𝟭 A) (𝟭 B) h).inv = 𝟙 e.inverse := by
  ext a
  simp [conjIso]

/-- `conjIso` at a square whose outer functors are *equal to* the identity.  Stated as a single
`eqToHom` so that no `𝟙` is left buried inside a whiskering, where `Category.id_comp` cannot
match. -/
theorem conjIso_id_congr {A B : Type*} [Category A] [Category B] (e : A ≌ B) {G : A ⥤ A}
    {H : B ⥤ B} (hG : G = 𝟭 A) (hH : H = 𝟭 B) (h : G ⋙ e.functor = e.functor ⋙ H) :
    (conjIso e e G H h).inv = eqToHom (by rw [hG, hH, Functor.comp_id, Functor.id_comp]) := by
  subst hG; subst hH; simpa using conjIso_id e h

end ConjComp

namespace Polygraph

variable {D : Type u₁} [Category.{v₁} D] (X : Dᵒᵖ ⥤ Type w) (P : D ⥤ Polygraph.{w', u'})

/-- The 0-cells of `P d` name objects of `Over d`, and `P.map f` acts on them by postcomposition. -/
structure SliceLabels where
  /-- the arrow into `d` that a 0-cell names -/
  ob (d : D) : (P.obj d).V → Over d
  /-- `P.map f` postcomposes with `f` -/
  map_ob {d' d : D} (f : d' ⟶ d) (a : GenObj (P.obj d').Gen) :
    ob d ((P.map f).cells.obj a).as = (Over.map f).obj (ob d' a.as)

variable {P} (L : SliceLabels P)

/-- The 0-cells of the glued polygraph: the objects of `∫X`. -/
abbrev GlueV : Type (max u₁ w) := Σ d : D, X.obj (op d)

/-- The object of `∫X` that a 0-cell of the copy at `x ∈ X d` names. -/
def gluePt (d : D) (x : X.obj (op d)) (a : (P.obj d).V) : GlueV X :=
  ⟨(L.ob d a).left, X.map ((L.ob d a).hom).op x⟩

/-- The overlap identification on 0-cells: the copy at `f* x` sits inside the copy at `x`. -/
theorem gluePt_map {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) (a : GenObj (P.obj d').Gen) :
    gluePt X L d x ((P.map f).cells.obj a).as = gluePt X L d' (X.map f.op x) a.as := by
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
    (gluePre X L d x).obj ((P.map f).cells.obj a) = (gluePre X L d' (X.map f.op x)).obj a :=
  congrArg (fun s => (⟨s⟩ : GenObj (GlueGen X L))) (gluePt_map X L f x a)

/-- 2-cells of the glued polygraph: each copy's own, plus the overlaps. -/
inductive GlueRel : ∀ {s t : Paths (GenObj (GlueGen X L))}, (s ⟶ t) → (s ⟶ t) → Prop
  | copy {d : D} (x : X.obj (op d)) {a b : GenObj (P.obj d).Gen} {u v : Quiver.Path a b} :
      (P.obj d).rel u v →
      GlueRel ((gluePre X L d x).mapPath u) ((gluePre X L d x).mapPath v)
  | overlap {d' d : D} (f : d' ⟶ d) (x : X.obj (op d)) {a b : GenObj (P.obj d').Gen}
      (g : a ⟶ b) :
      GlueRel ((gluePre X L d' (X.map f.op x)).mapPath g.toPath)
        (eqToHom (gluePre_obj_map X L f x a).symm ≫
          (gluePre X L d x).mapPath ((P.map f).cells.map g) ≫
          eqToHom (gluePre_obj_map X L f x b))

/-- **The glued polygraph.** -/
def glue : Polygraph.{max u₁ w u' w', max u₁ w} where
  V := GlueV X
  Gen := GlueGen X L
  rel := fun _ _ => GlueRel X L

/-- A copy's 2-cells hold in the glued polygraph. -/
theorem glueRel_copy_sound (d : D) (x : X.obj (op d)) {a b : GenObj (P.obj d).Gen}
    {u v : Quiver.Path a b} (h : (P.obj d).rel u v) :
    (glue X L).quot.map ((gluePre X L d x).mapPath u)
      = (glue X L).quot.map ((gluePre X L d x).mapPath v) :=
  Quotient.sound _ (GlueRel.copy x h)

/-- The inclusion of the copy of `P d` at `x ∈ X d`. -/
def glueIncl (d : D) (x : X.obj (op d)) : Hom (P.obj d) (glue X L) :=
  Hom.ofPre (gluePre X L d x) (glueRel_copy_sound X L d x)

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
      = (glue X L).quot.map ((gluePre X L d x).mapPath ((P.map f).cells.map e)) := by
    change (glue X L).quot.map
      ((glueIncl X L d x).words.map ((P.map f).words.map (Quiver.Hom.toPath e))) = _
    rw [show (P.map f).words.map (Quiver.Hom.toPath e) = (P.map f).cells.map e from
      Paths.lift_toPath _ e]
    exact congrArg (glue X L).quot.map (Paths.lift_comp_of_map (gluePre X L d x) _)
  have hG : ((glueIncl X L d' (X.map f.op x)).words ⋙ (glue X L).quot).map (Quiver.Hom.toPath e)
      = (glue X L).quot.map ((gluePre X L d' (X.map f.op x)).mapPath (Quiver.Hom.toPath e)) :=
    congrArg (glue X L).quot.map (Paths.lift_comp_of_map (gluePre X L d' _) _)
  have hs : (glue X L).quot.map ((gluePre X L d' (X.map f.op x)).mapPath (Quiver.Hom.toPath e))
      = (glue X L).quot.map (eqToHom (gluePre_obj_map X L f x a).symm ≫
          (gluePre X L d x).mapPath ((P.map f).cells.map e) ≫
          eqToHom (gluePre_obj_map X L f x b)) :=
    Quotient.sound (glue X L).rel (GlueRel.overlap f x e)
  rw [hF, hG, hs, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  refine Eq.trans ?_ (eqToHom_conj_conj _ _ _ _ _).symm
  exact ((Category.id_comp _).symm.trans
    (congrArg (· ≫ (glue X L).quot.map ((gluePre X L d x).mapPath ((P.map f).cells.map e)))
      (eqToHom_refl _ _).symm)).trans
    (congrArg (eqToHom _ ≫ ·) ((Category.comp_id _).symm.trans
      (congrArg ((glue X L).quot.map ((gluePre X L d x).mapPath ((P.map f).cells.map e)) ≫ ·)
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
    {u v : Quiver.Path a b} (h : (P.obj d).rel u v) :
    (Paths.lift (glueEval X L W p hL)).map ((gluePre X L d x).mapPath u) =
      (Paths.lift (glueEval X L W p hL)).map ((gluePre X L d x).mapPath v) := by
  rw [glueEval_mapPath, glueEval_mapPath, (p d).sound h]

include hL hP in
/-- **The overlap 2-cells are sound**: the copy at `f* x` is the copy at `x` read through
`P.map f`, because the cartesian lifts compose. -/
theorem glue_sound_overlap {d' d : D} (f : d' ⟶ d) (x : X.obj (op d))
    {a b : GenObj (P.obj d').Gen} (g : a ⟶ b) :
    (Paths.lift (glueEval X L W p hL)).map ((gluePre X L d' (X.map f.op x)).mapPath g.toPath)
      = (Paths.lift (glueEval X L W p hL)).map
          (eqToHom (gluePre_obj_map X L f x a).symm ≫
            (gluePre X L d x).mapPath ((P.map f).cells.map g) ≫
            eqToHom (gluePre_obj_map X L f x b)) := by
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, glueEval_mapPath,
    glueEval_mapPath]
  refine (eqToHom_conj_congr _ _
      (Functor.congr_hom (glueSliceEval_bridge X W p hP f x) (Quiver.Hom.toPath g))).trans ?_
  refine (eqToHom_conj_conj _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (eqToHom_conj_conj _ _ _ _ _).symm
  exact eqToHom_conj_congr _ _
    (congrArg (fun z => (glueSliceEval X W d x).map ((p d).eval.map z))
      (Paths.lift_toPath ((P.map f).cells) g))

include hL hP in
/-- **The 2-cells of the glued polygraph are sound.** -/
theorem glue_sound {s t : GenObj (GlueGen X L)} {u v : Quiver.Path s t} (h : GlueRel X L u v) :
    (Paths.lift (glueEval X L W p hL)).map u = (Paths.lift (glueEval X L W p hL)).map v := by
  cases h with
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
      Quotient.lift_spec _ _ fun _ _ _ _ h => glue_sound X L W p hL hP h, ← Functor.assoc]
  refine Functor.ext (fun a => (glueAt_gluePt X L W p hL d x a.as).symm) ?_
  intro a b u
  change (Paths.lift (glueEval X L W p hL)).map ((glueIncl X L d x).words.map u) = _
  rw [show (glueIncl X L d x).words.map u = (gluePre X L d x).mapPath u from
      Paths.lift_comp_of_map _ u]
  exact glueEval_mapPath X L W p hL d x u

include hL hP in
/-- **The copy at `f* x`, read by the comparison functor**: `glueIncl_desc` and
`glueIncl_elements` in one step.

One step, not two: under `glueDesc.map` no rewrite matches at all — not `Functor.map_comp`, not a
lemma shaped exactly to the term, not even with the category and the functor made concrete.  Only
`exact`-level unification reaches it, so the caller should never meet the composite. -/
theorem glueIncl_desc_elements {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor ⋙
        glueDesc X L W p hL hP
      = (p ((CategoryOfElements.π X).leftOp.obj c')).E ⋙
        glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c') c'.unop.2 := by
  rw [glueIncl_desc, ← Functor.assoc, hP, Functor.assoc, overMapLoc_comp_glueSliceEval,
    elements_snd_map]

/-! ## The retraction -/

section Retract

/-- For the elements projection, `Over.mapPost` is a strict **equality**: composition in
`(X.Elements)ᵒᵖ` is `.val`-wise, so `F.map (h ≫ u) = F.map h ≫ F.map u` holds definitionally. -/
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

/-- The retraction, before localizing: down to the base slice, then `P (F c)`'s presentation
inverted, then the copy inclusion at `c`'s own element.

Built from `Over.post F` rather than by inverting `sliceLocEquiv`.  The comparison of
`Machinery/Slice` is a `Localization.uniq` and opaque; this is the same lesson as `elementsLift` —
write the functor down instead of inverting an abstract equivalence — and it means the retraction
needs no coherence for `sliceLocEquivNatIso` at all. -/
noncomputable def glueRetractPre (c : (X.Elements)ᵒᵖ) : Over c ⥤ (glue X L).presented :=
  Over.post (CategoryOfElements.π X).leftOp ⋙
    (W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q ⋙
    (p ((CategoryOfElements.π X).leftOp.obj c)).equiv.inverse ⋙
    (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor

theorem glueRetractPre_inverts (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).IsInvertedBy
      (glueRetractPre X L W p c) := by
  intro Y Z φ hφ
  haveI : IsIso ((W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.map
      ((Over.post (CategoryOfElements.π X).leftOp).map φ)) :=
    Localization.inverts _ (W.over (X := (CategoryOfElements.π X).leftOp.obj c)) _ hφ
  exact inferInstanceAs (IsIso
    (((p ((CategoryOfElements.π X).leftOp.obj c)).equiv.inverse ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor).map
      ((W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.map
        ((Over.post (CategoryOfElements.π X).leftOp).map φ))))

include hL hP in
/-- **Ψ then Φ, one slice at a time.**  Both ends are strict — `glueIncl_desc` at the top and
`elementsLift_post` at the bottom — so the counit of `p c`'s presentation is the whole comparison,
and the target is exactly the `overCoconeLocEquiv` leg of `𝟭`. -/
noncomputable def glueRetractPreDesc (c : (X.Elements)ᵒᵖ) :
    glueRetractPre X L W p c ⋙ glueDesc X L W p hL hP
      ≅ Over.forget c ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q :=
  eqToIso (congrArg (fun Z => Over.post (CategoryOfElements.π X).leftOp ⋙
      (W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q ⋙
      (p ((CategoryOfElements.π X).leftOp.obj c)).equiv.inverse ⋙ Z)
    (glueIncl_desc X L W p hL hP ((CategoryOfElements.π X).leftOp.obj c) c.unop.2)) ≪≫
  Functor.isoWhiskerLeft (Over.post (CategoryOfElements.π X).leftOp)
    (Functor.isoWhiskerLeft (W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q
      (Functor.isoWhiskerRight (p ((CategoryOfElements.π X).leftOp.obj c)).equiv.counitIso
        (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2))) ≪≫
  eqToIso (by rw [Functor.id_comp, glueSliceEval_fac, ← Functor.assoc, elementsLift_post])

/-- The retraction's component at `c`. -/
noncomputable def glueRetract (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Localization ⥤
      (glue X L).presented :=
  Localization.Construction.lift _ (glueRetractPre_inverts X L W p c)

/-- The copy inclusion at `c'` is the one at `c` read through `P (F u)`. -/
theorem glueIncl_elements {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor
      = (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c') c'.unop.2).functor := by
  rw [glueIncl_naturality, elements_snd_map]

include hP in
/-- The comparison on the base slice: `hP` conjugated, then the copy inclusions.  This is the whole
non-strict content of the retraction's naturality. -/
noncomputable def glueRetractStep {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        (p ((CategoryOfElements.π X).leftOp.obj c)).equiv.inverse ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor
      ≅ (p ((CategoryOfElements.π X).leftOp.obj c')).equiv.inverse ⋙
        (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c') c'.unop.2).functor :=
  Functor.isoWhiskerRight
      (conjIso (p ((CategoryOfElements.π X).leftOp.obj c')).equiv
        (p ((CategoryOfElements.π X).leftOp.obj c)).equiv
        (P.map ((CategoryOfElements.π X).leftOp.map u)).functor
        (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)) (hP _))
      (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor ≪≫
    eqToIso (congrArg (fun Z => (p ((CategoryOfElements.π X).leftOp.obj c')).equiv.inverse ⋙ Z)
      (glueIncl_elements X L u))

include hP in
/-- The comparison at the identity is the canonical identification. -/
theorem glueRetractStep_id (c : (X.Elements)ᵒᵖ) :
    glueRetractStep X L W p hP (𝟙 c) = eqToIso (by
      rw [elementsPost_map_id, overMapLoc_id, Functor.id_comp]) := by
  unfold glueRetractStep
  refine Iso.ext ?_
  rw [← Iso.inv_eq_inv]
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, eqToIso.inv]
  rw [conjIso_id_congr _
      (show (P.map ((CategoryOfElements.π X).leftOp.map (𝟙 c))).functor = 𝟭 _ by
        rw [elementsPost_map_id, P.map_id, Polygraph.functor_id])
      (show overMapLoc W ((CategoryOfElements.π X).leftOp.map (𝟙 c)) = 𝟭 _ by
        rw [elementsPost_map_id, overMapLoc_id]) _,
    whiskerRight_eqToHom]
  exact eqToHom_trans _ _

include hP in
/-- The comparison respects composition.  Unlike the identity layer this is genuinely a
five-factor identity: `conjIso_comp` carries associators, so the proof descends to components,
where the associators are identities and `glueIncl_elements` is the only real content. -/
theorem glueRetractStep_comp {a b c : (X.Elements)ᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) :
    glueRetractStep X L W p hP (u ≫ v) =
      eqToIso (by rw [elementsPost_map_comp, overMapLoc_comp]; rfl) ≪≫
        Functor.isoWhiskerLeft (overMapLoc W ((CategoryOfElements.π X).leftOp.map u))
          (glueRetractStep X L W p hP v) ≪≫
        glueRetractStep X L W p hP u := by
  unfold glueRetractStep
  refine Iso.ext ?_
  rw [← Iso.inv_eq_inv]
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, eqToIso.inv]
  rw [conjIso_comp_congr (p ((CategoryOfElements.π X).leftOp.obj a)).equiv
      (p ((CategoryOfElements.π X).leftOp.obj b)).equiv
      (p ((CategoryOfElements.π X).leftOp.obj c)).equiv
      (P.map ((CategoryOfElements.π X).leftOp.map u)).functor
      (P.map ((CategoryOfElements.π X).leftOp.map v)).functor
      (overMapLoc W ((CategoryOfElements.π X).leftOp.map u))
      (overMapLoc W ((CategoryOfElements.π X).leftOp.map v))
      (hP _) (hP _)
      (show (P.map ((CategoryOfElements.π X).leftOp.map (u ≫ v))).functor = _ by
        rw [elementsPost_map_comp, P.map_comp, Polygraph.functor_comp])
      (show overMapLoc W ((CategoryOfElements.π X).leftOp.map (u ≫ v)) = _ by
        rw [elementsPost_map_comp, overMapLoc_comp])]
  ext Z
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, eqToHom_app, Functor.map_comp,
    eqToHom_map, Category.assoc, Category.id_comp, Functor.comp_obj]
  have key := fun (x y : (P.obj ((CategoryOfElements.π X).leftOp.obj b)).presented) (g : x ⟶ y) =>
    Functor.congr_hom (glueIncl_elements X L v) g
  simp only [Functor.comp_map] at key
  rw [key]
  simp

/-- Postcomposition, pushed through the retraction: everything outside `glueRetractStep` is
strict. -/
theorem glueRetractPre_map {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Over.map u ⋙ glueRetractPre X L W p c
      = Over.post (CategoryOfElements.π X).leftOp ⋙
        (W.over (X := (CategoryOfElements.π X).leftOp.obj c')).Q ⋙
        (overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
          (p ((CategoryOfElements.π X).leftOp.obj c)).equiv.inverse ⋙
          (glueIncl X L ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).functor) := by
  unfold glueRetractPre
  rw [← Functor.assoc, elementsPost_map, Functor.assoc, ← Functor.assoc (Over.map _),
    ← overMapLocFac, Functor.assoc]

include hP in
/-- The retraction's naturality, before localizing. -/
noncomputable def glueRetractPreIso {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Over.map u ⋙ glueRetractPre X L W p c ≅ glueRetractPre X L W p c' :=
  eqToIso (glueRetractPre_map X L W p u) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (glueRetractStep X L W p hP u))

include hP in
/-- …and so is the retraction's naturality. -/
theorem glueRetractPreIso_id (c : (X.Elements)ᵒᵖ) :
    glueRetractPreIso X L W p hP (𝟙 c) = eqToIso (by
      rw [Over.mapId_eq, Functor.id_comp]) := by
  unfold glueRetractPreIso
  refine Iso.ext ?_
  rw [← Iso.inv_eq_inv]
  simp only [Iso.trans_inv, eqToIso.inv, Functor.isoWhiskerLeft_inv]
  rw [glueRetractStep_id, eqToIso.inv, whiskerLeft_eqToHom, whiskerLeft_eqToHom]
  exact eqToHom_trans _ _

include hP in
/-- The retraction's naturality respects composition. -/
theorem glueRetractPreIso_comp {a b c : (X.Elements)ᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) :
    glueRetractPreIso X L W p hP (u ≫ v) =
      eqToIso (by rw [Over.mapComp_eq, Functor.assoc]) ≪≫
        Functor.isoWhiskerLeft (Over.map u) (glueRetractPreIso X L W p hP v) ≪≫
        glueRetractPreIso X L W p hP u := by
  unfold glueRetractPreIso
  refine Iso.ext ?_
  rw [← Iso.inv_eq_inv, glueRetractStep_comp]
  ext Z
  simp only [Iso.trans_inv, eqToIso.inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, eqToHom_app, Functor.comp_obj, Category.assoc]
  -- `elementsPost_map` is `rfl`, so this is the same statement in the goal's spelling
  have ho : ∀ Y : Over a,
      (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)).obj
          ((W.over (X := (CategoryOfElements.π X).leftOp.obj a)).Q.obj
            ((Over.post (CategoryOfElements.π X).leftOp).obj Y))
        = (W.over (X := (CategoryOfElements.π X).leftOp.obj b)).Q.obj
            ((Over.post (CategoryOfElements.π X).leftOp).obj ((Over.map u).obj Y)) :=
    fun Y => Functor.congr_obj (overMapLocFac W ((CategoryOfElements.π X).leftOp.map u)) _
  rw [natTrans_app_congr (glueRetractStep X L W p hP v).inv (ho Z)]
  -- both sides are now the same composite; only the bracketing of the trailing `eqToHom`s
  -- differs, and `Category.assoc` will not fire on it (see `eqToHom_conj_comp`)
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  refine (Category.assoc _ _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  simp

include hL hP in
/-- **The leg comparison is natural in `c`**, and the mate identity is its whole content: every
other step is strict, so what is left over is `eqToHom` bookkeeping. -/
theorem glueRetractPreDesc_naturality {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Functor.whiskerRight (glueRetractPreIso X L W p hP u).hom (glueDesc X L W p hL hP) ≫
        (glueRetractPreDesc X L W p hL hP c').hom
      = Functor.whiskerLeft (Over.map u) (glueRetractPreDesc X L W p hL hP c).hom := by
  ext Y
  simp only [glueRetractPreIso, glueRetractPreDesc, glueRetractStep, Iso.trans_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, eqToIso.hom, eqToHom_app,
    Functor.comp_obj]
  -- no rewrite reaches under `glueDesc.map`, so the sandwich is split by hand
  have hconj : ∀ {a b b' e : (glue X L).presented} (h₁ : a = b) (g : b ⟶ b') (h₂ : b' = e),
      (glueDesc X L W p hL hP).map (eqToHom h₁ ≫ g ≫ eqToHom h₂)
        = eqToHom (congrArg (glueDesc X L W p hL hP).obj h₁) ≫
          (glueDesc X L W p hL hP).map g ≫
          eqToHom (congrArg (glueDesc X L W p hL hP).obj h₂) := by
    intro a b b' e h₁ g h₂
    subst h₁; subst h₂; simp
  have key := fun (x y : (P.obj ((CategoryOfElements.π X).leftOp.obj c)).presented) (g : x ⟶ y) =>
    Functor.congr_hom (glueIncl_desc X L W p hL hP
      ((CategoryOfElements.π X).leftOp.obj c) c.unop.2) g
  simp only [Functor.comp_map] at key
  -- `elements_snd_map` is what puts the two `glueSliceEval`s at the same element
  have hgse : glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c') c'.unop.2
      = overMapLoc W ((CategoryOfElements.π X).leftOp.map u) ⋙
        glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2 := by
    rw [overMapLoc_comp_glueSliceEval, elements_snd_map]
  -- `conjIso_hom_comp_counit` reads through `(p _).equiv.functor`; `(p _).E` is the same functor
  -- under a spelling `rw` cannot see, so the type is written out and accepted by defeq
  have hmate :
      (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).map
          ((p ((CategoryOfElements.π X).leftOp.obj c)).E.map
            ((conjIso (p ((CategoryOfElements.π X).leftOp.obj c')).equiv
                    (p ((CategoryOfElements.π X).leftOp.obj c)).equiv
                    (P.map ((CategoryOfElements.π X).leftOp.map u)).functor
                    (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)) (hP _)).hom.app
              ((W.over (X := (CategoryOfElements.π X).leftOp.obj c')).Q.obj
                ((Over.post (CategoryOfElements.π X).leftOp).obj Y)))) ≫
        eqToHom (congrArg (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).obj
          (Functor.congr_obj (hP ((CategoryOfElements.π X).leftOp.map u))
            ((p ((CategoryOfElements.π X).leftOp.obj c')).equiv.inverse.obj
              ((W.over (X := (CategoryOfElements.π X).leftOp.obj c')).Q.obj
                ((Over.post (CategoryOfElements.π X).leftOp).obj Y))))) ≫
        (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).map
          ((overMapLoc W ((CategoryOfElements.π X).leftOp.map u)).map
            ((p ((CategoryOfElements.π X).leftOp.obj c')).equiv.counitIso.hom.app
              ((W.over (X := (CategoryOfElements.π X).leftOp.obj c')).Q.obj
                ((Over.post (CategoryOfElements.π X).leftOp).obj Y))))
      = (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).map
          ((p ((CategoryOfElements.π X).leftOp.obj c)).equiv.counitIso.hom.app
            ((overMapLoc W ((CategoryOfElements.π X).leftOp.map u)).obj
              ((W.over (X := (CategoryOfElements.π X).leftOp.obj c')).Q.obj
                ((Over.post (CategoryOfElements.π X).leftOp).obj Y)))) := by
    simpa [Functor.map_comp, eqToHom_map] using
      congrArg (glueSliceEval X W ((CategoryOfElements.π X).leftOp.obj c) c.unop.2).map
        (conjIso_hom_comp_counit (p ((CategoryOfElements.π X).leftOp.obj c')).equiv
          (p ((CategoryOfElements.π X).leftOp.obj c)).equiv
          (P.map ((CategoryOfElements.π X).leftOp.map u)).functor
          (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)) (hP _)
          ((W.over (X := (CategoryOfElements.π X).leftOp.obj c')).Q.obj
            ((Over.post (CategoryOfElements.π X).leftOp).obj Y)))
  have ho : (overMapLoc W ((CategoryOfElements.π X).leftOp.map u)).obj
        ((W.over (X := (CategoryOfElements.π X).leftOp.obj c')).Q.obj
          ((Over.post (CategoryOfElements.π X).leftOp).obj Y))
      = (W.over (X := (CategoryOfElements.π X).leftOp.obj c)).Q.obj
          ((Over.post (CategoryOfElements.π X).leftOp).obj ((Over.map u).obj Y)) :=
    Functor.congr_obj (overMapLocFac W ((CategoryOfElements.π X).leftOp.map u)) _
  rw [natTrans_app_congr _ ho] at hmate
  simp only [Functor.map_comp, eqToHom_map] at hmate
  refine Eq.trans (congrArg (· ≫ _)
    ((hconj _ _ _).trans
      ((eqToHom_conj_congr _ _ (key _ _ _)).trans (eqToHom_conj_conj _ _ _ _ _)))) ?_
  simp only []
  refine Eq.trans (congrArg (_ ≫ ·)
    ((eqToHom_conj_congr _ _ (Functor.congr_hom hgse _)).trans
      (eqToHom_conj_conj _ _ _ _ _))) ?_
  simp only []
  refine (eqToHom_conj_comp _ _ _ _ _ _).trans ?_
  refine (eqToHom_conj_congr _ _ hmate).trans ?_
  exact eqToHom_conj_conj _ _ _ _ _

theorem glueRetract_fac (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q ⋙ glueRetract X L W p c
      = glueRetractPre X L W p c :=
  Localization.Construction.fac _ _

noncomputable instance liftingGlueRetract (c : (X.Elements)ᵒᵖ) :
    Localization.Lifting ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q
      ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c))
      (glueRetractPre X L W p c) (glueRetract X L W p c) :=
  ⟨eqToIso (glueRetract_fac X L W p c)⟩

theorem glueRetract_comp_eq {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c')).Q ⋙
        (overMapLoc (W.inverseImage (CategoryOfElements.π X).leftOp) u ⋙ glueRetract X L W p c)
      = Over.map u ⋙ glueRetractPre X L W p c := by
  rw [← Functor.assoc, overMapLocFac, Functor.assoc, glueRetract_fac]

noncomputable instance liftingGlueRetractMap {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Localization.Lifting ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c')).Q
      ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c'))
      (Over.map u ⋙ glueRetractPre X L W p c)
      (overMapLoc (W.inverseImage (CategoryOfElements.π X).leftOp) u ⋙ glueRetract X L W p c) :=
  ⟨eqToIso (glueRetract_comp_eq X L W p u)⟩

include hP in
/-- **The retraction is natural in `c`**, up to isomorphism. -/
noncomputable def glueRetractIso {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    overMapLoc (W.inverseImage (CategoryOfElements.π X).leftOp) u ⋙ glueRetract X L W p c
      ≅ glueRetract X L W p c' :=
  Localization.liftNatIso ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c')).Q
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c'))
    (Over.map u ⋙ glueRetractPre X L W p c) (glueRetractPre X L W p c') _ _
    (glueRetractPreIso X L W p hP u)

include hP in
theorem glueRetractIso_id (c : (X.Elements)ᵒᵖ) :
    glueRetractIso X L W p hP (𝟙 c)
      = eqToIso (by rw [overMapLoc_id, Functor.id_comp]) := by
  refine Iso.ext (Localization.natTrans_ext
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)) fun Y => ?_)
  dsimp only [glueRetractIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app, glueRetractPreIso_id]
  simp [Localization.Lifting.iso]

include hP in
theorem glueRetractIso_comp {a b c : (X.Elements)ᵒᵖ} (u : a ⟶ b) (v : b ⟶ c) :
    glueRetractIso X L W p hP (u ≫ v) =
      eqToIso (by rw [overMapLoc_comp, Functor.assoc]) ≪≫
        Functor.isoWhiskerLeft (overMapLoc (W.inverseImage (CategoryOfElements.π X).leftOp) u)
          (glueRetractIso X L W p hP v) ≪≫
        glueRetractIso X L W p hP u := by
  refine Iso.ext (Localization.natTrans_ext
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := a)).Q
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := a)) fun Y => ?_)
  dsimp only [glueRetractIso, Localization.liftNatIso]
  have ho : (overMapLoc (W.inverseImage (CategoryOfElements.π X).leftOp) u).obj
        (((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := a)).Q.obj Y)
      = ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := b)).Q.obj
          ((Over.map u).obj Y) :=
    Functor.congr_obj (overMapLocFac (W.inverseImage (CategoryOfElements.π X).leftOp) u) Y
  rw [Localization.liftNatTrans_app, glueRetractPreIso_comp]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app, Category.assoc]
  rw [natTrans_app_congr _ ho, Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

include hP in
/-- The retraction, as a pseudo-cocone on the localized slices of `(∫X)[W⁻¹]`. -/
noncomputable def glueRetractCocone :
    OverPseudoCoconeLoc (W.inverseImage (CategoryOfElements.π X).leftOp)
      ((glue X L).presented) where
  obj c := glueRetract X L W p c
  iso u := glueRetractIso X L W p hP u
  iso_id := glueRetractIso_id X L W p hP
  iso_comp := glueRetractIso_comp X L W p hP

include hP in
/-- **The retraction** `Ψ : (∫X)[W⁻¹] ⥤ Glue`, descended from the slices. -/
noncomputable def glueRetractDesc :
    (W.inverseImage (CategoryOfElements.π X).leftOp).Localization ⥤ (glue X L).presented :=
  (glueRetractCocone X L W p hP).descLoc

/-! ## The counit `Ψ ⋙ Φ ≅ 𝟭` -/

include hL hP in
/-- The retraction's leg, read through `Φ`, still lifts what it lifted.  Stated so that the
`Lifting` below is a plain `eqToIso`: `Localization.Lifting.iso` then reduces to an `eqToHom` under
`simp`, which is what lets `liftNatTrans_app` be computed with. -/
theorem glueRetract_postcomp_fac (c : (X.Elements)ᵒᵖ) :
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q ⋙
        ((glueRetractCocone X L W p hP).postcomp (glueDesc X L W p hL hP)).obj c
      = glueRetractPre X L W p c ⋙ glueDesc X L W p hL hP := by
  rw [show ((glueRetractCocone X L W p hP).postcomp (glueDesc X L W p hL hP)).obj c
      = glueRetract X L W p c ⋙ glueDesc X L W p hL hP from rfl, ← Functor.assoc,
    glueRetract_fac]

noncomputable instance liftingIdLeg (c : (X.Elements)ᵒᵖ) :
    Localization.Lifting
      ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q
      ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c))
      (Over.forget c ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙ 𝟭 _)
      ((OverPseudoCoconeLoc.ofFunctor
        (W := W.inverseImage (CategoryOfElements.π X).leftOp) (𝟭 _)).obj c) :=
  ⟨eqToIso (overCoconeLocEquiv_apply
    (W.inverseImage (CategoryOfElements.π X).leftOp) (𝟭 _) c)⟩

include hL hP in
noncomputable instance liftingPostLeg (c : (X.Elements)ᵒᵖ) :
    Localization.Lifting
      ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q
      ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c))
      (glueRetractPre X L W p c ⋙ glueDesc X L W p hL hP)
      (((glueRetractCocone X L W p hP).postcomp (glueDesc X L W p hL hP)).obj c) :=
  ⟨eqToIso (glueRetract_postcomp_fac X L W p hL hP c)⟩

include hL hP in
/-- The counit's leg at `c`: `glueRetractPreDesc`, localized. -/
noncomputable def glueCounitLeg (c : (X.Elements)ᵒᵖ) :
    ((glueRetractCocone X L W p hP).postcomp (glueDesc X L W p hL hP)).obj c
      ≅ (OverPseudoCoconeLoc.ofFunctor
          (W := W.inverseImage (CategoryOfElements.π X).leftOp) (𝟭 _)).obj c :=
  Localization.liftNatIso
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c))
    (glueRetractPre X L W p c ⋙ glueDesc X L W p hL hP)
    (Over.forget c ⋙ (W.inverseImage (CategoryOfElements.π X).leftOp).Q ⋙ 𝟭 _) _ _
    (glueRetractPreDesc X L W p hL hP c)

include hL hP in
/-- …and the legs are compatible, because `glueRetractPreDesc_naturality` is. -/
theorem glueCounitLeg_naturality {c' c : (X.Elements)ᵒᵖ} (u : c' ⟶ c) :
    Functor.whiskerLeft (overMapLoc (W.inverseImage (CategoryOfElements.π X).leftOp) u)
        (glueCounitLeg X L W p hL hP c).hom ≫
        ((OverPseudoCoconeLoc.ofFunctor
          (W := W.inverseImage (CategoryOfElements.π X).leftOp) (𝟭 _)).iso u).hom
      = (((glueRetractCocone X L W p hP).postcomp (glueDesc X L W p hL hP)).iso u).hom ≫
        (glueCounitLeg X L W p hL hP c').hom := by
  refine Localization.natTrans_ext
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c')).Q
    ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c')) fun Y => ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    OverPseudoCoconeLoc.postcomp, OverPseudoCoconeLoc.ofFunctor, OverCoconeLoc.toPseudo,
    Functor.isoWhiskerRight_hom, eqToIso.hom, eqToHom_app, glueRetractCocone]
  -- the goal spells it `Q.obj ((Over.map u).obj Y)`, not `(overMapLoc W u).obj (Q.obj Y)`
  have ho : (overMapLoc (W.inverseImage (CategoryOfElements.π X).leftOp) u).obj
        (((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c')).Q.obj Y)
      = ((W.inverseImage (CategoryOfElements.π X).leftOp).over (X := c)).Q.obj
          ((Over.map u).obj Y) :=
    Functor.congr_obj (overMapLocFac (W.inverseImage (CategoryOfElements.π X).leftOp) u) Y
  rw [natTrans_app_congr (glueCounitLeg X L W p hL hP c).hom ho]
  dsimp only [glueCounitLeg, glueRetractIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app, Localization.liftNatTrans_app,
    Localization.liftNatTrans_app]
  have tri := congrArg (fun σ => NatTrans.app σ Y)
    (glueRetractPreDesc_naturality X L W p hL hP u)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at tri
  simp only [Localization.Lifting.iso, eqToIso.hom, eqToIso.inv, eqToHom_app]
  simp only [← tri, Functor.comp_obj, Over.forget_obj, Over.map_obj_left, Functor.id_obj,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Functor.map_comp, eqToHom_map]
  -- only `eqToHom` bookkeeping is left, and `Category.assoc` will not match it
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans ?_ (eqToHom_trans_assoc _ _ _).symm)
  refine Eq.trans ?_ ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)).symm
  congr 1

include hL hP in
/-- **The counit**: the retraction, read through the comparison, is the identity. -/
noncomputable def glueCounit :
    glueRetractDesc X L W p hP ⋙ glueDesc X L W p hL hP ≅ 𝟭 _ :=
  eqToIso (OverPseudoCoconeLoc.descLoc_postcomp _ _).symm ≪≫
    OverPseudoCoconeLoc.descLocIso (glueCounitLeg X L W p hL hP)
      (glueCounitLeg_naturality X L W p hL hP) ≪≫
    eqToIso (OverPseudoCoconeLoc.descLoc_ofFunctor _)

end Retract

end Compare

end Polygraph

end CategoryTheory
