import CubeChains.Machinery.Presentation.Glue

/-!
# Machinery/Presentation/GlueRefutation — the 0-cells must be a quotient, not an image

`flatGlue X L` glues the copies with their 0-cells **flattened onto `∫X`**: a 0-cell is the object
of `∫X` its label names, so two 0-cells of one copy carrying the same label become one.  That is
one identification too many, and `flatGlue` then presents a category with a loop the localization
does not have — here the glued endomorphisms are free on one generator where `(∫X)[W⁻¹]` is thin.

`hL` makes `L.ob d` the object map of `(p d).E` read through `Construction.objEquiv`, and
`Presents` asks only that `(p d).E` be an equivalence, so nothing forces `L.ob d` to be injective:
the flattening is not repairable by a hypothesis on the family.  What repairs it is taking the
0-cells as a *colimit* of the copies' rather than as their image — `colimit (elementsPoly X P)`.
-/

universe w w' v₁ u₁ u' w₂ v u

namespace CategoryTheory

open Opposite Polygraph

namespace Polygraph

variable {D : Type u₁} [Category.{v₁} D] (X : Dᵒᵖ ⥤ Type w) {P : D ⥤ Polygraph.{w', u', w₂}}
  (L : SliceLabels P)


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

/-- **The glued polygraph, with its 0-cells flattened onto `∫X`.** -/
def flatGlue : Polygraph.{max u₁ w u' w', max u₁ w, max u₁ v₁ w u' w' w₂} where
  V := GlueV X
  Gen := GlueGen X L
  Rel := GlueRel X L
  src := GlueRel.src X L
  tgt := GlueRel.tgt X L

end Polygraph

/-! ## Codiscrete categories -/

theorem nonempty_hom_of_equiv {C : Type*} [Category C] {E : Type*} [Category E] (e : C ≌ E)
    (h : ∀ X Y : C, Nonempty (X ⟶ Y)) (A B : E) : Nonempty (A ⟶ B) :=
  ⟨(e.counitIso.app A).inv ≫ e.functor.map (h _ _).some ≫ (e.counitIso.app B).hom⟩

/-- **Inverting isomorphisms changes nothing**: `𝟭` is then a localization too, so
`Localization.uniq` compares it with `Q`. -/
noncomputable def equivLocalizationOfLeIso {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    (hW : W ≤ MorphismProperty.isomorphisms C) : C ≌ W.Localization :=
  haveI := Functor.IsLocalization.for_id W hW
  Localization.uniq (𝟭 C) W.Q W

/-- **Any functor between codiscrete categories is an equivalence** — thin with every hom-set
inhabited leaves nothing for a functor to get wrong. -/
theorem isEquivalence_of_codiscrete {C : Type*} [Category C] {E : Type*} [Category E]
    [Quiver.IsThin C] [Quiver.IsThin E] (hC : ∀ X Y : C, Nonempty (X ⟶ Y))
    (hE : ∀ X Y : E, Nonempty (X ⟶ Y)) (X₀ : C) (F : C ⥤ E) : F.IsEquivalence :=
  haveI : F.Faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  haveI : F.Full := ⟨fun {X Y} _ => ⟨(hC X Y).some, Subsingleton.elim _ _⟩⟩
  haveI : F.EssSurj :=
    ⟨fun Y => ⟨X₀, ⟨iso_of_both_ways (hE _ _).some (hE _ _).some⟩⟩⟩
  Functor.IsEquivalence.mk

/-! ## The data -/

/-- The base: one object, one arrow, so `Over d` has a single object and every label is that
object. -/
abbrev Pt : Type := Discrete PUnit

instance isThinOver (d : Pt) : Quiver.IsThin (Over d) :=
  fun _ _ => ⟨fun _ _ => (Over.forget d).map_injective (Subsingleton.elim _ _)⟩

theorem nonempty_hom_over (d : Pt) (Y Z : Over d) : Nonempty (Y ⟶ Z) :=
  ⟨Over.homMk (eqToHom (Subsingleton.elim _ _)) (Subsingleton.elim _ _)⟩

/-- Two 0-cells and a 1-cell each way between them. -/
inductive Gen₂ : Bool → Bool → Type
  | fwd : Gen₂ false true
  | bwd : Gen₂ true false

/-- **The polygraph whose two 0-cells will share a label.**  Relating *every* parallel pair of
words makes it present a codiscrete category with no word problem to solve. -/
abbrev P₂ : Polygraph.{0, 0} := Polygraph.thin Gen₂

/-- A word between any two 0-cells. -/
def word₂ : ∀ x y : GenObj Gen₂, Quiver.Path x y
  | ⟨false⟩, ⟨false⟩ => Quiver.Path.nil
  | ⟨false⟩, ⟨true⟩ => Quiver.Hom.toPath (show (⟨false⟩ : GenObj Gen₂) ⟶ ⟨true⟩ from Gen₂.fwd)
  | ⟨true⟩, ⟨false⟩ => Quiver.Hom.toPath (show (⟨true⟩ : GenObj Gen₂) ⟶ ⟨false⟩ from Gen₂.bwd)
  | ⟨true⟩, ⟨true⟩ => Quiver.Path.nil

theorem nonempty_hom_presented₂ (X Y : P₂.presented) : Nonempty (X ⟶ Y) :=
  ⟨P₂.quot.map (word₂ X.as Y.as)⟩

/-- Nothing is inverted. -/
abbrev W₂ : MorphismProperty Pt := ⊥

theorem W₂_over_le (d : Pt) : W₂.over (X := d) ≤ MorphismProperty.isomorphisms _ :=
  fun _ _ _ h => h.elim

noncomputable def locEquiv₂ (d : Pt) : Over d ≌ (W₂.over (X := d)).Localization :=
  equivLocalizationOfLeIso _ (W₂_over_le d)

instance isThinLoc₂ (d : Pt) : Quiver.IsThin (W₂.over (X := d)).Localization :=
  isThin_of_equiv (locEquiv₂ d)

theorem nonempty_hom_loc₂ (d : Pt) (A B : (W₂.over (X := d)).Localization) : Nonempty (A ⟶ B) :=
  nonempty_hom_of_equiv (locEquiv₂ d) (nonempty_hom_over d) A B

/-- Both 0-cells are read at the one object of `Over d`. -/
noncomputable def eval₂ (d : Pt) : GenObj Gen₂ ⥤q (W₂.over (X := d)).Localization where
  obj _ := (W₂.over (X := d)).Q.obj (Over.mk (𝟙 d))
  map _ := 𝟙 _

noncomputable def presents₂ (d : Pt) : Presents P₂ ((W₂.over (X := d)).Localization) :=
  ⟨P₂.desc (eval₂ d) fun _ => Subsingleton.elim _ _,
    isEquivalence_of_codiscrete nonempty_hom_presented₂ (nonempty_hom_loc₂ d) ⟨⟨false⟩⟩ _⟩

/-- The constant family. -/
def P₂F : Pt ⥤ Polygraph.{0, 0} := (Functor.const Pt).obj P₂

theorem hP₂ {d' d : Pt} (f : d' ⟶ d) :
    (P₂F.map f).functor ⋙ (presents₂ d).E = (presents₂ d').E ⋙ overMapLoc W₂ f := by
  obtain ⟨⟨⟩⟩ := d'; obtain ⟨⟨⟩⟩ := d
  rw [Subsingleton.elim f (𝟙 _)]
  change (𝟙 P₂ : P₂ ⟶ P₂).functor ⋙ _ = _
  rw [Polygraph.functor_id, overMapLoc_id, Functor.id_comp, Functor.comp_id]

/-- The terminal presheaf: `∫X₂` is again a point. -/
def X₂ : Ptᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

/-- The labels the presentations supply. -/
noncomputable def L₂ : SliceLabels P₂F := labelsOf W₂ presents₂ hP₂

/-- **Both 0-cells carry the same label**, so they are one 0-cell of `flatGlue`. -/
theorem gluePt_false_eq_true (d : Pt) (x : X₂.obj (op d)) :
    gluePt X₂ L₂ d x false = gluePt X₂ L₂ d x true := rfl

/-! ## The winding number -/

/-- `ℤ` as a one-object category: what a word of `flatGlue` accumulates. -/
def Wind : Type := PUnit

instance : Category Wind where
  Hom _ _ := ℤ
  id _ := 0
  comp f g := f + g
  id_comp f := by show (0 : ℤ) + f = f; omega
  comp_id f := by show f + (0 : ℤ) = f; omega
  assoc f g h := by show f + g + h = f + (g + h); omega

theorem eqToHom_wind {a b : Wind} (h : a = b) : eqToHom h = 𝟙 a := by subst h; rfl

/-- The height of a 0-cell of `P₂`. -/
def height : Bool → ℤ := fun b => cond b 1 0

/-- What a 1-cell of `P₂` winds. -/
def windGen : ∀ {a b : Bool}, Gen₂ a b → ℤ
  | _, _, .fwd => 1
  | _, _, .bwd => -1

theorem windGen_eq {a b : Bool} (g : Gen₂ a b) : windGen g = height b - height a := by
  cases g <;> simp [windGen, height]

/-- The winding number, on the cells of `P₂`. -/
def windPre : GenObj Gen₂ ⥤q Wind where
  obj _ := PUnit.unit
  map g := windGen g

/-- **A word of `P₂` winds by the difference of its endpoints' heights** — so parallel words of
`P₂` wind alike, which is all `P₂`'s total 2-cell relation asks. -/
theorem windPre_mapPath : ∀ {a b : Paths (GenObj Gen₂)} (u : a ⟶ b),
    (Paths.lift windPre).map u = height b.as - height a.as := by
  intro a b u
  induction u with
  | nil => change (0 : ℤ) = _; omega
  | cons u e ih =>
      refine (Paths.lift_cons windPre u e).trans ?_
      rw [ih]
      change _ + windGen e = _
      rw [windGen_eq]
      omega

/-- The same, on the glued polygraph: a copy still knows which 1-cell of `P₂` it came from, even
though the glued 0-cells no longer tell that 1-cell's endpoints apart. -/
def wind : GenObj (GlueGen X₂ L₂) ⥤q Wind where
  obj _ := PUnit.unit
  map {X Y} g :=
    match X, Y, g with
    | ⟨_⟩, ⟨_⟩, GlueGen.mk _ g' => windGen g'

theorem gluePre_comp_wind (d : Pt) (x : X₂.obj (op d)) :
    gluePre X₂ L₂ d x ⋙q wind = windPre := rfl

/-- A copy's word winds by the difference of its `P₂`-endpoints' heights. -/
theorem wind_gluePre (d : Pt) (x : X₂.obj (op d)) {a b : GenObj Gen₂} (u : Quiver.Path a b) :
    (Paths.lift wind).map ((gluePre X₂ L₂ d x).mapPath u) = height b.as - height a.as := by
  rw [Paths.lift_mapPath, gluePre_comp_wind]
  exact windPre_mapPath u

/-- **The winding number kills the 2-cells of `flatGlue`**: the copy relations because parallel
words of `P₂` wind alike, the overlaps because `P₂F` is constant. -/
theorem wind_sound {s t : GenObj (GlueGen X₂ L₂)} (α : (flatGlue X₂ L₂).Rel s t) :
    (Paths.lift wind).map ((flatGlue X₂ L₂).src α)
      = (Paths.lift wind).map ((flatGlue X₂ L₂).tgt α) := by
  cases α with
  | copy x _ => exact (wind_gluePre _ _ _).trans (wind_gluePre _ _ _).symm
  | @overlap d' d f x a b g =>
      change (Paths.lift wind).map ((gluePre X₂ L₂ d' (X₂.map f.op x)).mapPath g.toPath)
          = (Paths.lift wind).map (eqToHom (gluePre_obj_map X₂ L₂ f x a).symm ≫
              (gluePre X₂ L₂ d x).mapPath ((P₂F.map f).pre.map g).toPath ≫
              eqToHom (gluePre_obj_map X₂ L₂ f x b))
      rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, eqToHom_wind,
        eqToHom_wind]
      refine Eq.trans ?_ ((Category.id_comp _).trans (Category.comp_id _)).symm
      exact (wind_gluePre _ _ _).trans (wind_gluePre _ _ _).symm

/-- The winding number of a word of the glued polygraph. -/
noncomputable def windDesc : (flatGlue X₂ L₂).presented ⥤ Wind :=
  (flatGlue X₂ L₂).desc wind wind_sound

/-! ## The refutation -/

/-- The one 0-cell. -/
def pt₂ : Pt := ⟨PUnit.unit⟩

/-- **The loop `flatGlue` invents**: `fwd` runs between two 0-cells of `P₂` that carry the same
label, so in `flatGlue` it is an endomorphism — of winding number `1`, hence not the identity. -/
noncomputable def loopGen : GlueGen X₂ L₂ (gluePt X₂ L₂ pt₂ PUnit.unit false)
    (gluePt X₂ L₂ pt₂ PUnit.unit true) :=
  @GlueGen.mk _ _ X₂ _ L₂ pt₂ PUnit.unit _ _ Gen₂.fwd

theorem wind_loopGen :
    windDesc.map ((flatGlue X₂ L₂).quot.map (Quiver.Hom.toPath loopGen)) = (1 : ℤ) := rfl

instance : Quiver.IsThin Ptᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin X₂.Elements :=
  fun _ _ => ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin (X₂.Elements)ᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

/-- **The labels are not injective here, and nothing makes them so**: `E` sends both 0-cells to the
one object of the slice.  It is exactly `SliceSkeleton.at_injective` that fails. -/
theorem presents₂_not_bijective (d : Pt) : ¬ Function.Bijective (presents₂ d).E.obj := by
  intro h
  have h₀ : (presents₂ d).E.obj ⟨⟨false⟩⟩ = (presents₂ d).E.obj ⟨⟨true⟩⟩ := rfl
  exact Bool.false_ne_true (congrArg (fun Z : P₂.presented => Z.as.as) (h.1 h₀))

/-- **`flatGlue X L` does not present `(∫X)[W⁻¹]`.**  Everything a family of slice presentations
supplies holds here — `presents₂` presents each localized slice, `L₂` is `labelsOf` so `hL` is
`labelsOf_ob`, `hP₂` is the compatibility square — and the flattening still invents a loop. -/
theorem not_nonempty_presents_flatGlue :
    ¬ Nonempty (Presents (flatGlue X₂ L₂)
      ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization)) := by
  rintro ⟨q⟩
  haveI : Quiver.IsThin
      ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
    isThin_of_equiv (equivLocalizationOfLeIso _ (fun _ _ _ h => h.elim))
  have hE : (flatGlue X₂ L₂).quot.map (Quiver.Hom.toPath loopGen) = 𝟙 _ :=
    q.E.map_injective (Subsingleton.elim _ _)
  have h1 : (1 : ℤ) = 0 := (congrArg windDesc.map hE).trans (windDesc.map_id _)
  exact absurd h1 (by decide)

/-! ## …and the colimit does present it

The same data, glued as a colimit: `∫X₂` is a point, so the colimit of the slice diagram is `P₂`
itself and its two 0-cells stay two.  There is then no loop to invent, and `P₂` presents the (also
codiscrete) localization.  So it is precisely the flattening of the 0-cells that fails — the
colimit needs no hypothesis on the labels at all. -/

/-- The one object of `∫X₂`. -/
def elt₂ : (X₂.Elements)ᵒᵖ := op ⟨op pt₂, PUnit.unit⟩

theorem eq_elt₂ (c : (X₂.Elements)ᵒᵖ) : c = elt₂ := by
  obtain ⟨⟨d, x⟩⟩ := c
  obtain ⟨⟨⟨⟩⟩⟩ := d
  rfl

noncomputable def isTerminalElt₂ : Limits.IsTerminal elt₂ :=
  Limits.IsTerminal.ofUniqueHom (fun c => eqToHom (eq_elt₂ c)) fun _ _ => Subsingleton.elim _ _

theorem isIso_iota₂ : IsIso (Limits.colimit.ι (elementsPoly X₂ P₂F) elt₂) :=
  (Limits.colimit.isColimit _).isIso_ι_app_of_isTerminal elt₂ isTerminalElt₂

/-- **The colimit of the slice diagram is `P₂` itself** — the index category is a point. -/
noncomputable def glueIso₂ : P₂ ≅ Limits.colimit (elementsPoly X₂ P₂F) :=
  @asIso _ _ _ _ (Limits.colimit.ι (elementsPoly X₂ P₂F) elt₂) isIso_iota₂

/-- Nothing is inverted, so the localization of the point is the point. -/
instance isThinLocElt₂ :
    Quiver.IsThin ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
  isThin_of_equiv (equivLocalizationOfLeIso _ (fun _ _ _ h => h.elim))

theorem nonempty_hom_locElt₂
    (A B : (W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) : Nonempty (A ⟶ B) :=
  nonempty_hom_of_equiv (equivLocalizationOfLeIso _ (fun _ _ _ h => h.elim))
    (fun x y => ⟨eqToHom ((eq_elt₂ x).trans (eq_elt₂ y).symm)⟩) A B

/-- Both 0-cells are read at the one object of `∫X₂`. -/
noncomputable def evalElt₂ :
    GenObj Gen₂ ⥤q (W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization where
  obj _ := (W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Q.obj elt₂
  map _ := 𝟙 _

noncomputable def presentsP₂Elt :
    Presents P₂ ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
  ⟨P₂.desc evalElt₂ fun _ => Subsingleton.elim _ _,
    isEquivalence_of_codiscrete nonempty_hom_presented₂ nonempty_hom_locElt₂ ⟨⟨false⟩⟩ _⟩

/-- **The colimit presents exactly where the flattening does not.**  `SliceSkeleton.at_injective`
fails for this data (`presents₂_not_bijective`), so `presentsSliceColimit` does not apply; the
conclusion holds all the same, which is what says the flattening — and nothing else — is the
fault. -/
noncomputable def presentsGlue₂ :
    Presents (Limits.colimit (elementsPoly X₂ P₂F))
      ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
  haveI : (glueIso₂.inv.functor).IsEquivalence :=
    (CategoryTheory.Equivalence.mk glueIso₂.inv.functor glueIso₂.hom.functor
      (eqToIso (by
        rw [← Polygraph.functor_comp, glueIso₂.inv_hom_id, Polygraph.functor_id])).symm
      (eqToIso (by
        rw [← Polygraph.functor_comp, glueIso₂.hom_inv_id,
          Polygraph.functor_id]))).isEquivalence_functor
  haveI := presentsP₂Elt.isEquiv
  ⟨glueIso₂.inv.functor ⋙ presentsP₂Elt.E, inferInstance⟩

end CategoryTheory
