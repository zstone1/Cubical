import CubeChains.Machinery.Presentation.Glue

/-!
# Machinery/Presentation/GlueRefutation — `glue` needs injective labels

A counterexample to `Presents (glue X L) ((∫X)[W⁻¹])` under the hypotheses of
`Machinery/Presentation/Glue`: two 0-cells of `P d` carrying the same label become **one** 0-cell
of `glue` while their 1-cells stay distinct, so words that were not composable in `P d` become
composable and `glueDesc` stops being faithful — here the glued endomorphisms are free on one
generator where the localization is thin.

`hL` makes `L.ob d` the object map of `(p d).E` read through `Construction.objEquiv`, and
`Presents` asks only that `(p d).E` be an equivalence, so nothing forces `L.ob d` to be injective.
-/

universe v u

namespace CategoryTheory

open Opposite Polygraph

/-! ## Codiscrete categories -/

theorem isThin_of_equiv {C : Type*} [Category C] {E : Type*} [Category E] (e : C ≌ E)
    [Quiver.IsThin C] : Quiver.IsThin E :=
  fun _ _ => ⟨fun _ _ => e.inverse.map_injective (Subsingleton.elim _ _)⟩

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
  ⟨(Quotient.functor P₂.rel).map (word₂ X.as Y.as)⟩

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

/-- **Both 0-cells carry the same label**, so they are one 0-cell of `glue`. -/
theorem gluePt_false_eq_true (d : Pt) (x : X₂.obj (op d)) :
    gluePt X₂ L₂ d x false = gluePt X₂ L₂ d x true := rfl

/-! ## The winding number -/

/-- `ℤ` as a one-object category: what a word of `glue` accumulates. -/
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

/-- **The winding number kills the 2-cells of `glue`**: the copy relations because parallel words
of `P₂` wind alike, the overlaps because `P₂F` is constant. -/
theorem wind_sound {s t : Paths (GenObj (GlueGen X₂ L₂))} {u v : s ⟶ t}
    (h : GlueRel X₂ L₂ u v) :
    (Paths.lift wind).map u = (Paths.lift wind).map v := by
  cases h with
  | copy x _ => exact (wind_gluePre _ _ _).trans (wind_gluePre _ _ _).symm
  | overlap f x g =>
      rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, eqToHom_wind,
        eqToHom_wind]
      refine Eq.trans ?_ ((Category.id_comp _).trans (Category.comp_id _)).symm
      exact (wind_gluePre _ _ _).trans (wind_gluePre _ _ _).symm

/-- The winding number of a word of the glued polygraph. -/
noncomputable def windDesc : (glue X₂ L₂).presented ⥤ Wind :=
  (glue X₂ L₂).desc wind fun h => wind_sound h

/-! ## The refutation -/

/-- The one 0-cell. -/
def pt₂ : Pt := ⟨PUnit.unit⟩

/-- **The loop `glue` invents**: `fwd` runs between two 0-cells of `P₂` that carry the same label,
so in `glue` it is an endomorphism — of winding number `1`, hence not the identity. -/
noncomputable def loopGen : GlueGen X₂ L₂ (gluePt X₂ L₂ pt₂ PUnit.unit false)
    (gluePt X₂ L₂ pt₂ PUnit.unit true) :=
  @GlueGen.mk _ _ X₂ _ L₂ pt₂ PUnit.unit _ _ Gen₂.fwd

theorem wind_loopGen :
    windDesc.map ((glue X₂ L₂).quot.map (Quiver.Hom.toPath loopGen)) = (1 : ℤ) := rfl

instance : Quiver.IsThin Ptᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin X₂.Elements :=
  fun _ _ => ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin (X₂.Elements)ᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

/-- **The hypothesis `presentsGlue` adds, and this data fails**: `E` sends both 0-cells to the one
object of the slice. -/
theorem presents₂_not_bijective (d : Pt) : ¬ Function.Bijective (presents₂ d).E.obj := by
  intro h
  have h₀ : (presents₂ d).E.obj ⟨⟨false⟩⟩ = (presents₂ d).E.obj ⟨⟨true⟩⟩ := rfl
  exact Bool.false_ne_true (congrArg (fun Z : P₂.presented => Z.as.as) (h.1 h₀))

/-- **`glue X L` does not present `(∫X)[W⁻¹]`.**  Every hypothesis of `presentsGlue` holds except
bijectivity — `presents₂` presents each localized slice, `L₂` is `labelsOf` so `hL` is
`labelsOf_ob`, and `hP₂` is the compatibility square — so it is exactly `presents₂_not_bijective`
that `presentsGlue` rules out. -/
theorem not_nonempty_presents_glue :
    ¬ Nonempty (Presents (glue X₂ L₂)
      ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization)) := by
  rintro ⟨q⟩
  haveI : Quiver.IsThin
      ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
    isThin_of_equiv (equivLocalizationOfLeIso _ (fun _ _ _ h => h.elim))
  have hE : (glue X₂ L₂).quot.map (Quiver.Hom.toPath loopGen) = 𝟙 _ :=
    q.E.map_injective (Subsingleton.elim _ _)
  have h1 : (1 : ℤ) = 0 := (congrArg windDesc.map hE).trans (windDesc.map_id _)
  exact absurd h1 (by decide)

end CategoryTheory
