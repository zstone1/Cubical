import CubeChains.Machinery.Presentation.Glue

/-!
# Machinery/Presentation/GlueRefutation — two 0-cells naming one slice object

`presentsSliceColimit` asks nothing of the 0-cells, and this is the data that says why it must
not: `P₂` has two 0-cells and the localized slice has one object, so both are labelled alike, and
yet the colimit presents the localization (`presentsGlue₂`) — computed by hand here, `∫X₂` being a
point and the colimit of the slice diagram `P₂` itself.

Two readings.  The comparison's unit *cannot* be an equality: `false` and `true` are not glued in
the colimit, so the retraction, which sends both to whichever 0-cell it chose, is only isomorphic
to `𝟭`.  And the 0-cells of the colimit are the copies', never their image in `∫X`: a construction
that flattened them onto `∫X` would identify `false` with `true` here and invent a loop.
-/

universe v u

namespace CategoryTheory

open Opposite Polygraph

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

/-- The terminal presheaf: `∫X₂` is again a point. -/
def X₂ : Ptᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

/-- **The two 0-cells name the one object of the slice** — `Presents`, asking only for an
equivalence, separates nothing. -/
theorem presents₂_not_injective (d : Pt) :
    ¬ Function.Injective fun a : P₂.V => (presents₂ d).at' ⟨a⟩ := by
  intro h
  exact Bool.false_ne_true
    (h (rfl : (presents₂ d).at' ⟨(false : P₂.V)⟩ = (presents₂ d).at' ⟨(true : P₂.V)⟩))

/-! ## …and the colimit presents it anyway

`∫X₂` is a point, so the colimit of the slice diagram is `P₂` itself and its two 0-cells stay two.
`P₂` presents the (also codiscrete) localization, and the colimit needs no hypothesis on the
0-cells at all. -/

/-- The one 0-cell of the base. -/
def pt₂ : Pt := ⟨PUnit.unit⟩

instance : Quiver.IsThin Ptᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin X₂.Elements :=
  fun _ _ => ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

instance : Quiver.IsThin (X₂.Elements)ᵒᵖ :=
  fun _ _ => ⟨fun _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

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

/-- **The colimit presents even so** — computed by hand, against `presents₂_not_injective`. -/
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
