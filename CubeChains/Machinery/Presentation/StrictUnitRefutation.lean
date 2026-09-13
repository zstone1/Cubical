import CubeChains.Machinery.Presentation.SliceColimit

/-!
# Machinery/Presentation/StrictUnitRefutation — two 0-cells naming one slice object

`presentsSliceColimit` asks nothing of the 0-cells, and this is the data that says why it must not:
`P₂` has two 0-cells and the localized slice has one object, so both are labelled alike, and yet the
colimit presents the localization (`presentsColim₂`) — `∫X₂` being a point and the colimit of the
slice diagram `P₂` itself.

Two readings.  The comparison's unit *cannot* be an equality: `false` and `true` are not glued in
the colimit, so the retraction, sending both to whichever 0-cell it chose, is only isomorphic to
`𝟭`.  And the 0-cells of the colimit are the copies', never their image in `∫X`: flattening them
onto `∫X` would identify `false` with `true` here and invent a loop.
-/

universe v u

namespace CategoryTheory

open Opposite Polygraph

/-! ## Codiscrete categories -/

/-- **Inverting isomorphisms changes nothing**: `𝟭` is then a localization too, so
`Localization.uniq` compares it with `Q`. -/
noncomputable def equivLocalizationOfLeIso {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    (hW : W ≤ MorphismProperty.isomorphisms C) : C ≌ W.Localization :=
  haveI := Functor.IsLocalization.for_id W hW
  Localization.uniq (𝟭 C) W.Q W

/-! ## Two 0-cells for one object -/

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

/-- **`P₂` presents every codiscrete category**: both 0-cells go to `X₀`, both 1-cells to `𝟙 X₀`,
and there is no word problem on either side. -/
noncomputable def presentsP₂ {C : Type} [Category.{0} C] [Quiver.IsThin C]
    (hC : ∀ X Y : C, Nonempty (X ⟶ Y)) (X₀ : C) : Presents P₂ C :=
  Presents.ofThin (show GenObj Gen₂ ⥤q C from ⟨fun _ => X₀, fun _ => 𝟙 X₀⟩)
    (fun x y _ => ⟨word₂ x y⟩)
    fun _ => ⟨⟨false⟩, ⟨iso_of_both_ways (hC _ _).some (hC _ _).some⟩⟩

/-! ## Nothing inverted, over a base whose arrows are all invertible

`Pt` here and `Loop` in `IsoComparisonRefutation` differ only in the base.  Both have every arrow
invertible, which forces an arrow of a slice to be `Y.hom ≫ Z.hom⁻¹` — so each slice is codiscrete
— and `⊥` inverts nothing, so `P₂` presents the localized slice either way. -/

section Bot

variable {B : Type} [Category.{0} B] (hiso : ∀ {X Y : B} (f : X ⟶ Y), IsIso f)

include hiso in
/-- **A slice of an invertible-arrow base is thin**: the label is a monomorphism. -/
theorem isThinOverOfIso (d : B) : Quiver.IsThin (Over d) := fun _ Z =>
  ⟨fun f g => (Over.forget d).map_injective
    (haveI := hiso Z.hom; (cancel_mono Z.hom).mp ((Over.w f).trans (Over.w g).symm))⟩

noncomputable def locEquivBot (d : B) :
    Over d ≌ ((⊥ : MorphismProperty B).over (X := d)).Localization :=
  equivLocalizationOfLeIso _ fun _ _ _ h => h.elim

include hiso in
theorem isThinLocBot (d : B) :
    Quiver.IsThin (((⊥ : MorphismProperty B).over (X := d)).Localization) :=
  haveI := isThinOverOfIso hiso d; isThin_of_equiv (locEquivBot d)

include hiso in
/-- **…and codiscrete**: `Y.hom ≫ Z.hom⁻¹` is the arrow of the slice, and nothing is inverted. -/
theorem nonempty_hom_locBot (d : B)
    (A C : ((⊥ : MorphismProperty B).over (X := d)).Localization) : Nonempty (A ⟶ C) :=
  nonempty_hom_of_equiv (locEquivBot d)
    (fun Y Z => haveI := hiso Z.hom; ⟨Over.homMk (Y.hom ≫ inv Z.hom) (by simp)⟩) A C

include hiso in
/-- **The localized slice of such a base, presented** — both 0-cells read at the top. -/
noncomputable def presentsBot (d : B) :
    Presents P₂ (((⊥ : MorphismProperty B).over (X := d)).Localization) :=
  haveI := isThinLocBot hiso d
  presentsP₂ (nonempty_hom_locBot hiso d) (((⊥ : MorphismProperty B).over (X := d)).Q.obj
    (Over.mk (𝟙 d)))

end Bot

/-! ## The data -/

/-- The base: one object, one arrow, so `Over d` has a single object and every label is that
object. -/
abbrev Pt : Type := Discrete PUnit

theorem isIso_pt {X Y : Pt} (f : X ⟶ Y) : IsIso f :=
  ⟨eqToHom (Subsingleton.elim _ _), Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Nothing is inverted. -/
abbrev W₂ : MorphismProperty Pt := ⊥

instance isThinLoc₂ (d : Pt) : Quiver.IsThin (W₂.over (X := d)).Localization :=
  isThinLocBot isIso_pt d

noncomputable def presents₂ (d : Pt) : Presents P₂ ((W₂.over (X := d)).Localization) :=
  presentsBot isIso_pt d

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

instance : Quiver.IsThin X₂.Elements :=
  fun _ _ => ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

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
noncomputable def colimIso₂ : P₂ ≅ Limits.colimit (elementsPoly X₂ P₂F) :=
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
noncomputable def presentsP₂Elt :
    Presents P₂ ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
  presentsP₂ nonempty_hom_locElt₂
    ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Q.obj elt₂)

/-- **The colimit presents even so** — computed by hand, against `presents₂_not_injective`. -/
noncomputable def presentsColim₂ :
    Presents (Limits.colimit (elementsPoly X₂ P₂F))
      ((W₂.inverseImage (CategoryOfElements.π X₂).leftOp).Localization) :=
  presentsP₂Elt.ofPolyIso colimIso₂

end CategoryTheory
