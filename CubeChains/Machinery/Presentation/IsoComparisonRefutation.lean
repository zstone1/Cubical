import CubeChains.Machinery.Presentation.StrictUnitRefutation
import CubeChains.Machinery.Presentation.Transition
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic

/-!
# Machinery/Presentation/IsoComparisonRefutation — the strict colimit is not the bicolimit

The gap between the two, measured at a base with one object and one involution: the localized slice
is codiscrete, so the comparison exists (`kappaLoop`) and is unique (`kappaLoop_unique`) while the
strict `hP` fails (`not_hP_loop`) — the comparison isomorphism is data, and `colimit` presents the
*strict* colimit, here `P₂` (`colimIsoLoop`) and thin.  The target is `B(ZMod 2)`, the homotopy
quotient of a point, which is the *bi*colimit, so `P₂` is too small to present it
(`not_presents_colimLoop`): it has no generator for `twist`, and the polygraph that carries one does
present it (`presentsLoopBicolim`).  What a 0-cell must name on the nose is its slice *object*; the
morphism half is free whenever the slice is thin (`hP_of_naming`).
-/

namespace CategoryTheory

open Opposite Polygraph Limits

/-! ## What a codiscrete target leaves free -/

/-- **A 2-cell into a thin category carries no data.**  Every coherence condition on a comparison is
an equation between such 2-cells, so in the data below each one holds by `Subsingleton.elim`. -/
instance subsingleton_natTrans_isThin {A : Type*} [Category A] {E : Type*} [Category E]
    [Quiver.IsThin E] (F G : A ⥤ E) : Subsingleton (F ⟶ G) :=
  ⟨fun _ _ => NatTrans.ext (funext fun _ => Subsingleton.elim _ _)⟩

/-- **Any two parallel functors into a codiscrete category are isomorphic.** -/
noncomputable def natIsoOfCodiscrete {A : Type*} [Category A] {E : Type*} [Category E]
    [Quiver.IsThin E] (hE : ∀ X Y : E, Nonempty (X ⟶ Y)) (F G : A ⥤ E) : F ≅ G :=
  NatIso.ofComponents (fun _ => iso_of_both_ways (hE _ _).some (hE _ _).some)
    fun _ => Subsingleton.elim _ _

/-- **`Grothendieck.forget` is an equivalence when every fibre is codiscrete** — a codiscrete fibre
leaves a morphism nothing to remember beyond its base. -/
theorem isEquivalence_grothendieck_forget {J : Type*} [Category J] (F : J ⥤ Cat)
    (hthin : ∀ j, Quiver.IsThin (F.obj j)) (hne : ∀ (j : J) (a b : F.obj j), Nonempty (a ⟶ b))
    (a₀ : ∀ j, F.obj j) : (Grothendieck.forget F).IsEquivalence := by
  haveI : (Grothendieck.forget F).Faithful := by
    constructor
    intro _ Y _ _ h
    haveI := hthin Y.base
    exact Grothendieck.ext _ _ h (Subsingleton.elim _ _)
  haveI : (Grothendieck.forget F).Full := ⟨fun {_ Y} u => ⟨⟨u, (hne Y.base _ _).some⟩, rfl⟩⟩
  haveI : (Grothendieck.forget F).EssSurj := ⟨fun j => ⟨⟨j, a₀ j⟩, ⟨Iso.refl _⟩⟩⟩
  exact Functor.IsEquivalence.mk

/-! ## The data: one object, one involution -/

/-- The twist: `ℤ/2`, written multiplicatively. -/
abbrev Tw : Type := Multiplicative (ZMod 2)

/-- The base: one object whose endomorphisms are `ℤ/2`.  `Over d` has one object per group element
and `Over.map` of the involution swaps them — which is the twist the comparison absorbs. -/
abbrev Loop : Type := SingleObj Tw

/-- The involution. -/
def twist : SingleObj.star Tw ⟶ SingleObj.star Tw := Multiplicative.ofAdd (1 : ZMod 2)

theorem twist_ne_id : twist ≠ 𝟙 (SingleObj.star Tw) := fun h =>
  absurd ((@ofAdd_eq_one (ZMod 2) _ 1).mp h) (by decide)

instance isThinOverLoop (d : Loop) : Quiver.IsThin (Over d) := fun _ Z =>
  ⟨fun f g => (Over.forget d).map_injective
    ((cancel_mono Z.hom).mp ((Over.w f).trans (Over.w g).symm))⟩

theorem nonempty_hom_overLoop (d : Loop) (Y Z : Over d) : Nonempty (Y ⟶ Z) :=
  ⟨Over.homMk (Y.hom ≫ inv Z.hom) (by simp)⟩

/-- Nothing is inverted; the twist is already there. -/
abbrev WLoop : MorphismProperty Loop := ⊥

theorem WLoop_over_le (d : Loop) :
    WLoop.over (X := d) ≤ MorphismProperty.isomorphisms _ := fun _ _ _ h => h.elim

noncomputable def locEquivLoop (d : Loop) : Over d ≌ (WLoop.over (X := d)).Localization :=
  equivLocalizationOfLeIso _ (WLoop_over_le d)

instance isThinLocLoop (d : Loop) : Quiver.IsThin (WLoop.over (X := d)).Localization :=
  isThin_of_equiv (locEquivLoop d)

theorem nonempty_hom_locLoop (d : Loop) (A B : (WLoop.over (X := d)).Localization) :
    Nonempty (A ⟶ B) :=
  nonempty_hom_of_equiv (locEquivLoop d) (nonempty_hom_overLoop d) A B

/-- Both 0-cells are read at the top of the slice. -/
noncomputable def evalLoop (d : Loop) : GenObj Gen₂ ⥤q (WLoop.over (X := d)).Localization where
  obj _ := (WLoop.over (X := d)).Q.obj (Over.mk (𝟙 d))
  map _ := 𝟙 _

noncomputable def presentsLoop (d : Loop) :
    Presents P₂ ((WLoop.over (X := d)).Localization) :=
  ⟨P₂.desc (evalLoop d) fun _ => Subsingleton.elim _ _,
    isEquivalence_of_codiscrete nonempty_hom_presented₂ (nonempty_hom_locLoop d) ⟨⟨false⟩⟩ _⟩

/-- The constant family: the base acts on the slice polygraph trivially, which is what the twist has
nowhere to go into. -/
def PLoop : Loop ⥤ Polygraph.{0, 0} := (Functor.const Loop).obj P₂

/-- The terminal presheaf: `∫X` is the loop again. -/
def XLoop : Loopᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

/-- **The comparison, as an isomorphism** — the slice is codiscrete, so this is the only one there
is, and every equation between comparisons holds (`subsingleton_natTrans_isThin`). -/
noncomputable def kappaLoop {d' d : Loop} (f : d' ⟶ d) :
    (PLoop.map f).functor ⋙ (presentsLoop d).E ≅ (presentsLoop d').E ⋙ overMapLoc WLoop f :=
  natIsoOfCodiscrete (nonempty_hom_locLoop d) _ _

/-- **…and there is only one comparison**, so every equation a cocycle or normalisation condition
could impose on `kappaLoop` holds, and no such condition cuts this data out. -/
theorem kappaLoop_unique {d' d : Loop} (f : d' ⟶ d)
    (α β : (PLoop.map f).functor ⋙ (presentsLoop d).E ⟶
      (presentsLoop d').E ⋙ overMapLoc WLoop f) : α = β :=
  Subsingleton.elim _ _

/-- **…but the strict comparison fails**: the 0-cell names the top of the slice, and the involution
pushes the top to itself twisted. -/
theorem not_hP_loop : ¬ ∀ {d' d : Loop} (f : d' ⟶ d),
    (PLoop.map f).functor ⋙ (presentsLoop d).E
      = (presentsLoop d').E ⋙ overMapLoc WLoop f := by
  intro h
  -- both sides are the top of the slice, read at the 0-cell `false`; `Over.mk (𝟙 _)` pushed along
  -- the involution is `Over.mk twist`
  have hobj : (WLoop.over (X := SingleObj.star Tw)).Q.obj (Over.mk (𝟙 (SingleObj.star Tw)))
      = (overMapLoc WLoop twist).obj
        ((WLoop.over (X := SingleObj.star Tw)).Q.obj (Over.mk (𝟙 (SingleObj.star Tw)))) :=
    Functor.congr_obj (h twist) (⟨⟨false⟩⟩ : P₂.presented)
  exact twist_ne_id (congrArg (fun Y : Over (SingleObj.star Tw) => Y.hom)
    ((Localization.Construction.objEquiv _).injective
      (hobj.trans (Polygraph.overMapLoc_top WLoop (Over.mk twist))))).symm

/-! ## The colimit, and what it cannot present -/

/-- The one element of `∫X`. -/
def eltLoop : (XLoop.Elements)ᵒᵖ := op ⟨op (SingleObj.star Tw), PUnit.unit⟩

theorem eq_eltLoop (c : (XLoop.Elements)ᵒᵖ) : c = eltLoop := rfl

/-- An arrow of `∫X` for each group element. -/
def eltHom (t : SingleObj.star Tw ⟶ SingleObj.star Tw) : eltLoop ⟶ eltLoop :=
  (CategoryOfElements.homMk eltLoop.unop eltLoop.unop t.op rfl).op

theorem eltHom_inj {s t : SingleObj.star Tw ⟶ SingleObj.star Tw} (h : eltHom s = eltHom t) :
    s = t :=
  congrArg (fun u : eltLoop ⟶ eltLoop => u.unop.val.unop) h

theorem not_isThin_elementsLoop : ¬ Quiver.IsThin ((XLoop.Elements)ᵒᵖ) := fun h =>
  twist_ne_id (eltHom_inj (@Subsingleton.elim _ (h eltLoop eltLoop) (eltHom twist) (eltHom (𝟙 _))))

theorem not_isThin_locLoop :
    ¬ Quiver.IsThin
      ((WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp).Localization) := fun hthin =>
  not_isThin_elementsLoop
    (haveI := hthin; isThin_of_equiv (equivLocalizationOfLeIso
      (WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp) (fun _ _ _ h => h.elim)).symm)

/-- The index category is the loop, and the family is constant, so every leg is the identity. -/
noncomputable def coconeLoop : Cocone (elementsPoly XLoop PLoop) where
  pt := P₂
  ι := { app := fun _ => 𝟙 P₂, naturality := fun _ _ _ => Category.comp_id _ }

noncomputable def isColimitCoconeLoop : IsColimit coconeLoop where
  desc s := s.ι.app eltLoop
  fac s c := by obtain rfl := eq_eltLoop c; exact Category.id_comp _
  uniq s m hm := (Category.id_comp m).symm.trans (hm eltLoop)

/-- **The colimit of the slice polygraphs is `P₂`** — nothing glues the two 0-cells, the twist
having nowhere to act. -/
noncomputable def colimIsoLoop : colimit (elementsPoly XLoop PLoop) ≅ P₂ :=
  (colimit.isColimit _).coconePointUniqueUpToIso isColimitCoconeLoop

/-- **…and `P₂` cannot present the loop**: it presents a thin category, and the loop is not thin.
So no comparison functor whatever is an equivalence, and the conclusion of `presentsSliceColimit`
is false for this data. -/
theorem not_presents_colimLoop :
    IsEmpty (Presents (colimit (elementsPoly XLoop PLoop))
      ((WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp).Localization)) :=
  ⟨fun q => not_isThin_locLoop (isThin_of_equiv (q.ofPolyIso colimIsoLoop).equiv)⟩

/-- **The strict colimit is not the bicolimit, in one statement**: the comparison isomorphism exists
for every arrow of the base, the strict one does not, and the strict colimit cannot present the
target.  The cocycle and normalisation conditions are no obstruction — every equation between
comparisons is a `Subsingleton.elim` here — the missing datum is a cell for `twist`. -/
theorem isoComparison_not_enough :
    (∀ {d' d : Loop} (f : d' ⟶ d), Nonempty ((PLoop.map f).functor ⋙ (presentsLoop d).E
        ≅ (presentsLoop d').E ⋙ overMapLoc WLoop f))
      ∧ (¬ ∀ {d' d : Loop} (f : d' ⟶ d), (PLoop.map f).functor ⋙ (presentsLoop d).E
        = (presentsLoop d').E ⋙ overMapLoc WLoop f)
      ∧ IsEmpty (Presents (colimit (elementsPoly XLoop PLoop))
        ((WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp).Localization)) :=
  ⟨fun f => ⟨kappaLoop f⟩, not_hP_loop, not_presents_colimLoop⟩

/-! ## The same data, presented

The transition polygraph has the cell the strict colimit lacked, and here everything in sight is
invertible: the fibres are codiscrete, so the Grothendieck construction *is* the index
(`isEquivalence_grothendieck_forget`), and both localizations invert isomorphisms only. -/

/-- The loop's slice diagram. -/
abbrev diagLoop : (XLoop.Elements)ᵒᵖ ⥤ Polygraph.{0, 0} := elementsPoly XLoop PLoop

instance isIso_loopOpHom {A B : Loopᵒᵖ} (m : A ⟶ B) : IsIso m :=
  ⟨(inv m.unop).op, Quiver.Hom.unop_inj (IsIso.inv_hom_id m.unop),
    Quiver.Hom.unop_inj (IsIso.hom_inv_id m.unop)⟩

/-- `XLoop` is the terminal presheaf, so an arrow of its elements is its base, and the base is
invertible. -/
instance isIso_eltLoopHom {a b : (XLoop.Elements)ᵒᵖ} (g : a ⟶ b) : IsIso g := by
  refine ⟨(CategoryOfElements.homMk a.unop b.unop (inv g.unop.val) rfl).op, ?_, ?_⟩
  · exact Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _
      (CategoryOfElements.comp_val.trans (IsIso.inv_hom_id g.unop.val)))
  · exact Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _
      (CategoryOfElements.comp_val.trans (IsIso.hom_inv_id g.unop.val)))

/-- The loop's diagram of presented categories. -/
abbrev fibLoop : (XLoop.Elements)ᵒᵖ ⥤ Cat.{0, 0} := diagLoop ⋙ presentedFunctor.{0, 0}

theorem isThin_fibLoop (c : (XLoop.Elements)ᵒᵖ) : Quiver.IsThin (fibLoop.obj c) :=
  inferInstanceAs (Quiver.IsThin P₂.presented)

theorem nonempty_hom_fibLoop (c : (XLoop.Elements)ᵒᵖ) (a b : fibLoop.obj c) : Nonempty (a ⟶ b) :=
  nonempty_hom_presented₂ a b

/-- **The Grothendieck construction of the loop's diagram is the loop** — codiscrete fibres. -/
noncomputable def grEquivLoop : Grothendieck fibLoop ≌ (XLoop.Elements)ᵒᵖ :=
  haveI := isEquivalence_grothendieck_forget fibLoop isThin_fibLoop
    nonempty_hom_fibLoop (fun _ => (⟨⟨false⟩⟩ : P₂.presented))
  (Grothendieck.forget fibLoop).asEquivalence

/-- …and there is nothing left to invert: the base is invertible and so is the fibre. -/
theorem fibrewiseIsosLoop_le :
    Grothendieck.fibrewiseIsos fibLoop ≤ MorphismProperty.isomorphisms (Grothendieck fibLoop) := by
  rintro X Y f hf
  exact show IsIso f from Iso.isIso_hom (Grothendieck.isoMk
    (@asIso _ _ _ _ f.base (isIso_eltLoopHom f.base)) (@asIso _ _ _ _ f.fiber hf))

/-- **The bicolimit of the loop's slice diagram is `B(ZMod 2)`.** -/
noncomputable def bicolimEquivLoop :
    bicolimit fibLoop
      ≌ (WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp).Localization :=
  (equivLocalizationOfLeIso _ fibrewiseIsosLoop_le).symm.trans
    (grEquivLoop.trans
      (equivLocalizationOfLeIso (WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp)
        (fun _ _ _ h => h.elim)))

/-- **The loop data, presented**: the copies with a transition for each arrow of the index present
`B(ZMod 2)`, which no polygraph without a cell for `twist` can (`not_presents_colimLoop`). -/
noncomputable def presentsLoopBicolim :
    Presents (transitionPoly diagLoop)
      ((WLoop.inverseImage (CategoryOfElements.π XLoop).leftOp).Localization) :=
  (presentsBicolimit diagLoop).transport bicolimEquivLoop

/-- …and what it presents is not thin, where the strict colimit's was. -/
theorem not_isThin_presentsLoopBicolim :
    ¬ Quiver.IsThin (transitionPoly diagLoop).presented := fun h =>
  not_isThin_locLoop (haveI := h; isThin_of_equiv presentsLoopBicolim.equiv)

end CategoryTheory
