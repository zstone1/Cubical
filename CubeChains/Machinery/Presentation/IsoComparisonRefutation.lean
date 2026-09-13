import CubeChains.Machinery.Presentation.StrictUnitRefutation
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic

/-!
# Machinery/Presentation/IsoComparisonRefutation — `hP` cannot be weakened to an isomorphism

Measured at a base with one object and one involution: the localized slice is codiscrete, so the
comparison exists (`kappaLoop`) and is unique (`kappaLoop_unique`) while the strict `hP` fails
(`not_hP_loop`), and the colimit — here `P₂` (`colimIsoLoop`), which is thin — cannot present the
target (`not_presents_colimLoop`), having no generator for `twist`.  So `presentsSliceColimit`'s
equality-of-functors hypothesis is not weakenable.  What a 0-cell must name on the nose is its
slice *object*; the morphism half is free whenever the slice is thin (`hP_of_naming`).
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

/-- Nothing is inverted; the twist is already there. -/
abbrev WLoop : MorphismProperty Loop := ⊥

instance isThinLocLoop (d : Loop) : Quiver.IsThin (WLoop.over (X := d)).Localization :=
  isThinLocBot (fun _ => inferInstance) d

theorem nonempty_hom_locLoop (d : Loop) (A B : (WLoop.over (X := d)).Localization) :
    Nonempty (A ⟶ B) :=
  nonempty_hom_locBot (fun _ => inferInstance) d A B

noncomputable def presentsLoop (d : Loop) :
    Presents P₂ ((WLoop.over (X := d)).Localization) :=
  presentsBot (fun _ => inferInstance) d

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

end CategoryTheory
