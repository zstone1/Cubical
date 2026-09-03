import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Machinery/Slice — discrete fibrations, and the slices they identify

`F : C ⥤ D` is a **discrete fibration** when every arrow into `F.obj c` lifts uniquely to an arrow
into `c`; said without choice, when `Over.post F : Over c ⥤ Over (F.obj c)` is an equivalence.  A
morphism property pulled back along `F` is then, on each slice, the pullback of the property on the
slice below (`MorphismProperty.over_inverseImage`, true of any `F`).

The projection of the category of elements of a presheaf is the example.  Mathlib's `Elements` is
the opfibration convention, so the fibration over `C` is `(π X).leftOp`; that bookkeeping lives
here and nowhere else.
-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- Every arrow into `F.obj c` has a unique lift to an arrow into `c`. -/
class Functor.IsDiscreteFibration (F : C ⥤ D) : Prop where
  /-- the slice over `c` *is* the slice over `F.obj c` -/
  isEquivalence_post (c : C) : (Over.post (X := c) F).IsEquivalence

attribute [instance] Functor.IsDiscreteFibration.isEquivalence_post

namespace Functor

instance (F : C ⥤ D) [F.IsEquivalence] : F.IsDiscreteFibration where
  isEquivalence_post _ := inferInstance

instance (F : C ⥤ D) (G : D ⥤ E) [F.IsDiscreteFibration] [G.IsDiscreteFibration] :
    (F ⋙ G).IsDiscreteFibration where
  isEquivalence_post _ := inferInstanceAs (Over.post F ⋙ Over.post G).IsEquivalence

theorem IsDiscreteFibration.of_natIso {F G : C ⥤ D} (e : F ≅ G) [F.IsDiscreteFibration] :
    G.IsDiscreteFibration where
  isEquivalence_post c :=
    haveI : (Over.map (e.hom.app c)).IsEquivalence :=
      inferInstanceAs (Over.mapIso (e.app c)).functor.IsEquivalence
    isEquivalence_of_iso (Over.postCongr (X := c) e)

end Functor

/-- A natural transformation, read at two spellings of the same object.  Generic re-spelling
helper: `rw` matches at `instances` transparency, so a defeq-but-differently-spelled object argument
has to be moved explicitly. -/
theorem natTrans_app_congr {G : Type u₁} [Category.{v₁} G] {H : Type u₂} [Category.{v₂} H]
    {F₁ F₂ : G ⥤ H} (τ : F₁ ⟶ F₂) {Y Z : G} (h : Y = Z) :
    τ.app Y = eqToHom (congrArg F₁.obj h) ≫ τ.app Z ≫ eqToHom (congrArg F₂.obj h).symm := by
  subst h; simp

/-- Pulling a morphism property back to a slice commutes with pulling it back along `F`. -/
theorem MorphismProperty.over_inverseImage (W : MorphismProperty D) (F : C ⥤ D) (c : C) :
    (W.inverseImage F).over (X := c) = W.over.inverseImage (Over.post F) := rfl

namespace CategoryOfElements

variable (X : Cᵒᵖ ⥤ Type w)

/-- **The projection of a category of elements is a discrete fibration**: elements pull back. -/
instance π_leftOp_isDiscreteFibration : ((π X).leftOp).IsDiscreteFibration where
  isEquivalence_post e := by
    have hfull : (Over.post (X := e) (π X).leftOp).Full := by
      constructor
      intro A B f
      -- the triangle over `e`, transposed into `Cᵒᵖ`
      have hcomp : B.hom.unop.val ≫ f.left.op = A.hom.unop.val :=
        congrArg Quiver.Hom.op (Over.w f)
      refine ⟨Over.homMk (homMk _ _ f.left.op ?_).op (Quiver.Hom.unop_inj (ext _ _ _ hcomp)), ?_⟩
      · rw [← map_snd A.hom.unop, ← hcomp]
        simp
      · exact Over.OverMorphism.ext rfl
    have hess : (Over.post (X := e) (π X).leftOp).EssSurj := by
      constructor
      intro Y
      exact ⟨Over.mk (homMk e.unop ⟨op Y.left, X.map Y.hom.op e.unop.2⟩ Y.hom.op rfl).op,
        ⟨Over.isoMk (Iso.refl _)⟩⟩
    exact { }

end CategoryOfElements

end CategoryTheory
