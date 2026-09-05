import CubeChains.Machinery.Cube.BoxMonoidal
import CubeChains.Precubical.Basic.Bipointed
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Machinery/DayTensor

The **geometric (parallel) product** of precubical sets: Day convolution of `Boxᵒᵖ ⥤ Type`
along the parallel tensor of `Box` (`Machinery/Cube/BoxMonoidal`).

The monoidal structure is mathlib's, on the type synonym `Boxᵒᵖ ⊛⥤ Type`
(`MonoidalCategory.DayFunctor`) — the plain functor category already carries the *pointwise*
monoidal structure, so Day convolution has to live on a synonym.  All hypotheses of
`monoidalOfHasDayConvolutions` hold for `V = Type` off the shelf (cocomplete; cartesian closed,
so `tensorLeft`/`tensorRight` are left adjoints).

What mathlib does not (yet) provide is that *Yoneda is strong monoidal*: that the convolution of
representables is the representable at the tensor.  `cubeDayIso` supplies it,

    □m ⊛ □n  ≅  □(m+n),        η (f, g)  ↦  f ⊗ₘ g

the Day unit `η` sending a pair of cube maps to the concatenation of their sign vectors.  The
proof is the universal property: mathlib's `Functor.CorepresentableBy`, read through the
universal element (`elem`/`desc`/`hom_ext`) in the shape `IsLeftKanExtension` wants.

GOTCHA: morphisms of `Type` are the bundled `TypeCat.Hom`, so functions must be wrapped with `↾`
and applications go through `ConcreteCategory.hom`.
-/

open CategoryTheory Opposite MonoidalCategory Limits
open scoped MonoidalCategory.DayFunctor MonoidalCategory.ExternalProduct

universe v u₁ u₂

namespace CategoryTheory.Functor.CorepresentableBy

variable {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]
variable {F : A ⥤ Type v} {G : B ⥤ Type v} {p : A} {q : B}

/-- The universal element `homEquiv (𝟙 p)`. -/
def elem (e : F.CorepresentableBy p) : F.obj p := e.homEquiv (𝟙 p)

/-- **Yoneda for a corepresentable**: a map out of `F` is its value at the universal element
(`descEquiv_apply`). -/
def descEquiv (e : F.CorepresentableBy p) (H : A ⥤ Type v) : (F ⟶ H) ≃ H.obj p :=
  (e.toIso.homCongr (Iso.refl H)).symm.trans coyonedaEquiv

@[simp] theorem descEquiv_apply (e : F.CorepresentableBy p) {H : A ⥤ Type v} (γ : F ⟶ H) :
    e.descEquiv H γ = γ.app p e.elem := by
  simp [descEquiv, elem, coyonedaEquiv_apply, toIso, corepresentableByEquiv]

/-- Every element of `H.obj p` extends to a map out of `F`. -/
def desc (e : F.CorepresentableBy p) {H : A ⥤ Type v} (t : H.obj p) : F ⟶ H :=
  (e.descEquiv H).symm t

theorem desc_elem (e : F.CorepresentableBy p) {H : A ⥤ Type v} (t : H.obj p) :
    (e.desc t).app p e.elem = t := by
  rw [← descEquiv_apply]; exact (e.descEquiv H).apply_symm_apply t

theorem hom_ext (e : F.CorepresentableBy p) {H : A ⥤ Type v} (γ δ : F ⟶ H)
    (h : γ.app p e.elem = δ.app p e.elem) : γ = δ :=
  (e.descEquiv H).injective (by simpa using h)

/-- The external product of two corepresentables is corepresented by the pair. -/
def prod (e : F.CorepresentableBy p) (f : G.CorepresentableBy q) :
    (F ⊠ G).CorepresentableBy (p, q) where
  homEquiv := e.homEquiv.prodCongr f.homEquiv
  homEquiv_comp g h := Prod.ext (e.homEquiv_comp g.1 h.1) (f.homEquiv_comp g.2 h.2)

end CategoryTheory.Functor.CorepresentableBy

namespace CubeDay

variable {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]

/-- **The left Kan extension of a corepresentable is the corepresentable at the image point.**
Both hom-sets are `H.obj (T.obj p)` and the comparison is the identity. -/
theorem isLeftKanExtension_of_corepBy {T : A ⥤ B} {F : A ⥤ Type v} {G : B ⥤ Type v} {p : A}
    (cF : F.CorepresentableBy p) (cG : G.CorepresentableBy (T.obj p)) (α : F ⟶ T ⋙ G)
    (hα : α.app p cF.elem = cG.elem) : G.IsLeftKanExtension α := by
  have fac : ∀ E : Functor.LeftExtension T F,
      (Functor.LeftExtension.mk G α).hom ≫
        ((Functor.whiskeringLeft A B (Type v)).obj T).map
          (cG.desc (E.hom.app p cF.elem)) = E.hom := by
    intro E
    refine cF.hom_ext _ _ ?_
    rw [NatTrans.comp_app, CategoryTheory.comp_apply]
    change (cG.desc (E.hom.app p cF.elem)).app (T.obj p) (α.app p cF.elem) = _
    rw [hα, cG.desc_elem]
  refine ⟨⟨IsInitial.ofUniqueHom
    (fun E => StructuredArrow.homMk (cG.desc (E.hom.app p cF.elem)) (fac E)) ?_⟩⟩
  intro E m
  refine StructuredArrow.hom_ext _ _ ?_
  change m.right = cG.desc (E.hom.app p cF.elem)
  refine cG.hom_ext _ _ ?_
  rw [cG.desc_elem, ← hα]
  have hw := ConcreteCategory.congr_hom (NatTrans.congr_app (StructuredArrow.w m) p) cF.elem
  rw [NatTrans.comp_app, CategoryTheory.comp_apply] at hw
  exact hw

/-! ### The two corepresentability witnesses -/

variable {C : Type u₁} [Category.{v} C]

/-- Yoneda: `yoneda.obj X` is corepresented by `op X`, universal element `𝟙 X`. -/
def corepYoneda (X : C) : (yoneda.obj X : Cᵒᵖ ⥤ Type v).CorepresentableBy (op X) where
  homEquiv {q} := opEquiv (op X) q

/-- Two-variable Yoneda: the external product of two representables is corepresented by the
pair of objects, universal element the pair of identities. -/
def corepExtProd (X Y : C) :
    ((yoneda.obj X : Cᵒᵖ ⥤ Type v) ⊠ (yoneda.obj Y)).CorepresentableBy (op X, op Y) :=
  (corepYoneda X).prod (corepYoneda Y)

end CubeDay

/-! ## The geometric product of the standard cubes -/

namespace Box

open StdCube CubeDay

/-- The Day-convolution unit at two representable cubes: a pair of cube maps goes to their
**parallel tensor** (concatenation of sign vectors).

    □m(x) × □n(y)  ⟶  □(m+n)(x ⊗ y),        (f, g) ↦ f ⊗ₘ g
-/
def cubeDayUnit (m n : ℕ) :
    (yoneda.obj ▫m : Boxᵒᵖ ⥤ Type) ⊠ (yoneda.obj ▫n) ⟶
      tensor Boxᵒᵖ ⋙ yoneda.obj ▫(m + n) where
  app q := ↾fun (fg : (q.1.unop ⟶ ▫m) × (q.2.unop ⟶ ▫n)) => fg.1 ⊗ₘ fg.2
  naturality := fun q q' uv => by
    refine ConcreteCategory.hom_ext _ _ (fun fg => ?_)
    change (uv.1.unop ≫ (fg : (q.1.unop ⟶ ▫m) × (q.2.unop ⟶ ▫n)).1) ⊗ₘ (uv.2.unop ≫ fg.2)
      = (uv.1.unop ⊗ₘ uv.2.unop) ≫ (fg.1 ⊗ₘ fg.2)
    rw [MonoidalCategory.tensorHom_comp_tensorHom]

@[simp] theorem cubeDayUnit_app (m n : ℕ) (q : Boxᵒᵖ × Boxᵒᵖ)
    (fg : (q.1.unop ⟶ ▫m) × (q.2.unop ⟶ ▫n)) :
    (cubeDayUnit m n).app q fg = fg.1 ⊗ₘ fg.2 := rfl

theorem cubeDayUnit_app_elem (m n : ℕ) :
    (cubeDayUnit m n).app (op ▫m, op ▫n) ((corepExtProd ▫m ▫n).elem)
      = (corepYoneda (▫m ⊗ ▫n)).elem :=
  MonoidalCategory.id_tensorHom_id ▫m ▫n

instance cubeIsLan (m n : ℕ) :
    (yoneda.obj ▫(m + n) : Boxᵒᵖ ⥤ Type).IsLeftKanExtension (cubeDayUnit m n) :=
  isLeftKanExtension_of_corepBy (T := tensor Boxᵒᵖ) (corepExtProd ▫m ▫n)
    (corepYoneda (▫m ⊗ ▫n)) _ (cubeDayUnit_app_elem m n)

/-- The representable `□(m+n)` *is* a Day convolution of `□m` and `□n`. -/
@[reducible] noncomputable def cubeDayConv (m n : ℕ) :
    DayConvolution (yoneda.obj ▫m : Boxᵒᵖ ⥤ Type) (yoneda.obj ▫n) where
  convolution := yoneda.obj ▫(m + n)
  unit := cubeDayUnit m n
  isPointwiseLeftKanExtensionUnit :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ (cubeDayUnit m n)

/-- The Day convolution chosen by the monoidal structure on `Boxᵒᵖ ⊛⥤ Type`. -/
@[reducible] noncomputable def cubeDayConvChosen (m n : ℕ) :
    DayConvolution (yoneda.obj ▫m : Boxᵒᵖ ⥤ Type) (yoneda.obj ▫n) :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolution Boxᵒᵖ Type (Boxᵒᵖ ⊛⥤ Type)
    (DayFunctor.mk (yoneda.obj ▫m)) (DayFunctor.mk (yoneda.obj ▫n))

/-- **`□m ⊗ □n ≅ □(m+n)`** for the underlying presheaves: Day convolution of representables is
the representable at the tensor. -/
noncomputable def cubeDayIso (m n : ℕ) :
    ((DayFunctor.mk (yoneda.obj ▫m) : Boxᵒᵖ ⊛⥤ Type) ⊗
      DayFunctor.mk (yoneda.obj ▫n)).functor ≅ (yoneda.obj ▫(m + n) : Boxᵒᵖ ⥤ Type) :=
  DayConvolution.uniqueUpToIso (cubeDayConvChosen m n) (cubeDayConv m n)

/-- The iso `□m ⊗ □n ≅ □(m+n)` sends the product cell `η (f, g)` to `f ⊗ₘ g`. -/
theorem cubeDayIso_hom_app (m n : ℕ) (q : Boxᵒᵖ × Boxᵒᵖ)
    (fg : (q.1.unop ⟶ ▫m) × (q.2.unop ⟶ ▫n)) :
    (cubeDayIso m n).hom.app (q.1 ⊗ q.2)
        ((DayFunctor.η (DayFunctor.mk (yoneda.obj ▫m)) (DayFunctor.mk (yoneda.obj ▫n))).app q fg)
      = fg.1 ⊗ₘ fg.2 := by
  have h := DayConvolution.unit_uniqueUpToIso_hom (cubeDayConvChosen m n) (cubeDayConv m n)
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app h q) fg
  rw [NatTrans.comp_app, CategoryTheory.comp_apply] at h2
  exact h2

end Box
