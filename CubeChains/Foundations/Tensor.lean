import CubeChains.Foundations.CubeConcat
import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Foundations/Tensor — the Day-convolution geometric tensor on `PrecubicalSet`

The **geometric tensor** `⊗` on precubical sets, built by Day convolution of the
cube-concatenation monoidal structure on `Box` (`Foundations/CubeConcat.lean`,
`⟨m⟩ ⊗ ⟨n⟩ = ⟨m + n⟩`, unit `⟨0⟩ = □⁰`).  This is geometric juxtaposition of cubes
extended cocontinuously to all presheaves, NOT the pointwise (cartesian-product)
monoidal structure that mathlib already puts on `Boxᵒᵖ ⥤ Type`.

**Layer:** Foundations.  **Imports:** `CubeConcat` (`MonoidalCategory Box`), mathlib
`DayConvolution.DayFunctor`, `Monoidal.Opposite`, `Monoidal.Closed.{Types,Braided}`,
`Monoidal.Transport`.

## Why the `DayFunctor` type synonym is canonical here

`PrecubicalSet := Boxᵒᵖ ⥤ Type` *already* carries mathlib's pointwise
`MonoidalCategory` instance (`functorCategoryMonoidal`, tensor `x ↦ F x × G x`),
because `Type` is monoidal.  Registering a *second* `MonoidalCategory PrecubicalSet`
(the Day/geometric one) would create an instance diamond.  Mathlib avoids exactly
this by giving the Day-convolution structure to the one-field type synonym
`Boxᵒᵖ ⊛⥤ Type` (`DayFunctor Boxᵒᵖ Type`) instead.  We follow that: the geometric
`⊗` lives on `PSetDay := Boxᵒᵖ ⊛⥤ Type`, and `pSetDayEquiv : PSetDay ≌ PrecubicalSet`
is the bridge.  Downstream (the cylinder stage) should work in `PSetDay` and
transport to `PrecubicalSet` via `pSetDayEquiv` only when feeding the topos-level
APIs, mirroring how `Chains/Slice.lean` stays inside `Over`.

## What the Day-convolution `MonoidalCategory (Boxᵒᵖ ⊛⥤ Type)` needs (all discharged)

* `MonoidalCategory Boxᵒᵖ` — free from `MonoidalCategory Box` via `monoidalCategoryOp`.
* pointwise left Kan extensions along `tensor Boxᵒᵖ` and along the unit — these are
  colimits of small diagrams in `Type 0`, which `Type 0` has (`Box` is small).
* `tensorLeft v` / `tensorRight v` in `Type` preserve those colimits — both are left
  adjoints (`Type` is cartesian closed: `Types.tensorProductAdjunction` and
  `Closed/Braided.lean`'s `(tensorRight A).IsLeftAdjoint`), and left adjoints preserve
  all colimits (`Adjunction.leftAdjoint_preservesColimits`).
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.DayFunctor

namespace Foundations.Tensor

/-! ### The Day-convolution category of precubical sets -/

/-- `Box` with the opposite of the cube-concatenation monoidal structure: the Day
base category.  Free from `MonoidalCategory Box` via mathlib's `monoidalCategoryOp`. -/
example : MonoidalCategory Boxᵒᵖ := inferInstance

/-- The Day-convolution category of precubical sets: the type synonym
`Boxᵒᵖ ⊛⥤ Type` (= `DayFunctor Boxᵒᵖ Type`) carrying the **geometric** (Day) tensor.
This is where the geometric `⊗` lives (see the module docstring on why this, not a
second instance on `PrecubicalSet`). -/
abbrev PSetDay : Type 1 := Boxᵒᵖ ⊛⥤ Type

/-- The geometric (Day-convolution) `MonoidalCategory` on `PSetDay`.  Confirms the
mathlib instance fires once `MonoidalCategory Boxᵒᵖ` and the cartesian-closed `Type`
preservation/Kan-extension instances are in scope. -/
noncomputable example : MonoidalCategory PSetDay := inferInstance

/-- The tautological bridge `PSetDay ≌ PrecubicalSet`: the geometric tensor on the
left transports to the usual presheaf category on the right. -/
noncomputable def pSetDayEquiv : PSetDay ≌ PrecubicalSet := DayFunctor.equiv Boxᵒᵖ Type

/-! ### The geometric tensor bifunctor -/

/-- The geometric tensor as a bifunctor `PSetDay ⥤ PSetDay ⥤ PSetDay`.  This is the
`MonoidalCategory.tensor` of the Day-convolution structure (the geometric `⊗`). -/
noncomputable def tensorPSetDay : PSetDay ⥤ PSetDay ⥤ PSetDay :=
  curriedTensor PSetDay

/-! ### Interval and point objects -/

/-- The geometric **interval** `□¹` as an object of `PSetDay`: the Day-wrapped
representable presheaf on the 1-cube `⟨1⟩`.  `yoneda : Box ⥤ PrecubicalSet`, so the
argument is the box `⟨1⟩` itself. -/
noncomputable def interval : PSetDay := DayFunctor.mk (yoneda.obj (Box.ob 1))

/-- The geometric **point** `□⁰` as an object of `PSetDay`: the Day-wrapped
representable presheaf on the 0-cube `⟨0⟩`. -/
noncomputable def point : PSetDay := DayFunctor.mk (yoneda.obj (Box.ob 0))

/-! ### Sanity lemmas

These are deliberately cheap (`rfl`-level): they pin the underlying presheaves of
`interval`/`point` and the action of the bifunctor handle, so the cylinder stage can
read off exactly what `X ⊗ □¹` unfolds to. -/

/-- `pSetDayEquiv` carries the geometric interval to the topos-level representable
`□¹ = yoneda.obj ⟨1⟩` (it just forgets the `DayFunctor` wrapper). -/
theorem pSetDayEquiv_interval :
    pSetDayEquiv.functor.obj interval = yoneda.obj (Box.ob 1) := rfl

/-- `pSetDayEquiv` carries the geometric point to the topos-level representable
`□⁰ = yoneda.obj ⟨0⟩`. -/
theorem pSetDayEquiv_point :
    pSetDayEquiv.functor.obj point = yoneda.obj (Box.ob 0) := rfl

/-- The geometric tensor as a bifunctor agrees with `MonoidalCategory`'s `⊗`: the
handle `tensorPSetDay` applied to `X` and `Y` is the monoidal tensor `X ⊗ Y`.  This
is the `rfl` that the cylinder stage will use to identify `tensorPSetDay.obj X` with
`tensorRight`-style cylinders. -/
theorem tensorPSetDay_obj_obj (X Y : PSetDay) :
    (tensorPSetDay.obj X).obj Y = X ⊗ Y := rfl

/-- The geometric **cylinder** functor `- ⊗ □¹`, packaged as `tensorRight interval`.
(The cylinder stage will decompose its cells; here we only record that it *is* the
right-tensoring with the interval, definitionally.) -/
noncomputable def cyl : PSetDay ⥤ PSetDay := tensorRight interval

/-- `cyl X` is `X ⊗ □¹`, definitionally — the precise object the cylinder stage works
with. -/
theorem cyl_obj (X : PSetDay) : cyl.obj X = X ⊗ interval := rfl

/-! ## Next stage: cylinder

The cylinder cell-decomposition is the follow-up stage and is intentionally NOT
built here.  Downstream the cylinder is the functor `cyl = - ⊗ □¹` on `PSetDay`
(`cyl.obj X = X ⊗ interval`, see `cyl`/`cyl_obj` above), with the two end-inclusions
`□⁰ ⟶ □¹` lifted from the cofaces `⟨0⟩ ⟶ ⟨1⟩` of `Box`, transported to
`PrecubicalSet` through `pSetDayEquiv` when the topos-level mono/sieve API is needed.
The combinatorial input the cylinder stage must supply is the cell-decomposition of
`(X ⊗ □¹)` — an `m`-cell as a cell of `X` annotated with an interval coordinate — plus
the mono/disjointness of the two ends; none of that is attempted here.
-/

end Foundations.Tensor
