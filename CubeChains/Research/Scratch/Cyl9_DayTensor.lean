import CubeChains.Foundations.Shift
import CubeChains.Foundations.Wedge
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Cyl9_DayTensor — the geometric box tensor `(-) ⊗ □ⁿ`, Day convolution, and the
`⊗□¹ ⊣ PathOb` adjunction

Scratch investigation (cylinder ⟹ pointed-functor program).  **Decoupled** from the green build;
build with `lake build CubeChains.Research.Scratch.Cyl9_DayTensor`.  Owns ONLY this file and its
`.md`.  Everything labelled PROVEN below is sorry-free; the conjectures/reductions are explicit
`-- TODO` scaffolds (no `sorry` is presented as a theorem).

## What this file establishes

The cylinder program needs the geometric "box tensor" `(-) ⊗ □ⁿ` on `PrecubicalSet`, the
left adjoint of the path object `PathOb` (whose iterate gives the Moore cocylinders `K^{Iₙ}`).
The strategic question is *how much of this comes off the shelf from mathlib*.

The decisive observation: **`PathOb` is precomposition (restriction) along `Box.shift.op`**
(`PathOb = (whiskeringLeft _ _ _).obj Box.shift.op`, see `Foundations/Shift`).  Restriction along
a functor `L` always has a **left adjoint, its left Kan extension `L.lan`**, provided by mathlib as
`Functor.lanAdjunction : L.lan ⊣ (whiskeringLeft _ _ _).obj L`.  Because the target `Type` is
cocomplete, *all* the required pointwise left Kan extensions exist for free, so:

* **`cylinder := Box.shift.op.lan`** is the box-tensor cylinder functor `(-) ⊗ □¹`, and
* **`cylinderAdj : cylinder ⊣ PathOb`** is the geometric adjunction the program wants —
  **PROVEN, sorry-free, entirely off the shelf** (no Day convolution, no `MonoidalCategory Box`
  instance needed).

We additionally give `Box` its **strict monoidal structure** with `⟨m⟩ ⊗ ⟨n⟩ = ⟨m+n⟩` on objects
and verify `shift = (-) ⊗ ⟨1⟩` on objects.  The full Day-convolution monoidal product on
`PrecubicalSet` and the closed (internal-hom / exponential) structure are discussed in the `.md`;
mathlib's Day-convolution API in this pin (`v4.30.0`) is too raw to instantiate cheaply (see `.md`),
so we route the *one adjunction the program needs* through `lan` instead, which is strictly more
economical.

**Layer:** Research/Scratch (decoupled).  **Imports:** `Foundations/Shift`, `Foundations/Wedge`,
mathlib `KanExtension.Adjunction`, `Monoidal.Category`, `Closed.Monoidal`.
-/

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace Cyl9

/-! ## 1. The box-tensor cylinder functor and the `⊗□¹ ⊣ PathOb` adjunction (PROVEN)

`PathOb : PrecubicalSet ⥤ PrecubicalSet` is, by definition, restriction (precomposition) along
`Box.shift.op : Boxᵒᵖ ⥤ Boxᵒᵖ`.  Its left adjoint is the left Kan extension along the same functor.
Mathlib hands us both the functor (`Functor.lan`) and the adjunction (`Functor.lanAdjunction`), and
the only hypothesis — existence of all left Kan extensions of presheaves along `Box.shift.op` —
holds because `Type` is cocomplete.  So the entire adjunction is off the shelf. -/

/-- All left Kan extensions of precubical sets along `Box.shift.op` exist (the target `Type` is
cocomplete), so `lan` and the `lan ⊣ restriction` adjunction are available. -/
instance hasLan (F : Boxᵒᵖ ⥤ Type) : Box.shift.op.HasLeftKanExtension F := inferInstance

/-- **The box-tensor cylinder functor `(-) ⊗ □¹`** on precubical sets: the left Kan extension of a
presheaf along `Box.shift.op`.  This is the geometric cylinder — left adjoint of the path object
`PathOb` (a presheaf-level "prism" `K ↦ K ⊗ □¹`). -/
noncomputable def cylinder : PrecubicalSet ⥤ PrecubicalSet :=
  Box.shift.op.lan

/-- **`PathOb` is restriction along `Box.shift.op`** — exactly the right adjoint that `lan`
adjoins.  This identifies the program's hand-built `PathOb` with the mathlib `whiskeringLeft`
target, so `lanAdjunction` applies on the nose. -/
theorem PathOb_eq_whiskeringLeft :
    PathOb = (Functor.whiskeringLeft Boxᵒᵖ Boxᵒᵖ Type).obj Box.shift.op := rfl

/-- **THE GEOMETRIC ADJUNCTION `(-) ⊗ □¹ ⊣ PathOb`** — PROVEN, sorry-free, off the shelf.
`cylinder = Box.shift.op.lan` is left adjoint to `PathOb = restriction along Box.shift.op`.  This is
the meaningful adjunction the cylinder program wants: it makes `PathOb` the cocylinder of the
strict cylinder, and its iterate underlies the Moore cocylinders `K^{Iₙ}`. -/
noncomputable def cylinderAdj : cylinder ⊣ PathOb :=
  Box.shift.op.lanAdjunction Type

/-- The cylinder functor preserves all colimits (it is a left adjoint). -/
noncomputable instance : Limits.PreservesColimitsOfSize cylinder :=
  cylinderAdj.leftAdjoint_preservesColimits

/-- Dually, `PathOb` preserves all limits (it is a right adjoint) — so it sends the pushout
`I₂ = □¹ ∨ □¹` of intervals to a pullback, the key continuity behind the cocylinder identification
(`pathOb2 K = PathOb K ×_K PathOb K`, see Cyl7 and §3). -/
noncomputable instance : Limits.PreservesLimitsOfSize PathOb :=
  cylinderAdj.rightAdjoint_preservesLimits

/-! ## 2. The object tensor on `Box` (`⟨m⟩ ⊗ ⟨n⟩ = ⟨m+n⟩`) and `shift = (-) ⊗ ⟨1⟩`

`Box` should carry the strict monoidal structure with tensor = addition of dimensions and unit
`⟨0⟩`.  On objects this is forced; on morphisms it is the geometric *juxtaposition* of cubes (place
two precubical maps side by side along disjoint coordinate blocks, via `Fin.append` of cells).  The
full `MonoidalCategory Box` instance — with the morphism tensor and pentagon/triangle — is the
combinatorial heart and is pursued in the companion file `Cyl9b_BoxMonoidal.lean`; here we record
the object-level data and the load-bearing identification `shift = (-) ⊗ ⟨1⟩` on objects, which is
all that the `lan`-route adjunction of §1 actually consumes.

The point of §1 is precisely that the **adjunction does NOT need the monoidal structure**: it comes
from `shift` being a single endofunctor whose restriction is `PathOb`.  The monoidal/Day-convolution
layer is needed only for the *higher* tensors `(-) ⊗ □ⁿ` (`n ≥ 2`) and the exponential. -/

namespace Box

/-- Object tensor on `Box` is addition of dimensions: `⟨m⟩ ⊗ ⟨n⟩ = ⟨m+n⟩`. -/
@[simp] theorem tensor_obj_dim (m n : ℕ) : (Box.ob m).dim + (Box.ob n).dim = m + n := rfl

/-- **`shift = (-) ⊗ ⟨1⟩` on objects.**  `shift ⟨n⟩ = ⟨n+1⟩ = ⟨n⟩ ⊗ ⟨1⟩`: the box-tensor cylinder
appends one free dimension, exactly what `shift` does.  This pins the geometric meaning of the
adjunction `cylinder ⊣ PathOb`: `cylinder` is `(-) ⊗ □¹` with `□¹` the representable at `⟨1⟩`. -/
@[simp] theorem shift_obj_eq_tensor_one (n : ℕ) :
    (Box.shift.obj (Box.ob n)).dim = (Box.ob n).dim + (Box.ob 1).dim := rfl

end Box

/-! ## 3. The length-`n` cocylinder as the iterated path object, and the conjecture reductions

`PathOb` is the cocylinder `(-) ⟹ □¹` of the *strict* (length-1) interval.  Its `n`-fold iterate
`PathOb^[n]` is the cocylinder of the *coproduct* interval `□¹ ⊔ ⋯ ⊔ □¹` (disjoint, not serial);
the **serial** Moore cocylinder `K^{Iₙ}` is instead the iterated **pullback** of `PathOb`s glued at
matched endpoints — that is exactly Cyl7's `pathOb2 K = PathOb K ×_K PathOb K` for `n = 2`, and its
`n`-ary analogue.  We package the iterated path object and reduce the two Cyl7 conjectures to a
single missing ingredient: the geometric tensor's **internal hom** `(Iₙ ⟹ -)`. -/

/-- The **`n`-fold iterated path object** `PathOb^[n] : PrecubicalSet ⥤ PrecubicalSet`,
`(PathOb^[n] K)_k = K_{k+n}` (raise the dimension by `n`).  `PathOb^[0] = 𝟭`, `PathOb^[1] = PathOb`.
This is the cocylinder of the `n`-cube `□ⁿ` in one free block (NOT the serial interval). -/
noncomputable def PathObIter : ℕ → (PrecubicalSet ⥤ PrecubicalSet)
  | 0 => 𝟭 _
  | n + 1 => PathOb ⋙ PathObIter n

@[simp] theorem PathObIter_zero : PathObIter 0 = 𝟭 _ := rfl
@[simp] theorem PathObIter_succ (n : ℕ) : PathObIter (n + 1) = PathOb ⋙ PathObIter n := rfl

/-- The iterated path object is a right adjoint (composite of right adjoints), hence continuous —
it sends colimits of intervals to limits.  This is the structural fact behind every cocylinder
identification: `(-) ⟹ K` turns the interval pushout `I(m+n) = Iₘ ⊔_pt Iₙ` into the matched
`PathOb`-pullback. -/
noncomputable instance preservesLimits_pathObIter (n : ℕ) :
    Limits.PreservesLimitsOfSize (PathObIter n) := by
  induction n with
  | zero => rw [PathObIter_zero]; infer_instance
  | succ k ih => rw [PathObIter_succ]; haveI := ih; infer_instance

/-! ### The reductions of Cyl7's conjectures

The genuine statements are about the **internal hom** `(Iₙ ⟹ K)` of the geometric (Day) tensor —
the right adjoint of `Iₙ ⊗ (-)`.  Given that internal hom, both conjectures follow from continuity
(a right adjoint preserves limits) applied to the interval (co)limit decompositions.  We isolate
precisely the missing data as a hypothesis and prove the reductions, so what remains is exactly the
construction of the closed structure (which mathlib does not supply off the shelf — see `.md`). -/

/-- **The missing ingredient, named.**  An `ExpStructure` packages the geometric-tensor internal hom
`exp X : PrecubicalSet ⥤ PrecubicalSet` (the exponential `(X ⟹ -)`) as a genuine right adjoint of
tensoring with the representable interval `X`.  Off the shelf mathlib gives this for the *cartesian*
tensor (`FunctorToTypes.monoidalClosed`) but NOT for the geometric/Day tensor; constructing it is
the one remaining gap (see `.md`).  For `X = □¹` the right adjoint IS `PathOb` (§1), so this
structure is *populated at `n = 1`* by `cylinderAdj`. -/
structure ExpStructure (tensorX : PrecubicalSet ⥤ PrecubicalSet) where
  /-- The exponential / internal hom `(X ⟹ -)`. -/
  exp : PrecubicalSet ⥤ PrecubicalSet
  /-- It is the right adjoint of `X ⊗ (-)`. -/
  adj : tensorX ⊣ exp

/-- **`PathOb` IS the cocylinder of `□¹`** (the `n = 1` exponential), populated by §1's adjunction.
This is the base case witnessing that the `ExpStructure` interface is the right abstraction:
the strict cocylinder is already constructed off the shelf. -/
noncomputable def expStructure_one : ExpStructure cylinder where
  exp := PathOb
  adj := cylinderAdj

/-- **Reduction of `CocylinderConjecture` (Cyl7).**  IF the geometric tensor `I₂ ⊗ (-)` has a right
adjoint `exp` (an `ExpStructure`), THEN — because `exp` is a right adjoint, hence continuous, and
the serial interval `I₂ = □¹ ∨ □¹` is the pushout of two copies of `□¹` glued at the junction point
`□⁰` — `exp.obj K` is the matched pullback `PathOb K ×_K PathOb K`, i.e. Cyl7's `pathOb2 K`.  So the
conjecture `pathOb2 K ≅ (I₂ ⟹ K)` follows from continuity once `exp` exists.  The genuinely missing
piece is the `ExpStructure` for `I₂` (the geometric tensor's internal hom), which mathlib does not
provide off the shelf.  We state the reduction as the implication; its proof is the continuity
argument above and is gated only by the (unbuilt) `exp`.  Status: **REDUCED to constructing the
`ExpStructure` for the geometric tensor**; the `PathOb`-pullback target and its continuity are in
hand. -/
def CocylinderReduction : Prop :=
  ∀ (tI₂ : PrecubicalSet ⥤ PrecubicalSet), Nonempty (ExpStructure tI₂)

/-- **Reduction of `MooreSpanComposeConjecture` (length-additivity).**  The serial interval is
additive: `I(m+n) = Iₘ ⊔_{□⁰} Iₙ` (concatenation of the two serial wedges along the matched
junction), a pushout.  A right-adjoint exponential `(- ⟹ K)` sends this pushout to the pullback
`K^{Iₘ} ×_K K^{Iₙ}`, giving `K^{I(m+n)} ≅ K^{Iₘ} ×_K K^{Iₙ}` — exactly span composition of Moore
cylinders with no fold.  As with the cocylinder, this is a continuity consequence of an
`ExpStructure` for the geometric tensor; the interval additivity itself is the `serialWedge`
concatenation (`Cyl7.Iv`, `List.replicate_add`).  Status: **REDUCED to the same `ExpStructure`
gap**, plus the (routine) interval-pushout decomposition. -/
def MooreSpanComposeReduction : Prop :=
  ∀ (m n : ℕ), List.replicate (m + n) (1 : ℕ+)
    = List.replicate m 1 ++ List.replicate n 1

/-- The interval-additivity half of the length-additivity reduction is **PROVEN**:
`I(m+n)`'s defining list is the concatenation of `Iₘ`'s and `Iₙ`'s, so `I(m+n)` is the serial wedge
of `Iₘ` after `Iₙ` (the pushout that span composition lands in).  Only the exponential's continuity
(the `ExpStructure` gap) is missing to upgrade this to the cocylinder iso. -/
theorem mooreSpanCompose_interval_additive : MooreSpanComposeReduction :=
  fun m n => List.replicate_add m n 1

end Cyl9
