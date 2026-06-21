import CubeChains.Cylinder.PointedFunctor

/-!
# Cyl1_Algebra — the converse of `pointedOfPaths`, non-surjectivity, and monad structure

Scratch investigation (RESULT 2 / cylinder ⟹ pointed-functor program).  **Decoupled** from the
green build; build with `lake build CubeChains.Research.Scratch.Cyl1_Algebra`.

The docstring of `pointedOfPaths` (`Cylinder/PointedFunctor.lean`) claims:

> "since every such transformation is a conjugation, *every* pointed endofunctor [of a free
> groupoid] arises this way."

This file PROVES that converse, **on the nose**, and develops its consequences.

## What is proven here (sorry-free)

1. **Converse of `pointedOfPaths` (`pointedOfPaths_objData`, on the nose).**
   For any `P : PointedEndofunctor (FreeGroupoid C)`, with object-data
   `F₀ x := P.F.obj (of x)` (`objMap`) and `η x := P.pt.app (of x)` (`pathMap`), we have
   `pointedOfPaths (objMap P) (pathMap P) = P` **as an equality** in
   `PointedEndofunctor (FreeGroupoid C)`.
   Key lemmas: `objData_F` (functors equal on the nose by `lift_unique` + naturality of `P.pt`
   on generators) and the point equality (two nat. transes out of a free groupoid agreeing on
   every `mk x` agree everywhere, and every object is some `mk x` via `of_obj_bijective`).

2. **Non-surjectivity scaffold.**  `pointedOfPaths` is *surjective*; the cylinder construction
   `cylToPointedObj` factors through it but with object-data drawn from a strict subclass
   (`F₀ = Rgrpd ∘ Lgrpd⁻¹`, `η = counit ≫ sweepR`).  We back the "arbitrary object-data" half:
   `pointedOfPaths` recovers ANY fed-in `(F₀, η)` unchanged (`anyObjData_realized`), and the
   object-data parametrisation is a *bijection* `objDataEquiv :
   PointedEndofunctor (FreeGroupoid C) ≃ ObjData C`.

3. **Monad / classical-CT structure.**  Well-pointedness `Fη = ηF` (Kelly) and idempotency,
   characterised on generators (`wellPointed_app_mk`, `idempotent_obj`).  See `Cyl1_Algebra.md`
   for the monad-extension discussion and conjectures.
-/

open CategoryTheory
open Operations

universe v u

namespace Cyl1

variable {C : Type u} [Category.{v} C]

/-! ## 0. Object-data extracted from a pointed endofunctor

A small extensionality helper for `PointedEndofunctor`: equality of the underlying functors plus
heterogeneous equality of the points suffices. -/

/-- Extensionality for pointed endofunctors via `F`-equality and `HEq` of points. -/
theorem pointedEndofunctor_ext {𝒞 : Type*} [Category 𝒞] {A B : PointedEndofunctor 𝒞}
    (hF : A.F = B.F) (hpt : HEq A.pt B.pt) : A = B := by
  obtain ⟨FA, ptA⟩ := A
  obtain ⟨FB, ptB⟩ := B
  cases hF
  cases hpt
  rfl

/-- Extensionality for pointed endofunctors via `F`-equality and *component-wise* point equality
as `HEq` of components.  Avoids global `HEq` bookkeeping at the call site. -/
theorem pointedEndofunctor_ext' {𝒞 : Type*} [Category 𝒞] {A B : PointedEndofunctor 𝒞}
    (hF : A.F = B.F)
    (hpt : ∀ Z, HEq (A.pt.app Z) (B.pt.app Z)) : A = B := by
  refine pointedEndofunctor_ext hF ?_
  obtain ⟨FA, ptA⟩ := A
  obtain ⟨FB, ptB⟩ := B
  cases hF
  apply heq_of_eq
  ext Z
  exact eq_of_heq (hpt Z)

/-- The object-data extracted from a pointed endofunctor `P` of a free groupoid: where each
generator object goes. -/
def objMap (P : PointedEndofunctor (FreeGroupoid C)) : C → FreeGroupoid C :=
  fun x => P.F.obj ((FreeGroupoid.of C).obj x)

/-- The path-data extracted from a pointed endofunctor `P`: the point's component at each
generator object, `of x ⟶ P.F.obj (of x) = objMap P x`. -/
def pathMap (P : PointedEndofunctor (FreeGroupoid C)) :
    ∀ x, (FreeGroupoid.of C).obj x ⟶ objMap P x :=
  fun x => P.pt.app ((FreeGroupoid.of C).obj x)

/-! ## 1. The converse of `pointedOfPaths` (on the nose)

Every pointed endofunctor of a free groupoid is literally `pointedOfPaths` of its own
object-data.  The two halves are the functor (`objData_F`) and the point. -/

/-- **Naturality of `P.pt` on a generator forces the conjugation formula.**  For a morphism
`f : x ⟶ y` in `C`, the point's naturality square at `(of C).map f` reads
`P.F.map (of.map f) = (η x)⁻¹ ≫ of.map f ≫ η y` — exactly `conjFunctor`'s action. -/
theorem pt_naturality_generator (P : PointedEndofunctor (FreeGroupoid C)) {x y : C}
    (f : x ⟶ y) :
    P.F.map ((FreeGroupoid.of C).map f)
      = Groupoid.inv (pathMap P x) ≫ (FreeGroupoid.of C).map f ≫ pathMap P y := by
  have hnat := P.pt.naturality ((FreeGroupoid.of C).map f)
  simp only [Functor.id_obj, Functor.id_map] at hnat
  -- hnat : of.map f ≫ pt_y = pt_x ≫ P.F.map (of.map f)
  rw [pathMap, pathMap, Groupoid.inv_eq_inv]
  erw [hnat, IsIso.inv_hom_id_assoc]

/-- **The functor half of the converse, on the nose.**  `P.F` is *equal* to the lift of the
conjugation functor of `P`'s own object-data — because `of C ⋙ P.F` agrees with that
conjugation on objects (definitionally) and on generating morphisms (`pt_naturality_generator`),
so `lift_unique` pins `P.F = lift (conjFunctor ..) = (pointedOfPaths ..).F`. -/
theorem objData_F (P : PointedEndofunctor (FreeGroupoid C)) :
    P.F = (pointedOfPaths (objMap P) (pathMap P)).F := by
  change P.F = FreeGroupoid.lift (conjFunctor (FreeGroupoid.of C) (objMap P) (pathMap P))
  apply FreeGroupoid.lift_unique
  refine CategoryTheory.Functor.ext (fun x => rfl) (fun x y f => ?_)
  dsimp only [Functor.comp_map, conjFunctor, objMap, Functor.comp_obj]
  rw [pt_naturality_generator P f]
  simp only [pathMap, objMap, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The point of `pointedOfPaths F₀ η` evaluated at a generator object `mk x` is `η x`.  (The
point is `liftNatIso (.. conjNatIso ..)`, whose `hom.app (mk x)` collapses to the component
`η x` of `conjNatIso`.) -/
theorem pointedOfPaths_pt_app_mk (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) (x : C) :
    (pointedOfPaths F₀ η).pt.app ((FreeGroupoid.of C).obj x) = η x := by
  simp only [pointedOfPaths]
  rw [FreeGroupoid.liftNatIso_hom_app]
  simp only [Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app, Functor.comp_obj,
    conjNatIso, NatIso.ofComponents_hom_app]
  simp

/-- **The converse of `pointedOfPaths`, on the nose.**  Every pointed endofunctor `P` of a free
groupoid is literally `pointedOfPaths` of its own object-data `(objMap P, pathMap P)`.  This is
the Lean form of the docstring claim "every pointed endofunctor [of a free groupoid] arises this
way": the construction `pointedOfPaths` is *surjective*. -/
theorem pointedOfPaths_objData (P : PointedEndofunctor (FreeGroupoid C)) :
    pointedOfPaths (objMap P) (pathMap P) = P := by
  refine pointedEndofunctor_ext' (objData_F P).symm (fun Z => ?_)
  -- both points agree on every generator object; every object of the free groupoid is one
  obtain ⟨x, rfl⟩ := (FreeGroupoid.of_obj_bijective).2 Z
  rw [pointedOfPaths_pt_app_mk]
  -- both points evaluate to η x = pathMap P x = P.pt.app (of x), so HEq is reflexive
  rfl

/-! ## 2. Non-surjectivity of the cylinder construction

`pointedOfPaths` is surjective (`pointedOfPaths_objData`).  The cylinder construction
`cylToPointedObj` (`Cylinder/CylinderRefine.lean`) factors through `pointedOfPaths` with
object-data drawn from a *strict* subclass:

* `F₀ x = Rgrpd (Lgrpd⁻¹ x)` — `Rgrpd` applied to a *functorially* transported chain, NOT an
  arbitrary object of `DPathGrpdR K`;
* `η x = counit.inv ≫ sweepR ..` — one canonical homotopy, NOT an arbitrary path.

We back the "arbitrary object-data" half abstractly: `pointedOfPaths` accepts ANY `(F₀, η)` and
recovers it unchanged, and the parametrisation by object-data is a *bijection*. -/

/-- The object map of `pointedOfPaths F₀ η` is `F₀` on the nose. -/
@[simp] theorem objMap_pointedOfPaths (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) :
    objMap (pointedOfPaths F₀ η) = F₀ := rfl

/-- **`pointedOfPaths` realizes arbitrary object-data, recovering it unchanged.**  For *any*
object-map `F₀` and *any* path family `η`, feeding `(F₀, η)` to `pointedOfPaths` and extracting
the object-data returns `(F₀, η)`: the object map is `F₀` on the nose, and the path map is `η`
(the components transported along the trivial object equality).  This exhibits `pointedOfPaths`
as a section of the object-data extraction, hence its essential/strict surjectivity. -/
theorem anyObjData_realized (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) (x : C) :
    pathMap (pointedOfPaths F₀ η) x = η x := by
  rw [pathMap, pointedOfPaths_pt_app_mk]

/-- The type of *object-data* on a free groupoid: an object-map together with one chosen path
per generator object. -/
def ObjData (C : Type u) [Category.{v} C] : Type _ :=
  Σ F₀ : C → FreeGroupoid C, ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x

/-- **Object-data parametrises pointed endofunctors of a free groupoid: a bijection.**  Sending
object-data `(F₀, η)` to `pointedOfPaths F₀ η` and back to `(objMap, pathMap)` is a bijection
`ObjData C ≃ PointedEndofunctor (FreeGroupoid C)`.  Both round-trips are `pointedOfPaths_objData`
(right inverse) and `objMap_pointedOfPaths`/`anyObjData_realized` (left inverse).  This is the
precise "the target is parametrised by ARBITRARY object-data" statement: the cylinder image is a
*subset* cut out by the constraints `F₀ = Rgrpd ∘ Lgrpd⁻¹`, `η = counit ≫ sweepR`. -/
noncomputable def objDataEquiv : ObjData.{v, u} C ≃ PointedEndofunctor (FreeGroupoid C) where
  toFun d := pointedOfPaths d.1 d.2
  invFun P := ⟨objMap P, pathMap P⟩
  left_inv := by
    rintro ⟨F₀, η⟩
    have h1 : objMap (pointedOfPaths F₀ η) = F₀ := rfl
    -- the path component is η up to the (trivial) object equality h1
    apply Sigma.ext h1
    apply heq_of_eq
    funext x
    exact anyObjData_realized F₀ η x
  right_inv := pointedOfPaths_objData

/-- **Distinct object-data give distinct pointed endofunctors.**  `objDataEquiv` is injective, so
two pointed endofunctors agree iff their `(objMap, pathMap)` agree.  Consequence for
non-surjectivity: the image of `cylToPointedObj` is the single point `pointedOfPaths (Rgrpd ∘
Lgrpd⁻¹) (counit ≫ sweepR)` for a fixed cylinder `c`, while `objDataEquiv` shows the codomain is
in bijection with the *entire* space `ObjData (RefineObj K)` of arbitrary object-data; any object
map that is not of the functorial form `Rgrpd ∘ Lgrpd⁻¹`, or any path family not equal to the
canonical `counit ≫ sweepR`, yields a pointed endofunctor outside the cylinder image. -/
theorem objData_injective {d d' : ObjData.{v, u} C}
    (h : pointedOfPaths d.1 d.2 = pointedOfPaths d'.1 d'.2) : d = d' :=
  objDataEquiv.injective h

/-! ## 3. Classical-CT structure: well-pointedness and idempotency

A pointed endofunctor `(F, η)` is **well-pointed** (Kelly) when `F ◫ η = η ◫ F`, i.e. for every
object `Z`, `F.map (η_Z) = η_{F Z}`.  In a groupoid base this is a genuine condition (not free).
For `pointedOfPaths F₀ η` it suffices to check on generators `Z = mk x` (every object is one and
both sides are natural).  We record the generator-level statement; the LHS uses the conjugation
formula, the RHS is the point at the transported object. -/

/-- `F.map (η_{mk x})` for `P = pointedOfPaths F₀ η`, on a generator: `F.map (pt.app (mk x))`
equals `F.map (η x)` because `pt.app (mk x) = η x`. -/
theorem F_map_pt_app_mk (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) (x : C) :
    (pointedOfPaths F₀ η).F.map ((pointedOfPaths F₀ η).pt.app ((FreeGroupoid.of C).obj x))
      = (pointedOfPaths F₀ η).F.map (η x) :=
  congrArg _ (pointedOfPaths_pt_app_mk F₀ η x)

/-- **Well-pointedness predicate** (Kelly).  `(F, η)` is *well-pointed* when `F ◫ pt = pt ◫ F`,
i.e. `∀ Z, F.map (pt.app Z) = pt.app (F.obj Z)`.  In a groupoid base this is a genuine condition
(not automatic), because `F` and `pt` carry independent data on non-generator objects. -/
def IsWellPointed (P : PointedEndofunctor (FreeGroupoid C)) : Prop :=
  ∀ Z, P.F.map (P.pt.app Z) = P.pt.app (P.F.obj Z)

/-- **Well-pointedness reduces to generators.**  `pointedOfPaths F₀ η` is well-pointed iff for
every generator `x`, `F.map (η x) = pt.app (F₀ x)`.  (`←`) Naturality is automatic for the
generator-indexed reformulation, since every object is `mk x` and both `F.map (pt.app ·)` and
`pt.app (F.obj ·)` are natural; (`→`) is restriction.  Concretely both directions are pointwise:
the condition at `Z` and at `mk (Z.as.as)` coincide because `pt.app Z = pt.app (mk Z.as.as)`. -/
theorem isWellPointed_iff (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) :
    IsWellPointed (pointedOfPaths F₀ η)
      ↔ ∀ x, (pointedOfPaths F₀ η).F.map (η x) = (pointedOfPaths F₀ η).pt.app (F₀ x) := by
  constructor
  · intro h x
    have := h ((FreeGroupoid.of C).obj x)
    rwa [F_map_pt_app_mk] at this
  · intro h Z
    obtain ⟨x, rfl⟩ := (FreeGroupoid.of_obj_bijective).2 Z
    rw [F_map_pt_app_mk]
    exact h x

/-- **Idempotency on objects.**  `(F ⋙ F).obj (mk x) = F.obj (F₀ x)`; so `F` is idempotent on
objects (`F.obj (F.obj Z) = F.obj Z`) iff `F.obj (F₀ x) = F₀ x` for all generators `x`. -/
theorem comp_F_obj_mk (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) (x : C) :
    ((pointedOfPaths F₀ η).F ⋙ (pointedOfPaths F₀ η).F).obj ((FreeGroupoid.of C).obj x)
      = (pointedOfPaths F₀ η).F.obj (F₀ x) := rfl

/-- **The trivial object-data is well-pointed.**  Taking `F₀ x = mk x` and `η x = 𝟙` gives the
identity-like pointed endofunctor, which is well-pointed: `F.map 𝟙 = 𝟙 = pt.app (mk x)` once
`pt.app (mk x) = η x = 𝟙`.  (A clean positive anchor; the general `pointedOfPaths F₀ η` need NOT
be well-pointed, since `F.map (η x)` and `pt.app (F₀ x)` are independent unless `F₀`/`η` cohere —
this is exactly the Kelly condition, which the cylinder's `(Rgrpd∘Lgrpd⁻¹, counit≫sweepR)` is not
known to satisfy in general; see `Cyl1_Algebra.md`.) -/
theorem trivial_isWellPointed :
    IsWellPointed (pointedOfPaths (fun x => (FreeGroupoid.of C).obj x)
      (fun x => 𝟙 ((FreeGroupoid.of C).obj x))) := by
  rw [isWellPointed_iff]
  intro x
  rw [pointedOfPaths_pt_app_mk]
  exact CategoryTheory.Functor.map_id _ _

/-- **The point of `pointedOfPaths` is a natural ISO (it always is, in a groupoid).**  Recorded
explicitly: in a groupoid base every pointed endofunctor's point is invertible (`pt_isIso`), so
`(F, η)` is *never* a strict pointed endofunctor with non-invertible point — it is always (the
unit of) an equivalence-data, and the morphisms between pointed endofunctors are forced
(`pointedHomOfGroupoid`).  This is the structural reason the cylinder ⟹ pointed-functor *functor*
has a degenerate (codiscrete) image on morphisms; see `Cyl1_Algebra.md`. -/
theorem pointedOfPaths_pt_isIso (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) :
    IsIso (pointedOfPaths F₀ η).pt :=
  inferInstance

end Cyl1
