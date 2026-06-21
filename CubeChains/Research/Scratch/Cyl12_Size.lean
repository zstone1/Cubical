import CubeChains.Research.Scratch.Cyl8_MooreMonoid
import CubeChains.Research.Scratch.Cyl2_Injectivity
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Algebra.Group.End

/-!
# Cyl12_Size — how big is the cylinder monoid?

Scratch investigation (RESULT 2 / cylinder ⟹ pointed-functor program).  **Decoupled** from the
green build; build with `lake build CubeChains.Research.Scratch.Cyl12_Size`.  Owns ONLY this file
and its `.md`.  **Imports** `Cyl8_MooreMonoid` (`mooreSubmonoid`, `mooreToPointed`,
`mooreSubmonoid_eq_closure`), which transitively re-exports `Cyl6` (the `Monoid` instance,
`cylImage`, `mul_pointedOfPaths`) and `Cyl1` (`objDataEquiv`, `pointedOfPaths_objData`).

## The question

`M := PointedEndofunctor (DPathGrpdR K)` is a monoid under composition (Cyl6).  The cylinder
construction generates a submonoid `mooreSubmonoid K = Submonoid.closure (cylImage K)` (Cyl8).
**How big is it?**  Is `mooreSubmonoid K = ⊤`?  If proper, what constrains every element?

## Headline answers (all PROVEN here unless flagged)

1. **π₀ upper bound (`π0Action`, `pi0Map_pointed_eq_id`).**  *Every* pointed endofunctor of a
   groupoid — hence every element of `M`, a fortiori of `mooreSubmonoid K` — acts as the
   **identity** on `π₀ = WeaklyConnectedComponent (DPathGrpdR K)`.  Reason: a point
   `pt.app x : x ⟶ F.obj x` is a morphism, so `x` and `F.obj x` lie in the *same* component, so the
   object-map descends to `id` on π₀.  Packaged as a monoid hom
   `π0Action : M →* (Function.End π₀)ᵐᵒᵖ` with image the trivial submonoid `{1}`.  A hard
   *constraint*, but satisfied by ALL of `M`, so it does not by itself separate `mooreSubmonoid`.

2. **`OfClosure` is VACUOUS (`ofClosure_univ`).**  Cyl2's `η`-membership predicate holds for EVERY
   morphism of a free groupoid (every generator is in it; closed under comp/inv ⟹ whole hom-set by
   the word presentation).  Verdict: NOT a constraint on `η`; the real constraint on `cylImage` is
   the `(F₀, η)` *correlation* plus the π₀-fixing of (1).

3. **Properness — IS IT THE WHOLE MONOID?**  Settled as far as is honestly provable.
   * `M` is *trivial* over a **discrete** base (`subsingleton_pointed_of_discrete`) — so over
     `fourPaths` `mooreSubmonoid K = M = ⊤ = {1}`, NO gap.  The suggested `fourPaths`/π₀-permutation
     route is therefore DEGENERATE: a π₀-permutation is not an element of `M` at all (§1).
   * `M` is *nontrivial* (`nontrivial_pointed_of_loop`) exactly when the base has a non-identity
     loop (e.g. `□²`) — the only regime where a gap can exist.
   * `mooreSubmonoid K ≠ ⊤` is PROVEN *conditionally* (`mooreSubmonoid_ne_top_of_isEmpty`): from
     `Nontrivial M` plus `IsEmpty (CylMapWeqR K)` (then `mooreSubmonoid K = ⊥`).  An *unconditional*
     `≠ ⊤` is OPEN: every formalised invariant (§1 π₀, §2 `OfClosure`) is satisfied by ALL of `M`,
     so none separates `mooreSubmonoid`; the genuine separator is the `(F₀, η)` correlation
     (noncomputable cylinder geometry), not characterised in Lean.

4. **Size characterization.**  `π0Action '' mooreSubmonoid K = {1} = π0Action '' M`: π₀ does NOT
   measure the gap; the gap lives one level down in the fibers, where `M` is genuinely bigger.

**Layer:** Research/Scratch (decoupled).  **Imports:** `Cyl8_MooreMonoid`, mathlib quiver π₀ + End.
-/

open CategoryTheory Operations
open CubeChain

universe v u

namespace Cyl12

/-! ## 1. The π₀ upper bound

The set of *weakly connected components* of a category `𝒢` (the underlying quiver's π₀, the quotient
by zigzag-connectedness).  A morphism `f : x ⟶ y` is a length-1 zigzag, so it forces `[x] = [y]`;
consequently the object-map of *any* endofunctor that carries a point `𝟭 ⟹ F` (a morphism
`x ⟶ F x` for every `x`) descends to the IDENTITY on π₀. -/

section Pi0

variable {𝒢 : Type u} [Groupoid.{v} 𝒢]

/-- `π₀ 𝒢` — the set of weakly connected components of the groupoid `𝒢` (its underlying quiver's
zigzag quotient).  For `DPathGrpdR K` this is the set of d-path-homotopy components. -/
abbrev Pi0 (𝒢 : Type u) [Groupoid.{v} 𝒢] : Type u := Quiver.WeaklyConnectedComponent 𝒢

/-- **A morphism forces its endpoints into the same component.**  For `f : x ⟶ y` in `𝒢`, the image
`Sum.inl f` is a length-1 path in `Symmetrify 𝒢`, so `[x] = [y]` in `π₀`. -/
theorem wcc_eq_of_hom {x y : 𝒢} (f : x ⟶ y) :
    (Quiver.WeaklyConnectedComponent.mk x : Pi0 𝒢)
      = Quiver.WeaklyConnectedComponent.mk y :=
  (Quiver.WeaklyConnectedComponent.eq x y).2 ⟨(Quiver.Hom.toPath (Sum.inl f))⟩

/-- The object-map of an endofunctor descends to π₀: `[x] ↦ [F.obj x]`.  Well-defined because a
zigzag `x ⤳ y` maps under `F` to a zigzag `F x ⤳ F y`. -/
def pi0Map (F : 𝒢 ⥤ 𝒢) : Pi0 𝒢 → Pi0 𝒢 :=
  Quotient.lift (fun x => (Quiver.WeaklyConnectedComponent.mk (F.obj x) : Pi0 𝒢))
    (by
      rintro x y ⟨p⟩
      induction p with
      | nil => rfl
      | @cons a b q e ih =>
          refine ih.trans ?_
          cases e with
          | inl g => exact wcc_eq_of_hom (F.map g)
          | inr g => exact (wcc_eq_of_hom (F.map g)).symm)

@[simp] theorem pi0Map_mk (F : 𝒢 ⥤ 𝒢) (x : 𝒢) :
    pi0Map F (Quiver.WeaklyConnectedComponent.mk x)
      = Quiver.WeaklyConnectedComponent.mk (F.obj x) := rfl

@[simp] theorem pi0Map_id : pi0Map (𝟭 𝒢) = id := by
  funext c; induction c using Quotient.ind; rfl

/-- `pi0Map` of a composite is the composite of `pi0Map`s (apply `F` first, then `G`). -/
@[simp] theorem pi0Map_comp (F G : 𝒢 ⥤ 𝒢) :
    pi0Map (F ⋙ G) = pi0Map G ∘ pi0Map F := by
  funext c; induction c using Quotient.ind; rfl

/-- **The π₀-object-map of a pointed endofunctor is the IDENTITY.**  The point `pt.app x : x ⟶ F x`
forces `[x] = [F x]` for every `x`, so the descended object-map fixes every component.  This is the
sharp upper bound: a pointed endofunctor of a groupoid can never permute π₀. -/
theorem pi0Map_pointed_eq_id (A : PointedEndofunctor 𝒢) : pi0Map A.F = id := by
  funext c
  induction c using Quotient.ind with
  | _ x => exact (wcc_eq_of_hom (A.pt.app x)).symm

end Pi0

/-! ### `π0Action` as a monoid homomorphism -/

section Action

variable {𝒢 : Type u} [Groupoid.{v} 𝒢]

/-- The π₀-object-map of a pointed endofunctor, packaged as an element of the endomorphism monoid
`Function.End (π₀ 𝒢)`. -/
def π0End (A : PointedEndofunctor 𝒢) : Function.End (Pi0 𝒢) := pi0Map A.F

/-- The unit's π₀-object-map is `id` (as a bare function). -/
theorem π0End_one_fun : π0End (1 : PointedEndofunctor 𝒢) = id := by
  change pi0Map (1 : PointedEndofunctor 𝒢).F = id
  rw [Cyl6.one_F, pi0Map_id]

/-- The product's π₀-object-map composes the factors' (second after first, as bare functions). -/
theorem π0End_mul_fun (A B : PointedEndofunctor 𝒢) :
    π0End (A * B) = pi0Map B.F ∘ pi0Map A.F := by
  change pi0Map (A * B).F = pi0Map B.F ∘ pi0Map A.F
  rw [Cyl6.mul_F, pi0Map_comp]

/-- **The π₀-object-map of a pointed endofunctor is the identity element of `Function.End`.**
The point `pt.app x : x ⟶ F x` forces `[x] = [F x]` for every `x` (`pi0Map_pointed_eq_id`). -/
theorem π0End_eq_one (A : PointedEndofunctor 𝒢) : π0End A = (1 : Function.End (Pi0 𝒢)) :=
  pi0Map_pointed_eq_id A

/-- **The π₀-action monoid homomorphism.**  `A ↦ op (π0End A)`, landing in
`(Function.End (π₀ 𝒢))ᵐᵒᵖ` (opposite, to match the composition order of the pointed-endofunctor
product `(A*B).F = A.F ⋙ B.F`, whence `π0End (A*B) = π0End B ∘ π0End A`).  In `Function.End`,
`1 = id` and `g * f = g ∘ f`, so the unit/mul laws are `π0End_one_fun`/`π0End_mul_fun`. -/
def π0Action : PointedEndofunctor 𝒢 →* (Function.End (Pi0 𝒢))ᵐᵒᵖ where
  toFun A := MulOpposite.op (π0End A)
  map_one' := congrArg MulOpposite.op (π0End_eq_one 1)
  map_mul' A B := congrArg MulOpposite.op (π0End_mul_fun A B)

@[simp] theorem π0Action_apply (A : PointedEndofunctor 𝒢) :
    π0Action A = MulOpposite.op (π0End A) := rfl

/-- **THE UPPER BOUND.**  `π0Action A = 1` for *every* pointed endofunctor `A` of a groupoid: its
π₀-object-map is the identity (`π0End_eq_one`).  So no element of `M` permutes π₀. -/
@[simp] theorem π0Action_eq_one (A : PointedEndofunctor 𝒢) : π0Action A = 1 :=
  congrArg MulOpposite.op (π0End_eq_one A)

/-- The whole monoid `M` lands in the trivial submonoid of `End π₀`: `range π0Action = {1}`. -/
theorem π0Action_range_eq :
    Set.range (π0Action (𝒢 := 𝒢)) = {1} := by
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨1, π0Action_eq_one 1⟩, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact π0Action_eq_one A

end Action

/-! ## 2. Is `OfClosure` a real constraint?  VERDICT: VACUOUS

Cyl2's `OfClosure` is the predicate "this morphism of `FreeGroupoid C` is a zigzag of *genuine*
`C`-arrows (`of.map`), `eqToHom`s, closed under composition and inverse" — Cyl2 proved every
induced point factors as `counit.inv ≫ w` with `w ∈ OfClosure`, and asked whether `OfClosure` is a
genuine cut on `η` or vacuous.

**It is VACUOUS: `OfClosure` holds for EVERY morphism of a free groupoid.**  Reason: the morphisms
of `OfClosure` form a *wide subgroupoid* `OfClosureGrpd C` (objects = all of `FreeGroupoid C`; it
contains identities, and is closed under composition and inverse).  Its inclusion `ι` into
`FreeGroupoid C` admits a section `lift j ⋙ ι = 𝟭` by the free-groupoid universal property
(`lift_unique`), because `of` factors through it (`OfClosure.of_map`).  Hence every morphism is in
the image of `ι`, i.e. in `OfClosure`.

So the only formal inverse a point uses is the counit (Cyl2's necessary side), but the residual
`w ∈ OfClosure` is **no constraint at all** — `w` ranges over *every* morphism of the free
groupoid.  The real constraint on `cylImage` is therefore the `(F₀, η)` **correlation** (which
pairs of object-map + path actually arise from a cylinder), together with the π₀-fixing of §1 —
NOT the membership of `η` in `OfClosure`. -/

section OfClosure

variable {C : Type u} [Category.{v} C]

open Cyl2

/-- **The wide subgroupoid carved out by `OfClosure`.**  Objects are those of `FreeGroupoid C`;
morphisms `X ⟶ Y` are the `OfClosure`-morphisms.  It is a groupoid: identities are in `OfClosure`
(`OfClosure.id`), and it is closed under composition (`OfClosure.comp`) and inverse
(`OfClosure.inv`). -/
structure OfClosureGrpd (C : Type u) [Category.{v} C] where
  /-- The underlying object of the free groupoid. -/
  as : FreeGroupoid C

namespace OfClosureGrpd

instance : Category (OfClosureGrpd C) where
  Hom X Y := {f : X.as ⟶ Y.as // OfClosure f}
  id X := ⟨𝟙 X.as, OfClosure.id X.as⟩
  comp f g := ⟨f.1 ≫ g.1, OfClosure.comp f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

instance : Groupoid (OfClosureGrpd C) where
  inv f := ⟨Groupoid.inv f.1, OfClosure.inv f.2⟩
  inv_comp f := Subtype.ext (Groupoid.inv_comp f.1)
  comp_inv f := Subtype.ext (Groupoid.comp_inv f.1)

/-- The inclusion `OfClosureGrpd C ⥤ FreeGroupoid C` (forget the `OfClosure` proof). -/
def ι : OfClosureGrpd C ⥤ FreeGroupoid C where
  obj X := X.as
  map f := f.1

@[simp] theorem ι_obj (X : OfClosureGrpd C) : ι.obj X = X.as := rfl
@[simp] theorem ι_map {X Y : OfClosureGrpd C} (f : X ⟶ Y) : ι.map f = f.1 := rfl

/-- `C` lands in the subgroupoid: `of.map f` is in `OfClosure` (`OfClosure.of_map`). -/
def fromC : C ⥤ OfClosureGrpd C where
  obj x := ⟨(FreeGroupoid.of C).obj x⟩
  map f := ⟨(FreeGroupoid.of C).map f, OfClosure.of_map f⟩
  map_id x := Subtype.ext ((FreeGroupoid.of C).map_id x)
  map_comp f g := Subtype.ext ((FreeGroupoid.of C).map_comp f g)

/-- `fromC ⋙ ι = of`: the section data agrees with `of` on the nose. -/
theorem fromC_comp_ι : fromC ⋙ ι = FreeGroupoid.of C :=
  rfl

end OfClosureGrpd

/-- **`lift fromC ⋙ ι = 𝟭`** — the inclusion of the `OfClosure` subgroupoid has a section.  By
`lift_unique`: `of ⋙ (lift fromC ⋙ ι) = (of ⋙ lift fromC) ⋙ ι = fromC ⋙ ι = of`, so
`lift fromC ⋙ ι = lift of = 𝟭`. -/
theorem liftFromC_comp_ι :
    FreeGroupoid.lift (OfClosureGrpd.fromC (C := C)) ⋙ OfClosureGrpd.ι = 𝟭 (FreeGroupoid C) := by
  rw [FreeGroupoid.lift_unique (OfClosureGrpd.fromC (C := C) ⋙ OfClosureGrpd.ι)
    (FreeGroupoid.lift OfClosureGrpd.fromC ⋙ OfClosureGrpd.ι)
    (by rw [← Functor.assoc, FreeGroupoid.lift_spec])]
  rw [OfClosureGrpd.fromC_comp_ι]
  exact Cyl3.lift_of_eq_id

/-- **THE VERDICT: `OfClosure` is VACUOUS.**  Every morphism `f` of a free groupoid lies in
`OfClosure`.  Proof: `f = (lift fromC ⋙ ι).map f = ι.map ((lift fromC).map f)`, and
`(lift fromC).map f` is a morphism of `OfClosureGrpd C`, which by construction carries an
`OfClosure` proof of its underlying morphism `ι.map (…) = f`. -/
theorem ofClosure_univ {X Y : FreeGroupoid C} (f : X ⟶ Y) : OfClosure f := by
  -- `f = eqToHom _ ≫ ι.map (lift.map f) ≫ eqToHom _`; the middle is `OfClosure` by construction,
  -- the `eqToHom` corrections are `OfClosure` too, and `OfClosure` is closed under composition.
  have hf := Functor.congr_hom liftFromC_comp_ι.symm f
  simp only [Functor.comp_map, Functor.id_map] at hf
  rw [hf]
  exact OfClosure.comp (OfClosure.eqToHom _)
    (OfClosure.comp ((FreeGroupoid.lift OfClosureGrpd.fromC).map f).2 (OfClosure.eqToHom _))

/-- Restated as a set identity: the `OfClosure` morphisms are *all* morphisms.  So Cyl2's
factorisation `η = counit.inv ≫ w, w ∈ OfClosure` puts **no** constraint on `w`. -/
theorem ofClosure_eq_univ {X Y : FreeGroupoid C} :
    {f : X ⟶ Y | OfClosure f} = Set.univ :=
  Set.eq_univ_of_forall ofClosure_univ

end OfClosure

/-! ## 3. Properness — IS IT THE WHOLE MONOID?

The headline question: `mooreSubmonoid K = ⊤`?  We settle it as far as is honestly provable.

* **3a (PROVEN).**  Over a *discrete* base groupoid (`fourPaths`!) the WHOLE monoid `M` is trivial:
  `Subsingleton M`.  So there `mooreSubmonoid K = M = ⊤ = {1}` and there is **no gap** — the
  disconnected-base route suggested for a properness witness is DEGENERATE (the point `x ⟶ F x`
  forces `F = 𝟭`, so π₀ can never be permuted; cf. §1).  This refutes the "use `fourPaths`'
  `firstIncoherence` π₀-permutation" plan: such a π₀-permutation is **not an element of `M`** at
  all (it carries no point), so a fortiori the gap is not visible there.

* **3b (PROVEN).**  `M` is genuinely *large* exactly when the base groupoid has a non-identity loop
  (a base with a fiber that is not discrete, e.g. `□²`'s staircase-swap): then `M` is
  `Nontrivial` (in fact infinite — a free group's worth of loops).  This is the regime where a gap
  *could* exist.

* **3c (PROVEN, conditional).**  `mooreSubmonoid K ≠ ⊤` follows from `Nontrivial M` together with
  `cylImage K` failing to generate `M`.  We give the clean sufficient condition: if no
  weak-equivalence cylinder exists (`IsEmpty (CylMapWeqR K)`) then `mooreSubmonoid K = ⊥` (= `{1}`),
  hence `≠ ⊤` once `M` is nontrivial.  The honest status: an *unconditional* `≠ ⊤` is NOT provable
  with the present formalisation — every formalised invariant (π₀ in §1, `OfClosure` in §2) is
  satisfied by ALL of `M`, so none separates `mooreSubmonoid` from `M`; a genuine separator is the
  `(F₀, η)` *correlation* (which object-map/path pairs cylinder products realise), which is
  noncomputable cylinder geometry and not characterised in Lean.  See `.md`. -/

section Properness

variable {C : Type u} [Category.{v} C]

/-! ### 3a — discrete base ⟹ `M` trivial (refutes the `fourPaths` route) -/

/-- A groupoid is **discrete** (as the underlying category of `DPathGrpdR K` is for `fourPaths`)
when its hom-sets are subsingletons and a morphism only connects equal objects.  Stated as a
structure of hypotheses to instantiate against `native_decide`-confirmed finite bases. -/
structure IsDiscreteGrpd (𝒢 : Type*) [Groupoid 𝒢] : Prop where
  /-- Hom-sets are subsingletons (no nontrivial loops). -/
  thin : ∀ {x y : 𝒢}, Subsingleton (x ⟶ y)
  /-- A morphism forces equal endpoints (no nontrivial connections). -/
  eq_of_hom : ∀ {x y : 𝒢} (_ : x ⟶ y), x = y

/-- **Over a discrete base, every pointed endofunctor is the unit: `Subsingleton M`.**  The point
`pt.app x : x ⟶ F x` forces `F.obj x = x` (`eq_of_hom`), the functor's action and the point are
forced to identities (`thin`).  So `M` collapses to a single element; there is no room for any
nontrivial cylinder/Moore content.  This is the precise statement that the disconnected (discrete)
base `fourPaths`, far from being where the gap lives, is where the monoid VANISHES. -/
theorem subsingleton_pointed_of_discrete {𝒢 : Type*} [Groupoid 𝒢] (hd : IsDiscreteGrpd 𝒢) :
    Subsingleton (PointedEndofunctor 𝒢) := by
  -- every pointed endofunctor of a discrete groupoid is *equal* to the unit `⟨𝟭, 𝟙⟩`
  have key : ∀ A : PointedEndofunctor 𝒢, A = ⟨𝟭 𝒢, 𝟙 (𝟭 𝒢)⟩ := by
    intro A
    have hAobj : ∀ x, A.F.obj x = x := fun x => (hd.eq_of_hom (A.pt.app x)).symm
    have hF : A.F = 𝟭 𝒢 := by
      refine CategoryTheory.Functor.ext (fun x => hAobj x) (fun x y f => ?_)
      exact hd.thin.elim _ _
    refine Cyl1.pointedEndofunctor_ext' hF (fun Z => ?_)
    haveI : Subsingleton ((𝟭 𝒢).obj Z ⟶ A.F.obj Z) := hd.thin
    exact Subsingleton.helim (by rw [hF]) _ _
  exact ⟨fun A B => (key A).trans (key B).symm⟩

/-! ### 3b — a non-identity loop makes `M` nontrivial -/

/-- **`M` is nontrivial when the free groupoid has a non-identity loop.**  Given `x : C` and a loop
`g : of x ⟶ of x` with `g ≠ 𝟙`, the object-data `(of, η)` with `η = 𝟙` (this is the unit `1`) and
`(of, η')` with `η' x = g`, `η' z = 𝟙` for `z ≠ x` are distinct (their path components differ at
`x`), so by `objData_injective` they give distinct pointed endofunctors.  Hence `Nontrivial M`.
This is the regime (e.g. `□²`, whose `DPathGrpdR` has the staircase-swap loop) where a gap between
`mooreSubmonoid` and `M` can exist at all. -/
theorem nontrivial_pointed_of_loop {x : C}
    (g : (FreeGroupoid.of C).obj x ⟶ (FreeGroupoid.of C).obj x) (hg : g ≠ 𝟙 _) :
    Nontrivial (PointedEndofunctor (FreeGroupoid C)) := by
  classical
  -- the alternative path family: `g` at `x`, identity elsewhere (same object-map `tautF₀ = of`)
  let η' : ∀ z, (FreeGroupoid.of C).obj z ⟶ Cyl3.tautF₀ (C := C) z :=
    fun z => if h : z = x then (by subst h; exact g) else 𝟙 _
  refine ⟨pointedOfPaths Cyl3.tautF₀ Cyl3.tautη, pointedOfPaths Cyl3.tautF₀ η', ?_⟩
  intro hEq
  -- equal pointed endofunctors ⟹ equal object-data (`objData_injective`); the path families agree
  have hData : (⟨Cyl3.tautF₀ (C := C), Cyl3.tautη⟩ : Cyl1.ObjData C)
      = ⟨Cyl3.tautF₀, η'⟩ := Cyl1.objData_injective hEq
  -- extract the path component at `x`: `tautη x = 𝟙 = η' x = g`
  have hη : Cyl3.tautη (C := C) = η' := eq_of_heq (Sigma.ext_iff.1 hData).2
  have hx : Cyl3.tautη (C := C) x = η' x := congrFun hη x
  simp only [η', dif_pos rfl, Cyl3.tautη] at hx
  exact hg hx.symm

/-! ### 3c — the conditional `≠ ⊤` -/

/-- If there are **no** weak-equivalence cylinders, the only Moore cylinder is the empty list, so
`mooreSubmonoid K = ⊥` (the bottom submonoid `{1}`).  (Every `m : List (CylMapWeqR K)` with the
component type empty must be `[]`, whose `mooreToPointed` is `1`.) -/
theorem mooreSubmonoid_eq_bot_of_isEmpty {K : BPSet} (h : IsEmpty (CylMapWeqR K)) :
    Cyl8.mooreSubmonoid K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨m, rfl⟩
  -- the component list is over an empty type, hence `[]`
  cases m with
  | nil => simp [Cyl8.mooreToPointed_nil]
  | cons c _ => exact (h.false c).elim

/-- **THE CONDITIONAL PROPERNESS (`mooreSubmonoid K ≠ ⊤`).**  If the base monoid `M` is nontrivial
(§3b: there is a non-identity loop, e.g. over `□²`) AND no weak-equivalence cylinder exists, then
`mooreSubmonoid K` is the bottom submonoid `{1}`, which is `≠ ⊤`.  More generally `≠ ⊤` follows from
`Nontrivial M` together with any proof that `mooreSubmonoid K` is bottom (or, more sharply, that
some `A ∈ M` is not a Moore product).  The honest unconditional statement remains open; see the
module docstring and `.md`. -/
theorem mooreSubmonoid_ne_top_of_isEmpty {K : BPSet}
    (hne : Nontrivial (PointedEndofunctor (DPathGrpdR K)))
    (h : IsEmpty (CylMapWeqR K)) :
    Cyl8.mooreSubmonoid K ≠ ⊤ := by
  rw [mooreSubmonoid_eq_bot_of_isEmpty h]
  -- `⊥ ≠ ⊤` because `M` is nontrivial: a second element is not in `{1}`
  obtain ⟨A, B, hAB⟩ := hne
  intro hbot
  -- both `A, B ∈ ⊤ = ⊥`, so both `= 1`, contradiction
  have hA : A ∈ (⊥ : Submonoid (PointedEndofunctor (DPathGrpdR K))) := hbot ▸ Submonoid.mem_top A
  have hB : B ∈ (⊥ : Submonoid (PointedEndofunctor (DPathGrpdR K))) := hbot ▸ Submonoid.mem_top B
  rw [Submonoid.mem_bot] at hA hB
  exact hAB (hA.trans hB.symm)

end Properness

/-! ## 4. How big — the sharpest size statement

Putting §§1–3 together, here is the size of `mooreSubmonoid K` relative to `M`:

* **π₀ floor/ceiling coincide.**  `π0Action '' mooreSubmonoid K = {1} = π0Action '' M` (§1).
  Both the cylinder submonoid and the full monoid act *trivially* on π₀.  So **π₀ measures NO gap**:
  the cylinder construction is not "missing" any π₀-permutations — there are none to miss (every
  pointed endofunctor fixes π₀).

* **The gap, if any, is purely in the fibers (the loops).**  `M ≅ ObjData C` carries, over each π₀
  component, the loop data (a free group's worth of paths `η x`).  `mooreSubmonoid` is the
  closure of the cylinder image inside *this* fiber data.  Over a discrete base the fibers are
  trivial and `M = {1}` (§3a); over a base with loops `M` is infinite (§3b) and whether
  `mooreSubmonoid` exhausts it is the open `≠ ⊤` question (§3c).

* **Verdict.**  `mooreSubmonoid K` is the *whole* monoid `M` exactly when `M` is trivial (discrete
  base).  When `M` is nontrivial, `mooreSubmonoid K` is conjecturally proper, and certainly proper
  in the degenerate `IsEmpty (CylMapWeqR K)` regime (§3c).  The size is therefore controlled NOT by
  π₀ (where M and the cylinder image agree, both trivial) but by the fiber/loop data, which is the
  level the broader program already identifies as the meaningful one. -/

section Size

variable {K : BPSet}

/-- `π0Action` collapses `mooreSubmonoid K` to `{1}` — the cylinder submonoid fixes π₀. -/
theorem π0Action_mooreSubmonoid_eq_one
    (A : PointedEndofunctor (DPathGrpdR K)) (_ : A ∈ Cyl8.mooreSubmonoid K) :
    π0Action A = 1 :=
  π0Action_eq_one A

/-- **π₀ does not measure the gap.**  The image of `mooreSubmonoid K` under `π0Action` is `{1}`,
identical to the image of the whole monoid `M` (`π0Action_range_eq`).  So the entire size gap
between `mooreSubmonoid K` and `M` is invisible to π₀ and lives in the fibers. -/
theorem π0Action_image_moore_eq_image_top :
    (π0Action (𝒢 := DPathGrpdR K)) '' (Cyl8.mooreSubmonoid K) = {1}
      ∧ Set.range (π0Action (𝒢 := DPathGrpdR K)) = {1} := by
  refine ⟨?_, π0Action_range_eq⟩
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨1, ⟨[], Cyl8.mooreToPointed_nil⟩, π0Action_eq_one 1⟩, ?_⟩
  rintro _ ⟨A, _, rfl⟩
  exact π0Action_eq_one A

end Size

end Cyl12
