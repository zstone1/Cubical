import CubeChains.Cylinder.CylinderRefine
import CubeChains.Chains.Correspondence

/-!
# Cyl5_Altitude — simplifications under `NonSelfLinked` + `AdmitsAltitude`

Scratch investigation (RESULT 2 program, user item 6): under the two side conditions
`BPSet.NonSelfLinked K` and `BPSet.AdmitsAltitude K` — exactly the regime where
`Correspondence.equivWedgeCat : RefineObj K.init K.final ≌ ChainCat.Obj K` holds and the
refinement category is **thin** (`refineObj_hom_subsingleton`) — what does the cylinder ⟹
pointed-functor construction simplify to?

This file isolates the genuinely-provable payoff and pins down the central question:

* **Does thinness force `η` to be canonical?** (item 1) — `cylToPointedObj` is
  `pointedOfPaths F₀ η` with `η x : (of x) ⟶ F₀ x` a morphism in the *free groupoid*
  `DPathGrpdR K = FreeGroupoid (RefineObj …)`.  Thinness of the **base** `RefineObj …` does
  **not** make `η x` unique, because `η x` lives in the free *groupoid*, whose hom-sets are
  torsors over the fundamental group of the base — generally nontrivial even for a thin
  (poset-like) base.  The precise positive statement is conditional on thinness of the *free
  groupoid* itself:
  `pointedOfPaths_eq_of_thin` — if `Quiver.IsThin (FreeGroupoid C)` then any two
  `pointedOfPaths F₀ η`, `pointedOfPaths F₀ η'` with the same `F₀` are **equal**.

* **Transport across `equivWedgeCat`** (item 3) — the side conditions give an equivalence of
  *groupoids* `DPathGrpdR K = FreeGroupoid (RefineObj …) ≌ FreeGroupoid (ChainCat.Obj K)`
  (`dpathEquivChain`), built from `equivWedgeCat` by `FreeGroupoid.map`, and pointed
  endofunctors transport along it (`pointedEndofunctorEquiv`).  So the pointed-endofunctor
  target may equivalently be computed on the wedge-map model `ChainCat.Obj K`.

**Build:** `lake build CubeChains.Research.Scratch.Cyl5_Altitude`.
Decoupled from the root build; sorry-free for every claimed lemma.
-/

open CategoryTheory Opposite
open Operations
open CubeChain

namespace Cyl5

universe v u

/-! ## 0. Thinness of the base under the side conditions (recap from `Correspondence`)

These are the two `Quiver.IsThin` facts that this file's analysis hinges on; both are theorems
of `Correspondence.lean`, repackaged here as local instances under the side hypotheses. -/

section Thin

variable {K : BPSet}

/-- Under the side conditions the refinement category `RefineObj K.init K.final` is thin
(`Correspondence.refineObj_hom_subsingleton`). -/
theorem refineObj_isThin (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    Quiver.IsThin (RefineObj K.init K.final) :=
  fun _ _ => refineObj_hom_subsingleton h₁ h₂ _ _

/-- Under the side conditions the wedge-map category `ChainCat.Obj K` is thin
(`Correspondence.chainCat_hom_subsingleton`). -/
theorem chainCat_isThin (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    Quiver.IsThin (ChainCat.Obj K) :=
  fun _ _ => chainCat_hom_subsingleton h₁ h₂ _ _

end Thin

/-! ## 1. The central question: does thinness force `η` to be canonical?

The construction `pointedOfPaths F₀ η` consumes, per object `x`, a chosen path
`η x : (of C).obj x ⟶ F₀ x` **in the free groupoid** `FreeGroupoid C`.  The free groupoid on a
thin category is the *fundamental groupoid* of the base's order complex; its hom-sets are
torsors over the fundamental group, which is generally nontrivial even when the base is thin.
So thinness of `C` does **not** by itself pin `η`.

What *is* forced is conditional on thinness of the **free groupoid**.  The clean statement: if
the hom-sets of `FreeGroupoid C` are subsingletons, then `pointedOfPaths` does not see `η` at
all — any two choices with the same `F₀` give the **same** pointed endofunctor.  This is the
honest "canonicity" payoff: it is governed by `Quiver.IsThin (FreeGroupoid C)`, not by thinness
of `C`. -/

section Canonicity

variable {C : Type u} [Category.{v} C]

/-- The conjugation functor of `pointedOfPaths` is determined by `F₀` alone when the free
groupoid is thin: its action on a morphism lands in a subsingleton hom-set, so the two `η`
choices give equal functors. -/
theorem conjFunctor_eq_of_thin [Quiver.IsThin (FreeGroupoid C)] (F₀ : C → FreeGroupoid C)
    (η η' : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) :
    conjFunctor (FreeGroupoid.of C) F₀ η = conjFunctor (FreeGroupoid.of C) F₀ η' :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- **[KEY — conditional canonicity].**  If the *free groupoid* `FreeGroupoid C` is thin
(`Quiver.IsThin`), then `pointedOfPaths` is **independent of the path choice `η`**: any two
`pointedOfPaths F₀ η`, `pointedOfPaths F₀ η'` with the same object map `F₀` are **equal**.

This is the precise sense in which "thinness forces `η` canonical": it is thinness of the free
groupoid (equivalently, all path-homs `of x ⟶ F₀ x` subsingletons), *not* thinness of the base
`C`, that does the forcing.  When it holds, the construction depends only on `F₀`. -/
theorem pointedOfPaths_eq_of_thin [Quiver.IsThin (FreeGroupoid C)]
    (F₀ : C → FreeGroupoid C) (η η' : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) :
    pointedOfPaths F₀ η = pointedOfPaths F₀ η' := by
  -- The underlying functors are equal: `pointedOfPaths.F = lift (conjFunctor …)`, and the
  -- conjugation functors agree by `conjFunctor_eq_of_thin`.
  have hF : (pointedOfPaths F₀ η).F = (pointedOfPaths F₀ η').F := by
    simp only [pointedOfPaths]; rw [conjFunctor_eq_of_thin F₀ η η']
  -- A `PointedEndofunctor` of a thin category is pinned by its `.F` field: the `.pt` lands in a
  -- subsingleton hom-set (`functor_thin`).
  cases A : pointedOfPaths F₀ η
  cases A' : pointedOfPaths F₀ η'
  rw [A, A'] at hF
  subst hF
  congr 1
  exact Subsingleton.elim _ _

/-- **`η` is fully recoverable from the pointed endofunctor** (the converse direction of
canonicity).  The point's component at `of x` is exactly the chosen path `η x` (the `eqToIso`s in
`pointedOfPaths.pt` are at `mk`-objects identities, so `liftNatIso_hom_app` reads off the middle
`conjNatIso` component, which is `η x`).

Together with `pointedOfPaths_eq_of_thin` this pins the answer to item 1 *both ways*:
`pointedOfPaths F₀ η = pointedOfPaths F₀ η'` **iff** `η x = η' x` for all `x` — so `η` is
canonical (forced by `F₀`) **exactly** when every path-hom `of x ⟶ F₀ x` is a subsingleton,
i.e. when `FreeGroupoid C` is thin.  Thinness of the *base* `C` is neither used nor sufficient. -/
@[simp] theorem pointedOfPaths_pt_app (F₀ : C → FreeGroupoid C)
    (η : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) (x : C) :
    (pointedOfPaths F₀ η).pt.app ((FreeGroupoid.of C).obj x) = η x := by
  simp only [pointedOfPaths, FreeGroupoid.liftNatIso_hom_app, Iso.trans_hom, eqToIso.hom,
    NatTrans.comp_app, eqToHom_app, conjNatIso, NatIso.ofComponents_hom_app]
  -- the two flanking `eqToHom`s are identities (their object equalities are `rfl`).
  simp

/-- **Path-equality is equivalent to construction-equality** (the exact governing condition for
item 1).  Two object-data give the same pointed endofunctor iff their paths agree pointwise.
The forward direction reads off `pointedOfPaths_pt_app`; the backward is `congrArg`. -/
theorem pointedOfPaths_eq_iff (F₀ : C → FreeGroupoid C)
    (η η' : ∀ x, (FreeGroupoid.of C).obj x ⟶ F₀ x) :
    pointedOfPaths F₀ η = pointedOfPaths F₀ η' ↔ ∀ x, η x = η' x := by
  constructor
  · intro h x
    rw [← pointedOfPaths_pt_app F₀ η x, ← pointedOfPaths_pt_app F₀ η' x]
    -- `h` makes the two pointed endofunctors equal; the `pt`-component-at-`of x` is then `HEq`,
    -- and the two ends have the same type (`A.F.obj (of x)` is defeq `F₀ x` on both sides), so
    -- the `HEq` upgrades to `Eq`.
    apply eq_of_heq
    exact congr_arg_heq (fun A : PointedEndofunctor (FreeGroupoid C) =>
      A.pt.app ((FreeGroupoid.of C).obj x)) h
  · intro h
    have : η = η' := funext h
    rw [this]

end Canonicity

/-! ## 1b. The negative half (stated; the standard π₁ reasoning)

`pointedOfPaths_eq_of_thin` is conditional on `Quiver.IsThin (FreeGroupoid C)`.  The negative
claim — that thinness of `C` (the base) does **not** suffice — is exactly the statement that
`Quiver.IsThin C` does not imply `Quiver.IsThin (FreeGroupoid C)`.  The free groupoid on a thin
category is the fundamental groupoid of its order complex; the four-element poset whose Hasse
diagram is a 4-cycle (the "square" `□¹ ∨ □¹` boundary) has order complex a circle, so its free
groupoid has `End x ≅ ℤ`, hence is *not* thin.  We do not formalize `End x ≅ ℤ` here (it is a
genuine `π₁`-computation, out of scope for this scratch); it is recorded as the OPEN witness in
the companion `.md`.  Consequence: for a generic `K`, the cylinder's `η` is a genuine choice of
homotopy class and is **not** forced by `F₀` alone. -/

/-! ## 1c. The target is a PREORDER on objects (item 2: classification)

Independently of the side conditions, the *target* `PointedEndofunctor (DPathGrpdR K)` is a
groupoid-base pointed-endofunctor category, hence **thin**: `pointedHomOfGroupoid` is the *unique*
morphism between any two objects (the point axiom `pt_A ≫ τ = pt_B` forces `τ = pt_A⁻¹ ≫ pt_B`).
So the classification reduces to the objects: the cylinder construction lands in a *preorder*, and
all the content of `cylToPointedR` is in its **object map** `cylToPointedObj` — the morphism map
carries no information (it is the forced comparison).  This is the codiscreteness already noted in
the cylinder roadmap, here pinned as a `Subsingleton`/`Quiver.IsThin` statement. -/

section TargetThin

variable {𝒢 : Type u} [Groupoid.{v} 𝒢]

/-- **The pointed-endofunctor category of a groupoid is thin.**  Any `τ : A ⟶ B` satisfies the
point axiom `A.pt ≫ τ = B.pt`; since `A.pt` is iso (groupoid base), `τ = A.pt⁻¹ ≫ B.pt` is
forced, so there is at most one morphism `A ⟶ B`. -/
theorem pointedEndofunctor_hom_subsingleton (A B : PointedEndofunctor 𝒢) :
    Subsingleton (A ⟶ B) := by
  refine ⟨fun f g => ?_⟩
  apply PointedEndofunctor.Hom.ext
  have hf : A.pt ≫ f.τ = B.pt := f.w
  have hg : A.pt ≫ g.τ = B.pt := g.w
  rw [← cancel_epi A.pt, hf, hg]

instance pointedEndofunctor_isThin : Quiver.IsThin (PointedEndofunctor 𝒢) :=
  fun A B => pointedEndofunctor_hom_subsingleton A B

/-- Consequently any morphism of pointed endofunctors of a groupoid equals the forced comparison
`pointedHomOfGroupoid`. -/
theorem hom_eq_pointedHomOfGroupoid {A B : PointedEndofunctor 𝒢} (f : A ⟶ B) :
    f = pointedHomOfGroupoid A B :=
  Subsingleton.elim _ _

end TargetThin

/-! ## 2. Transport across `equivWedgeCat` (item 3): the d-path groupoid on the wedge model

The free-groupoid functor sends the equivalence `equivWedgeCat` to an equivalence of groupoids
`DPathGrpdR K ≌ FreeGroupoid (ChainCat.Obj K)`, and pointed endofunctors transport along any
equivalence of categories.  So under the side conditions the pointed-endofunctor *target* may be
computed equivalently on the wedge-map model `ChainCat.Obj K`. -/

section Transport

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- **`FreeGroupoid.map` respects natural isomorphisms.**  From `α : φ ≅ ψ` (functors `C ⥤ D`)
build `map φ ≅ map ψ`: both are `lift (· ⋙ of D)`, so the iso is the `liftNatIso` of `α`
whiskered by `of D`. -/
noncomputable def freeMapNatIso {φ ψ : C ⥤ D} (α : φ ≅ ψ) :
    FreeGroupoid.map φ ≅ FreeGroupoid.map ψ :=
  FreeGroupoid.liftNatIso _ _ (Functor.isoWhiskerRight α (FreeGroupoid.of D))

/-- **The free groupoid of an equivalence is an equivalence of groupoids.**  From `e : C ≌ D`,
`FreeGroupoid.map e.functor`/`FreeGroupoid.map e.inverse` are mutually inverse, the unit/counit
assembled from `e`'s unit/counit via `freeMapNatIso` and the `eqToIso` of the strict laws
`FreeGroupoid.map_comp`/`map_id`.  Built by `Equivalence.mk'` so the triangle coherence is
free in the groupoid target. -/
noncomputable def freeGroupoidEquiv (e : C ≌ D) : FreeGroupoid C ≌ FreeGroupoid D :=
  CategoryTheory.Equivalence.mk (FreeGroupoid.map e.functor) (FreeGroupoid.map e.inverse)
    (eqToIso (FreeGroupoid.map_id C).symm ≪≫ freeMapNatIso e.unitIso
      ≪≫ eqToIso (FreeGroupoid.map_comp e.functor e.inverse))
    (eqToIso (FreeGroupoid.map_comp e.inverse e.functor).symm
      ≪≫ freeMapNatIso e.counitIso ≪≫ eqToIso (FreeGroupoid.map_id D))

/-- **The d-path groupoid on the wedge-map model.**  Under the side conditions, the free
groupoid of `equivWedgeCat` is an equivalence
`DPathGrpdR K = FreeGroupoid (RefineObj …) ≌ FreeGroupoid (ChainCat.Obj K)`. -/
noncomputable def dpathEquivChain {K : BPSet} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) :
    DPathGrpdR K ≌ FreeGroupoid (ChainCat.Obj K) :=
  freeGroupoidEquiv (equivWedgeCat h₁ h₂)

end Transport

/-! ## 3. Pointed endofunctors transport along an equivalence

A pointed endofunctor of `𝒞` transports to one of `𝒟` along any `e : 𝒞 ≌ 𝒟` by conjugating the
endofunctor and the point.  Combined with `dpathEquivChain` this moves the cylinder's
pointed-endofunctor target between the `RefineObj` and `ChainCat.Obj` models under the side
conditions. -/

section PointedTransport

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u} [Category.{v} 𝒟]

/-- **Transport of a pointed endofunctor along an equivalence.**  `F ↦ e⁻¹ ⋙ F ⋙ e`, with the
point `𝟭 ⟹ e⁻¹ ⋙ F ⋙ e` assembled from `e`'s counit and the whiskered point of `F`.  The
`eqToHom` bridges `e⁻¹ ⋙ 𝟭 ⋙ e` and `e⁻¹ ⋙ e` (a `Functor.id_comp`). -/
noncomputable def pointedTransport (e : 𝒞 ≌ 𝒟) (A : PointedEndofunctor 𝒞) :
    PointedEndofunctor 𝒟 where
  F := e.inverse ⋙ A.F ⋙ e.functor
  pt :=
    e.counitIso.inv ≫ eqToHom (by rw [Functor.id_comp]) ≫
      Functor.whiskerLeft e.inverse (Functor.whiskerRight A.pt e.functor)

end PointedTransport

/-! ## 4. The cylinder construction under the side conditions — summary handle

Composing the pieces: under `NonSelfLinked` + `AdmitsAltitude`, the cylinder's pointed
endofunctor `cylToPointedObj c` of `DPathGrpdR K` may be transported to a pointed endofunctor of
the wedge-map free groupoid `FreeGroupoid (ChainCat.Obj K)` via `pointedTransport
(dpathEquivChain …)`.  This is the clean "the construction commutes with the equivalence"
transport requested in item 3. -/

/-- **The cylinder's pointed endofunctor on the wedge-map model** (item 3).  Under the side
conditions, transport `cylToPointedObj c` across `dpathEquivChain` to land in
`PointedEndofunctor (FreeGroupoid (ChainCat.Obj K))`. -/
noncomputable def cylToPointedChain {K : BPSet} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (c : CylMapWeqR K) : PointedEndofunctor (FreeGroupoid (ChainCat.Obj K)) :=
  pointedTransport (dpathEquivChain h₁ h₂) (CylMapR.cylToPointedObj c)

/-! ## 5. Synthesis for the actual cylinder target `DPathGrpdR K`

The pieces above specialise to the live target of the program, `DPathGrpdR K = FreeGroupoid
(RefineObj K.init K.final)`. -/

section Synthesis

variable {K : BPSet}

/-- **The cylinder target is a preorder.**  `PointedEndofunctor (DPathGrpdR K)` is thin
*unconditionally* (`DPathGrpdR K` is a free groupoid, hence a groupoid).  So all the content of
`cylToPointedR` is in its object map; the morphism map is forced. -/
instance dpath_target_isThin : Quiver.IsThin (PointedEndofunctor (DPathGrpdR K)) :=
  pointedEndofunctor_isThin

/-- **Between any two cylinder-images there is at most one comparison.**  Restatement of target
thinness for the construction's objects: the cylinder construction sees cylinders only up to the
*preorder* on `PointedEndofunctor (DPathGrpdR K)`; the morphism map of `cylToPointedR` carries no
information beyond this forced comparison. -/
theorem cylToPointedObj_thin (c c' : CylMapWeqR K) :
    Subsingleton (CylMapR.cylToPointedObj c ⟶ CylMapR.cylToPointedObj c') :=
  pointedEndofunctor_hom_subsingleton _ _

end Synthesis

end Cyl5
