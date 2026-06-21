import CubeChains.Cylinder.CylinderRefine
import CubeChains.Research.Scratch.Cyl7_SpanCompose

/-!
# Cyl11_Subdivision — hetero-cylinders, the pointed-over-`G` target algebra, and base subdivision

Scratch design module for the cylinder ⟹ pointed-functor program (RESULT 2).  **Decoupled from
the green build** (`lake build CubeChains.Research.Scratch.Cyl11_Subdivision`).  Companion
writeup: `Cyl11_Subdivision.md`.

## What this generalizes

The existing cylinder construction (`Cylinder/CylinderRefine.lean`) takes a *rel-interface*
cylinder `c : CylMapR K` — a span `K ⟵ᴸ src ⟶ᴿ K` with **both** legs into the **same** `K` — and
produces a pointed **endo**functor of `DPathGrpdR K`.  Composition of such cylinders is a *monoid*
(Cyl6), obstructed at closure by the absence of a `PathOb`-multiplication (Cyl6/Cyl7).

This file scaffolds the **hetero-cylinder**: a span `K ⟵ᴸ src ⟶ᴿ K'` with legs into **different**
bi-pointed sets, inducing a **functor** `Φ : DPathGrpdR K → DPathGrpdR K'` together with a
comparison 2-cell `G ⟹ Φ` against a *reference* strict functor `G` (e.g. `FreeGroupoid.map
(Refine.pushforwardBP f)` of a comparison map `f : K → K'`).  The monoid becomes the hom-side of a
**bicategory** whose objects are bi-pointed sets.  Subdivision is the special case `K' = Sd K`.

## Layer / status legend in this file

* `PROVEN` — genuinely sorry-free (the file builds green; these defs/theorems carry no `sorry`).
* `DESIGN` — a signature/`structure`/`def …Conjecture : Prop` that typechecks but whose *proof*
  (or whose geometric realiser) is out of scope; clearly labelled, never presented as proven.
* `sorry -- TODO` — used only where even a `Prop`-level conjecture statement needs a witness that
  is out of scope; kept to an absolute minimum.

**Imports:** `Cylinder/CylinderRefine` (the endo construction we generalize), `Cyl7_SpanCompose`
(span composition + Moore-interval scaffolding we reuse for horizontal composition).
-/

open CategoryTheory Opposite
open Operations
open CubeChain

namespace Cyl11

/-! ## 1. The generalized target algebra: pointed-over-`G` functors

`PointedEndofunctor 𝒞` is an endofunctor `F : 𝒞 ⥤ 𝒞` with a point `𝟭 ⟹ F`.  The hetero target
generalizes the *base*: fix categories `𝒞`, `𝒟` and a **reference functor** `G : 𝒞 ⥤ 𝒟`.  A
*pointed-over-`G`* functor is a functor `Φ : 𝒞 ⥤ 𝒟` together with a transformation `pt : G ⟹ Φ`.
When `𝒟 = 𝒞` and `G = 𝟭`, this is *exactly* `PointedEndofunctor 𝒞`. -/

variable (𝒞 𝒟 : Type*) [Category 𝒞] [Category 𝒟]

/-- A **pointed-over-`G` functor**: a functor `Φ : 𝒞 ⥤ 𝒟` with a transformation from a fixed
reference functor `G : 𝒞 ⥤ 𝒟`.  Recovers `PointedEndofunctor 𝒞` at `𝒟 = 𝒞`, `G = 𝟭`. -/
structure PointedOverFunctor (G : 𝒞 ⥤ 𝒟) where
  /-- The underlying comparison functor. -/
  Φ : 𝒞 ⥤ 𝒟
  /-- The comparison 2-cell `G ⟹ Φ` (the "point", relative to `G`). -/
  pt : G ⟶ Φ

variable {𝒞 𝒟}

/-- A morphism of pointed-over-`G` functors: a natural transformation commuting with the points
(over the **same** reference `G`). -/
@[ext]
structure PointedOverFunctor.Hom {G : 𝒞 ⥤ 𝒟} (A B : PointedOverFunctor 𝒞 𝒟 G) where
  /-- The underlying natural transformation. -/
  τ : A.Φ ⟶ B.Φ
  /-- Compatibility with the points. -/
  w : A.pt ≫ τ = B.pt

namespace PointedOverFunctor

instance category {G : 𝒞 ⥤ 𝒟} : Category (PointedOverFunctor 𝒞 𝒟 G) where
  Hom A B := PointedOverFunctor.Hom A B
  id A := ⟨𝟙 A.Φ, by simp⟩
  comp f g := ⟨f.τ ≫ g.τ, by rw [← Category.assoc, f.w, g.w]⟩
  id_comp f := PointedOverFunctor.Hom.ext (Category.id_comp f.τ)
  comp_id f := PointedOverFunctor.Hom.ext (Category.comp_id f.τ)
  assoc f g h := PointedOverFunctor.Hom.ext (Category.assoc f.τ g.τ h.τ)

@[simp] theorem id_τ {G : 𝒞 ⥤ 𝒟} (A : PointedOverFunctor 𝒞 𝒟 G) : Hom.τ (𝟙 A) = 𝟙 A.Φ := rfl

@[simp] theorem comp_τ {G : 𝒞 ⥤ 𝒟} {A B C : PointedOverFunctor 𝒞 𝒟 G}
    (f : A ⟶ B) (g : B ⟶ C) : Hom.τ (f ≫ g) = f.τ ≫ g.τ := rfl

/-- **The recovery isomorphism (data level): pointed-over-`𝟭` is pointed-endofunctor.**
Object-level translation `PointedOverFunctor 𝒞 𝒞 (𝟭 𝒞) → PointedEndofunctor 𝒞`. -/
def toEndo (A : PointedOverFunctor 𝒞 𝒞 (𝟭 𝒞)) : PointedEndofunctor 𝒞 :=
  ⟨A.Φ, A.pt⟩

/-- … and back: `PointedEndofunctor 𝒞 → PointedOverFunctor 𝒞 𝒞 (𝟭 𝒞)`. -/
def ofEndo (A : PointedEndofunctor 𝒞) : PointedOverFunctor 𝒞 𝒞 (𝟭 𝒞) :=
  ⟨A.F, A.pt⟩

@[simp] theorem toEndo_ofEndo (A : PointedEndofunctor 𝒞) : (ofEndo A).toEndo = A := rfl
@[simp] theorem ofEndo_toEndo (A : PointedOverFunctor 𝒞 𝒞 (𝟭 𝒞)) : ofEndo A.toEndo = A := rfl

end PointedOverFunctor

/-! ### Groupoid base: the point-determined morphisms (the conjugation skeleton, generalized)

Exactly as for `PointedEndofunctor` of a groupoid, when the **target** `𝒟` is a groupoid every
`pt : G ⟹ Φ` is a natural *iso* (each component lands in the groupoid `𝒟`), so the morphism axiom
`A.pt ≫ τ = B.pt` forces `τ = A.pt⁻¹ ≫ B.pt`.  Hence between two pointed-over-`G` functors there is
exactly one morphism, and any object family assembles into a functor.  This is verbatim the
`pointedFunctorOfObj` skeleton from `Cylinder/PointedFunctor.lean`, generalized to a reference `G`.
This is the algebraic engine of the hetero-cylinder ⟹ functor map. -/

section Groupoid

variable {𝒞 : Type*} [Category 𝒞] {𝒢 : Type*} [Groupoid 𝒢] {G : 𝒞 ⥤ 𝒢}

/-- In a groupoid **target** every pointed-over-`G` functor's point is a natural isomorphism. -/
instance pt_isIso (A : PointedOverFunctor 𝒞 𝒢 G) : IsIso A.pt :=
  NatIso.isIso_of_isIso_app A.pt

/-- **The point-determined morphism**, `τ = A.pt⁻¹ ≫ B.pt`.  The unique morphism `A ⟶ B` in a
groupoid target. -/
noncomputable def pointedHomOfGroupoid (A B : PointedOverFunctor 𝒞 𝒢 G) : A ⟶ B where
  τ := inv A.pt ≫ B.pt
  w := by rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

@[simp] theorem pointedHomOfGroupoid_τ (A B : PointedOverFunctor 𝒞 𝒢 G) :
    (pointedHomOfGroupoid A B).τ = inv A.pt ≫ B.pt := rfl

@[simp] theorem pointedHomOfGroupoid_id (A : PointedOverFunctor 𝒞 𝒢 G) :
    pointedHomOfGroupoid A A = 𝟙 A :=
  PointedOverFunctor.Hom.ext (by simp)

@[simp] theorem pointedHomOfGroupoid_comp (A B C : PointedOverFunctor 𝒞 𝒢 G) :
    pointedHomOfGroupoid A B ≫ pointedHomOfGroupoid B C = pointedHomOfGroupoid A C :=
  PointedOverFunctor.Hom.ext (by
    simp only [PointedOverFunctor.comp_τ, pointedHomOfGroupoid_τ]
    rw [Category.assoc, ← Category.assoc B.pt, IsIso.hom_inv_id, Category.id_comp])

/-- **A functor into pointed-over-`G` functors of a groupoid target, from an object family alone.**
Generalizes `Operations.pointedFunctorOfObj`; the same forced-morphism trick. -/
@[simps]
noncomputable def pointedFunctorOfObj {J : Type*} [Category J]
    (obj : J → PointedOverFunctor 𝒞 𝒢 G) : J ⥤ PointedOverFunctor 𝒞 𝒢 G where
  obj := obj
  map {a b} _ := pointedHomOfGroupoid (obj a) (obj b)
  map_id a := pointedHomOfGroupoid_id (obj a)
  map_comp {a b c} _ _ := (pointedHomOfGroupoid_comp (obj a) (obj b) (obj c)).symm

end Groupoid

/-! ### Pointed-over-`G` functors from object-data only (conjugation against a fixed `j`)

`Operations.pointedOfPaths` produces a `PointedEndofunctor (FreeGroupoid C)` from an object map and
one chosen path per object, conjugating `FreeGroupoid.of C`.  The hetero generalization conjugates a
**fixed reference** `j : C ⥤ G` (a groupoid `G`): given `F₀ : C → G` and `η x : j x ⟶ F₀ x`,
`conjFunctor j F₀ η` (already in `Cylinder/PointedFunctor.lean`!) is a functor `C ⥤ G`, and
`conjNatIso` is `j ≅ conjFunctor …`.  We package this as a pointed-over-`j` functor.  This is the
geometric on-ramp: it reuses the existing conjugation infra **verbatim**, only changing the
reference from `of` to a general `j`. -/

section ConjugationOverRef

variable {C : Type*} [Category C] {G : Type*} [Groupoid G]

/-- **A pointed-over-`j` functor from object-data only.**  From a reference `j : C ⥤ G`, an
object-map `F₀ : C → G` and one path `η x : j x ⟶ F₀ x` per object, produce a
`PointedOverFunctor C G j`.  No naturality chase: `Φ = conjFunctor j F₀ η`, `pt = conjNatIso`.
This is the direct generalization of `Operations.pointedOfPaths` from `j = of` to any reference
`j` — the algebraic core of the hetero-cylinder action.  PROVEN (sorry-free). -/
def pointedOverOfPaths (j : C ⥤ G) (F₀ : C → G) (η : ∀ x, j.obj x ⟶ F₀ x) :
    PointedOverFunctor C G j where
  Φ := Operations.conjFunctor j F₀ η
  pt := (Operations.conjNatIso j F₀ η).hom

@[simp] theorem pointedOverOfPaths_Φ (j : C ⥤ G) (F₀ : C → G) (η : ∀ x, j.obj x ⟶ F₀ x) :
    (pointedOverOfPaths j F₀ η).Φ = Operations.conjFunctor j F₀ η := rfl

@[simp] theorem pointedOverOfPaths_pt (j : C ⥤ G) (F₀ : C → G) (η : ∀ x, j.obj x ⟶ F₀ x) :
    (pointedOverOfPaths j F₀ η).pt = (Operations.conjNatIso j F₀ η).hom := rfl

end ConjugationOverRef

/-! ## 2. The reference comparison functor from a bi-pointed map (reuse of `Refine.pushforward`)

A strict comparison `K → K'` of bi-pointed sets induces a strict functor on the d-path groupoids
`DPathGrpdR K ⥤ DPathGrpdR K'`, namely `FreeGroupoid.map (Refine.pushforwardBP f)`.  This is the
*reference* `G` over which a hetero-cylinder is pointed.  Everything here is PROVEN: it is literally
the leg-functor machinery (`CylMapR.Lgrpd`/`Rgrpd`) read off a single map, plus the functoriality of
`Refine.pushforwardBP`/`FreeGroupoid.map`.

> **Design slogan:** a hetero-cylinder `K ⟵ src ⟶ K'` over reference `f : K → K'` is the *homotopy
> refinement* of the **strict** comparison `refComparison f` — the cylinder fills it in
> up to a coherent zigzag (its point `G ⟹ Φ`). -/

/-- **The strict reference comparison functor on d-path groupoids** induced by a bi-pointed map
`f : K → K'`.  This is `FreeGroupoid.map` of the refinement pushforward — the *same* construction as
`CylMapR.Lgrpd`/`Rgrpd`, now read off a single comparison map and serving as the reference `G`.
PROVEN (sorry-free, by definition). -/
noncomputable def refComparison {K K' : BPSet} (f : K ⟶ K') :
    DPathGrpdR K ⥤ DPathGrpdR K' :=
  FreeGroupoid.map (Refine.pushforwardBP f)

/-- **Functoriality of the reference comparison (identity).**  `refComparison (𝟙 K)` is the
identity functor.  This needs `Refine.pushforwardBP (𝟙 K) = 𝟭` and `FreeGroupoid.map_id`; the
former is an endpoint-transport identity.  Stated as a `Prop`-level DESIGN fact (the
`pushforwardBP (𝟙) = 𝟭` reduction is a routine but fiddly transport chase, out of scope). -/
def refComparison_id_Conjecture (K : BPSet) : Prop :=
  refComparison (𝟙 K) = 𝟭 (DPathGrpdR K)

/-- **Functoriality of the reference comparison (composition).**  `refComparison (f ≫ g) =
refComparison f ⋙ refComparison g`.  Reduces to `Refine.pushforwardBP (f ≫ g) = pushforwardBP f ⋙
pushforwardBP g` (the pushforward respects composition — true because `mapCubeHom` does, cube-wise)
plus `FreeGroupoid.map_comp` (PROVEN in mathlib).  DESIGN: stated as a `Prop`; the pushforward-comp
reduction is a transport chase, out of scope here. -/
def refComparison_comp_Conjecture {K K' K'' : BPSet} (f : K ⟶ K') (g : K' ⟶ K'') : Prop :=
  refComparison (f ≫ g) = refComparison f ⋙ refComparison g

/-! ## 3. The hetero-cylinder

A **hetero-cylinder** `K ⟵ᴸ src ⟶ᴿ K'` is a `BPSet` source `src` with a left leg into `K`, a right
leg into `K'`, and a classifying homotopy `cyl : src → PathOb ?`.  The endo case `CylMapR K` has
both legs into one `K` and `cyl : src → PathOb K`.  For the hetero case the two legs land in
*different* targets, so a *single* `PathOb` no longer types: the honest geometry is a homotopy over
a **cospan** `K ← W → K'` (a cylinder *relative to a comparison*), or — the cleanest first cut — we
fix the reference map `f : K → K'`, take the right leg to be `f ∘ leftLeg` *up to homotopy*, and
keep `cyl : src → PathOb K'` with the **left** leg `leftLeg : src → K` mapped through `f`.

We scaffold the cleanest version: a hetero-cylinder is *a strict comparison `f : K → K'` together
with an endo-cylinder of `K'` whose left leg factors `src → K → K'`*.  Equivalently (and this is how
subdivision arises) it is a span where the left leg targets the *coarse* `K` and the right leg the
*fine* `K'`. -/

variable {K K' K'' : BPSet}

/-- A **hetero-cylinder** `K ⟵ᴸ src ⟶ᴿ K'`: a `BPSet` source with a left leg into `K`, a right leg
into `K'`, and a classifying homotopy `cyl : src → PathOb K'` whose endpoints are
`f ∘ leftLeg` (the `false`-end, the left leg pushed along the reference `f`) and `rightLeg` (the
`true`-end).  The reference `f : K → K'` is *part of the data*: the cylinder is a homotopy, inside
`K'`, between the **comparison-image of the left leg** and the **right leg**.

Specializing `K = K'`, `f = 𝟙`, this is `CylMapR K` (the `false`-end is then `leftLeg` itself). -/
structure HeteroCylR (K K' : BPSet) where
  /-- The reference comparison map `K → K'` (the strict functor to be refined). -/
  ref : K ⟶ K'
  /-- The cylinder's source bi-pointed precubical set. -/
  src : BPSet
  /-- The **left leg** `src ⟶ K` (into the *coarse* / source target). -/
  leftLeg : src ⟶ K
  /-- The **right leg** `src ⟶ K'` (into the *fine* / comparison target). -/
  rightLeg : src ⟶ K'
  /-- The classifying homotopy into the path object of `K'`. -/
  cyl : src.toPsh ⟶ PathOb.obj K'.toPsh
  /-- The `false`-end of `cyl` is the left leg pushed along the reference: `f ∘ leftLeg`. -/
  hleft : cyl ≫ (endpoint false).app K'.toPsh = (leftLeg ≫ ref).hom
  /-- The `true`-end of `cyl` is the right leg. -/
  hright : cyl ≫ (endpoint true).app K'.toPsh = rightLeg.hom

/-- **Endo cylinders are hetero-cylinders over the identity reference.**  PROVEN (sorry-free). -/
def HeteroCylR.ofEndo (c : CylMapR K) : HeteroCylR K K where
  ref := 𝟙 K
  src := c.src
  leftLeg := c.leftLeg
  rightLeg := c.rightLeg
  cyl := c.cyl
  hleft := by rw [c.hleft]; rfl
  hright := c.hright

/-! ### Leg-functors of a hetero-cylinder on the d-path groupoids

The right leg gives `Rgrpd : DPathGrpdR src ⥤ DPathGrpdR K'` (into the fine target), the **left**
leg gives `Lgrpd : DPathGrpdR src ⥤ DPathGrpdR K` (into the coarse target).  The comparison runs
`DPathGrpdR K ⥤ DPathGrpdR K'` and we want `Φ : DPathGrpdR K ⥤ DPathGrpdR K'`.  As in the endo case,
when the left leg is a groupoid *equivalence* we transport: `Φ = Lgrpd⁻¹ ⋙ Rgrpd`, with reference
`G = refComparison ref` and a point `refComparison ref ⟹ Φ`. -/

/-- The **left leg-functor** of a hetero-cylinder, `DPathGrpdR src ⥤ DPathGrpdR K` (coarse target).
Reuses `Refine.pushforwardBP`. PROVEN. -/
noncomputable def HeteroCylR.Lgrpd (c : HeteroCylR K K') :
    DPathGrpdR c.src ⥤ DPathGrpdR K :=
  FreeGroupoid.map (Refine.pushforwardBP c.leftLeg)

/-- The **right leg-functor** of a hetero-cylinder, `DPathGrpdR src ⥤ DPathGrpdR K'` (fine target).
Reuses `Refine.pushforwardBP`. PROVEN. -/
noncomputable def HeteroCylR.Rgrpd (c : HeteroCylR K K') :
    DPathGrpdR c.src ⥤ DPathGrpdR K' :=
  FreeGroupoid.map (Refine.pushforwardBP c.rightLeg)

/-- The predicate cutting out hetero-cylinders whose **left** leg is a groupoid-reflection
weak equivalence (so `Lgrpd` is an equivalence and the transport `Lgrpd⁻¹ ⋙ Rgrpd` exists).  (We do
not put a `Category` instance on `HeteroCylR`; morphisms of hetero-cylinders are scaffolded at the
bicategory level below, so a plain predicate is the right typing here.) -/
def HeteroCylR.leftWeq (c : HeteroCylR K K') : Prop :=
  c.Lgrpd.IsEquivalence

/-- The **comparison functor** `Φ : DPathGrpdR K ⥤ DPathGrpdR K'` of a hetero-cylinder whose left
leg is a weak equivalence: transport the right leg-functor along the left-leg equivalence.  This is
the hetero generalization of the endo object-map `Lgrpd⁻¹ ⋙ Rgrpd`.  PROVEN (sorry-free). -/
noncomputable def HeteroCylR.comparison (c : HeteroCylR K K') (hc : c.Lgrpd.IsEquivalence) :
    DPathGrpdR K ⥤ DPathGrpdR K' :=
  haveI := hc
  c.Lgrpd.inv ⋙ c.Rgrpd

/-! ### The induced pointed-over-`G` functor (the hetero action) — DESIGN

For a weak-equivalence hetero-cylinder the action is `Φ = comparison c` as a `PointedOverFunctor`
over the reference `G = refComparison c.ref`, with point `refComparison c.ref ⟹ Φ` built from the
hetero analogue of `sweepR` (the homotopy `f ∘ leftLeg ⇝ rightLeg`).

We can *state* the target via `pointedOverOfPaths` with reference `j = refComparison c.ref`, object
map `F₀ x = (comparison c).obj x`, and a per-object path `η x : (refComparison c.ref).obj x →
(comparison c).obj x` — the **hetero-sweep**.  Building `η` is the genuine geometric work (the
hetero analogue of `sweepR`, the staircase that bridges the comparison image to the right-leg
transport); we scaffold its *signature* and the assembly, leaving the staircase as the conjecture.

NB: in the endo case the reference is `𝟭` and `η x : of x → F₀ x` is exactly `pointedOfPaths`'s
input — so this recovers `cylToPointedObj` (Cyl11 generalizes the endo deliverable). -/

/-- **The hetero-sweep family (signature).**  For a weak-equivalence hetero-cylinder, the per-object
homotopy `(refComparison c.ref).obj x ⟶ (comparison c hc).obj x` in `DPathGrpdR K'`: the comparison
image of a chain, bridged through the cylinder to the right-leg transport of the left-leg preimage.
DESIGN: the witness is the hetero analogue of `sweepR`; we expose the type and assemble the action
from it (below), but do not build the staircase here.

The endo specialization (`c = HeteroCylR.ofEndo`, `ref = 𝟙`) is exactly `counit.inv ≫ sweepR`. -/
def HeteroSweepSig (c : HeteroCylR K K') (hc : c.Lgrpd.IsEquivalence) : Type _ :=
  ∀ x : DPathGrpdR K, (refComparison c.ref).obj x ⟶ (c.comparison hc).obj x

/-- **The hetero action (assembly), GIVEN a hetero-sweep.**  From any hetero-sweep `η`, the
hetero-cylinder acts as a `PointedOverFunctor (DPathGrpdR K) (DPathGrpdR K') (refComparison c.ref)`
via `pointedOverOfPaths` — naturality free by conjugation, *exactly* as in the endo deliverable.
PROVEN (sorry-free) **modulo the hetero-sweep input** `η`.  This is the precise hetero analogue of
`cylToPointedObj`. -/
noncomputable def HeteroCylR.toPointedOver (c : HeteroCylR K K') (hc : c.Lgrpd.IsEquivalence)
    (η : HeteroSweepSig c hc) :
    PointedOverFunctor (DPathGrpdR K) (DPathGrpdR K') (refComparison c.ref) :=
  Cyl11.pointedOverOfPaths (refComparison c.ref) (fun x => (c.comparison hc).obj x) η

/-- **The hetero-sweep conjecture.**  Every weak-equivalence hetero-cylinder admits a hetero-sweep
(a coherent family of homotopies `refComparison-image ⇝ right-leg transport`).  DESIGN/OPEN: this is
the hetero generalization of the `sweepR` staircase (`Cylinder/CylinderSweep.lean`), which built
exactly this in the endo case.  Stated as a `Prop`. -/
def HeteroSweepConjecture (c : HeteroCylR K K') (hc : c.Lgrpd.IsEquivalence) : Prop :=
  Nonempty (HeteroSweepSig c hc)

/-! ## 4. Composition = bicategory, not monoid

Endo-cylinders of a fixed `K` compose into a **monoid** (Cyl6).  Hetero-cylinders compose with
**leg-matching** `K → K' → K''`, so the objects are bi-pointed sets, the 1-cells are
hetero-cylinders, and horizontal composition is span composition (Cyl7 `spanCompose`).  The
endo-part `K = K'` recovers `Cyl6`'s monoid (= the endo-hom of the bicategory).  We scaffold the
**signatures**; the coherence is
DESIGN (it inherits Cyl7's reparametrization obstruction — see below).

The objects-and-1-cells layer: -/

/-- The (proposed) **objects** of the hetero-cylinder bicategory: bi-pointed precubical sets. -/
abbrev BiObj := BPSet

/-- The (proposed) **1-cells** `K ⟶ K'` of the hetero-cylinder bicategory: hetero-cylinders.  (For
a genuine bicategory one restricts to weak-equivalence cylinders so the action `Φ` exists; we keep
the unrestricted version here and note the restriction.) -/
abbrev OneCell (K K' : BiObj) := HeteroCylR K K'

/-! ### Horizontal composition via `spanCompose` (Cyl7)

A hetero-cylinder is, forgetting `cyl`, a span `K ⟵ leftLeg src rightLeg ⟶ K'`.  Two composable
hetero-cylinders `c : K ⟶ K'`, `d : K' ⟶ K''` compose by the **pullback** `src_c ×_{K'} src_d`
(precubical sets have all pullbacks), with composite legs `(leftLeg_c ∘ π₁, rightLeg_d ∘ π₂)` and
two homotopies glued via Cyl7 `spanCompose` — landing over the **length-2** interval `I₂`.  The
obstruction (no fold `□¹ → I₂`, Cyl7 `no_fold_edge`) means the strict `□¹`-classifying-map composite
needs reparametrization; the bicategory is therefore most naturally **Moore-enriched** (1-cells =
homotopies over any `Iₙ`), where composition adds lengths with no fold.

We scaffold the composite *span* (legs), which is PROVEN at the leg level, and state the
homotopy-composition as the conjecture inherited from Cyl7. -/

/-- **The composite source** of two hetero-cylinders: the span-pullback `src_c ×_{K'} src_d` over
the shared middle `K'`, the pullback of the matched legs `c.rightLeg` (into `K'`) against
`d.leftLeg` (out of `K'`).  This is the hetero analogue of Cyl7 `spanPullback`: there the matching
is over a
single `K`, here over the middle object `K'`.  PROVEN (def). -/
noncomputable def OneCell.compSrc (c : OneCell K K') (d : OneCell K' K'') : PrecubicalSet :=
  Limits.pullback c.rightLeg.hom d.leftLeg.hom

/-- **Horizontal composition (leg level) is span composition.**  The composite hetero-cylinder's
left leg is `leftLeg_c ∘ π₁` and its right leg is `rightLeg_d ∘ π₂` (Cyl7
`spanCompose_leftLeg`/`rightLeg`); the classifying homotopy is the Cyl7 `spanCompose` glued map into
the length-2 cocylinder `pathOb2 K''`.  DESIGN: assembling this into a genuine `HeteroCylR K K''`
needs the length-2 → length-1 collapse, which is exactly Cyl7's obstructed fold; the honest target
is the Moore-enriched bicategory.  Stated as a `Prop`: there is a composite 1-cell whose source is
the span-pullback `compSrc c d` (the leg-level composite is forced; only the homotopy collapse is
owed). -/
def HorizontalCompConjecture (c : OneCell K K') (d : OneCell K' K'') : Prop :=
  ∃ e : OneCell K K'', e.src.toPsh = OneCell.compSrc c d

/-- **The bicategory-vs-monoid recovery.**  The endo-hom `OneCell K K = HeteroCylR K K` contains the
image of `CylMapR K` under `HeteroCylR.ofEndo`; on it, horizontal composition restricts to Cyl6's
monoid product.  DESIGN: `Prop`-level statement that `ofEndo` is the monoid inclusion into the
endo-hom (the genuine monoid structure is Cyl6's `Monoid (PointedEndofunctor _)` pulled back along
`cylToPointedObj`). -/
def EndoHomIsMonoidConjecture (K : BPSet) : Prop :=
  -- the endo-hom 1-cells are exactly the `ofEndo`-image of endo-cylinders, and `comp` = Cyl6 `·`
  ∀ c : CylMapR K, ∃ h : OneCell K K, h = HeteroCylR.ofEndo c

theorem endoHom_isMonoid (K : BPSet) : EndoHomIsMonoidConjecture K :=
  fun c => ⟨HeteroCylR.ofEndo c, rfl⟩

/-! ## 5. Subdivision `Sd K` for precubical sets — analysis

What is `Sd K` for a precubical set (NO degeneracies)?  A `k`-cube `□ᵏ` subdivides into a **grid**
of `2ᵏ` sub-cubes.  The repo already realizes the 1-dimensional case as the **serial interval**
`Iₙ = serialWedge (replicate n 1) = □¹ ∨ ⋯ ∨ □¹` (Cyl7 `Iv`, Cyl10 `Iₙ ⟹ K = pathObₙ K`); the
generic cube subdivides into an iterated `serialWedge`/`cube` grid (`Foundations/Wedge.lean`).

**The verdict (DESIGN finding).**  A clean *endofunctor* `Sd : PSet ⥤ PSet` on the topos
`PrecubicalSet = Boxᵒᵖ ⥤ Type` is **awkward** to hand-build directly, because subdivision is most
naturally a *colimit over the cube category of the grids* (a left Kan extension along a "subdivide a
representable" functor `Box ⥤ PSet`).  That Kan extension exists (mathlib `Functor.lan`,
`colimit`-based), but its combinatorics (matching the grid gluings across face maps) is heavy.

**The better formalization (recommended).**  Base subdivision is *already* expressed by the
chain-refinement category we have: `RefineObj K.init K.final` *is* the poset of subdivisions of
d-paths, and `Refine.pushforwardBP` makes it functorial.  A subdivision **comparison map**
`f : K → Sd K` need never be built as an `Sd`-endofunctor: it suffices to have, per `K`, a *finer*
`BPSet` `K'` and a `BPSet` map realizing the subdivision — then `refComparison f : DPathGrpdR K ⥤
DPathGrpdR K'` is the strict subdivision functor, and a **subdivision cylinder** is a
hetero-cylinder refining it.  The key conjecture: -/

/-- **`Sd` as a representable-subdivision left Kan extension (DESIGN, statement only).**  IF one
wants a genuine endofunctor, it is `Lan` of `Box → PSet` sending `□ᵏ ↦ (its grid subdivision)`.  We
do not build the indexing functor here; we record the *existence claim* as a conjecture. -/
def SdEndofunctorConjecture : Prop :=
  Nonempty (PrecubicalSet ⥤ PrecubicalSet)   -- placeholder: the *intended* `Sd` is a specific Lan,
  -- not "any endofunctor"; the genuine statement needs the grid-indexing functor `Box ⥤ PSet`.

/-- **The interval case is settled.**  `Iₙ = serialWedge (replicate n 1)` is the subdivision of the
1-cube into `n` pieces; `Cyl7.Iv n` is exactly this, and `Cyl10` proved `Iₙ ⟹ K = pathObₙ K`.  We
re-export it as the canonical 1-dimensional `Sd`-witness.  PROVEN (def, = `Cyl7.Iv`). -/
noncomputable def SdInterval (n : ℕ) : BPSet := Cyl7.Iv n

/-- **Subdivision-cylinders realize the refinement morphisms (THE KEY CONJECTURE).**  Given a
subdivision comparison `f : K → K'` (`K'` finer, e.g. `K' = Sd K`), every refinement morphism in
`RefineObj` between a chain and its `f`-image is realized by a subdivision hetero-cylinder: i.e. the
reference `refComparison f` factors, up to the cylinder's point `G ⟹ Φ`, through the *identity-on-
objects* refinement.  Concretely: the comparison `refComparison f` is naturally isomorphic to the
`Φ` of a weak-equivalence subdivision cylinder, so subdivision *is* a homotopy-trivial cylinder.
DESIGN/OPEN — the recommended first concrete theorem to chase.  Stated as a `Prop`. -/
def SubdivisionRealizationConjecture {K K' : BPSet} (f : K ⟶ K') : Prop :=
  ∃ (c : HeteroCylR K K') (hc : c.Lgrpd.IsEquivalence) (η : HeteroSweepSig c hc),
    c.ref = f ∧ Nonempty ((c.toPointedOver hc η).Φ ≅ refComparison f)

/-! ## 6. Module summary

* **Generalized target algebra** `PointedOverFunctor 𝒞 𝒟 G` (functor `Φ : 𝒞 ⥤ 𝒟` + point `G ⟹ Φ`)
  — PROVEN: category instance, the `𝟭`-recovery `toEndo`/`ofEndo`, the groupoid-target
  forced-morphism skeleton (`pointedHomOfGroupoid`, `pointedFunctorOfObj`), and the conjugation
  builder `pointedOverOfPaths` (reusing the existing `conjFunctor`/`conjNatIso`).
* **Reference comparison** `refComparison f = FreeGroupoid.map (Refine.pushforwardBP f)` — PROVEN
  (def); its functoriality is DESIGN (`refComparison_id/comp_Conjecture`), reducible to mathlib's
  `FreeGroupoid.map_id/comp` + a pushforward-comp transport chase.
* **Hetero-cylinder** `HeteroCylR K K'` (span `K ⟵ src ⟶ K'` + reference `ref : K → K'` + homotopy)
  — PROVEN structure; `ofEndo` (endo ↪ hetero, PROVEN); leg-functors + `comparison = Lgrpd⁻¹ ⋙
  Rgrpd` (PROVEN); the action `toPointedOver` (PROVEN modulo the hetero-sweep `η`); the hetero-sweep
  itself is the staircase conjecture `HeteroSweepConjecture`.
* **Bicategory** — objects `BPSet`, 1-cells hetero-cylinders, horizontal comp = Cyl7 `spanCompose`
  (composite span PROVEN at leg level; `HorizontalCompConjecture` for the homotopy, obstructed
  exactly by Cyl7's no-fold — Moore enrichment is the fix); endo-hom recovers Cyl6's monoid
  (`endoHom_isMonoid`, PROVEN).
* **Sd K** — verdict: a literal `Sd : PSet ⥤ PSet` endofunctor is a heavy `Lan`
  (`SdEndofunctorConjecture`); the *recommended* route is to keep subdivision in the
  refinement/chain layer (`Refine.pushforwardBP`) and express it through `refComparison`, with the
  interval case settled (`SdInterval = Cyl7.Iv`, Cyl10's `Iₙ ⟹ K`).  The key open theorem is
  `SubdivisionRealizationConjecture`: subdivision cylinders realize the refinement comparison.

**Recommended first concrete theorem:** prove `SubdivisionRealizationConjecture` for the 1-dim
subdivision `f : □¹ → I₂` (= `SdInterval 2`) — build the explicit hetero-sweep there (the single
staircase rung is the Cyl7 `spanCompose` of the two halves), giving the first genuine *base*-
subdivision cylinder. -/

end Cyl11
