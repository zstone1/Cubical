import CubeChains.Operations.Cylinder
import CubeChains.Chains.RefineFunctor
import CubeChains.Operations.PointedFunctor

/-!
# Cylinder maps and their action on the d-path groupoid `Grpd(RefineObj K)` (the live target)

The investigation (`Testing/WedgeMapDivergence.lean`, memory `cubechains-cylinder-roadmap`)
settled that the d-path groupoid for the cylinder ⟹ pointed-functor program must be built on
the **face-poset / refinement category** `RefineObj K.init K.final`, *not* the wedge-map
`ChainCat.Obj K`: for the self-linked `K` that rel-interface cylinders force, the flat chain
ends `b₀`, `b₁` are *isolated* in the wedge-map category (no `Box` morphism `□ᵐ ⟶ □^{m+1}`
preserves both corners), whereas in `RefineObj` the direct cospan `b₀ → R ← b₁` into the prism
cube is a genuine morphism unconditionally.

This file builds the **target side** on `RefineObj`:

* `DPathGrpdR K = FreeGroupoid (RefineObj K.init K.final)` — the d-path homotopy groupoid;
* `CylMapR K` — a **rel-interface cylinder** (a `BPSet` source with two basepoint-preserving
  legs and a classifying map into the path object `PathOb K`); identical data to the wedge-map
  `CylMapB`, only the groupoid it acts on differs;
* the **leg-functors** `Lgrpd`/`Rgrpd : DPathGrpdR src ⥤ DPathGrpdR K`, via
  `FreeGroupoid.map (Refine.pushforward leg)` — now available because
  `Chains/RefineFunctor.lean` makes `RefineObj` functorial in `K` *without* thinness.

The per-chain homotopy (the direct prism cospan `b₀ → R ← b₁`) and the assembly into
`cylToPointedR : CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)` via `pointedOfPaths` are
built on top of this (subsequent sections / files).
-/

open CategoryTheory Opposite
open Operations Operations.Precubical
open CubeChain

variable {K : BPSet}

/-! ## 1. The refinement d-path groupoid -/

/-- The **d-path homotopy groupoid** of a bi-pointed `K`, built on the refinement category:
the groupoid reflection of `RefineObj K.init K.final` (objects = cube chains `init → final`,
morphisms = subdivisions).  This is the live base for the cylinder program (see the file
header); its morphisms are the zigzags of refinements. -/
abbrev DPathGrpdR (K : BPSet) := FreeGroupoid (RefineObj (K := K) K.init K.final)

/-! ## 2. Rel-interface cylinder maps -/

/-- A **rel-interface cylinder map** to `K`: a `BPSet` source `src` with two
basepoint-preserving legs `leftLeg`/`rightLeg : src ⟶ K` and a classifying map
`cyl : src.toPsh ⟶ PathOb K` whose two `endpoint`-evaluations are the legs.  (Identical data
to the wedge-map `CylMapB`; only the groupoid it acts on, `DPathGrpdR`, differs.) -/
structure CylMapR (K : BPSet) where
  /-- The cylinder's source bi-pointed precubical set. -/
  src : BPSet
  /-- The **left leg** `src ⟶ K` (basepoint-preserving). -/
  leftLeg : src ⟶ K
  /-- The **right leg** `src ⟶ K` (basepoint-preserving). -/
  rightLeg : src ⟶ K
  /-- The classifying map into the path object (a directed cubical homotopy). -/
  cyl : src.toPsh ⟶ PathOb.obj K.toPsh
  /-- The `false`-end evaluation of `cyl` is the left leg. -/
  hleft : cyl ≫ (endpoint false).app K.toPsh = leftLeg.hom
  /-- The `true`-end evaluation of `cyl` is the right leg. -/
  hright : cyl ≫ (endpoint true).app K.toPsh = rightLeg.hom

/-! ## 3. Pushforward of refinement chains along a bi-pointed map (basepoint version)

`Refine.pushforward` (`Chains/RefineFunctor.lean`) lands in `RefineObj` re-based at the *image*
vertices `f.app init`, `f.app final`.  For a `BPSet` morphism these are exactly `B.init`,
`B.final` (`app_init`/`app_final`), so the functor restricts to the `(init, final)` chains. -/

/-- **Pushforward of `init → final` refinement chains along a `BPSet` map.**  Specialises
`Refine.pushforward` to the basepoints, using `app_init`/`app_final` to land in
`RefineObj B.init B.final`. -/
noncomputable def Refine.pushforwardBP {A B : BPSet} (f : A ⟶ B) :
    RefineObj (K := A) A.init A.final ⥤ RefineObj (K := B) B.init B.final := by
  rw [← f.app_init, ← f.app_final]
  exact Refine.pushforward f.hom

/-! ## 4. The leg-functors on the d-path groupoid -/

/-- The **left leg-functor** on the d-path groupoid, `DPathGrpdR src ⥤ DPathGrpdR K`, induced
by post-composing chains with the left leg.  Mirrors `CylMapB.Lgrpd`, now on `RefineObj`. -/
noncomputable def CylMapR.Lgrpd (c : CylMapR K) : DPathGrpdR c.src ⥤ DPathGrpdR K :=
  FreeGroupoid.map (Refine.pushforwardBP c.leftLeg)

/-- The **right leg-functor** on the d-path groupoid, induced by the right leg. -/
noncomputable def CylMapR.Rgrpd (c : CylMapR K) : DPathGrpdR c.src ⥤ DPathGrpdR K :=
  FreeGroupoid.map (Refine.pushforwardBP c.rightLeg)

/-! ## 5. The weak-equivalence subcategory of cylinder maps

A morphism of cylinder maps is a `BPSet` map of sources commuting with `cyl` (the legs then
commute automatically, being `endpoint`-evaluations of `cyl`). -/

/-- A **morphism of cylinder maps**: a `BPSet` map of sources commuting with `cyl`. -/
@[ext]
structure CylMapR.Hom (a b : CylMapR K) where
  /-- The underlying `BPSet` map of sources. -/
  hom : a.src ⟶ b.src
  /-- It commutes with the cylinder classifying maps. -/
  w : hom.hom ≫ b.cyl = a.cyl

namespace CylMapR

instance category (K : BPSet) : Category (CylMapR K) where
  Hom a b := CylMapR.Hom a b
  id a := ⟨𝟙 a.src, by rw [BPSet.id_hom, Category.id_comp]⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [BPSet.comp_hom, Category.assoc, g.w, f.w]⟩
  id_comp f := CylMapR.Hom.ext (Category.id_comp _)
  comp_id f := CylMapR.Hom.ext (Category.comp_id _)
  assoc f g h := CylMapR.Hom.ext (Category.assoc _ _ _)

@[simp] theorem id_hom (a : CylMapR K) : CylMapR.Hom.hom (𝟙 a) = 𝟙 a.src := rfl

@[simp] theorem comp_hom {a b c : CylMapR K} (f : a ⟶ b) (g : b ⟶ c) :
    CylMapR.Hom.hom (f ≫ g) = CylMapR.Hom.hom f ≫ CylMapR.Hom.hom g := rfl

end CylMapR

/-- The object-property cutting out cylinder maps whose left leg is a groupoid-reflection weak
equivalence (so `Lgrpd` is an equivalence and the transport `Lgrpd⁻¹ ⋙ Rgrpd` exists). -/
def CylMapR.leftWeq (K : BPSet) : ObjectProperty (CylMapR K) :=
  fun c => c.Lgrpd.IsEquivalence

/-- Cylinder maps whose left leg is a weak equivalence: the full subcategory of `CylMapR K`. -/
abbrev CylMapWeqR (K : BPSet) := (CylMapR.leftWeq K).FullSubcategory

/-- The left leg-functor of a `CylMapWeqR` object is an equivalence. -/
theorem CylMapWeqR.left_weq (c : CylMapWeqR K) : c.obj.Lgrpd.IsEquivalence := c.property
