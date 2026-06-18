import CubeChains.Operations.Precubical
import CubeChains.Operations.Shift
import CubeChains.Operations.PointedFunctor
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import CubeChains.Chains.WedgeMap

/-!
# Cylinder maps and their action on the d-path groupoid (CylinderPlan.md §2, piece 1)

This is Module B of the cylinder ⇒ pointed-functor program.  Building on the path
object `PathOb` (Module A, `Operations/Shift.lean`) and the groupoid/pointed-functor
algebra (`Operations/GroupoidTarget.lean`, `Operations/PointedFunctor.lean`), it
introduces:

* `DPathGrpd K = FreeGroupoid (ChP.obj K)` — the **d-path homotopy groupoid** of `K`,
  i.e. the groupoid reflection `M K = ChP(K)[ChP(K)⁻¹]`, whose arrows are the zigzags
  of `ChP K`;
* `CylMap K` — a **cylinder map** to `K`: a precubical set `src` with a map
  `cyl : src ⟶ PathOb K` (adjoint to a directed cubical homotopy `src ⊗ □¹ ⟶ K`);
* its two legs `leftLeg`/`rightLeg : src ⟶ K` (the `endpoint`-evaluations of `cyl`),
  and the induced **leg-functors** `Lgrpd`/`Rgrpd : DPathGrpd src ⥤ DPathGrpd K`;
* `CylMapWeq K` — cylinder maps whose left leg is a groupoid-reflection weak
  equivalence (so `Lgrpd` is an equivalence), and its category.

The geometric comparison `CylMap.toTransf : Lgrpd ⟶ Rgrpd` (B2) and the resulting
functor `cylToPointed : CylMapWeq K ⥤ PointedEndofunctor (DPathGrpd K)` (B3) are the
**crux** and are *not yet supplied*; see the note at the end of this file for the
precise geometric obstruction.
-/

open CategoryTheory Opposite
open Operations Operations.Precubical

variable {K : PrecubicalSet}

/-! ## The box tensor agrees with the cocylinder (on representables)

The path object `PathOb` is the **internal hom for the box tensor** `(-) ⊗ □¹` (NOT
the cartesian exponential).  The box tensor itself — `□ᵐ ⊗ □ⁿ = □ᵐ⁺ⁿ`, extended to all
precubical sets by colimits — is deferred (it needs Day convolution); but on
representables it is exactly the shift, `□ᵇ ⊗ □¹ := □^{shift b}` (so `□ⁿ ⊗ □¹ = □ⁿ⁺¹`
by `Box.shift_obj`), and the defining adjunction `(-) ⊗ □¹ ⊣ PathOb` already holds
there.  This is the transpose consumed later in B2: a cylinder `□ᵇ ⟶ PathOb K` is the
same data as a prism `□ᵇ ⊗ □¹ = □^{shift b} ⟶ K`, and the two `endpoint`-evaluations of
the cylinder are the two `coface`-ends of that prism. -/

/-- **The box-tensor / cocylinder adjunction on representables.**  A cylinder over the
cube `□ᵇ` (a map `□ᵇ ⟶ PathOb K`) is the same data as a prism `□^{shift b} ⟶ K` over it
(`□^{shift b} = □ᵇ ⊗ □¹`).  Both sides are the `(shift b)`-cells of `K`, identified by
`yonedaEquiv` on each side. -/
def cylTranspose (K : PrecubicalSet) (b : Box) :
    (yoneda.obj b ⟶ PathOb.obj K) ≃ (yoneda.obj (Box.shift.obj b) ⟶ K) :=
  yonedaEquiv.trans (yonedaEquiv (X := Box.shift.obj b) (F := K)).symm

/-- The transpose preserves the underlying cell: both `f` and its prism transpose are
`yonedaEquiv` of the same `(shift b)`-cell of `K`. -/
@[simp] theorem yonedaEquiv_cylTranspose (K : PrecubicalSet) (b : Box)
    (f : yoneda.obj b ⟶ PathOb.obj K) :
    yonedaEquiv (cylTranspose K b f) = yonedaEquiv f :=
  Equiv.apply_symm_apply (yonedaEquiv (X := Box.shift.obj b) (F := K))
    (yonedaEquiv (X := b) (F := PathOb.obj K) f)

/-- **Endpoint compatibility.**  The `ε`-`endpoint` evaluation of a cylinder
`f : □ᵇ ⟶ PathOb K` is the `ε`-`coface` end of its transposed prism: precomposing the
prism `cylTranspose K b f` with the coface `□ᵇ ⟶ □^{shift b}` recovers the leg
`f ≫ endpoint ε`.  (For `f = p ≫ c.cyl` these are exactly `p ≫ c.leftLeg`/`rightLeg`,
i.e. the bottom/top faces of the prism over the chain `p`.) -/
theorem cylTranspose_endpoint (ε : Bool) (K : PrecubicalSet) (b : Box)
    (f : yoneda.obj b ⟶ PathOb.obj K) :
    f ≫ (endpoint ε).app K = yoneda.map ((Box.coface ε).app b) ≫ cylTranspose K b f := by
  have e1 : f = (yonedaEquiv (X := b) (F := PathOb.obj K)).symm (yonedaEquiv f) :=
    (yonedaEquiv.symm_apply_apply f).symm
  conv_lhs => rw [e1]
  rw [show cylTranspose K b f = (yonedaEquiv (X := Box.shift.obj b) (F := K)).symm
        (yonedaEquiv (X := b) (F := PathOb.obj K) f) from rfl,
      yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_right]
  rfl

/-- **Naturality of the transpose in the cube.**  Reindexing the cylinder's domain by a
cube map `g : □ᵇ' ⟶ □ᵇ` is, after transposing, reindexing the prism by `shift g` (the
prism of the reindexing).  This is the per-block naturality the fence comparison
consumes. -/
theorem cylTranspose_naturality {K : PrecubicalSet} {b b' : Box} (g : b' ⟶ b)
    (f : yoneda.obj b ⟶ PathOb.obj K) :
    cylTranspose K b' (yoneda.map g ≫ f)
      = yoneda.map (Box.shift.map g) ≫ cylTranspose K b f := by
  rw [show cylTranspose K b f = (yonedaEquiv (X := Box.shift.obj b) (F := K)).symm
        (yonedaEquiv (X := b) (F := PathOb.obj K) f) from rfl,
      yonedaEquiv_symm_naturality_left,
      show cylTranspose K b' (yoneda.map g ≫ f)
        = (yonedaEquiv (X := Box.shift.obj b') (F := K)).symm
            (yonedaEquiv (X := b') (F := PathOb.obj K) (yoneda.map g ≫ f)) from rfl]
  congr 1
  exact (yonedaEquiv_naturality f g).symm

/-- **Naturality of the transpose in `K`.**  A map of precubical sets `h : K ⟶ L`
commutes with transposing: post-composing a cylinder by `PathOb.map h` and transposing
equals transposing then post-composing the prism by `h`.  (The `§4` endpoint
compatibility, at the transpose level.) -/
theorem cylTranspose_naturality_target {K L : PrecubicalSet} (h : K ⟶ L) (b : Box)
    (f : yoneda.obj b ⟶ PathOb.obj K) :
    cylTranspose L b (f ≫ PathOb.map h) = cylTranspose K b f ≫ h := by
  rw [show cylTranspose K b f = (yonedaEquiv (X := Box.shift.obj b) (F := K)).symm
        (yonedaEquiv (X := b) (F := PathOb.obj K) f) from rfl,
      yonedaEquiv_symm_naturality_right,
      show cylTranspose L b (f ≫ PathOb.map h)
        = (yonedaEquiv (X := Box.shift.obj b) (F := L)).symm
            (yonedaEquiv (X := b) (F := PathOb.obj L) (f ≫ PathOb.map h)) from rfl]
  congr 1

/-! ### The box tensor as a left adjoint (CylinderPlan §5)

`PathOb` is *definitionally* the precomposition `(whiskeringLeft …).obj shift.op`, so its
left adjoint — the box tensor `(-) ⊗ □¹` — is the left Kan extension `shift.op.lan`, and
the cylinder/path adjunction is `shift.op.lanAdjunction`, **off the shelf**.  A cylinder
`src ⟶ PathOb K` therefore transposes *globally* to `src ⊗ □¹ ⟶ K` via the adjunction
hom-equivalence; `cylTranspose` above is its concrete shadow on representables, where the
Yoneda computation `□ⁿ ⊗ □¹ ≅ □ⁿ⁺¹` is far cheaper than the Kan-extension colimit.

We keep cylinders stored as `src ⟶ PathOb K` (the data is then a map into the *concrete*
presheaf `PathOb K`, with `(PathOb K)_n = K_{n+1}`, rather than into an abstract colimit),
and use the tensor only for *geometry*: `(-) ⊗ □¹` is a left adjoint, hence cocontinuous,
so `serialWedge dims ⊗ □¹` is the prism cubes `□^{dᵢ+1}` glued along the vertical edges
over the junctions — the prism decomposition, for free. -/

/-- The box tensor with the interval `(-) ⊗ □¹`, as the left Kan extension along
`shift.op`: the left adjoint of the cocylinder `PathOb`. -/
noncomputable def boxTensorInterval : PrecubicalSet ⥤ PrecubicalSet := Box.shift.op.lan

/-- **The cylinder/path adjunction** `(-) ⊗ □¹ ⊣ PathOb` (CylinderPlan §5): off the shelf,
since `PathOb` is definitionally the precomposition along `shift.op`. -/
noncomputable def cylinderPathAdjunction : boxTensorInterval ⊣ PathOb :=
  Box.shift.op.lanAdjunction Type

/-- **The box tensor is cocontinuous** — being a left adjoint, `(-) ⊗ □¹` preserves all
colimits.  This is the off-the-shelf engine behind the prism decomposition: it makes
`(-) ⊗ □¹` commute with the `serialWedge` pushouts, so the prism over a wedge is the
prisms over its cubes glued along the tensored junctions, with no hand-built comparison. -/
noncomputable instance : Limits.PreservesColimitsOfSize boxTensorInterval :=
  cylinderPathAdjunction.leftAdjoint_preservesColimits

/-- **Prism decomposition of a binary wedge (cocontinuity, for free).**  `(X ∨ Y) ⊗ □¹`
is the pushout of `X ⊗ □¹` and `Y ⊗ □¹` along the tensored junction — the geometric
"edge-glued" structure of the prism, obtained from `PreservesPushout` rather than by
hand.  Iterating this over `serialWedge` gives the prism cubes glued along the vertical
edges over the junctions. -/
noncomputable def boxTensorInterval_wedge2 (X Y : BPSet) :
    boxTensorInterval.obj (BPSet.wedge2 X Y).toPsh
      ≅ Limits.pushout (boxTensorInterval.map X.finalVertex)
          (boxTensorInterval.map Y.initVertex) :=
  (Limits.PreservesPushout.iso boxTensorInterval X.finalVertex Y.initVertex).symm

/-! ### Single-block chains are cubes (the trailing point collapses)

`serialWedge [m] = wedge2 (cube m) (cube 0)` glues a trailing point at `(cube 0).initVertex`,
which is the identity (`cube 0` is a single vertex), so the head inclusion
`serialWedge.ι [m] 0 : cube m ⟶ serialWedge [m]` is an isomorphism.  This dissolves the
trailing-`cube 0` bookkeeping when reasoning about single-block chains. -/

/-- The initial-vertex inclusion of the point `cube 0` is the identity. -/
@[simp] theorem cube0_initVertex_eq_id :
    (BPSet.cube 0).initVertex = 𝟙 (yoneda.obj (Box.ob 0)) := by
  rw [BPSet.initVertex, BPSet.vertexMap, Equiv.symm_apply_eq]
  exact Subsingleton.elim _ _

instance : IsIso ((BPSet.cube 0).initVertex) := by
  rw [cube0_initVertex_eq_id]; exact IsIso.id _

/-- The head inclusion `cube m ⟶ serialWedge [m]` is an isomorphism (the trailing point
collapses): the wedge is `pushout (cube m).finalVertex (cube 0).initVertex` with the right
leg an iso, so `IsPushout.isIso_inl_of_isIso` applies. -/
instance serialWedge_singleton_ι_isIso (m : ℕ+) :
    IsIso (BPSet.serialWedge.ι [m] 0) := by
  change IsIso (Limits.pushout.inl (BPSet.cube (m : ℕ)).finalVertex (BPSet.cube 0).initVertex)
  exact (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso

/-- **A single-block chain is just a cube**: `cube m ≅ serialWedge [m]`, the head
inclusion promoted to an isomorphism. -/
noncomputable def serialWedgeSingletonIso (m : ℕ+) :
    (BPSet.cube (m : ℕ)).toPsh ≅ (BPSet.serialWedge [m]).toPsh :=
  @asIso _ _ _ _ (BPSet.serialWedge.ι [m] 0) (serialWedge_singleton_ι_isIso m)

/-- The final-vertex inclusion of the point `cube 0` is the identity (dual of
`cube0_initVertex_eq_id`). -/
@[simp] theorem cube0_finalVertex_eq_id :
    (BPSet.cube 0).finalVertex = 𝟙 (yoneda.obj (Box.ob 0)) := by
  rw [BPSet.finalVertex, BPSet.vertexMap, Equiv.symm_apply_eq]
  exact Subsingleton.elim _ _

instance : IsIso ((BPSet.cube 0).finalVertex) := by
  rw [cube0_finalVertex_eq_id]; exact IsIso.id _

/-- Prepending the point `cube 0` to a wedge collapses: the right inclusion
`X ⟶ wedge2 (cube 0) X` is an iso. -/
instance wedge2_cube0_inr_isIso (X : BPSet) :
    IsIso (Limits.pushout.inr (BPSet.cube 0).finalVertex X.initVertex) :=
  (IsPushout.of_hasPushout _ _).isIso_inr_of_isIso

/-- **A leading point collapses**: `X ≅ wedge2 (cube 0) X`, the right inclusion promoted
to an iso.  The base case for concatenating chains (`serialWedge ([] ++ ys) ≅
wedge2 (cube 0) (serialWedge ys)`). -/
noncomputable def wedge2Cube0Iso (X : BPSet) :
    X.toPsh ≅ (BPSet.wedge2 (BPSet.cube 0) X).toPsh :=
  @asIso _ _ _ _ (Limits.pushout.inr (BPSet.cube 0).finalVertex X.initVertex)
    (wedge2_cube0_inr_isIso X)

/-- The initial-vertex *map* of `X ∨ Y` factors through the left inclusion. -/
theorem wedge2_initVertex (X Y : BPSet) :
    (BPSet.wedge2 X Y).initVertex
      = X.initVertex ≫ Limits.pushout.inl X.finalVertex Y.initVertex := by
  conv_lhs => rw [show (BPSet.wedge2 X Y).initVertex
    = yonedaEquiv.symm ((BPSet.wedge2 X Y).init) from rfl, CubeChain.wedge2_init']
  exact (yonedaEquiv_symm_naturality_right (Box.ob 0)
    (Limits.pushout.inl X.finalVertex Y.initVertex) X.init).symm

/-- The final-vertex *map* of `X ∨ Y` factors through the right inclusion. -/
theorem wedge2_finalVertex (X Y : BPSet) :
    (BPSet.wedge2 X Y).finalVertex
      = Y.finalVertex ≫ Limits.pushout.inr X.finalVertex Y.initVertex := by
  conv_lhs => rw [show (BPSet.wedge2 X Y).finalVertex
    = yonedaEquiv.symm ((BPSet.wedge2 X Y).final) from rfl, CubeChain.wedge2_final']
  exact (yonedaEquiv_symm_naturality_right (Box.ob 0)
    (Limits.pushout.inr X.finalVertex Y.initVertex) Y.final).symm

/-- **Associativity of the wedge** `(A ∨ B) ∨ C ≅ A ∨ (B ∨ C)`, from mathlib's
`pushoutAssoc` (gluing three bi-pointed sets in a row).  The reusable engine behind
serial-wedge concatenation/associativity. -/
noncomputable def wedge2Assoc (A B C : BPSet) :
    (BPSet.wedge2 (BPSet.wedge2 A B) C).toPsh ≅ (BPSet.wedge2 A (BPSet.wedge2 B C)).toPsh :=
  eqToIso (by
    change Limits.pushout (BPSet.wedge2 A B).finalVertex C.initVertex
      = Limits.pushout
          (B.finalVertex ≫ Limits.pushout.inr A.finalVertex B.initVertex) C.initVertex
    rw [wedge2_finalVertex]; rfl)
  ≪≫ Limits.pushoutAssoc A.finalVertex B.initVertex B.finalVertex C.initVertex
  ≪≫ eqToIso (by
    change Limits.pushout A.finalVertex
          (B.initVertex ≫ Limits.pushout.inl B.finalVertex C.initVertex)
      = Limits.pushout A.finalVertex (BPSet.wedge2 B C).initVertex
    rw [wedge2_initVertex]; rfl)

/-! ### Building chains from cube cells (plain-`PrecubicalSet` port of `wedgeDesc`)

`CubeChain.wedgeDesc` builds `□^∨(cubes) ⟶ K` from a cube chain, but assumes `K : BPSet`.
The cube-chain category here is over a plain `PrecubicalSet`, and `wedgeDesc` never uses
`K`'s basepoints (only `K.toPsh`), so we port it verbatim with `K.toPsh ↦ K`.  This is the
serial-wedge concatenation engine: the fence chains `P_j`/`R_j` are cube chains assembled
from prism faces and vertical edges. -/

/-- A wedge map `□^∨(cubes) ⟶ K` (plain `PrecubicalSet`) bundled with its `init`/`final`
vertices. -/
structure WedgeDescP {K : PrecubicalSet} (a b : K.cells 0)
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) where
  /-- The underlying wedge map. -/
  map : (BPSet.serialWedge (cubes.map (·.1))).toPsh ⟶ K
  /-- It sends the wedge's initial vertex to `a`. -/
  init_spec : map.app (op (Box.ob 0)) (BPSet.serialWedge (cubes.map (·.1))).init = a
  /-- It sends the wedge's final vertex to `b`. -/
  final_spec : map.app (op (Box.ob 0)) (BPSet.serialWedge (cubes.map (·.1))).final = b

/-- Build the classifying wedge map of a cube chain `IsCubeChain a cubes b`, bundled with
its endpoints — the plain-`PrecubicalSet` port of `CubeChain.wedgeDesc`. -/
noncomputable def wedgeDescP {K : PrecubicalSet} (a b : K.cells 0) :
    (cubes : List (Σ n : ℕ+, K.cells (n : ℕ))) → IsCubeChain a cubes b →
    WedgeDescP a b cubes
  | [], h =>
      { map := yonedaEquiv.symm a
        init_spec := by
          simp only [List.map_nil, BPSet.serialWedge_nil]
          rw [show (BPSet.cube 0).init = 𝟙 (Box.ob 0) from Subsingleton.elim _ _]
          exact yonedaEquiv.apply_symm_apply a
        final_spec := by
          simp only [List.map_nil, BPSet.serialWedge_nil]
          rw [show (BPSet.cube 0).final = 𝟙 (Box.ob 0) from Subsingleton.elim _ _]
          exact (yonedaEquiv.apply_symm_apply a).trans h }
  | ⟨n, c⟩ :: rest, h =>
      let r := wedgeDescP (K.vertex₁ c) b rest h.2
      { map := Limits.pushout.desc (yonedaEquiv.symm c) r.map (by
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp, BPSet.finalVertex, BPSet.initVertex, BPSet.vertexMap,
            Equiv.apply_symm_apply]
          rw [r.init_spec]; rfl)
        init_spec := by
          simp only [List.map_cons, BPSet.serialWedge_cons, CubeChain.wedge2_init']
          exact (CubeChain.inl_desc_app _).trans h.1
        final_spec := by
          simp only [List.map_cons, BPSet.serialWedge_cons, CubeChain.wedge2_final']
          exact (CubeChain.inr_desc_app _).trans r.final_spec }

/-- The **d-path homotopy groupoid** of `K`: the groupoid reflection
`M K = ChP(K)[ChP(K)⁻¹]` of the cube-chain category, whose morphisms are exactly the
zigzags of `ChP K`. -/
abbrev DPathGrpd (K : PrecubicalSet) := FreeGroupoid (ChP.obj K)

/-- A **cylinder map** to `K`: an object of the over-category `Over (PathOb K)` — a
precubical set with a map to the path object (a directed cubical homotopy
`src ⊗ □¹ ⟶ K` by the box-tensor adjunction).  Reusing `Over` inherits its `Category`
instance, the forgetful functor, and all comma-category API (no hand-rolled structure
or category instance). -/
abbrev CylMap (K : PrecubicalSet) := Over (PathOb.obj K)

/-- The cylinder's source precubical set (the over-object's domain). -/
abbrev CylMap.src (c : CylMap K) : PrecubicalSet := c.left

/-- The classifying map into the path object (the over-object's structure map). -/
abbrev CylMap.cyl (c : CylMap K) : c.src ⟶ PathOb.obj K := c.hom

/-- The **left leg** `src ⟶ K`: evaluate the cylinder at the `false`-end. -/
def CylMap.leftLeg (c : CylMap K) : c.src ⟶ K := c.cyl ≫ (endpoint false).app K

/-- The **right leg** `src ⟶ K`: evaluate the cylinder at the `true`-end. -/
def CylMap.rightLeg (c : CylMap K) : c.src ⟶ K := c.cyl ≫ (endpoint true).app K

/-- The **prism cube over a single block** `p : □ⁿ ⟶ c.src` of a cylinder: the
transpose (`cylTranspose`) of the restricted cylinder `p ≫ c.cyl`, an `(n+1)`-cube
`□^{shift n} ⟶ K` of `K` — "the block, swept across the interval". -/
noncomputable def CylMap.prism (c : CylMap K) {n : ℕ}
    (p : yoneda.obj (Box.ob n) ⟶ c.src) :
    yoneda.obj (Box.shift.obj (Box.ob n)) ⟶ K :=
  cylTranspose K (Box.ob n) (p ≫ c.cyl)

/-- **The two end-faces of a block prism are the two legs.**  The `false`-coface of
`c.prism p` recovers the left leg over the block, the `true`-coface the right leg.
This is exactly the per-block datum B2 consumes: over each block the cylinder is a
single cube whose bottom/top faces are `leftLeg`/`rightLeg`. -/
theorem CylMap.coface_prism (c : CylMap K) (ε : Bool) {n : ℕ}
    (p : yoneda.obj (Box.ob n) ⟶ c.src) :
    yoneda.map ((Box.coface ε).app (Box.ob n)) ≫ c.prism p
      = p ≫ (bif ε then c.rightLeg else c.leftLeg) := by
  have hleg : (bif ε then c.rightLeg else c.leftLeg) = c.cyl ≫ (endpoint ε).app K := by
    cases ε <;> rfl
  rw [hleg, CylMap.prism, ← cylTranspose_endpoint ε K (Box.ob n) (p ≫ c.cyl)]
  exact Category.assoc p c.cyl ((endpoint ε).app K)

/-- **`prism` is functorial in the block.**  Reindexing the block `p` by a cube map `g`
reindexes its prism by `shift g`. -/
theorem CylMap.prism_precomp (c : CylMap K) {m n : ℕ} (g : Box.ob m ⟶ Box.ob n)
    (p : yoneda.obj (Box.ob n) ⟶ c.src) :
    c.prism (yoneda.map g ≫ p) = yoneda.map (Box.shift.map g) ≫ c.prism p := by
  rw [CylMap.prism, Category.assoc, cylTranspose_naturality, CylMap.prism]

/-- The left leg-functor on the d-path groupoid, `DPathGrpd src ⥤ DPathGrpd K`. -/
noncomputable def CylMap.Lgrpd (c : CylMap K) : DPathGrpd c.src ⥤ DPathGrpd K :=
  FreeGroupoid.map (ChP.map c.leftLeg).toFunctor

/-- The right leg-functor on the d-path groupoid, `DPathGrpd src ⥤ DPathGrpd K`. -/
noncomputable def CylMap.Rgrpd (c : CylMap K) : DPathGrpd c.src ⥤ DPathGrpd K :=
  FreeGroupoid.map (ChP.map c.rightLeg).toFunctor

/-! ### The tautological (terminal) cylinder, and the reduction of `toTransf`

The cylinder with source `PathOb K` and cylinder the identity is `Over.mk (𝟙 (PathOb K))`,
the **terminal** object of `CylMap K = Over (PathOb K)`.  Every cylinder `c` maps to it
uniquely by `c.cyl`, and its two legs are the bare endpoint evaluations `endpoint ε`.
This is the lever that organises the whole construction: the geometric comparison
`toTransf` need only be built **once**, for this terminal cylinder (call it `θ`); for any
other `c` the legs (hence `Lgrpd`/`Rgrpd`) factor through `tauto` (lemmas below), so
`c.toTransf` is obtained from `θ` by whiskering with `FreeGroupoid.map (ChP c.cyl)` — and
its naturality in the chain is then automatic (whiskering preserves naturality), with no
per-cylinder chase. -/

/-- The **tautological (terminal) cylinder** over `K`: source `PathOb K`, cylinder the
identity.  As `Over.mk (𝟙 (PathOb K))` it is the *terminal* object of
`CylMap K = Over (PathOb K)`. -/
def CylMap.tauto (K : PrecubicalSet) : CylMap K := Over.mk (𝟙 (PathOb.obj K))

/-- The tautological cylinder is terminal in `CylMap K` — off the shelf from `Over`. -/
noncomputable def CylMap.tautoIsTerminal (K : PrecubicalSet) :
    Limits.IsTerminal (CylMap.tauto K) := Over.mkIdTerminal

@[simp] theorem CylMap.tauto_leftLeg (K : PrecubicalSet) :
    (CylMap.tauto K).leftLeg = (endpoint false).app K := by
  simp [CylMap.tauto, CylMap.leftLeg]

@[simp] theorem CylMap.tauto_rightLeg (K : PrecubicalSet) :
    (CylMap.tauto K).rightLeg = (endpoint true).app K := by
  simp [CylMap.tauto, CylMap.rightLeg]

/-- The left leg of any cylinder factors through the tautological one: `leftLeg = cyl ≫ e₀`. -/
theorem CylMap.leftLeg_eq_comp (c : CylMap K) :
    c.leftLeg = c.cyl ≫ (CylMap.tauto K).leftLeg := by
  rw [CylMap.tauto_leftLeg, CylMap.leftLeg]

/-- The right leg of any cylinder factors through the tautological one: `rightLeg = cyl ≫ e₁`. -/
theorem CylMap.rightLeg_eq_comp (c : CylMap K) :
    c.rightLeg = c.cyl ≫ (CylMap.tauto K).rightLeg := by
  rw [CylMap.tauto_rightLeg, CylMap.rightLeg]

/-- **The left leg-functor factors through the tautological cylinder.**
`c.Lgrpd = FreeGroupoid.map (ChP c.cyl) ⋙ (tauto K).Lgrpd` — so the universal `θ` on
`tauto K` determines every `Lgrpd` by whiskering.  Pure functoriality
(`ChP.map_comp`, `Cat.Hom.comp_toFunctor`, `FreeGroupoid.map_comp`). -/
theorem CylMap.Lgrpd_eq_comp (c : CylMap K) :
    c.Lgrpd = FreeGroupoid.map (ChP.map c.cyl).toFunctor ⋙ (CylMap.tauto K).Lgrpd := by
  unfold CylMap.Lgrpd
  rw [CylMap.leftLeg_eq_comp, ChP.map_comp, Cat.Hom.comp_toFunctor, FreeGroupoid.map_comp]
  rfl

/-- **The right leg-functor factors through the tautological cylinder** (as `Lgrpd_eq_comp`). -/
theorem CylMap.Rgrpd_eq_comp (c : CylMap K) :
    c.Rgrpd = FreeGroupoid.map (ChP.map c.cyl).toFunctor ⋙ (CylMap.tauto K).Rgrpd := by
  unfold CylMap.Rgrpd
  rw [CylMap.rightLeg_eq_comp, ChP.map_comp, Cat.Hom.comp_toFunctor, FreeGroupoid.map_comp]
  rfl

/-- The object-property cutting out cylinder maps whose left leg is a
groupoid-reflection weak equivalence (so `Lgrpd` is an equivalence and the transport
`Lgrpd⁻¹ ⋙ Rgrpd` exists). -/
def CylMap.leftWeq (K : PrecubicalSet) : ObjectProperty (CylMap K) :=
  fun c => c.Lgrpd.IsEquivalence

/-- Cylinder maps whose left leg is a weak equivalence: the full subcategory of
`Over (PathOb K)` cut out by `Lgrpd.IsEquivalence`.  Reusing `ObjectProperty.FullSubcategory`
inherits the category and the forgetful functor `ι : CylMapWeq K ⥤ CylMap K`; an
object's `left_weq` witness is its `.property`. -/
abbrev CylMapWeq (K : PrecubicalSet) := (CylMap.leftWeq K).FullSubcategory

/-- The left leg-functor of a `CylMapWeq` object is an equivalence (its defining
property). -/
theorem CylMapWeq.left_weq (c : CylMapWeq K) : c.obj.Lgrpd.IsEquivalence := c.property

/-! ### Vertices of the prism cells (the combinatorial kernel for the fence's `IsCubeChain`)

The multi-block fence chains `P_j`/`R_j` are cube chains assembled from prism cube cells,
prism face cells and vertical-edge cells; their `IsCubeChain` (junction-vertex matching)
proofs need the extremal vertices of those cells.  The geometric content is that the prism
cube over a block has the *same* initial vertex as its bottom (`e₀`-)face and the *same*
final vertex as its top (`e₁`-)face: the all-`0` corner of `□^{d+1}` lies in the bottom
face, the all-`1` corner in the top face.  These reduce to the factorization of the cube
vertex inclusions through the end-cofaces (`initVertexMap_succ`/`finalVertexMap_succ`)
together with `CylMap.coface_prism`.  (Specialised to `d = 0` they also give the two
endpoints of a vertical edge `(tauto K).prism v`.) -/

/-- Appending a fixed coordinate `ε` to the constant-`ε` vertex gives the constant-`ε`
vertex one dimension up. -/
theorem StdCube.snocFix_constVertex (ε : Bool) (N : ℕ) :
    StdCube.snocFix ε (StdCube.constVertex N ε) = StdCube.constVertex (N + 1) ε := by
  apply Subtype.ext
  rw [StdCube.snocFix_val]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [Fin.snoc_last, Fin.snoc_castSucc, StdCube.constVertex]

/-- **The initial-vertex inclusion factors through the `false`-end coface**: the all-`0`
corner of `□^{n+1}` is the all-`0` corner of `□ⁿ` followed by the bottom face. -/
theorem initVertexMap_succ (n : ℕ) :
    PrecubicalSet.initVertexMap (n + 1)
      = PrecubicalSet.initVertexMap n ≫ (Box.coface false).app (Box.ob n) := by
  have hev : StdCube.ev (PrecubicalSet.initVertexMap n ≫ (Box.coface false).app (Box.ob n))
      = StdCube.constVertex (n + 1) false := by
    change StdCube.snocFix false
        (StdCube.sapp (StdCube.constVertex n false) (StdCube.topCell 0)) = _
    rw [StdCube.sapp_topCell, StdCube.snocFix_constVertex]
  rw [show PrecubicalSet.initVertexMap (n + 1)
        = StdCube.canonicalMap (StdCube.constVertex (n + 1) false) from rfl, ← hev]
  exact (StdCube.cubeRepr (StdCube.stdPre (n + 1)) 0).left_inv
    (PrecubicalSet.initVertexMap n ≫ (Box.coface false).app (Box.ob n))

/-- **The final-vertex inclusion factors through the `true`-end coface** (dual of
`initVertexMap_succ`): the all-`1` corner of `□^{n+1}` is the all-`1` corner of `□ⁿ`
followed by the top face. -/
theorem finalVertexMap_succ (n : ℕ) :
    PrecubicalSet.finalVertexMap (n + 1)
      = PrecubicalSet.finalVertexMap n ≫ (Box.coface true).app (Box.ob n) := by
  have hev : StdCube.ev (PrecubicalSet.finalVertexMap n ≫ (Box.coface true).app (Box.ob n))
      = StdCube.constVertex (n + 1) true := by
    change StdCube.snocFix true
        (StdCube.sapp (StdCube.constVertex n true) (StdCube.topCell 0)) = _
    rw [StdCube.sapp_topCell, StdCube.snocFix_constVertex]
  rw [show PrecubicalSet.finalVertexMap (n + 1)
        = StdCube.canonicalMap (StdCube.constVertex (n + 1) true) from rfl, ← hev]
  exact (StdCube.cubeRepr (StdCube.stdPre (n + 1)) 0).left_inv
    (PrecubicalSet.finalVertexMap n ≫ (Box.coface true).app (Box.ob n))

/-- The source extremal vertex of a Yoneda-classified cell (plain-`PrecubicalSet` form of
`CubeChain.vertex₀_yonedaEquiv`): `vertex₀ (yonedaEquiv f) = f` at the initial-vertex map. -/
theorem PrecubicalSet.vertex₀_yonedaEquiv {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj (Box.ob n) ⟶ K) :
    K.vertex₀ (yonedaEquiv f) = f.app (op (Box.ob 0)) (PrecubicalSet.initVertexMap n) := by
  unfold PrecubicalSet.vertex₀
  exact map_yonedaEquiv f (PrecubicalSet.initVertexMap n)

/-- The target extremal vertex of a Yoneda-classified cell (plain-`PrecubicalSet` form). -/
theorem PrecubicalSet.vertex₁_yonedaEquiv {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj (Box.ob n) ⟶ K) :
    K.vertex₁ (yonedaEquiv f) = f.app (op (Box.ob 0)) (PrecubicalSet.finalVertexMap n) := by
  unfold PrecubicalSet.vertex₁
  exact map_yonedaEquiv f (PrecubicalSet.finalVertexMap n)

/-- The source extremal vertex as the Yoneda class of the precomposed initial-vertex
inclusion (the morphism-level form used for vertex chases). -/
theorem PrecubicalSet.vertex₀_eq {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj (Box.ob n) ⟶ K) :
    K.vertex₀ (yonedaEquiv f)
      = yonedaEquiv (yoneda.map (PrecubicalSet.initVertexMap n) ≫ f) := by
  rw [PrecubicalSet.vertex₀_yonedaEquiv, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- The target extremal vertex as the Yoneda class of the precomposed final-vertex
inclusion. -/
theorem PrecubicalSet.vertex₁_eq {K : PrecubicalSet} {n : ℕ}
    (f : yoneda.obj (Box.ob n) ⟶ K) :
    K.vertex₁ (yonedaEquiv f)
      = yonedaEquiv (yoneda.map (PrecubicalSet.finalVertexMap n) ≫ f) := by
  rw [PrecubicalSet.vertex₁_yonedaEquiv, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- **The prism cube and its bottom face share an initial vertex.**  For a block
`p : □ᵈ ⟶ PathOb K`, the all-`0` vertex of the prism cube `(tauto K).prism p` equals the
all-`0` vertex of the bottom (`e₀`-)face cell `p ≫ e₀`. -/
theorem prism_vertex₀ {d : ℕ} (p : yoneda.obj (Box.ob d) ⟶ PathOb.obj K) :
    K.vertex₀ (yonedaEquiv ((CylMap.tauto K).prism p))
      = K.vertex₀ (yonedaEquiv (p ≫ (endpoint false).app K)) := by
  rw [PrecubicalSet.vertex₀_eq, PrecubicalSet.vertex₀_eq]
  congr 1
  change yoneda.map (PrecubicalSet.initVertexMap (d + 1)) ≫ (CylMap.tauto K).prism p
      = yoneda.map (PrecubicalSet.initVertexMap d) ≫ (p ≫ (endpoint false).app K)
  have hcf : yoneda.map ((Box.coface false).app (Box.ob d)) ≫ (CylMap.tauto K).prism p
      = p ≫ (endpoint false).app K := by
    have h := CylMap.coface_prism (CylMap.tauto K) false p
    rw [CylMap.tauto_leftLeg] at h
    exact h
  rw [initVertexMap_succ d]
  erw [Functor.map_comp, Category.assoc]
  exact congrArg (fun z => yoneda.map (PrecubicalSet.initVertexMap d) ≫ z) hcf

/-- **The prism cube and its top face share a final vertex** (dual of `prism_vertex₀`): the
all-`1` vertex of `(tauto K).prism p` equals the all-`1` vertex of the top (`e₁`-)face cell
`p ≫ e₁`. -/
theorem prism_vertex₁ {d : ℕ} (p : yoneda.obj (Box.ob d) ⟶ PathOb.obj K) :
    K.vertex₁ (yonedaEquiv ((CylMap.tauto K).prism p))
      = K.vertex₁ (yonedaEquiv (p ≫ (endpoint true).app K)) := by
  rw [PrecubicalSet.vertex₁_eq, PrecubicalSet.vertex₁_eq]
  congr 1
  change yoneda.map (PrecubicalSet.finalVertexMap (d + 1)) ≫ (CylMap.tauto K).prism p
      = yoneda.map (PrecubicalSet.finalVertexMap d) ≫ (p ≫ (endpoint true).app K)
  have hcf : yoneda.map ((Box.coface true).app (Box.ob d)) ≫ (CylMap.tauto K).prism p
      = p ≫ (endpoint true).app K := by
    have h := CylMap.coface_prism (CylMap.tauto K) true p
    rw [CylMap.tauto_rightLeg] at h
    exact h
  rw [finalVertexMap_succ d]
  erw [Functor.map_comp, Category.assoc]
  exact congrArg (fun z => yoneda.map (PrecubicalSet.finalVertexMap d) ≫ z) hcf

/-- **Concatenation of cube chains.**  Two cube chains `xs : a ⇝ m` and `ys : m ⇝ b`
splice to a cube chain `xs ++ ys : a ⇝ b`. -/
theorem isCubeChain_append {K : PrecubicalSet} {a m b : K.cells 0} :
    ∀ {xs : List (Σ n : ℕ+, K.cells (n : ℕ))} {ys : List (Σ n : ℕ+, K.cells (n : ℕ))},
      IsCubeChain a xs m → IsCubeChain m ys b → IsCubeChain a (xs ++ ys) b
  | [], _, hxs, hys => by
      obtain rfl : a = m := hxs
      exact hys
  | ⟨n, c⟩ :: tl, _, hxs, hys =>
      ⟨hxs.1, isCubeChain_append hxs.2 hys⟩

/-- Prepend a cube cell `⟨d, H⟩` to a chain `a`, glued by `vertex₁ H = chainInit a`
(the cons step of `wedgeDescP`, packaged as an operation on `ChainObj`). -/
noncomputable def consChain (d : ℕ+) (H : K.cells (d : ℕ)) (a : ChainObj K)
    (hv : K.vertex₁ H
      = a.map.app (op (Box.ob 0)) (BPSet.serialWedge a.dims).init) : ChainObj K where
  dims := d :: a.dims
  map := Limits.pushout.desc (yonedaEquiv.symm H) a.map (by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, BPSet.finalVertex, BPSet.initVertex, BPSet.vertexMap,
      Equiv.apply_symm_apply]
    rw [← hv]
    rfl)

/-- The initial vertex (a `0`-cell of `K`) of a chain. -/
noncomputable def chainInit (a : ChainObj K) : K.cells 0 :=
  a.map.app (op (Box.ob 0)) (BPSet.serialWedge a.dims).init

/-- An **initial-vertex-preserving chain map**: a chain morphism whose underlying wedge
map carries the initial vertex to the initial vertex.  These are exactly the maps that
`consChain` can prepend a fixed head block onto (the prepend cocone condition *is*
initial-vertex preservation), so the fence's zigzag is assembled from them. -/
structure IPHom (a b : ChainObj K) where
  /-- The underlying chain morphism. -/
  hom : a ⟶ b
  /-- It preserves the initial vertex. -/
  hinit : (BPSet.serialWedge a.dims).initVertex ≫ hom.φ
    = (BPSet.serialWedge b.dims).initVertex

/-- An initial-vertex-preserving chain map preserves the initial vertex *cell*
(`chainInit`); hence `chainInit` is constant along zigzags of such maps. -/
theorem chainInit_eq_of_IPHom {a b : ChainObj K} (f : IPHom a b) :
    chainInit a = chainInit b := by
  have e : ∀ c : ChainObj K,
      chainInit c = yonedaEquiv ((BPSet.serialWedge c.dims).initVertex ≫ c.map) := by
    intro c
    rw [yonedaEquiv_comp, BPSet.initVertex, BPSet.vertexMap, Equiv.apply_symm_apply]
    rfl
  rw [e a, e b, ← f.hinit, Category.assoc, f.hom.w]

/-- **Prepend a fixed head block to an initial-vertex-preserving chain map.**  Given a
head cube cell `⟨d, H⟩` gluing onto both ends, an `IPHom a b` lifts to a chain morphism
`consChain H a ⟶ consChain H b` (identity on the head block, `f` on the tail). -/
noncomputable def prependMor (d : ℕ+) (H : K.cells (d : ℕ)) {a b : ChainObj K}
    (f : IPHom a b) (hva : K.vertex₁ H = chainInit a) :
    consChain d H a hva ⟶ consChain d H b (hva.trans (chainInit_eq_of_IPHom f)) where
  φ := Limits.pushout.desc
    (Limits.pushout.inl (BPSet.cube (d : ℕ)).finalVertex (BPSet.serialWedge b.dims).initVertex)
    (f.hom.φ ≫ Limits.pushout.inr (BPSet.cube (d : ℕ)).finalVertex
      (BPSet.serialWedge b.dims).initVertex)
    (Limits.pushout.condition.trans
      (((congrArg (· ≫ Limits.pushout.inr (BPSet.cube (d : ℕ)).finalVertex
        (BPSet.serialWedge b.dims).initVertex) f.hinit).symm).trans (Category.assoc _ _ _)))
  w := by
    apply Limits.pushout.hom_ext
    · erw [Limits.pushout.inl_desc_assoc, Limits.pushout.inl_desc, Limits.pushout.inl_desc]
    · erw [Limits.pushout.inr_desc_assoc, Category.assoc, Limits.pushout.inr_desc,
        Limits.pushout.inr_desc, f.hom.w]

/-! ### The single-block component of `θ`

For a one-block chain `(m, w)` in `PathOb K`, the homotopy `w ≫ e₀ ⇝ w ≫ e₁` is the
cospan `b₀ → R ← b₁` through the prism cube `R`.  Single-block chains are cubes
(`serialWedgeSingletonIso`), so `R`, the two cofaces and the commuting triangles assemble
cleanly from `coface_prism` — no fence yet (that's the multi-block step). -/

/-- The prism cube over a single-block chain `(m, q)` in `PathOb K`, as a one-block chain
`([m+1], _)` in `K` (the `(m+1)`-cube presented as a serial wedge via
`serialWedgeSingletonIso`). -/
noncomputable def singleBlockPrism (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K) : ChainObj K where
  dims := [m + 1]
  map := (serialWedgeSingletonIso (m + 1)).inv
    ≫ (CylMap.tauto K).prism ((serialWedgeSingletonIso m).hom ≫ q)

/-- The single block `(m, q)` in `PathOb K` evaluated at an endpoint, as a one-block
chain in `K`. -/
noncomputable def singleBlockEnd (ε : Bool) (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K) : ChainObj K :=
  ⟨[m], q ≫ (endpoint ε).app K⟩

/-- The `ε`-coface refinement `(m, q≫eε) ⟶ R` into the prism cube — the two arrows of the
single-block cospan.  The commuting triangle is exactly `coface_prism` (the prism's
`ε`-face is the `ε`-leg), with the singleton isos cancelling. -/
noncomputable def singleBlockCoface (ε : Bool) (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K) :
    singleBlockEnd ε m q ⟶ singleBlockPrism m q where
  φ := (serialWedgeSingletonIso m).inv
    ≫ yoneda.map ((Box.coface ε).app (Box.ob m))
    ≫ (serialWedgeSingletonIso (m + 1)).hom
  w := by
    have hleg : (bif ε then (CylMap.tauto K).rightLeg else (CylMap.tauto K).leftLeg)
        = (endpoint ε).app K := by cases ε <;> simp
    dsimp only [singleBlockPrism, singleBlockEnd]
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_assoc,
        CylMap.coface_prism (CylMap.tauto K) ε ((serialWedgeSingletonIso m).hom ≫ q)]
    rw [hleg]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc]
    rfl

/-- **The single-block component of `θ`.**  For a one-block chain `(m, q)` in `PathOb K`,
the homotopy `q ≫ e₀ ⇝ q ≫ e₁` realized as a morphism `mk(m, q≫e₀) ⟶ mk(m, q≫e₁)` of
`DPathGrpd K`: the cospan `b₀ → R ← b₁` through the prism cube, `of(coface₀)` followed by
the inverse of `of(coface₁)`.  This is the geometric heart of `θ` on one block (the
multi-block fence glues these). -/
noncomputable def singleBlockComp (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K) :
    (FreeGroupoid.of (ChP.obj K)).obj (singleBlockEnd false m q)
      ⟶ (FreeGroupoid.of (ChP.obj K)).obj (singleBlockEnd true m q) :=
  (FreeGroupoid.of (ChP.obj K)).map (singleBlockCoface false m q)
    ≫ Groupoid.inv ((FreeGroupoid.of (ChP.obj K)).map (singleBlockCoface true m q))

/-! ### The empty-chain (base) component of `θ`

The empty chain `([], v)` is a *point* `v : □⁰ ⟶ PathOb K`; its two endpoints are vertices
of `K`, connected by the prism *edge* `cylTranspose v : □¹ ⟶ K`.  This is the base case of
the recursion on the dimension list (the head/tail step over `n :: rest` is the multi-block
fence, still to come).  It is cleaner than the single-block case: `serialWedge [] = □⁰`
needs no singleton iso on the source side. -/

/-- The empty chain `(v)` evaluated at an endpoint, as a `0`-chain in `K`. -/
noncomputable def emptyBlockEnd (ε : Bool)
    (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K) : ChainObj K :=
  ⟨[], v ≫ (endpoint ε).app K⟩

/-- The prism edge over the empty chain `(v)`, as a one-block chain `([1], _)` in `K`. -/
noncomputable def emptyBlockPrism (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K) : ChainObj K where
  dims := [1]
  map := (serialWedgeSingletonIso 1).inv ≫ (CylMap.tauto K).prism v

/-- The `ε`-coface refinement `([], v≫eε) ⟶ (prism edge)` — the two arrows of the base
cospan; the commuting triangle is `coface_prism`. -/
noncomputable def emptyBlockCoface (ε : Bool)
    (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K) :
    emptyBlockEnd ε v ⟶ emptyBlockPrism v where
  φ := yoneda.map ((Box.coface ε).app (Box.ob 0)) ≫ (serialWedgeSingletonIso 1).hom
  w := by
    have hleg : (bif ε then (CylMap.tauto K).rightLeg else (CylMap.tauto K).leftLeg)
        = (endpoint ε).app K := by cases ε <;> simp
    dsimp only [emptyBlockPrism, emptyBlockEnd]
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_assoc, CylMap.coface_prism (CylMap.tauto K) ε v]
    rw [hleg]
    rfl

/-- **The empty-chain (base) component of `θ`.**  The homotopy `v ≫ e₀ ⇝ v ≫ e₁` between
two vertices of `K`, realized as the cospan `([],v≫e₀) → ([1], edge) ← ([],v≫e₁)` in
`DPathGrpd K`. -/
noncomputable def emptyBlockComp (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K) :
    (FreeGroupoid.of (ChP.obj K)).obj (emptyBlockEnd false v)
      ⟶ (FreeGroupoid.of (ChP.obj K)).obj (emptyBlockEnd true v) :=
  (FreeGroupoid.of (ChP.obj K)).map (emptyBlockCoface false v)
    ≫ Groupoid.inv ((FreeGroupoid.of (ChP.obj K)).map (emptyBlockCoface true v))

/-!
## B2/B3 deferred — the geometric comparison `CylMap.toTransf`

The crux `CylMap.toTransf : c.Lgrpd ⟶ c.Rgrpd` and the functor
`cylToPointed : CylMapWeq K ⥤ PointedEndofunctor (DPathGrpd K)` it powers are not yet
supplied.  Per project policy they are *data* (a natural-transformation family), so
they cannot be parked as a `sorry`; rather than ship a `sorry`-built `def`, they are
left out until the geometry is in place.

**The single remaining geometric obligation is `θ := (tauto K).toTransf`.**  By
`Lgrpd_eq_comp`/`Rgrpd_eq_comp`, for *every* cylinder `c` the leg-functors factor as
`c.Lgrpd = FreeGroupoid.map (ChP c.cyl) ⋙ (tauto K).Lgrpd` (and dually for `Rgrpd`).  So
once `θ : (tauto K).Lgrpd ⟶ (tauto K).Rgrpd` is built for the **terminal** cylinder
(`tauto K = Over.mk (𝟙 (PathOb K))`), every `c.toTransf` is `whiskerLeft (FreeGroupoid.map
(ChP c.cyl)) θ` (transported across those equalities) — and its **naturality in the chain
is automatic** (whiskering preserves it), with no per-cylinder chase.  All the plumbing
(legs, factorization, the `Over`/`FullSubcategory` category, the box-tensor adjunction and
its cocontinuity `boxTensorInterval_wedge2`) is in place and proved; `θ` is the lone
geometric input.

**The construction route** (CylinderPlan §2) is: by `FreeGroupoid.liftNatIso`, since
`DPathGrpd K` is a groupoid it suffices to give a natural iso of functors
`ChP src ⥤ DPathGrpd K`,
`(ChP.map leftLeg).toFunctor ⋙ of  ≅  (ChP.map rightLeg).toFunctor ⋙ of`,
whose component at a chain `a = (dims, p : □^∨dims ⟶ src)` is a zigzag in `ChP K`
from `(dims, p ≫ leftLeg)` to `(dims, p ≫ rightLeg)` built from the prism
`p ≫ c.cyl : □^∨dims ⟶ PathOb K`.

**Why the prism is not itself a chain.**  A morphism of `ChP K` requires *both*
endpoints to be serial-wedge chains.  The prism over a chain is `□^∨dims ⊗ □¹`;
because `(-) ⊗ □¹` is a left adjoint it preserves the wedge colimit, so the prism is
the cubes `□^{dᵢ+1}` glued **along the cylinder edges** over the junction vertices —
an *edge*-glued complex, **not** a serial wedge (which glues at single vertices).  So
no single chain covers the prism, and the comparison must be a genuine zigzag.

**The explicit comparison zigzag (the prism staircase fence).**  For a chain
`a = (dims = [d₁,…,d_m], p)` write `b₀ = (dims, p ≫ leftLeg)`,
`b₁ = (dims, p ≫ rightLeg)` (the bottom/top of the cylinder).  Introduce, for the
prism, two families of *serial-wedge* chains in `K`:

* `P_j := [d₁,…,d_j, 1, d_{j+1},…,d_m]` (`j = 0,…,m`): blocks `1..j` at cylinder
  level 0, then the **vertical cylinder edge** over junction vertex `j`, then blocks
  `j+1..m` at level 1.  Consecutive blocks glue at matching vertices, so this *is* a
  serial-wedge chain.
* `R_j := [d₁,…,d_j, d_{j+1}+1, d_{j+2},…,d_m]` (`j = 0,…,m-1`): blocks `1..j` at
  level 0, the **full prism cube** `□^{d_{j+1}+1}` over block `j+1`, then blocks
  `j+2..m` at level 1.

Then `R_j` receives refinement maps from both `P_j` (the "up-then-along" boundary path
of the prism cube) and `P_{j+1}` (the "along-then-up" boundary path), and the ends
close up via `b₀ → P_m` (include blocks as a prefix, dropping the trailing edge) and
`b₁ → P_0` (include as a suffix).  This yields the zigzag

`b₀ → P_m → R_{m-1} ← P_{m-1} → ⋯ → R₀ ← P₀ ← b₁`

connecting `mk b₀` to `mk b₁` in `FreeGroupoid (ChP K)`.  `toTransf.app a` is this
composite; `toTransf` is the `liftNatIso` of the resulting natural family.

**Remaining work for piece 1** (with what is now in hand noted):
1. *Available.*  The wedge universal property is already proved: `serialWedge_hom_ext`
   (uniqueness, `ι`-form) in `Chains/WedgeMap.lean`, with `serialWedge_ι_zero`/`_succ`
   and `wedge2_glue`; and maps out of a serial wedge are built by iterated
   `pushout.desc` (with `serialWedge_ι_*` + `pushout.inl/inr_desc` computing their `ι`
   restrictions).  So no new descent/`hom_ext` API is needed — only the geometric
   inputs below.
2. the two boundary-path inclusions `serialWedge [1, d] ⟶ cube (d+1)` and
   `serialWedge [d, 1] ⟶ cube (d+1)` of a prism cube: built by `pushout.desc` from the
   end-faces `Box.coface ε` and the vertical edges `canonicalMap (snocFree
   (constVertex d ε))` (`snocFree` from `Shift.lean` appends the free interval coord),
   with the junction agreement at the corner vertices;
3. *Single-block core done* (`CylMap.prism`/`CylMap.coface_prism` above): over each
   block the cylinder is one cube whose two cofaces are `leftLeg`/`rightLeg`.  **What
   remains** is to assemble blocks along `serialWedge.ι` and prove the end-faces agree
   at the junction vertices (the coherence that lets the `P_j`/`R_j` glue) — a vertex
   computation feeding `wedge2_glue`;
4. the naturality of the whole fence in `a` (a diagram chase: a chain map
   `φ : a ⟶ a'` carries each `P_j`/`R_j` of `a` to that of `a'`, and every square
   commutes because the maps are coface- and inclusion-natural).  *Per-block in hand:*
   `cylTranspose_naturality`/`CylMap.prism_precomp` above already give that the prism
   commutes with cube reindexing `g`/`shift g`; what remains is to thread this through
   the wedge inclusions.
-/
