import CubeChains.Operations.Precubical
import CubeChains.Operations.Shift
import CubeChains.Operations.PointedFunctor
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

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

/-!
## B2/B3 deferred — the geometric comparison `CylMap.toTransf`

The crux `CylMap.toTransf : c.Lgrpd ⟶ c.Rgrpd` and the functor
`cylToPointed : CylMapWeq K ⥤ PointedEndofunctor (DPathGrpd K)` it powers are not yet
supplied.  Per project policy they are *data* (a natural-transformation family), so
they cannot be parked as a `sorry`; rather than ship a `sorry`-built `def`, they are
left out until the geometry is in place.

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
