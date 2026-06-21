import CubeChains.Operations.Precubical
import CubeChains.Operations.Shift
import CubeChains.Operations.PointedFunctor
import Mathlib.CategoryTheory.Comma.Over.Basic
import CubeChains.Chains.WedgeMap

/-!
# The prism-cell core of a cylinder map

The reusable prism-cell kernel consumed by `Operations/CylinderRefine.lean` (which
houses the actual `cylToPointedR` functor).  Building on the path object `PathOb`
(`Operations/Shift.lean`), it provides:

* `cylTranspose` — the box-tensor/cocylinder adjunction on representables, identifying
  a cylinder `□ᵇ ⟶ PathOb K` with its prism `□^{shift b} ⟶ K`;
* `CylMap K := Over (PathOb K)` and the **tautological** cylinder `CylMap.tauto`;
* `CylMap.prism` — the `(n+1)`-cube "block swept across the interval", with
  `coface_prism` (its two end-faces are the two legs) and `prism_precomp`/`prism_vertex₀₁`;
* `isCubeChain_append` — concatenation of cube chains.
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
prism of the reindexing).  This is the per-block naturality consumed by
`CylMap.prism_precomp`. -/
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

/-! ### The tautological (terminal) cylinder

The cylinder with source `PathOb K` and cylinder the identity is `Over.mk (𝟙 (PathOb K))`,
the **terminal** object of `CylMap K = Over (PathOb K)`; its two legs are the bare
endpoint evaluations `endpoint ε`.  `CylinderRefine` builds the prism cells over this
`tauto K`. -/

/-- The **tautological (terminal) cylinder** over `K`: source `PathOb K`, cylinder the
identity.  As `Over.mk (𝟙 (PathOb K))` it is the *terminal* object of
`CylMap K = Over (PathOb K)`. -/
def CylMap.tauto (K : PrecubicalSet) : CylMap K := Over.mk (𝟙 (PathOb.obj K))

@[simp] theorem CylMap.tauto_leftLeg (K : PrecubicalSet) :
    (CylMap.tauto K).leftLeg = (endpoint false).app K := by
  simp [CylMap.tauto, CylMap.leftLeg]

@[simp] theorem CylMap.tauto_rightLeg (K : PrecubicalSet) :
    (CylMap.tauto K).rightLeg = (endpoint true).app K := by
  simp [CylMap.tauto, CylMap.rightLeg]

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

