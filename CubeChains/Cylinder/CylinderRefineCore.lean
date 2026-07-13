import CubeChains.Cylinder.Cylinder
import CubeChains.Chains.RefineFunctor
import CubeChains.Cylinder.PointedFunctor
import CubeChains.Chains.RefineConcat

/-!
# Cylinder/CylinderRefineCore

Cylinder maps and the geometry of their action on `Grpd(RefineObj K)`.
This is the **geometry core** of the cylinder ⟹ pointed-functor program (the staircase assembly
`sweepR` and the deliverable `cylToPointedR` are built on top in `CylinderSweep`/`CylinderRefine`).

It builds the target side on `RefineObj`:

* `DPathGrpdR K = FreeGroupoid (RefineObj K.init K.final)` — the d-path homotopy groupoid;
* `CylMapR K` — a **rel-interface cylinder** (a `BPSet` source with two basepoint-preserving legs
  and a classifying map into the path object `PathOb K`) + its category of cylinder-map morphisms
  (the section-primary entry point `SecCyl K` inherits these morphisms);
* `Refine.pushforwardBP` (pushforward of `init → final` chains along a `BPSet` map) + bridge lemmas,
  and the leg-functors `Lgrpd`/`Rgrpd : DPathGrpdR src ⥤ DPathGrpdR K`;
* the **single-block sweep cospan** in `RefineObj` (Piece 3 — the geometric core):
  `prism_coface_cell`,
  `blockQ`/`blockQ_face`/`blockQ_precomp`, `prism_edge_coface_cell`(`_final`), and the cospan pieces
  `refineEndG`/`refinePrismG`/`refineCofaceG`/`refineEdgeG` together with the four bridge cofaces
  `refineBridge*`.

See `CylinderSweep.lean` for the list-indexed staircase that assembles these into `sweepR`, and
`CylinderRefine.lean` for the deliverable `cylToPointedR`.

**Layer:** Cylinder.  **Imports:** `Cylinder/Cylinder`, `Cylinder/PointedFunctor`,
`Chains/RefineFunctor`, `Chains/RefineConcat`.
-/

open CategoryTheory Opposite BPSet
open Operations
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
`RefineObj B.init B.final`.

The endpoint move (`app_init`/`app_final`) is carried by an `Eq.mpr` produced by a *type* rewrite;
the cube data is endpoint-independent, so the bridge lemma `pushforwardBP_obj_cubes` peels it off
(via the generic `refineObj_endpoint_transport_cubes`). -/
noncomputable def Refine.pushforwardBP {A B : BPSet} (f : A ⟶ B) :
    RefineObj (K := A) A.init A.final ⥤ RefineObj (K := B) B.init B.final :=
  f.app_final ▸ f.app_init ▸ Refine.pushforward f.hom

/-- A functor `F : 𝒞 ⥤ RefineObj b₀ b₁`, transported across endpoint equalities `h₀ : b₀ = b₀'`,
`h₁ : b₁ = b₁'`, has the same cubes on objects (the `RefineObj` index does not enter `.cubes`).
Proved by `subst`ing both equalities (the transport becomes `rfl`). -/
theorem refineObj_endpoint_transport_cubes {𝒞 : Type*} [Category 𝒞] {K : BPSet}
    {b₀ b₁ b₀' b₁' : K.cells 0} (h₀ : b₀ = b₀') (h₁ : b₁ = b₁')
    (F : 𝒞 ⥤ RefineObj (K := K) b₀ b₁) (a : 𝒞) :
    ((h₁ ▸ h₀ ▸ F : 𝒞 ⥤ RefineObj (K := K) b₀' b₁').obj a).cubes = (F.obj a).cubes := by
  subst h₀; subst h₁; rfl

/-- **Bridge lemma: the cubes of `(pushforwardBP f).obj a`.**  `pushforwardBP` is the endpoint
transport of `Refine.pushforward f.hom`, which is invisible to `.cubes`
(`refineObj_endpoint_transport_cubes`); so the pushed chain's cubes are literally `a.cubes` mapped
cube-wise by `f`. -/
@[simp] theorem Refine.pushforwardBP_obj_cubes {A B : BPSet} (f : A ⟶ B)
    (a : RefineObj (K := A) A.init A.final) :
    ((Refine.pushforwardBP f).obj a).cubes = a.cubes.map (mapCubeHom f.hom) := by
  rw [Refine.pushforwardBP,
    refineObj_endpoint_transport_cubes f.app_init f.app_final (Refine.pushforward f.hom)]
  rfl

/-! ## 4. The leg-functors on the d-path groupoid -/

/-- The **left leg-functor** on the d-path groupoid, `DPathGrpdR src ⥤ DPathGrpdR K`, induced
by post-composing chains with the left leg.  Mirrors `CylMapB.Lgrpd`, now on `RefineObj`. -/
noncomputable def CylMapR.Lgrpd (c : CylMapR K) : DPathGrpdR c.src ⥤ DPathGrpdR K :=
  FreeGroupoid.map (Refine.pushforwardBP c.leftLeg)

/-- The **right leg-functor** on the d-path groupoid, induced by the right leg. -/
noncomputable def CylMapR.Rgrpd (c : CylMapR K) : DPathGrpdR c.src ⥤ DPathGrpdR K :=
  FreeGroupoid.map (Refine.pushforwardBP c.rightLeg)

/-! ## 5. The category of cylinder maps

A morphism of cylinder maps is a `BPSet` map of sources commuting with `cyl` (the legs then
commute automatically, being `endpoint`-evaluations of `cyl`).  This makes `CylMapR K` a category;
the section-primary entry point `SecCyl K` (`Cylinder/CylinderRefine.lean`) inherits its morphisms
from here. -/

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
  id a := ⟨𝟙 a.src, by rw [id_hom, Category.id_comp]⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [comp_hom, Category.assoc, g.w, f.w]⟩
  id_comp f := CylMapR.Hom.ext (Category.id_comp _)
  comp_id f := CylMapR.Hom.ext (Category.comp_id _)
  assoc f g h := CylMapR.Hom.ext (Category.assoc _ _ _)

@[simp] theorem id_hom (a : CylMapR K) : CylMapR.Hom.hom (𝟙 a) = 𝟙 a.src := rfl

@[simp] theorem comp_hom {a b c : CylMapR K} (f : a ⟶ b) (g : b ⟶ c) :
    CylMapR.Hom.hom (f ≫ g) = CylMapR.Hom.hom f ≫ CylMapR.Hom.hom g := rfl

end CylMapR

/-! ## 6. The single-block sweep cospan in `RefineObj` (Piece 3 — the geometric core)

For one cube block presented as a cell `q : □ᵐ ⟶ PathOb K.toPsh` of the path object, the
**prism cube** `R = (tauto).prism q : □^{m+1} ⟶ K.toPsh` sweeps the block across the
interval; its bottom (`e₀`-)face is the left-leg block `b₀ = q ≫ e₀` and its top
(`e₁`-)face is the right-leg block `b₁ = q ≫ e₁` (`CylMap.coface_prism`).

In the **refinement category** `RefineObj` — unlike the wedge-map `Ch` — the two
direct cofaces `b₀ → R` and `b₁ → R` are genuine morphisms *unconditionally*: a `ChainRefine`
asks only that the two single-cube chains share their endpoints `a, b` (which they do — the
self-loops a rel-interface cylinder forces collapse `R`'s formal corners to the block's
junction vertices) and carries the face inclusion `incl = (Box.coface ε).app (□ᵐ)` as *data*,
with `inclSpec` *exactly* the cell-form of `coface_prism`.  This is why `RefineObj` works where
wedge-maps hit the closing-end obstruction (the wedge-map approach, since removed).

We build the single-block cospan for a *whole-chain* block: the two corner cells are the
basepoints `K.init`/`K.final`, so the three single-cube chains live in
`RefineObj K.init K.final` (the d-path groupoid base), and the sweep is a morphism of
`DPathGrpdR K`. -/

namespace CylMapR

open CubeChain

/-- **The face relation of the prism cube, in cell form.**  Pulling the prism cube cell
`yonedaEquiv ((tauto).prism q)` back along the `ε`-end coface `□ᵐ ↪ □^{m+1}` gives the
`ε`-leg block cell `yonedaEquiv (q ≫ eε)`.  This is the `inclSpec` of the direct-coface
refinement `b_ε → R`; it is exactly `CylMap.coface_prism` read through `yonedaEquiv`. -/
theorem prism_coface_cell {K : PrecubicalSet} {m : ℕ}
    (q : yoneda.obj ▫m ⟶ PathOb.obj K) (ε : Bool) :
    K.map ((Box.coface ε).app ▫m).op
        (yonedaEquiv ((CylMap.tauto K).prism q))
      = yonedaEquiv (q ≫ (endpoint ε).app K) := by
  rw [yonedaEquiv_naturality ((CylMap.tauto K).prism q) ((Box.coface ε).app ▫m)]
  congr 1
  have h := CylMap.coface_prism (CylMap.tauto K) ε q
  cases ε with
  | false => rw [CylMap.tauto_leftLeg] at h; exact h
  | true => rw [CylMap.tauto_rightLeg] at h; exact h

/-! ### The single-cube chains and the two direct cofaces

For a block `q : □ᵐ ⟶ PathOb K.toPsh` over **junction vertices** `u, v`, the bottom-face block
`b₀`, the top-face block `b₁` and the prism cube `R` are all single-cube chains `u → v`, i.e.
objects of `RefineObj u v`.  `R`'s own chain condition reuses `b₀`'s init (`prism_vertex₀`) and
`b₁`'s final (`prism_vertex₁`). -/

/-- The `ε`-leg block `b_ε = q ≫ eε`, as a single-cube chain `u → v` over arbitrary endpoints. -/
noncomputable def refineEndG (ε : Bool) {m : ℕ+} {u v : K.cells 0}
    (q : yoneda.obj ▫(m : ℕ) ⟶ PathOb.obj K.toPsh)
    (hi : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = u)
    (hf : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = v) :
    RefineObj (K := K) u v where
  cubes := [⟨m, yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)⟩]
  isChain := ⟨hi, hf⟩

/-- The prism cube over a single block, as a single-cube `[m+1]`-chain `u → v`. -/
noncomputable def refinePrismG {m : ℕ+} {u v : K.cells 0}
    (q : yoneda.obj ▫(m : ℕ) ⟶ PathOb.obj K.toPsh)
    (hi₀ : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint false).app K.toPsh)) = u)
    (hf₁ : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint true).app K.toPsh)) = v) :
    RefineObj (K := K) u v where
  cubes := [⟨m + 1, yonedaEquiv ((CylMap.tauto K.toPsh).prism q)⟩]
  isChain := ⟨(prism_vertex₀ q).trans hi₀, (prism_vertex₁ q).trans hf₁⟩

/-- The `ε`-direct-coface refinement `b_ε → R` over arbitrary endpoints `u, v`. -/
noncomputable def refineCofaceG (ε : Bool) {m : ℕ+} {u v : K.cells 0}
    (q : yoneda.obj ▫(m : ℕ) ⟶ PathOb.obj K.toPsh)
    (hi : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = u)
    (hf : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = v)
    (hi₀ : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint false).app K.toPsh)) = u)
    (hf₁ : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint true).app K.toPsh)) = v) :
    refineEndG ε q hi hf ⟶ refinePrismG q hi₀ hf₁ where
  chainx := (refineEndG ε q hi hf).isChain
  chainy := (refinePrismG q hi₀ hf₁).isChain
  refinement := id
  refinementMono := fun _ _ h => h
  incl := fun i => Fin.cases ((Box.coface ε).app ▫(m : ℕ)) (fun j => j.elim0) i
  inclSpec := fun i => by
    refine Fin.cases ?_ (fun j => j.elim0) i
    exact (prism_coface_cell q ε).symm

/-! ### The per-block classifying cell and its leg-faces

For a cylinder `c : CylMapR K` and a source cube cell `cell : c.src.cells m`, the block's
path-object cell is `blockQ c cell = yonedaEquiv.symm cell ≫ c.cyl : □ᵐ ⟶ PathOb K.toPsh`.  Its
two `endpoint`-faces are exactly the cube `cell` pushed along the two legs (`blockQ_face`), so
`refineEndG ε (blockQ c cell)` *is* the single-cube chain of the pushed cube
`mapCubeHom (leg ε).hom ⟨m, cell⟩`. -/

/-- The **per-block classifying cell** of a source cube cell `cell : c.src.cells m`: the
`□ᵐ`-shaped path-object cell `yonedaEquiv.symm cell ≫ c.cyl`. -/
noncomputable def blockQ (c : CylMapR K) {m : ℕ} (cell : c.src.cells m) :
    yoneda.obj ▫m ⟶ PathOb.obj K.toPsh :=
  yonedaEquiv.symm cell ≫ c.cyl

/-- The `ε`-end face of the block cell is the source cube `cell` pushed along the `ε`-leg:
`yonedaEquiv (blockQ c cell ≫ endpoint ε) = (leg ε).hom.app cell`. -/
theorem blockQ_face (c : CylMapR K) {m : ℕ} (cell : c.src.cells m) (ε : Bool) :
    yonedaEquiv (c.blockQ cell ≫ (endpoint ε).app K.toPsh)
      = (bif ε then c.rightLeg else c.leftLeg).hom⟪m⟫ cell := by
  have hleg : c.cyl ≫ (endpoint ε).app K.toPsh
      = (bif ε then c.rightLeg else c.leftLeg).hom := by
    cases ε with
    | false => exact c.hleft
    | true => exact c.hright
  rw [blockQ, Category.assoc, hleg, yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-! ### The junction vertical edge and the bridge coface (multi-block staircase pieces)

For the multi-block sweep the staircase crosses each interior junction `sⱼ` (a 0-cell of `c.src`)
by the **vertical junction edge** `eⱼ = (tauto).prism (blockQ c sⱼ)`, a `□¹` cube of `K` running
`leftLeg.app sⱼ → rightLeg.app sⱼ`.  The decisive geometric fact is that this edge is a *face* of
the adjacent block's prism cube `Rⱼ = (tauto).prism (blockQ c cellⱼ)`: precisely, `e_{j-1}` (over
the block's *initial* junction `vertex₀ cellⱼ`) is the boundary edge of `Rⱼ` selected by the
shifted initial-vertex coface `shift (initVertexMap m) : □¹ ↪ □^{m+1}`.  This is what makes the
`Sⱼ₋₁ → Pⱼ` staircase arrow a genuine `ChainRefine` (the two boundary faces `e_{j-1}`, `rcⱼ` of
`Rⱼ` both refine into it). -/

/-- **`blockQ` is natural in the cube.**  Reindexing the source cube `cell` by a cube map `g`
(here packaged as a presheaf map `g.op`-action) precomposes the block cell by `yoneda.map g`. -/
theorem blockQ_precomp (c : CylMapR K) {m₀ m : ℕ} (g : ▫m₀ ⟶ ▫m)
    (cell : c.src.cells m) :
    c.blockQ (c.src.toPsh.map g.op cell) = yoneda.map g ≫ c.blockQ cell := by
  rw [blockQ, blockQ, ← Category.assoc]
  congr 1
  exact (yonedaEquiv_symm_naturality_left g c.src.toPsh cell).symm

/-- **The vertical edge over the initial junction is a face of the block's prism cube** (cell
form).  Pulling the prism cube cell `yonedaEquiv ((tauto).prism (blockQ c cell))` back along the
shifted initial-vertex coface `shift (initVertexMap m) : □¹ ↪ □^{m+1}` recovers the vertical-edge
cell `yonedaEquiv ((tauto).prism (blockQ c (vertex₀ cell)))`.  Proof: `blockQ`'s naturality
(`blockQ_precomp` at `g = initVertexMap m`) turns `blockQ c (vertex₀ cell)` into
`yoneda.map (initVertexMap m) ≫ blockQ c cell`, then `prism_precomp` shifts the reindexing onto
the prism, and `yonedaEquiv_naturality` reads it off in cell form. -/
theorem prism_edge_coface_cell (c : CylMapR K) {m : ℕ} (cell : c.src.cells m) :
    K.toPsh.map (Box.shift.map (PrecubicalSet.initVertexMap m)).op
      (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ cell)))
      = yonedaEquiv ((CylMap.tauto K.toPsh).prism
          (c.blockQ (c.src.toPsh.vertex₀ cell))) := by
  rw [yonedaEquiv_naturality ((CylMap.tauto K.toPsh).prism (c.blockQ cell))
      (Box.shift.map (PrecubicalSet.initVertexMap m))]
  congr 1
  rw [← CylMap.prism_precomp (CylMap.tauto K.toPsh) (PrecubicalSet.initVertexMap m) (c.blockQ cell)]
  congr 1
  rw [show c.src.toPsh.vertex₀ cell
        = c.src.toPsh.map (PrecubicalSet.initVertexMap m).op cell from rfl,
    blockQ_precomp]
  rfl

/-- **The vertical edge over the FINAL junction is a face of the block's prism cube** (cell form,
the dual of `prism_edge_coface_cell`).  Pulling `R = (tauto).prism (blockQ c cell)` back along the
shifted final-vertex coface `shift (finalVertexMap m) : □¹ ↪ □^{m+1}` recovers the vertical-edge
cell over `vertex₁ cell`.  Same proof with `finalVertexMap` in place of `initVertexMap`. -/
theorem prism_edge_coface_cell_final (c : CylMapR K) {m : ℕ} (cell : c.src.cells m) :
    K.toPsh.map (Box.shift.map (PrecubicalSet.finalVertexMap m)).op
      (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ cell)))
      = yonedaEquiv ((CylMap.tauto K.toPsh).prism
          (c.blockQ (c.src.toPsh.vertex₁ cell))) := by
  rw [yonedaEquiv_naturality ((CylMap.tauto K.toPsh).prism (c.blockQ cell))
      (Box.shift.map (PrecubicalSet.finalVertexMap m))]
  congr 1
  rw [← CylMap.prism_precomp (CylMap.tauto K.toPsh) (PrecubicalSet.finalVertexMap m)
    (c.blockQ cell)]
  congr 1
  rw [show c.src.toPsh.vertex₁ cell
        = c.src.toPsh.map (PrecubicalSet.finalVertexMap m).op cell from rfl,
    blockQ_precomp]
  rfl

/-- **The vertical junction edge over a 0-cell `v`**, as a single-`□¹`-cube chain
`leftLeg.app v → rightLeg.app v` in `RefineObj`.  This is `(tauto).prism (blockQ c v)` (a `□¹`,
the prism of the *point* `v` across the interval); it is the staircase's level-crossing bridge.
It is NOT produced by `refinePrismG` (whose block dimension must be `ℕ+`); the block here is the
0-cell `v`, so we build it directly with `m = 0` (the cube dimension `0+1 = 1 : ℕ+`). -/
noncomputable def refineEdgeG (c : CylMapR K) {u w : K.cells 0} (v : c.src.cells 0)
    (hi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ v))) = u)
    (hf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ v))) = w) :
    RefineObj (K := K) u w where
  cubes := [⟨1, yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ v))⟩]
  isChain := ⟨hi, hf⟩

/-- **The bridge source chain `[e_{j-1}, rcⱼ]`** over endpoints `u, v`: the vertical edge over the
explicit junction 0-cell `s` (equal to the block's *initial* junction `vertex₀ cell` via `hs`),
followed by the block's *right* (`true`-leg) face.  Taking `s` *explicitly* (rather than computing
it as `vertex₀ cell`) is what lets the multi-block staircase **share** one edge cell between this
bridge and the mirror bridge of the previous block (whose final junction is the same `s`). -/
noncomputable def refineBridgeSrc (c : CylMapR K) {m : ℕ+} {u v : K.cells 0}
    (cell : c.src.cells (m : ℕ)) (s : c.src.cells 0)
    (hi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))) = u)
    (hmid : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
      = K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))))
    (hf : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = v) :
    RefineObj (K := K) u v where
  cubes := [⟨1, yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))⟩,
            ⟨m, yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)⟩]
  isChain := ⟨hi, hmid, hf⟩

/-- **The bridge coface `[e_{j-1}, rcⱼ] → Rⱼ`** (the 2-into-1 staircase arrow).  Both cubes of the
bridge source refine into the single prism cube `Rⱼ = (tauto).prism (blockQ c cell)`: the vertical
edge `e_{j-1}` (over the explicit junction `s = vertex₀ cell`, via `hs`) is the boundary face
selected by the shifted initial-vertex coface `shift (initVertexMap m)` (`inclSpec` =
`prism_edge_coface_cell`, transported across `hs`), and the right face `rcⱼ` is the `true`-end
coface (`inclSpec` = `prism_coface_cell .. true`).  The reindexing is constant `0`. -/
noncomputable def refineBridgeCoface (c : CylMapR K) {m : ℕ+} {u v : K.cells 0}
    (cell : c.src.cells (m : ℕ)) (s : c.src.cells 0)
    (hs : c.src.toPsh.vertex₀ cell = s)
    (hi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))) = u)
    (hmid : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
      = K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))))
    (hf : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = v)
    (hi₀ : K.toPsh.vertex₀
      (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = u)
    (hf₁ : K.toPsh.vertex₁
      (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = v) :
    refineBridgeSrc c cell s hi hmid hf ⟶ refinePrismG (c.blockQ cell) hi₀ hf₁ where
  chainx := (refineBridgeSrc c cell s hi hmid hf).isChain
  chainy := (refinePrismG (c.blockQ cell) hi₀ hf₁).isChain
  refinement := fun _ => ⟨0, by simp [refinePrismG]⟩
  refinementMono := fun _ _ _ => le_refl _
  incl := fun i =>
    Fin.cases (Box.shift.map (PrecubicalSet.initVertexMap (m : ℕ)))
      (fun j => Fin.cases ((Box.coface true).app ▫(m : ℕ)) (fun k => k.elim0) j) i
  inclSpec := fun i => by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) i
    · subst hs; exact (prism_edge_coface_cell c cell).symm
    · exact (prism_coface_cell (c.blockQ cell) true).symm

/-- **The mirror bridge source chain `[lcⱼ, eⱼ]`** over endpoints `u, v`: the block's *left*
(`false`-leg) face, followed by the vertical edge over the block's *final* junction
`vertex₁ cell`.  The two cubes chain through `mid = leftLeg.app (vertex₁ cell)`.  This is the
`Sⱼ`-side fragment of the bridge that both it and the apex `Pⱼ` refine. -/
noncomputable def refineBridgeSrcR (c : CylMapR K) {m : ℕ+} {u v : K.cells 0}
    (cell : c.src.cells (m : ℕ)) (s : c.src.cells 0)
    (hi : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = u)
    (hmid : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s)))
      = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)))
    (hf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))) = v) :
    RefineObj (K := K) u v where
  cubes := [⟨m, yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)⟩,
            ⟨1, yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))⟩]
  isChain := ⟨hi, hmid, hf⟩

/-- **The mirror bridge coface `[lcⱼ, eⱼ] → Rⱼ`** (the dual 2-into-1 staircase arrow).  The left
face `lcⱼ` is the `false`-end coface (`inclSpec` = `prism_coface_cell .. false`), and the vertical
edge `eⱼ` over the *final* junction `s = vertex₁ cell` (via `hs`) is the boundary face selected
by `shift (finalVertexMap m)` (`inclSpec` = `prism_edge_coface_cell_final`, transported across
`hs`). -/
noncomputable def refineBridgeCofaceR (c : CylMapR K) {m : ℕ+} {u v : K.cells 0}
    (cell : c.src.cells (m : ℕ)) (s : c.src.cells 0)
    (hs : c.src.toPsh.vertex₁ cell = s)
    (hi : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = u)
    (hmid : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s)))
      = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)))
    (hf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ s))) = v)
    (hi₀ : K.toPsh.vertex₀
      (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = u)
    (hf₁ : K.toPsh.vertex₁
      (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = v) :
    refineBridgeSrcR c cell s hi hmid hf ⟶ refinePrismG (c.blockQ cell) hi₀ hf₁ where
  chainx := (refineBridgeSrcR c cell s hi hmid hf).isChain
  chainy := (refinePrismG (c.blockQ cell) hi₀ hf₁).isChain
  refinement := fun _ => ⟨0, by simp [refinePrismG]⟩
  refinementMono := fun _ _ _ => le_refl _
  incl := fun i =>
    Fin.cases ((Box.coface false).app ▫(m : ℕ))
      (fun j => Fin.cases (Box.shift.map (PrecubicalSet.finalVertexMap (m : ℕ)))
        (fun k => k.elim0) j) i
  inclSpec := fun i => by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) i
    · exact (prism_coface_cell (c.blockQ cell) false).symm
    · subst hs; exact (prism_edge_coface_cell_final c cell).symm

end CylMapR
