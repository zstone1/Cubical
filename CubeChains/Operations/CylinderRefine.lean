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
    {b₀ b₁ b₀' b₁' : K.toPsh.cells 0} (h₀ : b₀ = b₀') (h₁ : b₁ = b₁')
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

/-! ## 6. The single-block sweep cospan in `RefineObj` (Piece 3 — the geometric core)

For one cube block presented as a cell `q : □ᵐ ⟶ PathOb K.toPsh` of the path object, the
**prism cube** `R = (tauto).prism q : □^{m+1} ⟶ K.toPsh` sweeps the block across the
interval; its bottom (`e₀`-)face is the left-leg block `b₀ = q ≫ e₀` and its top
(`e₁`-)face is the right-leg block `b₁ = q ≫ e₁` (`CylMap.coface_prism`).

In the **refinement category** `RefineObj` — unlike the wedge-map `ChainCat.Obj` — the two
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
    (q : yoneda.obj (Box.ob m) ⟶ PathOb.obj K) (ε : Bool) :
    K.map ((Box.coface ε).app (Box.ob m)).op
        (yonedaEquiv ((CylMap.tauto K).prism q))
      = yonedaEquiv (q ≫ (endpoint ε).app K) := by
  rw [yonedaEquiv_naturality ((CylMap.tauto K).prism q) ((Box.coface ε).app (Box.ob m))]
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
noncomputable def refineEndG (ε : Bool) {m : ℕ+} {u v : K.toPsh.cells 0}
    (q : yoneda.obj (Box.ob (m : ℕ)) ⟶ PathOb.obj K.toPsh)
    (hi : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = u)
    (hf : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = v) :
    RefineObj (K := K) u v where
  cubes := [⟨m, yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)⟩]
  isChain := ⟨hi, hf⟩

/-- The prism cube over a single block, as a single-cube `[m+1]`-chain `u → v`. -/
noncomputable def refinePrismG {m : ℕ+} {u v : K.toPsh.cells 0}
    (q : yoneda.obj (Box.ob (m : ℕ)) ⟶ PathOb.obj K.toPsh)
    (hi₀ : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint false).app K.toPsh)) = u)
    (hf₁ : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint true).app K.toPsh)) = v) :
    RefineObj (K := K) u v where
  cubes := [⟨m + 1, yonedaEquiv ((CylMap.tauto K.toPsh).prism q)⟩]
  isChain := ⟨(prism_vertex₀ q).trans hi₀, (prism_vertex₁ q).trans hf₁⟩

/-- The `ε`-direct-coface refinement `b_ε → R` over arbitrary endpoints `u, v`. -/
noncomputable def refineCofaceG (ε : Bool) {m : ℕ+} {u v : K.toPsh.cells 0}
    (q : yoneda.obj (Box.ob (m : ℕ)) ⟶ PathOb.obj K.toPsh)
    (hi : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = u)
    (hf : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint ε).app K.toPsh)) = v)
    (hi₀ : K.toPsh.vertex₀ (yonedaEquiv (q ≫ (endpoint false).app K.toPsh)) = u)
    (hf₁ : K.toPsh.vertex₁ (yonedaEquiv (q ≫ (endpoint true).app K.toPsh)) = v) :
    refineEndG ε q hi hf ⟶ refinePrismG q hi₀ hf₁ where
  chainx := (refineEndG ε q hi hf).isChain
  chainy := (refinePrismG q hi₀ hf₁).isChain
  refinement := id
  refinementMono := fun _ _ h => h
  incl := fun i => Fin.cases ((Box.coface ε).app (Box.ob (m : ℕ))) (fun j => j.elim0) i
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
noncomputable def blockQ (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    yoneda.obj (Box.ob m) ⟶ PathOb.obj K.toPsh :=
  yonedaEquiv.symm cell ≫ c.cyl

/-- The `ε`-end face of the block cell is the source cube `cell` pushed along the `ε`-leg:
`yonedaEquiv (blockQ c cell ≫ endpoint ε) = (leg ε).hom.app cell`. -/
theorem blockQ_face (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) (ε : Bool) :
    yonedaEquiv (c.blockQ cell ≫ (endpoint ε).app K.toPsh)
      = (bif ε then c.rightLeg else c.leftLeg).hom.app (op (Box.ob m)) cell := by
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
theorem blockQ_precomp (c : CylMapR K) {m₀ m : ℕ} (g : Box.ob m₀ ⟶ Box.ob m)
    (cell : c.src.toPsh.cells m) :
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
theorem prism_edge_coface_cell (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
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
theorem prism_edge_coface_cell_final (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
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
noncomputable def refineEdgeG (c : CylMapR K) {u w : K.toPsh.cells 0} (v : c.src.toPsh.cells 0)
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
noncomputable def refineBridgeSrc (c : CylMapR K) {m : ℕ+} {u v : K.toPsh.cells 0}
    (cell : c.src.toPsh.cells (m : ℕ)) (s : c.src.toPsh.cells 0)
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
noncomputable def refineBridgeCoface (c : CylMapR K) {m : ℕ+} {u v : K.toPsh.cells 0}
    (cell : c.src.toPsh.cells (m : ℕ)) (s : c.src.toPsh.cells 0)
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
      (fun j => Fin.cases ((Box.coface true).app (Box.ob (m : ℕ))) (fun k => k.elim0) j) i
  inclSpec := fun i => by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) i
    · subst hs; exact (prism_edge_coface_cell c cell).symm
    · exact (prism_coface_cell (c.blockQ cell) true).symm

/-- **The mirror bridge source chain `[lcⱼ, eⱼ]`** over endpoints `u, v`: the block's *left*
(`false`-leg) face, followed by the vertical edge over the block's *final* junction
`vertex₁ cell`.  The two cubes chain through `mid = leftLeg.app (vertex₁ cell)`.  This is the
`Sⱼ`-side fragment of the bridge that both it and the apex `Pⱼ` refine. -/
noncomputable def refineBridgeSrcR (c : CylMapR K) {m : ℕ+} {u v : K.toPsh.cells 0}
    (cell : c.src.toPsh.cells (m : ℕ)) (s : c.src.toPsh.cells 0)
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
noncomputable def refineBridgeCofaceR (c : CylMapR K) {m : ℕ+} {u v : K.toPsh.cells 0}
    (cell : c.src.toPsh.cells (m : ℕ)) (s : c.src.toPsh.cells 0)
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
    Fin.cases ((Box.coface false).app (Box.ob (m : ℕ)))
      (fun j => Fin.cases (Box.shift.map (PrecubicalSet.finalVertexMap (m : ℕ)))
        (fun k => k.elim0) j) i
  inclSpec := fun i => by
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) i
    · exact (prism_coface_cell (c.blockQ cell) false).symm
    · subst hs; exact (prism_edge_coface_cell_final c cell).symm

end CylMapR

/-! ## 7. RefineObj-native concatenation (Piece 4 backbone)

Unlike the wedge-map `ChainCat.Obj` — whose concatenation needs the Segal pushout machinery
(`concatWedgeMap`, `Chains/Segal.lean`) — concatenation in the refinement category is
**literally list append**: an object is `⟨cubes, isChain⟩`, and `isCubeChain_append` splices
the chain proofs; a `ChainRefine` morphism is index-keyed reindexing + per-cube inclusion data,
so two morphisms concatenate by offsetting the second block's indices.  This is the reusable
backbone for the multi-block sweep (the analogue of `Ch'.concatMor`/`Ch'.whisker`, far simpler
here). -/

namespace CubeChain

variable {K : BPSet}

/-- **Object-level concatenation of refinement chains.**  Append the cube lists; the spliced
chain proof is `isCubeChain_append`.  (`a ⇝ m` then `m ⇝ b` gives `a ⇝ b`.) -/
def RefineObj.append {a m b : K.toPsh.cells 0}
    (x : RefineObj (K := K) a m) (y : RefineObj (K := K) m b) : RefineObj (K := K) a b where
  cubes := x.cubes ++ y.cubes
  isChain := isCubeChain_append x.isChain y.isChain

@[simp] theorem RefineObj.append_cubes {a m b : K.toPsh.cells 0}
    (x : RefineObj (K := K) a m) (y : RefineObj (K := K) m b) :
    (x.append y).cubes = x.cubes ++ y.cubes := rfl

/-- A refinement object is determined by its cube list (`isChain` is a `Prop`); local copy of
`Correspondence.RefineObj.ext'` (not imported here). -/
theorem RefineObj.ext'' {a b : K.toPsh.cells 0} {x y : RefineObj (K := K) a b}
    (h : x.cubes = y.cubes) : x = y := by
  obtain ⟨xc, xh⟩ := x; obtain ⟨yc, _⟩ := y; subst h; rfl

/-- **Associativity of refinement-chain concatenation** (on the nose, `isChain` being a `Prop`):
`(x.append y).append z = x.append (y.append z)`.  This is the single object bridge the
list-indexed staircase fold reassociates `.append` by (`eqToHom` of it, promoted through
`FreeGroupoid.of`). -/
theorem RefineObj.append_assoc {a m₁ m₂ b : K.toPsh.cells 0}
    (x : RefineObj (K := K) a m₁) (y : RefineObj (K := K) m₁ m₂) (z : RefineObj (K := K) m₂ b) :
    (x.append y).append z = x.append (y.append z) :=
  RefineObj.ext'' (by simp [RefineObj.append, List.append_assoc])

/-! ### Morphism-level concatenation

A `ChainRefine` on appended chains is the disjoint union of the two component refinements:
index `i` in the first block uses `f`, in the second block uses `g` offset by the first
refined block's length.  This is the `RefineObj` analogue of the wedge-map `Ch'.concatMor` —
but *combinatorially*, over raw `++` lists, rather than via Segal pushouts. -/

/-- The reindexing of the concatenation: `Fin.addCases` of `f.refinement` (cast into the left
block of `x' ++ y'`) and `g.refinement` (cast into the right block), under the
`List.length_append` casts. -/
def appendRefinement
    {x x' y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (rf : Fin x.length → Fin x'.length) (rg : Fin y.length → Fin y'.length) :
    Fin (x ++ y).length → Fin (x' ++ y').length := fun i =>
  Fin.cast (List.length_append ..).symm
    (Fin.addCases
      (fun a => (rf a).castAdd y'.length)
      (fun b => (rg b).natAdd x'.length)
      (Fin.cast (List.length_append ..) i))

/-- The `ℕ`-value of `appendRefinement` at an index in the **left** block (`i.val < x.length`)
is the value of `rf` there. -/
theorem appendRefinement_val_left
    {x x' y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (rf : Fin x.length → Fin x'.length) (rg : Fin y.length → Fin y'.length)
    (i : Fin (x ++ y).length) (hi : (i : ℕ) < x.length) :
    (appendRefinement rf rg i : ℕ) = (rf ⟨i, hi⟩ : ℕ) := by
  simp only [appendRefinement, Fin.val_cast]
  rw [show Fin.cast (List.length_append ..) i
        = Fin.castAdd y.length ⟨i, hi⟩ from by apply Fin.ext; simp,
    Fin.addCases_left]
  simp

/-- The `ℕ`-value of `appendRefinement` at an index in the **right** block
(`x.length ≤ i.val`) is `x'.length` plus the value of `rg` there. -/
theorem appendRefinement_val_right
    {x x' y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (rf : Fin x.length → Fin x'.length) (rg : Fin y.length → Fin y'.length)
    (i : Fin (x ++ y).length) (hi : x.length ≤ (i : ℕ))
    (hi' : (i : ℕ) - x.length < y.length) :
    (appendRefinement rf rg i : ℕ) = x'.length + (rg ⟨(i : ℕ) - x.length, hi'⟩ : ℕ) := by
  simp only [appendRefinement, Fin.val_cast]
  rw [show Fin.cast (List.length_append ..) i
        = Fin.natAdd x.length ⟨(i : ℕ) - x.length, hi'⟩ from by apply Fin.ext; simp; omega,
    Fin.addCases_right]
  simp

/-- The left-block `.get` of an append (with the `length_append` cast). -/
theorem get_append_castAdd {l l' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))} (i : Fin l.length) :
    (l ++ l').get (Fin.cast (List.length_append ..).symm (i.castAdd l'.length)) = l.get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_left] <;> simp

/-- The right-block `.get` of an append (with the `length_append` cast). -/
theorem get_append_natAdd {l l' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))} (i : Fin l'.length) :
    (l ++ l').get (Fin.cast (List.length_append ..).symm (i.natAdd l.length)) = l'.get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_right] <;> simp

/-- The per-cube inclusion of the concatenation, as a *named* `Fin.addCases` (so the
`inclSpec` proof can rewrite it by `Fin.addCases_left/right`): each cube keeps its own block's
`incl`, bridged by the `get_append_*` `eqToHom` transports. -/
noncomputable def appendIncl {a m b : K.toPsh.cells 0}
    {x x' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (i : Fin (x ++ y).length) :
    Box.ob (((x ++ y).get i).1 : ℕ) ⟶
      Box.ob (((x' ++ y').get (appendRefinement f.refinement g.refinement i)).1 : ℕ) :=
  Fin.addCases
    (motive := fun i₀ =>
      Box.ob (((x ++ y).get (Fin.cast (List.length_append ..).symm i₀)).1 : ℕ) ⟶
        Box.ob (((x' ++ y').get (appendRefinement f.refinement g.refinement
          (Fin.cast (List.length_append ..).symm i₀))).1 : ℕ))
    (fun ia =>
      eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ)) (get_append_castAdd ia))
        ≫ f.incl ia
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ))
            ((get_append_castAdd (f.refinement ia)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))))
    (fun ib =>
      eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ)) (get_append_natAdd ib))
        ≫ g.incl ib
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ))
            ((get_append_natAdd (g.refinement ib)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))))
    (Fin.cast (List.length_append ..) i)

/-- `appendIncl` reduces on a **left**-block index `i.castAdd` to `f`'s inclusion (the cast
inside `appendIncl` collapses, then `Fin.addCases_left` fires). -/
theorem appendIncl_castAdd {a m b : K.toPsh.cells 0}
    {x x' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (ia : Fin x.length) :
    appendIncl f g (Fin.cast (List.length_append ..).symm (ia.castAdd y.length))
      = eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ)) (get_append_castAdd ia))
        ≫ f.incl ia
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ))
            ((get_append_castAdd (f.refinement ia)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))) := by
  rw [appendIncl]
  simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_left]

/-- `appendIncl` reduces on a **right**-block index `i.natAdd` to `g`'s inclusion. -/
theorem appendIncl_natAdd {a m b : K.toPsh.cells 0}
    {x x' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (ib : Fin y.length) :
    appendIncl f g (Fin.cast (List.length_append ..).symm (ib.natAdd x.length))
      = eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ)) (get_append_natAdd ib))
        ≫ g.incl ib
        ≫ eqToHom (congrArg (fun c : Σ n : ℕ+, _ => Box.ob (c.1 : ℕ))
            ((get_append_natAdd (g.refinement ib)).symm.trans (by
              rw [appendRefinement]; congr 1; simp))) := by
  rw [appendIncl]
  simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.addCases_right]

/-- The block-wise `inclSpec` of the concatenation, proved by `Fin.addCases` on the casted
index: on each branch `appendIncl` reduces (`appendIncl_castAdd`/`_natAdd`), the `.get`s reduce
(`get_append_*`), and the goal is `f`/`g`'s own `inclSpec` modulo the `eqToHom` transports
(`map_eqToHom_op_cell`). -/
theorem appendInclSpec {a m b : K.toPsh.cells 0}
    {x x' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') (i : Fin (x ++ y).length) :
    ((x ++ y).get i).2
      = K.toPsh.map (appendIncl f g i).op
        ((x' ++ y').get (appendRefinement f.refinement g.refinement i)).2 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = Fin.cast (List.length_append ..).symm j :=
    ⟨Fin.cast (List.length_append ..) i, by apply Fin.ext; simp⟩
  induction j using Fin.addCases with
  | left ia =>
    -- the source/target cube cells are `x.get ia`, `x'.get (f.refinement ia)`.
    have hsrc := get_append_castAdd (l := x) (l' := y) ia
    have htgt : (x' ++ y').get (appendRefinement f.refinement g.refinement
          (Fin.cast (List.length_append ..).symm (ia.castAdd y.length)))
        = x'.get (f.refinement ia) := by
      rw [show appendRefinement f.refinement g.refinement
            (Fin.cast (List.length_append ..).symm (ia.castAdd y.length))
          = Fin.cast (List.length_append ..).symm ((f.refinement ia).castAdd y'.length) from by
          apply Fin.ext; rw [appendRefinement_val_left _ _ _ (by simp)]; simp]
      exact get_append_castAdd (f.refinement ia)
    rw [appendIncl_castAdd f g ia, op_comp, op_comp, K.toPsh.map_comp, K.toPsh.map_comp,
      types_comp_apply, types_comp_apply,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp htgt).2, ← f.inclSpec ia,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp hsrc).2.symm]
  | right ib =>
    have hsrc := get_append_natAdd (l := x) (l' := y) ib
    have htgt : (x' ++ y').get (appendRefinement f.refinement g.refinement
          (Fin.cast (List.length_append ..).symm (ib.natAdd x.length)))
        = y'.get (g.refinement ib) := by
      rw [show appendRefinement f.refinement g.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd x.length))
          = Fin.cast (List.length_append ..).symm ((g.refinement ib).natAdd x'.length) from by
          apply Fin.ext; rw [appendRefinement_val_right _ _ _ (by simp) (by simp)]; simp]
      exact get_append_natAdd (g.refinement ib)
    rw [appendIncl_natAdd f g ib, op_comp, op_comp, K.toPsh.map_comp, K.toPsh.map_comp,
      types_comp_apply, types_comp_apply,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp htgt).2, ← g.inclSpec ib,
      map_eqToHom_op_cell _ (Sigma.ext_iff.mp hsrc).2.symm]

/-- **Morphism-level concatenation of refinements.**  Given `f : ChainRefine a m x x'` and
`g : ChainRefine m b y y'`, splice them to a refinement of the appended chains
`x ++ y ⟶ x' ++ y'` (over `a, b`): the reindexing is `appendRefinement`, each cube keeps its
own block's inclusion (`appendIncl`, bridged by the `get_append_*` `eqToHom` transports), and
`inclSpec`/monotonicity hold block-wise. -/
noncomputable def ChainRefine.append {a m b : K.toPsh.cells 0}
    {x x' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    {y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y') :
    ChainRefine a b (x ++ y) (x' ++ y') where
  chainx := isCubeChain_append f.chainx g.chainx
  chainy := isCubeChain_append f.chainy g.chainy
  refinement := appendRefinement f.refinement g.refinement
  refinementMono := by
    intro i j hij
    have hijn : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
    rw [Fin.le_def]
    by_cases hj : (j : ℕ) < x.length
    · -- both in the left block (`i ≤ j < x.length`); use `f` monotone.
      have hi : (i : ℕ) < x.length := lt_of_le_of_lt hijn hj
      rw [appendRefinement_val_left _ _ i hi, appendRefinement_val_left _ _ j hj]
      exact Fin.le_def.mp (f.refinementMono ⟨i, hi⟩ ⟨j, hj⟩ (by rw [Fin.le_def]; exact hijn))
    · -- `j` in the right block; `appendRefinement j ≥ x'.length`.
      rw [not_lt] at hj
      have hj' : (j : ℕ) - x.length < y.length := by have := j.isLt; simp at this; omega
      rw [appendRefinement_val_right _ _ j hj hj']
      by_cases hi : (i : ℕ) < x.length
      · -- `i` left, `j` right: left value `< x'.length ≤ right value`.
        rw [appendRefinement_val_left _ _ i hi]
        exact le_trans (Nat.le_of_lt (f.refinement ⟨i, hi⟩).isLt) (Nat.le_add_right _ _)
      · -- both right; use `g` monotone.
        rw [not_lt] at hi
        have hi' : (i : ℕ) - x.length < y.length := by have := i.isLt; simp at this; omega
        rw [appendRefinement_val_right _ _ i hi hi']
        have : (⟨(i : ℕ) - x.length, hi'⟩ : Fin y.length) ≤ ⟨(j : ℕ) - x.length, hj'⟩ := by
          rw [Fin.le_def]; simp only []; omega
        exact Nat.add_le_add_left (Fin.le_def.mp (g.refinementMono _ _ this)) _
  incl := appendIncl f g
  inclSpec := appendInclSpec f g

/-! ### Left-whiskering: prepend a fixed chain (the per-block promotion functor)

Fixing a prefix chain `pre : RefineObj a m`, post-composing `pre.append (-) : RefineObj m b ⥤
RefineObj a b` is a functor: on morphisms it is `ChainRefine.append (𝟙 pre) g` (identity on the
fixed prefix, `g` on the variable tail).  `FreeGroupoid.map` of it promotes a *local* per-block
sweep up to the d-path groupoid — the analogue of the wedge-map `Ch'.whisker`, but combinatorial.

The morphism map is `RefineObj.appendLeftMap` (identity on the fixed prefix, `g` on the tail); the
functor laws `map_id`/`map_comp` are discharged via `ChainRefine.ext` over the
`appendIncl`-`Fin.addCases` transports (the reindexings collapse to the identity/composite
definitionally).  The assembled functor is `RefineObj.appendLeft` below. -/

/-- The value of `appendRefinement id rg` is `rg` offset, computed pointwise (the prefix block
is fixed: `id` on the first `x.length` indices). -/
theorem appendRefinement_id_left {x y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (rg : Fin y.length → Fin y'.length) (i : Fin (x ++ y).length) :
    (appendRefinement (id : Fin x.length → Fin x.length) rg i : ℕ)
      = if h : (i : ℕ) < x.length then (i : ℕ)
        else x.length + (rg ⟨(i : ℕ) - x.length, by
          have := i.isLt
          have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
          omega⟩ : ℕ) := by
  by_cases h : (i : ℕ) < x.length
  · rw [dif_pos h, appendRefinement_val_left _ _ i h]; rfl
  · rw [dif_neg h]
    have hi' : (i : ℕ) - x.length < y.length := by
      have h1 := i.isLt; have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
      omega
    rw [appendRefinement_val_right _ _ i (by omega) hi']

/-- **Left-whiskering on morphisms.**  Prepend the identity on the fixed prefix `pre` to a tail
refinement `g : y₁ ⟶ y₂`. -/
noncomputable def RefineObj.appendLeftMap {a m b : K.toPsh.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂) :
    pre.append y₁ ⟶ pre.append y₂ :=
  ChainRefine.append (𝟙 pre) g

/-- The prefix-whiskering reindexing of the **identity** tail is the identity. -/
theorem appendRefinement_id_id {x y : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))} :
    appendRefinement (id : Fin x.length → Fin x.length) (id : Fin y.length → Fin y.length)
      = id := by
  funext i
  apply Fin.ext
  rw [appendRefinement_id_left]
  by_cases h : (i : ℕ) < x.length
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; simp only [id_eq]
    have h1 := i.isLt; have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
    omega

/-- The prefix-whiskering reindexing distributes over composition of the tail (the
`refineCategory` composition `g₂.refinement ∘ g₁.refinement`). -/
theorem appendRefinement_id_comp {x y y' y'' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (rg₁ : Fin y.length → Fin y'.length) (rg₂ : Fin y'.length → Fin y''.length) :
    appendRefinement (id : Fin x.length → Fin x.length) (rg₂ ∘ rg₁)
      = appendRefinement (id : Fin x.length → Fin x.length) rg₂
        ∘ appendRefinement (id : Fin x.length → Fin x.length) rg₁ := by
  funext i
  apply Fin.ext
  -- abbreviate the inner whiskering and its value (via `appendRefinement_id_left`).
  set j := appendRefinement (id : Fin x.length → Fin x.length) rg₁ i with hj
  have hjv := appendRefinement_id_left (x := x) rg₁ i
  rw [← hj] at hjv
  by_cases h : (i : ℕ) < x.length
  · -- left block: LHS `= i`; inner `j` also `= i < x.length`, outer `= j = i`.
    have hji : (j : ℕ) = (i : ℕ) := by rw [hjv, dif_pos h]
    rw [Function.comp_apply, appendRefinement_id_left, dif_pos h, ← hj, appendRefinement_id_left,
      dif_pos (by rw [hji]; exact h), hji]
  · -- right block: LHS `= x.length + rg₂ (rg₁ (i-x.length))`; outer of inner agrees.
    have hi' : (i : ℕ) - x.length < y.length := by
      have h1 := i.isLt; have h2 : (x ++ y).length = x.length + y.length := List.length_append ..
      omega
    -- inner `j` lands in the right block of `x ++ y'` at offset `rg₁ (i-x.length)`.
    have hjge : ¬ (j : ℕ) < x.length := by
      rw [hjv, dif_neg h]; omega
    have hjsub : (j : ℕ) - x.length = (rg₁ ⟨(i : ℕ) - x.length, hi'⟩ : ℕ) := by
      rw [hjv, dif_neg h]; omega
    rw [Function.comp_apply, appendRefinement_id_left, dif_neg h, ← hj, appendRefinement_id_left,
      dif_neg hjge]
    -- `x.length + ↑((rg₂∘rg₁)⟨i-x.length⟩) = x.length + ↑(rg₂⟨j-x.length⟩)`; the `Fin` args agree.
    congr 1
    exact congrArg (fun z : Fin y'.length => (rg₂ z : ℕ)) (Fin.ext hjsub.symm)

/-! ### The left-whiskering functor

Assembling `appendLeftMap` into a genuine `Functor`.  The two functor laws are proved as
plain morphism equalities by `ChainRefine.ext`: the reindexings of `map_id`/`map_comp` are
*not* definitionally `id`/`∘` (they route through `Fin.addCases`/`Fin.cast`), so the
reindexing halves are `appendRefinement_id_id`/`appendRefinement_id_comp`, and the inclusion
halves are `HEq`s reduced branch-wise via `appendIncl_castAdd`/`_natAdd`.

The `incl`-`HEq` is reduced to a *pointwise equality* via `incl_heq_of_index_eq`: when two
refinements `f g` of the SAME pair of chains have reindexings related by `hr : f.ref = g.ref`,
their inclusion families are `HEq` iff they agree after the canonical `eqToHom` transport of
`hr` (the `subst`-based `incl_index_eq` of `RefineFunctor.lean`, here over `f.ref i = g.ref i`).
Both functor laws are between refinements of the same chains, so this applies. -/

/-- The identity refinement's reindexing is `id` (definitional unfold of `refineCategory.id`). -/
theorem refine_id_refinement {a b : K.toPsh.cells 0} (x : RefineObj (K := K) a b) :
    (𝟙 x : x ⟶ x).refinement = id := rfl

/-- The identity refinement's inclusion is `𝟙` (definitional unfold of `refineCategory.id`). -/
theorem refine_id_incl {a b : K.toPsh.cells 0} (x : RefineObj (K := K) a b)
    (i : Fin x.cubes.length) : (𝟙 x : x ⟶ x).incl i = 𝟙 _ := rfl

/-- A composite refinement's reindexing is the composite of reindexings. -/
theorem refine_comp_refinement {a b : K.toPsh.cells 0} {x y z : RefineObj (K := K) a b}
    (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).refinement = g.refinement ∘ f.refinement := rfl

/-- A composite refinement's inclusion is the composite of inclusions. -/
theorem refine_comp_incl {a b : K.toPsh.cells 0} {x y z : RefineObj (K := K) a b}
    (f : x ⟶ y) (g : y ⟶ z) (i : Fin x.cubes.length) :
    (f ≫ g).incl i = f.incl i ≫ g.incl (f.refinement i) := rfl

/-- `incl`-`HEq` between two refinements of the **same** chains whose reindexings are equal:
it suffices to check, for each index, that `f.incl i` equals `g.incl i` post-composed with the
canonical `eqToHom` transport of the target across `hr : f.ref = g.ref` (`f`/`g` share the
source `x.get i`, differing only on the target `y.get (· i)`). -/
private theorem incl_heq_of_index_eq {a b : K.toPsh.cells 0}
    {x y : RefineObj (K := K) a b} {f g : x ⟶ y} (hr : f.refinement = g.refinement)
    (h : ∀ i, f.incl i
      = g.incl i
        ≫ eqToHom (congrArg (fun l => Box.ob ((y.cubes.get l).1 : ℕ)) (congrFun hr i).symm)) :
    HEq f.incl g.incl := by
  refine Function.hfunext rfl ?_
  intro i i' hii
  obtain rfl : i = i' := eq_of_heq hii
  rw [h i]
  -- `HEq (g.incl i ≫ eqToHom η) (g.incl i)`: the `eqToHom` is between equal objects (`hr`).
  exact comp_eqToHom_heq _ _

/-- Any morphism built from `eqToHom`s and a `𝟙` seam, framed by an `eqToHom h` of the right
endpoints, equals `eqToHom h`: the `eqToHom`-conjugate of a `𝟙` is again an `eqToHom`.  Used to
close the per-index `map_id` goals where `simp`'s syntactic `id_comp` cannot see the defeq
seam. -/
theorem eqToHom_id_seam {C : Type*} [Category C] {X Y Z : C}
    (h1 : X = Y) (h2 : Y = Z) (h : X = Z) :
    eqToHom h1 ≫ 𝟙 Y ≫ eqToHom h2 = eqToHom h := by
  subst h1; subst h2; simp

/-- `𝟙 ≫ eqToHom h₂ = eqToHom h` framed at the right endpoints (the `𝟙`-seam variant with no
leading `eqToHom`). -/
theorem id_eqToHom_seam {C : Type*} [Category C] {X Z : C} (h2 : X = Z) (h : X = Z) :
    𝟙 X ≫ eqToHom h2 = eqToHom h := by
  subst h2; simp

/-- **`eqToHom`-composites are heterogeneously the identity.**  Any morphism that is `≍ 𝟙` of
its domain (e.g. any composite of `eqToHom`s and `𝟙`s) is determined: two such parallel
morphisms are equal.  This sidesteps `eqToHom_trans`'s *syntactic* seam-matching, which fails
when the intermediate objects are only *definitionally* equal (as the `appendIncl` transports
produce). -/
theorem hom_eq_of_heq_id {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y}
    (hf : f ≍ 𝟙 X) (hg : g ≍ 𝟙 X) : f = g :=
  eq_of_heq (hf.trans hg.symm)

/-- Two parallel morphisms that are each `≍` a common `core` are equal (the `core` may live over
different — but defeq — endpoints; used to compare two `eqToHom`-framed copies of the same
`incl`-composite). -/
theorem hom_eq_of_heq_core {C : Type*} [Category C] {X Y X' Y' : C} {f g : X ⟶ Y}
    {core : X' ⟶ Y'} (hf : f ≍ core) (hg : g ≍ core) : f = g :=
  eq_of_heq (hf.trans hg.symm)

/-- A leading `eqToHom` is `≍`-transparent: from `f ≍ g` conclude `eqToHom h ≫ f ≍ g` — the
`=`-typed restatement of `eqToHom_comp_heq` that unifies the seam by **defeq** (so it fires
where the syntactic `eqToHom_trans` simp lemma stalls on the `appendIncl` transports).  `g` is
fully general (`≍` ignores its endpoints). -/
theorem eqToHom_comp_heq' {C : Type*} [Category C] {W X Y : C} (h : W = X)
    (f : X ⟶ Y) {Z Z' : C} (g : Z ⟶ Z') (hfg : f ≍ g) : eqToHom h ≫ f ≍ g :=
  (eqToHom_comp_heq f h).trans hfg

/-- A trailing `eqToHom` is `≍`-transparent: from `f ≍ g` conclude `f ≫ eqToHom h ≍ g` (defeq
seam; `g` fully general). -/
theorem comp_eqToHom_heq' {C : Type*} [Category C] {X Y Z : C} (h : Y = Z)
    (f : X ⟶ Y) {W W' : C} (g : W ⟶ W') (hfg : f ≍ g) : f ≫ eqToHom h ≍ g :=
  (comp_eqToHom_heq f h).trans hfg

/-- Move a `ChainRefine.append`'s inclusion across an index equality `i = i'`, inserting the
canonical `eqToHom` transports (`subst`-robust against the `Fin.cast` round-trips). -/
theorem appendIncl_index_eq {a m b : K.toPsh.cells 0}
    {x x' y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))}
    (f : ChainRefine a m x x') (g : ChainRefine m b y y')
    {i i' : Fin (x ++ y).length} (h : i = i') :
    appendIncl f g i
      = eqToHom (congrArg (fun l => Box.ob (((x ++ y).get l).1 : ℕ)) h)
        ≫ appendIncl f g i'
        ≫ eqToHom (congrArg
            (fun l => Box.ob (((x' ++ y').get
              (appendRefinement f.refinement g.refinement l)).1 : ℕ)) h.symm) :=
  -- `appendIncl f g = (f.append g).incl` definitionally, so this is the promoted
  -- index-transport lemma `ChainRefine.incl_index_eq` of `RefineFunctor.lean`.
  ChainRefine.incl_index_eq (f.append g) h

/-- The cube of `pre.append y` at a prefix-whiskered tail index (`appendRefinement id rg` of a
`natAdd ib`) is the tail's cube `y.get (rg ib)` (the prefix-`id` part collapses). -/
theorem append_get_natAdd
    {x y y' : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))} (rg : Fin y.length → Fin y'.length)
    (ib : Fin y.length) :
    ((x ++ y').get (appendRefinement (id : Fin x.length → Fin x.length) rg
        (Fin.cast (List.length_append ..).symm (ib.natAdd x.length)))).1
      = (y'.get (rg ib)).1 := by
  have hv : appendRefinement (id : Fin x.length → Fin x.length) rg
        (Fin.cast (List.length_append ..).symm (ib.natAdd x.length))
      = Fin.cast (List.length_append ..).symm ((rg ib).natAdd x.length) := by
    apply Fin.ext
    rw [appendRefinement_val_right _ _ _ (by simp) (by simp)]; simp
  rw [hv]; exact congrArg (·.1) (get_append_natAdd (rg ib))

/-- **The prefix-whiskered inclusion is heterogeneously the tail's inclusion.**  On a tail
(`natAdd`) index, `appendIncl (𝟙 pre) g` is `g.incl ib` framed by `eqToHom`s, so `≍ g.incl ib`
(the frames strip under `≍`, which tolerates the defeq seams). -/
theorem appendIncl_natAdd_heq {a m b : K.toPsh.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂)
    (ib : Fin y₁.cubes.length) :
    appendIncl (𝟙 pre) g (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length))
      ≍ g.incl ib := by
  rw [appendIncl_natAdd]
  refine eqToHom_comp_heq' _ _ (g.incl ib) ?_
  exact comp_eqToHom_heq' _ _ (g.incl ib) HEq.rfl

/-- `appendLeftMap pre g` is definitionally `ChainRefine.append (𝟙 pre) g`, hence its inclusion
is `appendIncl (𝟙 pre) g` — a `rfl` bridge so `appendIncl_castAdd`/`_natAdd` apply. -/
theorem appendLeftMap_incl {a m b : K.toPsh.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂) :
    (pre.appendLeftMap g).incl = appendIncl (𝟙 pre) g := rfl

/-- The reindexing of `appendLeftMap` is `appendRefinement id g.refinement`. -/
theorem appendLeftMap_refinement {a m b : K.toPsh.cells 0}
    (pre : RefineObj (K := K) a m) {y₁ y₂ : RefineObj (K := K) m b} (g : y₁ ⟶ y₂) :
    (pre.appendLeftMap g).refinement = appendRefinement id g.refinement := rfl

/-- **The left-whiskering functor.**  Prepend the fixed prefix `pre` to a tail chain; on
morphisms this is `appendLeftMap`.  `FreeGroupoid.map` of it promotes a local sweep up to the
d-path groupoid (the combinatorial analogue of the wedge-map `Ch'.whisker`). -/
noncomputable def RefineObj.appendLeft {a m b : K.toPsh.cells 0}
    (pre : RefineObj (K := K) a m) : RefineObj (K := K) m b ⥤ RefineObj (K := K) a b where
  obj y := pre.append y
  map g := pre.appendLeftMap g
  map_id y := by
    refine ChainRefine.ext appendRefinement_id_id (incl_heq_of_index_eq appendRefinement_id_id ?_)
    intro i
    rw [refine_id_incl, appendLeftMap_incl]
    obtain ⟨j, rfl⟩ : ∃ j, i = Fin.cast (List.length_append ..).symm j :=
      ⟨Fin.cast (List.length_append ..) i, by apply Fin.ext; simp⟩
    induction j using Fin.addCases with
    | left ia =>
      rw [appendIncl_castAdd, refine_id_incl]
      simp only [refine_id_refinement, id_eq, Category.id_comp, eqToHom_trans]
      rfl
    | right ib =>
      rw [appendIncl_natAdd, refine_id_incl]
      simp only [refine_id_refinement, id_eq, Category.id_comp, eqToHom_trans]
      rfl
  map_comp {y₁ y₂ y₃} g₁ g₂ := by
    refine ChainRefine.ext (appendRefinement_id_comp g₁.refinement g₂.refinement)
      (incl_heq_of_index_eq (appendRefinement_id_comp g₁.refinement g₂.refinement) ?_)
    intro i
    -- The helper's goal: `(appendLeftMap pre (g₁≫g₂)).incl i = (compose).incl i ≫ eqToHom _`.
    -- `(compose).incl i = (appendLeftMap pre g₁).incl i ≫ (appendLeftMap pre g₂).incl (f.ref i)`
    -- (defeq, `refine_comp_incl`); index-split and reduce each side branch-wise.
    change (pre.appendLeftMap (g₁ ≫ g₂)).incl i
        = ((pre.appendLeftMap g₁).incl i
            ≫ (pre.appendLeftMap g₂).incl (appendRefinement id g₁.refinement i)) ≫ eqToHom _
    rw [appendLeftMap_incl, appendLeftMap_incl, appendLeftMap_incl]
    obtain ⟨j, rfl⟩ : ∃ j, i = Fin.cast (List.length_append ..).symm j :=
      ⟨Fin.cast (List.length_append ..) i, by apply Fin.ext; simp⟩
    induction j using Fin.addCases with
    | left ia =>
      -- prefix block: LHS `append (𝟙 pre) (g₁≫g₂)` is `𝟙`-conjugated; RHS composes two
      -- `𝟙`-conjugated appends; both collapse to a single `eqToHom`.
      rw [appendIncl_castAdd (𝟙 pre) (g₁ ≫ g₂) ia, refine_id_incl,
        appendIncl_index_eq (𝟙 pre) g₂ (i := appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ia.castAdd y₁.cubes.length)))
          (i' := Fin.cast (List.length_append ..).symm (ia.castAdd y₂.cubes.length)) (by
            apply Fin.ext; rw [appendRefinement_val_left _ _ _ (by simp)]; simp),
        appendIncl_castAdd (𝟙 pre) g₁ ia, refine_id_incl,
        appendIncl_castAdd (𝟙 pre) g₂ ia, refine_id_incl]
      simp only [refine_id_refinement, id_eq, Category.id_comp]
      refine hom_eq_of_heq_id ?_ ?_ <;>
        · repeat first
            | refine eqToHom_comp_heq' _ _ _ ?_
            | refine comp_eqToHom_heq' _ _ _ ?_
            | refine (heq_of_eq (Category.assoc _ _ _)).trans ?_
          refine (eqToHom_heq_id_dom _ _ _).trans ?_
          rw [get_append_castAdd ia]
    | right ib =>
      -- Tail block.  Both sides are `≍ g₁.incl ib ≫ g₂.incl (g₁.refinement ib)`:
      --   LHS = `appendIncl (𝟙 pre) (g₁≫g₂) (natAdd ib) ≍ (g₁≫g₂).incl ib` (the frame strips);
      --   RHS = `(appendIncl g₁ (natAdd ib) ≫ appendIncl g₂ (natAdd (g₁.ref ib))) ≫ eqToHom`,
      --   each `appendIncl` stripping to its `incl` (`appendIncl_natAdd_heq`), the `eqToHom`
      --   stripping, and the two `incl`s glued by `heq_comp` (object eqs via `append_get_natAdd`).
      apply eq_of_heq
      refine (appendIncl_natAdd_heq pre (g₁ ≫ g₂) ib).trans ?_
      rw [refine_comp_incl]
      refine HEq.symm (comp_eqToHom_heq' _ _ (g₁.incl ib ≫ g₂.incl (g₁.refinement ib)) ?_)
      -- the second factor's index is
      -- `appendRefinement id g₁.ref (natAdd ib) = natAdd (g₁.ref ib)`; move it across
      -- (`appendIncl_index_eq`, frames strip) then reduce by `appendIncl_natAdd_heq`.
      have hidx : (appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length)))
          = Fin.cast (List.length_append ..).symm
              ((g₁.refinement ib).natAdd pre.cubes.length) := by
        apply Fin.ext; rw [appendRefinement_val_right _ _ _ (by simp) (by simp)]; simp
      have hg₂ : appendIncl (𝟙 pre) g₂ (appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length)))
          ≍ g₂.incl (g₁.refinement ib) := by
        rw [appendIncl_index_eq (𝟙 pre) g₂ hidx]
        exact eqToHom_comp_heq' _ _ (g₂.incl (g₁.refinement ib))
          (comp_eqToHom_heq' _ _ (g₂.incl (g₁.refinement ib))
            (appendIncl_natAdd_heq pre g₂ (g₁.refinement ib)))
      -- the three object equalities (domain/middle/codomain), via `get_append_natAdd` and
      -- `append_get_natAdd`; stated up to the defeq `pre.append y = pre.cubes ++ y.cubes`.
      have hdom : ((pre.append y₁).cubes.get
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length))).1
          = (y₁.cubes.get ib).1 := congrArg (·.1) (get_append_natAdd (l := pre.cubes) ib)
      have hmid : ((pre.append y₂).cubes.get (appendRefinement id g₁.refinement
            (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length)))).1
          = (y₂.cubes.get (g₁.refinement ib)).1 :=
        append_get_natAdd (x := pre.cubes) g₁.refinement ib
      have hcod : ((pre.append y₃).cubes.get (appendRefinement id g₂.refinement
            (appendRefinement id g₁.refinement
              (Fin.cast (List.length_append ..).symm (ib.natAdd pre.cubes.length))))).1
          = (y₃.cubes.get (g₂.refinement (g₁.refinement ib))).1 := by
        rw [hidx]; exact append_get_natAdd (x := pre.cubes) g₂.refinement (g₁.refinement ib)
      exact heq_comp (congrArg (fun n : ℕ+ => Box.ob (n : ℕ)) hdom)
        (congrArg (fun n : ℕ+ => Box.ob (n : ℕ)) hmid)
        (congrArg (fun n : ℕ+ => Box.ob (n : ℕ)) hcod) (appendIncl_natAdd_heq pre g₁ ib) hg₂

end CubeChain

/-! ## 8.5. The total multi-block sweep `sweepR` (list-indexed staircase)

The junction-bridge staircase lifts blocks `k → 1` through apexes/bridges.  The **total** `sweepR`
runs that staircase for an arbitrary source chain, indexed by the block list.  To keep every
staircase object inside the *global* fence `RefineObj K.init K.final` we package each block with
*all* of its endpoint data into a `BlockRec`, and recurse on the **suffix** of blocks while
carrying a fixed left prefix `pre : RefineObj K.init mL` (the already-fixed left faces) and the
vertical edge over the split junction.

The recursion `sweepTail` produces, for a fixed prefix `pre` ending at the split junction's
*left* leg-image `mL` and a list of remaining blocks (a `c.src`-chain from the split junction to
`final`):

    pre.append (leftPush blocks)  ⟶  pre.append (edge.append (rightPush blocks))

i.e. it sweeps the *tail* across the interval, leaving the prefix on the left leg and inserting
the split-junction vertical `edge : mL → mR` to bridge the level gap.  At the top level the
prefix is empty (`pre = ε·`, mL = init) and the edge is the *initial* self-loop, which collapses,
so the result is the genuine `ℓ·a ⟶ r·a`.  Each recursion step lifts the *first* remaining block
through its prism cospan, exactly mirroring §8's interior arrows. -/

namespace CylMapR

open CubeChain

/-- A **block record**: one block of the source chain together with every endpoint condition the
staircase needs — the block cell `cell`, its left/right leg-image junction vertices `uL/vL`
(`false`-face) and `uR/vR` (`true`-face), the initial/final source junction 0-cells `s₀/s₁`
(`vertex₀/₁ cell`), and the leg-face / prism / edge endpoint equalities.  Bundling these makes the
recursion's transport bookkeeping a matter of *projecting* fields rather than re-deriving vertex
equalities. -/
structure BlockRec (c : CylMapR K) where
  /-- The block dimension. -/
  m : ℕ+
  /-- The source cube cell of this block. -/
  cell : c.src.toPsh.cells (m : ℕ)
  /-- Left leg-image of the block's *initial* junction (`vertex₀` of the `false`-face). -/
  uL : K.toPsh.cells 0
  /-- Left leg-image of the block's *final* junction (`vertex₁` of the `false`-face). -/
  vL : K.toPsh.cells 0
  /-- Right leg-image of the block's *initial* junction. -/
  uR : K.toPsh.cells 0
  /-- Right leg-image of the block's *final* junction. -/
  vR : K.toPsh.cells 0
  /-- The block's initial source junction 0-cell. -/
  s₀ : c.src.toPsh.cells 0
  /-- The block's final source junction 0-cell. -/
  s₁ : c.src.toPsh.cells 0
  hs₀ : c.src.toPsh.vertex₀ cell = s₀
  hs₁ : c.src.toPsh.vertex₁ cell = s₁
  /-- `lc`: left face initial vertex. -/
  hiL : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = uL
  /-- `lc`: left face final vertex. -/
  hfL : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh)) = vL
  /-- `rc`: right face initial vertex. -/
  hiR : K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = uR
  /-- `rc`: right face final vertex. -/
  hfR : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh)) = vR

namespace BlockRec

variable {c : CylMapR K}

/-- The `false`-leg face of a block, as a single-cube chain `uL → vL`. -/
noncomputable def lc (B : BlockRec c) : RefineObj (K := K) B.uL B.vL :=
  refineEndG false (c.blockQ B.cell) B.hiL B.hfL

/-- The `true`-leg face of a block, as a single-cube chain `uR → vR`. -/
noncomputable def rc (B : BlockRec c) : RefineObj (K := K) B.uR B.vR :=
  refineEndG true (c.blockQ B.cell) B.hiR B.hfR

/-- The prism cube of a block, as a single-cube chain `uL → vR`. -/
noncomputable def R (B : BlockRec c) : RefineObj (K := K) B.uL B.vR :=
  refinePrismG (c.blockQ B.cell) B.hiL B.hfR

end BlockRec

end CylMapR

/-! ## 8.6. The total list-indexed sweep `sweepTail`/`sweepR`

The junction-bridge staircase is run for an arbitrary block list `bs : List (BlockRec c)` in a
**prefix-carrying** recursion `sweepTail`, living in the *sub-fence*
`RefineObj mL K.final` (from the split junction's left leg-image `mL` to `final`).  For a non-empty
list it produces

    leftPush mL bs  ⟶  edge.append (rightPush mR bs)

where `leftPush`/`rightPush` are the right-fold appends of the blocks' `lc`/`rc` faces (starting at
`mL`/`mR`), and `edge : mL → mR` is the vertical junction edge over the split junction's source
0-cell.  At the cons step the *first* block is lifted through its prism cospan (the two §8 bridge
cofaces, whiskered by an `rc`-suffix), and the tail is recursed and re-whiskered by the
`lc`-prefix via `FreeGroupoid.map (RefineObj.appendLeft _)` (`of_comp_map` makes this a per-arrow
whisker).  Every object identity in the recursion is `RefineObj.ext''` (cube lists agree by
`List.append_assoc` / singleton `++`), promoted to an `eqToHom`. -/

namespace CylMapR

open CubeChain

variable {c : CylMapR K}

/-- **Block-list consistency**: the blocks `bs` form a genuine source chain starting at the split
junction whose two leg-images are `mL` (left) and `mR` (right), and whose final block closes at
`K.final` on both legs.  Recursively: the head block `B` has `B.uL = mL`, `B.uR = mR`; the next
block's initial junction equals `B`'s final (`B.s₁ = next.s₀`) and its leg-images match
(`B.vL = next.uL`, `B.vR = next.uR`); the last block has `B.vL = B.vR = K.final`. -/
def BlockConsec : (bs : List (BlockRec c)) → (mL mR : K.toPsh.cells 0) → Prop
  | [], mL, mR => mL = K.final ∧ mR = K.final
  | B :: rest, mL, mR =>
      B.uL = mL ∧ B.uR = mR ∧
      -- the vertical edge over the head's initial junction `s₀` runs `mL → mR`
      K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mL ∧
      K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mR ∧
      (match rest with
       | [] => B.vL = K.final ∧ B.vR = K.final
       | B' :: _ => B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀) ∧
      BlockConsec rest B.vL B.vR

/-- The right-fold of the blocks' `false`-leg (`lc`) faces into one chain `mL → K.final`.  The
start vertex is kept *explicit* (as `mL`, tied to `B.uL` by consistency) so the cube list comes
out free of `▸`-transport — `leftPush_cubes` reads it off as a plain `List.map`. -/
noncomputable def leftPush (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) : RefineObj (K := K) mL K.final where
  cubes := bs.map (fun B => ⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint false).app K.toPsh)⟩)
  isChain := by
    induction bs generalizing mL mR with
    | nil => obtain ⟨rfl, _⟩ := h; rfl
    | cons B rest ih =>
        obtain ⟨huL, _, _, _, _, hrec⟩ := h
        refine ⟨by rw [B.hiL, huL], ?_⟩
        have hlink : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ B.cell ≫ (endpoint false).app K.toPsh))
            = B.vL := B.hfL
        rw [hlink]; exact ih B.vL B.vR hrec

/-- The right-fold of the blocks' `true`-leg (`rc`) faces into one chain `mR → K.final`. -/
noncomputable def rightPush (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) : RefineObj (K := K) mR K.final where
  cubes := bs.map (fun B => ⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint true).app K.toPsh)⟩)
  isChain := by
    induction bs generalizing mL mR with
    | nil => obtain ⟨_, rfl⟩ := h; rfl
    | cons B rest ih =>
        obtain ⟨_, huR, _, _, _, hrec⟩ := h
        refine ⟨by rw [B.hiR, huR], ?_⟩
        have hlink : K.toPsh.vertex₁ (yonedaEquiv (c.blockQ B.cell ≫ (endpoint true).app K.toPsh))
            = B.vR := B.hfR
        rw [hlink]; exact ih B.vL B.vR hrec

/-- The cubes of `leftPush` are exactly the `List.map` of the blocks' `lc` cells (definitional). -/
@[simp] theorem leftPush_cubes (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) :
    (leftPush bs mL mR h).cubes
      = bs.map (fun B => (⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint false).app K.toPsh)⟩ :
          Σ n : ℕ+, K.toPsh.cells (n : ℕ))) := rfl

/-- The cubes of `rightPush` are exactly the `List.map` of the blocks' `rc` cells (definitional). -/
@[simp] theorem rightPush_cubes (bs : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec bs mL mR) :
    (rightPush bs mL mR h).cubes
      = bs.map (fun B => (⟨B.m, yonedaEquiv (c.blockQ B.cell ≫ (endpoint true).app K.toPsh)⟩ :
          Σ n : ℕ+, K.toPsh.cells (n : ℕ))) := rfl

/-! ### The cons decompositions and the staircase target

`leftPush (B::rest)` splits as `B.lc.append (leftPush rest)` and `rightPush (B::rest)` as
`B.rc.append (rightPush rest)`, both as on-the-nose `RefineObj` equalities (`ext''`, the cube lists
agree by `List.map_cons`).  These are the recursion's object identities. -/

/-- `leftPush (B::rest) = B.lc.append (leftPush rest)` (the head `lc` prepended). -/
theorem leftPush_cons (B : BlockRec c) (rest : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec (B :: rest) mL mR) (huL : B.uL = mL) (hrec : BlockConsec rest B.vL B.vR) :
    leftPush (B :: rest) mL mR h
      = huL ▸ (B.lc.append (leftPush rest B.vL B.vR hrec)) := by
  apply RefineObj.ext''
  cases huL
  simp only [leftPush_cubes, List.map_cons, RefineObj.append_cubes, BlockRec.lc, refineEndG,
    leftPush_cubes, List.singleton_append]

/-- `rightPush (B::rest) = B.rc.append (rightPush rest)` (the head `rc` prepended). -/
theorem rightPush_cons (B : BlockRec c) (rest : List (BlockRec c)) (mL mR : K.toPsh.cells 0)
    (h : BlockConsec (B :: rest) mL mR) (huR : B.uR = mR) (hrec : BlockConsec rest B.vL B.vR) :
    rightPush (B :: rest) mL mR h
      = huR ▸ (B.rc.append (rightPush rest B.vL B.vR hrec)) := by
  apply RefineObj.ext''
  cases huR
  simp only [rightPush_cubes, List.map_cons, RefineObj.append_cubes, BlockRec.rc, refineEndG,
    rightPush_cubes, List.singleton_append]

/-- The **vertical junction edge over a block's initial junction**, as a chain `mL → mR`, when
its endpoints are the split junction's two leg-images (`BlockConsec`'s edge fields). -/
noncomputable def BlockRec.edge0 (B : BlockRec c) {mL mR : K.toPsh.cells 0}
    (hEi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mL)
    (hEf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = mR) :
    RefineObj (K := K) mL mR :=
  refineEdgeG c B.s₀ hEi hEf

/-- **The staircase target of `sweepTail`.**  For a non-empty list it is the split-junction
vertical edge `mL → mR` followed by the right-leg push of the blocks (`mR → final`), i.e.
`edge.append (rightPush bs)`; for the empty list it is just `rightPush []` (the empty chain at
`final`).  This is the right-hand object of the sub-fence homotopy. -/
noncomputable def tailTarget : (bs : List (BlockRec c)) → (mL mR : K.toPsh.cells 0) →
    BlockConsec bs mL mR → RefineObj (K := K) mL K.final
  | [], mL, _, h => ⟨[], by obtain ⟨rfl, _⟩ := h; rfl⟩
  | B :: rest, mL, mR, h =>
      (B.edge0 h.2.2.1 h.2.2.2.1).append (rightPush (B :: rest) mL mR h)

/-! ### The apex and the two arrows into it (per-block prism lift, list-generic)

For the head block `B` lifted over its prism cube, the apex is `B.R.append (rightPush rest)` (the
prism cube of `B`, with the right-leg push of the remaining blocks suffixed).  The two staircase
arrows into the apex are the §8 bridge cofaces whiskered by the fixed `rightPush rest` suffix
(`ChainRefine.append · (𝟙 _)`):

* the **top/bridge arrow** `tailTarget (B::rest) → apex`, from the `[e,rc]` bridge
  `refineBridgeCoface` over `B`'s *initial* junction `s₀`;
* the **bottom/mirror arrow** `B.lc.append (tailTarget rest) → apex`, from the `[lc,e]` mirror
  bridge `refineBridgeCofaceR` over `B`'s *final* junction `s₁` (when `rest ≠ []`) or the single
  bottom coface `refineCofaceG false` (when `rest = []`, `B` the last block — final edge absent). -/

/-- The apex object for lifting the head block `B`: its prism cube suffixed by the remaining
blocks' right-leg push. -/
noncomputable def apexHead (B : BlockRec c) (rest : List (BlockRec c))
    {mL mR : K.toPsh.cells 0} (h : BlockConsec (B :: rest) mL mR) :
    RefineObj (K := K) mL K.final :=
  h.1 ▸ B.R.append (rightPush rest B.vL B.vR h.2.2.2.2.2)

/-- **The top/bridge arrow into the apex** (substituted form `mL = B.uL`, `mR = B.uR`): the
`[e,rc]` bridge coface over `B`'s *initial* junction `s₀`, whiskered by the `rightPush rest`
suffix.  Source `refineBridgeSrc c B.cell B.s₀ ≫ suffix`, target `B.R ≫ suffix = apex`. -/
noncomputable def topArrow (B : BlockRec c) (rest : List (BlockRec c))
    (hEi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uL)
    (hEf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uR)
    (hrec : BlockConsec rest B.vL B.vR) :
    (refineBridgeSrc c B.cell B.s₀ hEi (B.hiR.trans hEf.symm) B.hfR).append
        (rightPush rest B.vL B.vR hrec)
      ⟶ B.R.append (rightPush rest B.vL B.vR hrec) :=
  ChainRefine.append
    (refineBridgeCoface c B.cell B.s₀ B.hs₀ hEi (B.hiR.trans hEf.symm) B.hfR B.hiL B.hfR)
    (𝟙 (rightPush rest B.vL B.vR hrec))

/-- The edge-over-`B.s₁` initial-vertex equality, extracted from the *next* block's
`BlockConsec` edge field (over `B'.s₀ = B.s₁`).  Only `rest = B' :: _`. -/
theorem next_edge_init (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₁))) = B.vL := by
  rw [hmatch.2.2]; exact hrec.2.2.1

/-- The edge-over-`B.s₁` final-vertex equality (dual of `next_edge_init`). -/
theorem next_edge_final (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₁))) = B.vR := by
  rw [hmatch.2.2]; exact hrec.2.2.2.1

/-- **The bottom/mirror arrow into the apex** (interior case `rest = B' :: tl`): the `[lc,e]`
mirror-bridge coface over `B`'s *final* junction `s₁`, whiskered by the `rightPush rest` suffix.
Source `refineBridgeSrcR c B.cell B.s₁ ≫ suffix`, target `B.R ≫ suffix = apex`. -/
noncomputable def botArrowCons (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    (refineBridgeSrcR c B.cell B.s₁ B.hiL
        ((next_edge_init B B' tl hmatch hrec).trans B.hfL.symm)
        (next_edge_final B B' tl hmatch hrec)).append (rightPush (B' :: tl) B.vL B.vR hrec)
      ⟶ B.R.append (rightPush (B' :: tl) B.vL B.vR hrec) :=
  ChainRefine.append
    (refineBridgeCofaceR c B.cell B.s₁ B.hs₁ B.hiL
      ((next_edge_init B B' tl hmatch hrec).trans B.hfL.symm)
      (next_edge_final B B' tl hmatch hrec) B.hiL B.hfR)
    (𝟙 (rightPush (B' :: tl) B.vL B.vR hrec))

/-- **The bottom arrow into the apex** (terminal case `rest = []`, `B` the last block): the single
bottom coface `B.lc → B.R` (the final junction's edge is absent).  Here `B.vL = B.vR = K.final`,
so `B.lc` and `B.R` both close at `final`; the arrow is `refineCofaceG false`. -/
noncomputable def botArrowNil (B : BlockRec c) (hvL : B.vL = K.final) (hvR : B.vR = K.final) :
    (refineEndG false (c.blockQ B.cell) B.hiL (B.hfL.trans (hvL.trans hvR.symm)))
      ⟶ (refinePrismG (c.blockQ B.cell) B.hiL B.hfR) :=
  refineCofaceG false (c.blockQ B.cell) B.hiL (B.hfL.trans (hvL.trans hvR.symm)) B.hiL B.hfR

/-! ### The cons-step head sweep `headSweep`

Given the head block `B`, the apex `B.R.append (rightPush rest)`, and the recursive tail homotopy
`tail : leftPush rest ⟶ tailTarget rest`, produce the head's contribution to the staircase:

    leftPush (B::rest)  ⟶  tailTarget (B::rest)

namely `eqToHom ≫ (lift of tail by appendLeft B.lc) ≫ eqToHom ≫ of(botArrow) ≫ inv(of(topArrow)) ≫
eqToHom`.  The object `eqToHom`s are `RefineObj.ext''` cube-list identities (append-assoc / the two
bridge presentations / the `leftPush`/`rightPush` cons splits). -/

/-- The two object-bridge equalities the cons step needs, branch `rest = B' :: tl`. -/
theorem midEq_cons (B B' : BlockRec c) (tl : List (BlockRec c))
    (hmatch : B.vL = B'.uL ∧ B.vR = B'.uR ∧ B.s₁ = B'.s₀)
    (hrec : BlockConsec (B' :: tl) B.vL B.vR) :
    B.lc.append (tailTarget (B' :: tl) B.vL B.vR hrec)
      = (refineBridgeSrcR c B.cell B.s₁ B.hiL
          ((next_edge_init B B' tl hmatch hrec).trans B.hfL.symm)
          (next_edge_final B B' tl hmatch hrec)).append (rightPush (B' :: tl) B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [RefineObj.append_cubes, tailTarget, BlockRec.lc, BlockRec.edge0, refineEndG,
    refineEdgeG, refineBridgeSrcR, rightPush_cubes, List.cons_append, List.nil_append]
  rw [hmatch.2.2]

/-- The top-source object bridge (substituted form `mL = B.uL`, `mR = B.uR`): `tailTarget (B::rest)`
equals the `[e,rc]` bridge over `B.s₀` suffixed by `rightPush rest`.  Uses `rightPush_cons` + the
bridge presentation (`ext''`). -/
theorem tgtEq_cons (B : BlockRec c) (rest : List (BlockRec c))
    (h : BlockConsec (B :: rest) B.uL B.uR)
    (hEi : K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uL)
    (hEf : K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ B.s₀))) = B.uR)
    (hrec : BlockConsec rest B.vL B.vR) :
    tailTarget (B :: rest) B.uL B.uR h
      = (refineBridgeSrc c B.cell B.s₀ hEi (B.hiR.trans hEf.symm) B.hfR).append
          (rightPush rest B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [tailTarget, BlockRec.edge0, refineEdgeG, refineBridgeSrc,
    RefineObj.append_cubes, rightPush_cubes, List.map_cons, List.cons_append, List.nil_append]

/-- The source object bridge: `leftPush (B::rest)` (substituted) equals `B.lc.append (leftPush
rest)`.  Specialisation of `leftPush_cons` with `huL = rfl`. -/
theorem srcEq_cons (B : BlockRec c) (rest : List (BlockRec c))
    (h : BlockConsec (B :: rest) B.uL B.uR) (hrec : BlockConsec rest B.vL B.vR) :
    leftPush (B :: rest) B.uL B.uR h = B.lc.append (leftPush rest B.vL B.vR hrec) :=
  leftPush_cons B rest B.uL B.uR h rfl hrec

/-- The bottom-source object bridge, branch `rest = []`: `B.lc.append (tailTarget [])` equals the
`false`-face single-cube chain suffixed by the empty `rightPush`. -/
theorem midEq_nil (B : BlockRec c) (hvL : B.vL = K.final) (hvR : B.vR = K.final)
    (hrec : BlockConsec ([] : List (BlockRec c)) B.vL B.vR) :
    B.lc.append (tailTarget [] B.vL B.vR hrec)
      = (refineEndG false (c.blockQ B.cell) B.hiL (B.hfL.trans (hvL.trans hvR.symm))).append
          (rightPush [] B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [RefineObj.append_cubes, tailTarget, BlockRec.lc, refineEndG, rightPush_cubes,
    List.map_nil, List.append_nil]

/-! ### The total tail sweep `sweepTail`

By structural recursion on `bs`.  Cons (`B :: rest`): substitute `mL := B.uL`, `mR := B.uR`, lift
`sweepTail rest` by `FreeGroupoid.map (RefineObj.appendLeft B.lc)`, then splice the head block's
prism cospan via the mirror (`botArrow*`) and top (`topArrow`) arrows.  Object identities are the
`eqToHom`s of `srcEq_cons`/`midEq_*`/`tgtEq_cons` (FreeGroupoid objects are `RefineObj`s, so a
`RefineObj` equality is directly an `eqToHom`). -/
noncomputable def sweepTail : (bs : List (BlockRec c)) → (mL mR : K.toPsh.cells 0) →
    (h : BlockConsec bs mL mR) →
    (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (leftPush bs mL mR h)
      ⟶ (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (tailTarget bs mL mR h)
  | [], mL, mR, h =>
      eqToHom (congrArg _ (RefineObj.ext'' (by
        simp only [leftPush_cubes, tailTarget, List.map_nil])))
  | B :: rest, mL, mR, h => by
      obtain ⟨huL, huR, hEi, hEf, hmatch, hrec⟩ := h
      subst huL; subst huR
      have hcons : BlockConsec (B :: rest) B.uL B.uR := ⟨rfl, rfl, hEi, hEf, hmatch, hrec⟩
      -- the recursive tail homotopy, lifted by the `lc`-prefix whiskering.  The codomain
      -- `(map (appendLeft B.lc)).obj (tailTarget rest) = B.lc.append (tailTarget rest)` by
      -- `of_comp_map` (rfl); the type ascription forces that defeq at definition time.
      let lifted : (FreeGroupoid.of _).obj (B.lc.append (leftPush rest B.vL B.vR hrec))
          ⟶ (FreeGroupoid.of _).obj (B.lc.append (tailTarget rest B.vL B.vR hrec)) :=
        (FreeGroupoid.map (RefineObj.appendLeft (b := K.final) B.lc)).map
          (sweepTail rest B.vL B.vR hrec)
      -- the top arrow into the apex (always the `[e,rc]` bridge over `s₀`), inverted
      let top := (FreeGroupoid.of _).map (topArrow B rest hEi hEf hrec)
      refine eqToHom (congrArg (FreeGroupoid.of _).obj (srcEq_cons B rest hcons hrec))
        ≫ lifted
        ≫ ?mid ≫ Groupoid.inv top
        ≫ eqToHom (congrArg (FreeGroupoid.of _).obj (tgtEq_cons B rest hcons hEi hEf hrec).symm)
      -- the mirror arrow `B.lc.append (tailTarget rest) → apex`, split on `rest`:
      match rest, hmatch, hrec with
      | [], hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_nil B hmatch.1 hmatch.2 hrec))
            ≫ (FreeGroupoid.of _).map
              (ChainRefine.append (botArrowNil B hmatch.1 hmatch.2)
                (𝟙 (rightPush [] B.vL B.vR hrec)))
      | B' :: tl, hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_cons B B' tl hmatch hrec))
            ≫ (FreeGroupoid.of _).map (botArrowCons B B' tl hmatch hrec)

/-! ### Decomposing a source chain into `BlockRec`s

A single cube `⟨m, cell⟩` of the source chain `a` gives a `BlockRec` whose four leg-image junction
vertices are *defined* to be the `vertex₀/₁` of the two leg-faces, so all four leg-vertex equalities
are `rfl`.  The list of all cubes of `a` gives `blocksOf a`, and the chain's link/endpoint data
makes it `BlockConsec` over the basepoints. -/

/-- The `BlockRec` of a single source cube `⟨m, cell⟩` (m : ℕ+), with every endpoint *defined* as
the corresponding vertex (so all field equalities are `rfl`). -/
noncomputable def BlockRec.ofCube (c : CylMapR K) (m : ℕ+) (cell : c.src.toPsh.cells (m : ℕ)) :
    BlockRec c where
  m := m
  cell := cell
  uL := K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
  vL := K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
  uR := K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
  vR := K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
  s₀ := c.src.toPsh.vertex₀ cell
  s₁ := c.src.toPsh.vertex₁ cell
  hs₀ := rfl
  hs₁ := rfl
  hiL := rfl
  hfL := rfl
  hiR := rfl
  hfR := rfl

/-- The **block-list decomposition** of a source chain `a`: each cube becomes a `BlockRec.ofCube`.
This is the list the total sweep is indexed by; `leftPush`/`rightPush` of it recover the two
leg-pushforwards of `a` (`blockQ_face` cube-wise), and (given `BlockConsec`) `sweepTail` sweeps it.
-/
noncomputable def blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) : List (BlockRec c) :=
  a.cubes.map (fun cb => BlockRec.ofCube c cb.1 cb.2)

/-- The `false`-leg block-face vertices are the *left leg* applied to the source cube's vertices:
`vertex₀(blockQ cell ≫ e_false) = leftLeg.app (vertex₀ cell)` (via `blockQ_face` + naturality).  The
`uL` of `BlockRec.ofCube` therefore equals `leftLeg.app (vertex₀ cell)`. -/
theorem ofCube_uL_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
      = c.leftLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₀ cell) :=
  (congrArg K.toPsh.vertex₀ (blockQ_face c cell false)).trans
    (PrecubicalSet.map_vertex₀ c.leftLeg.hom cell).symm

/-- `vertex₁(blockQ cell ≫ e_false) = leftLeg.app (vertex₁ cell)`. -/
theorem ofCube_vL_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
      = c.leftLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₁ cell) :=
  (congrArg K.toPsh.vertex₁ (blockQ_face c cell false)).trans
    (PrecubicalSet.map_vertex₁ c.leftLeg.hom cell).symm

/-- `vertex₀(blockQ cell ≫ e_true) = rightLeg.app (vertex₀ cell)`. -/
theorem ofCube_uR_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
      = c.rightLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₀ cell) :=
  (congrArg K.toPsh.vertex₀ (blockQ_face c cell true)).trans
    (PrecubicalSet.map_vertex₀ c.rightLeg.hom cell).symm

/-- `vertex₁(blockQ cell ≫ e_true) = rightLeg.app (vertex₁ cell)`. -/
theorem ofCube_vR_eq (c : CylMapR K) {m : ℕ} (cell : c.src.toPsh.cells m) :
    K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
      = c.rightLeg.hom.app (op (Box.ob 0)) (c.src.toPsh.vertex₁ cell) :=
  (congrArg K.toPsh.vertex₁ (blockQ_face c cell true)).trans
    (PrecubicalSet.map_vertex₁ c.rightLeg.hom cell).symm

/-- `initVertexMap 0 = 𝟙 (Box.ob 0)`: the unique `0`-cell of `□⁰` is its top cell, so the
constant-vertex `canonicalMap` is `canonicalMap (topCell 0) = 𝟙`. -/
theorem initVertexMap_zero : PrecubicalSet.initVertexMap 0 = 𝟙 (Box.ob 0) := by
  rw [PrecubicalSet.initVertexMap,
    show StdCube.constVertex 0 false = StdCube.topCell 0 from
      Subtype.ext (funext (fun i => i.elim0))]
  exact StdCube.canonicalMap_topCell 0

/-- `finalVertexMap 0 = 𝟙 (Box.ob 0)` (dual of `initVertexMap_zero`). -/
theorem finalVertexMap_zero : PrecubicalSet.finalVertexMap 0 = 𝟙 (Box.ob 0) := by
  rw [PrecubicalSet.finalVertexMap,
    show StdCube.constVertex 0 true = StdCube.topCell 0 from
      Subtype.ext (funext (fun i => i.elim0))]
  exact StdCube.canonicalMap_topCell 0

/-- `vertex₀` of a 0-cell is itself (`initVertexMap 0 = 𝟙`). -/
theorem vertex₀_zero_cell {X : PrecubicalSet} (v : X.cells 0) : X.vertex₀ v = v := by
  rw [PrecubicalSet.vertex₀, initVertexMap_zero, op_id, X.map_id_apply]

/-- `vertex₁` of a 0-cell is itself. -/
theorem vertex₁_zero_cell {X : PrecubicalSet} (v : X.cells 0) : X.vertex₁ v = v := by
  rw [PrecubicalSet.vertex₁, finalVertexMap_zero, op_id, X.map_id_apply]

/-- The vertical edge over a source 0-cell `v` runs `leftLeg.app v → rightLeg.app v`
(`prism_vertex₀/₁` + the leg-face reconciliation; `v` a 0-cell so its own `vertex₀/₁` is itself). -/
theorem edge_over_vertex_init (c : CylMapR K) (v : c.src.toPsh.cells 0) :
    K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ v)))
      = c.leftLeg.hom.app (op (Box.ob 0)) v :=
  (prism_vertex₀ (c.blockQ v)).trans
    ((ofCube_uL_eq c v).trans (congrArg _ (vertex₀_zero_cell v)))

theorem edge_over_vertex_final (c : CylMapR K) (v : c.src.toPsh.cells 0) :
    K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism (c.blockQ v)))
      = c.rightLeg.hom.app (op (Box.ob 0)) v :=
  (prism_vertex₁ (c.blockQ v)).trans
    ((ofCube_vR_eq c v).trans (congrArg _ (vertex₁_zero_cell v)))

/-- **The block-list of a source chain is `BlockConsec`.**  Over the leg-images of the chain's
start vertex `start`, the `ofCube` blocks of a cube list `cs` forming a chain `start → final`
satisfy `BlockConsec` — every link/edge field is the chain link `vertex₁ cube = vertex₀ next`
pushed through the leg (`ofCube_*_eq` + `map_vertex*_psh` + `edge_over_vertex_*`). -/
theorem blockConsec_blocksOf_aux (c : CylMapR K) :
    ∀ (cs : List (Σ n : ℕ+, c.src.toPsh.cells (n : ℕ))) (start : c.src.toPsh.cells 0)
      (_hchain : IsCubeChain start cs c.src.final),
      BlockConsec (cs.map (fun cb => BlockRec.ofCube c cb.1 cb.2))
        (c.leftLeg.hom.app (op (Box.ob 0)) start) (c.rightLeg.hom.app (op (Box.ob 0)) start)
  | [], start, hchain => by
      -- empty chain: `start = final`, and `leg.app final = K.basepoint`.
      obtain rfl : start = c.src.final := hchain
      exact ⟨c.leftLeg.app_final, c.rightLeg.app_final⟩
  | ⟨m, cell⟩ :: rest, start, hchain => by
      obtain ⟨hsrc, hrest⟩ := hchain
      -- `hsrc : vertex₀ cell = start`, `hrest : IsCubeChain (vertex₁ cell) rest final`.
      have hIH := blockConsec_blocksOf_aux c rest (c.src.toPsh.vertex₁ cell) hrest
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- B.uL = leftLeg.app start
        rw [show (BlockRec.ofCube c m cell).uL
              = K.toPsh.vertex₀ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint false).app K.toPsh)) from rfl,
          ofCube_uL_eq, hsrc]
      · rw [show (BlockRec.ofCube c m cell).uR
              = K.toPsh.vertex₀ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint true).app K.toPsh)) from rfl,
          ofCube_uR_eq, hsrc]
      · -- edge over s₀ = vertex₀ cell, init = leftLeg.app start
        rw [show (BlockRec.ofCube c m cell).s₀ = c.src.toPsh.vertex₀ cell from rfl,
          edge_over_vertex_init, hsrc]
      · rw [show (BlockRec.ofCube c m cell).s₀ = c.src.toPsh.vertex₀ cell from rfl,
          edge_over_vertex_final, hsrc]
      · -- the link match, depending on `rest`
        cases rest with
        | nil =>
            refine ⟨?_, ?_⟩
            · -- B.vL = K.final : leftLeg.app (vertex₁ cell), and vertex₁ cell = final
              rw [show (BlockRec.ofCube c m cell).vL
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
                  from rfl, ofCube_vL_eq, (hrest : c.src.toPsh.vertex₁ cell = c.src.final),
                c.leftLeg.app_final]
            · rw [show (BlockRec.ofCube c m cell).vR
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
                  from rfl, ofCube_vR_eq, (hrest : c.src.toPsh.vertex₁ cell = c.src.final),
                c.rightLeg.app_final]
        | cons hd tl =>
            obtain ⟨n', cell'⟩ := hd
            obtain ⟨hlink, _⟩ := hrest
            -- hlink : vertex₀ cell' = vertex₁ cell
            refine ⟨?_, ?_, ?_⟩
            · rw [show (BlockRec.ofCube c m cell).vL
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint false).app K.toPsh))
                  from rfl,
                show (BlockRec.ofCube c n' cell').uL
                    = K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell' ≫ (endpoint false).app K.toPsh))
                  from rfl, ofCube_vL_eq, ofCube_uL_eq, hlink]
            · rw [show (BlockRec.ofCube c m cell).vR
                    = K.toPsh.vertex₁ (yonedaEquiv (c.blockQ cell ≫ (endpoint true).app K.toPsh))
                  from rfl,
                show (BlockRec.ofCube c n' cell').uR
                    = K.toPsh.vertex₀ (yonedaEquiv (c.blockQ cell' ≫ (endpoint true).app K.toPsh))
                  from rfl, ofCube_vR_eq, ofCube_uR_eq, hlink]
            · -- B.s₁ = B'.s₀ : vertex₁ cell = vertex₀ cell'
              change c.src.toPsh.vertex₁ cell = c.src.toPsh.vertex₀ cell'
              exact hlink.symm
      · -- recursive `BlockConsec rest (leftLeg.app (vertex₁ cell)) (rightLeg.app (vertex₁ cell))`
        -- but the running endpoints must be `B.vL`/`B.vR`; they reduce to the leg-images.
        rw [show (BlockRec.ofCube c m cell).vL
              = K.toPsh.vertex₁ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint false).app K.toPsh)) from rfl,
          show (BlockRec.ofCube c m cell).vR
              = K.toPsh.vertex₁ (yonedaEquiv
                  (c.blockQ cell ≫ (endpoint true).app K.toPsh)) from rfl,
          ofCube_vL_eq, ofCube_vR_eq]
        exact hIH

/-- The `BlockConsec` of `blocksOf c a` over the basepoints (`leg.app init = K.init` by
`app_init`). -/
theorem blockConsec_blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) :
    BlockConsec (blocksOf c a) K.init K.init := by
  have h := blockConsec_blocksOf_aux c a.cubes c.src.init a.isChain
  rw [c.leftLeg.app_init, c.rightLeg.app_init] at h
  exact h

/-- **Source identification.**  `leftPush (blocksOf c a)` is exactly the left-leg pushforward
`(pushforwardBP c.leftLeg).obj a`: cube-wise, `yonedaEquiv (blockQ cell ≫ e_false) = leftLeg.app
cell` (`blockQ_face`), so the two `List.map`s coincide. -/
theorem leftPush_blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) :
    leftPush (blocksOf c a) K.init K.init (blockConsec_blocksOf c a)
      = (Refine.pushforwardBP c.leftLeg).obj a := by
  apply RefineObj.ext''
  rw [leftPush_cubes, Refine.pushforwardBP_obj_cubes, blocksOf, List.map_map]
  apply List.map_congr_left
  intro cb _
  simp only [Function.comp_apply, BlockRec.ofCube, mapCubeHom]
  exact congrArg (fun z => (⟨cb.1, z⟩ : Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
    (blockQ_face c cb.2 false)

/-- **Right-source identification.**  `rightPush (blocksOf c a)` is the right-leg pushforward
`(pushforwardBP c.rightLeg).obj a`. -/
theorem rightPush_blocksOf (c : CylMapR K)
    (a : RefineObj (K := c.src) c.src.init c.src.final) :
    rightPush (blocksOf c a) K.init K.init (blockConsec_blocksOf c a)
      = (Refine.pushforwardBP c.rightLeg).obj a := by
  apply RefineObj.ext''
  rw [rightPush_cubes, Refine.pushforwardBP_obj_cubes, blocksOf, List.map_map]
  apply List.map_congr_left
  intro cb _
  simp only [Function.comp_apply, BlockRec.ofCube, mapCubeHom]
  exact congrArg (fun z => (⟨cb.1, z⟩ : Σ n : ℕ+, K.toPsh.cells (n : ℕ)))
    (blockQ_face c cb.2 true)

/-! ### The top-level sweep `sweepFirst`

The whole-chain sweep lifts the *first* block with a single **top coface** `refineCofaceG true`
(not a bridge): at the basepoint the two leg-images agree (`B.uL = B.uR = K.init`), so there is no
initial vertical edge to bridge — exactly §8's `α₃`.  Hence `sweepFirst` targets `rightPush bs`
directly (no init edge), and the rest of the staircase is `sweepTail rest`.  This is the entry
point the total `sweepR` wraps. -/

/-- The **top single-coface arrow** for the first block (`B.uL = B.uR`): `B.rc → B.R`, whiskered by
the `rightPush rest` suffix.  Source `refineEndG true ≫ suffix`, target `B.R ≫ suffix = apex`. -/
noncomputable def topCofaceFirst (B : BlockRec c) (rest : List (BlockRec c))
    (huLR : B.uL = B.uR) (hrec : BlockConsec rest B.vL B.vR) :
    (refineEndG true (c.blockQ B.cell) (B.hiR.trans huLR.symm) B.hfR).append
        (rightPush rest B.vL B.vR hrec)
      ⟶ B.R.append (rightPush rest B.vL B.vR hrec) :=
  ChainRefine.append
    (refineCofaceG true (c.blockQ B.cell) (B.hiR.trans huLR.symm) B.hfR B.hiL B.hfR)
    (𝟙 (rightPush rest B.vL B.vR hrec))

/-- The right-target object bridge for `sweepFirst`: `rightPush (B::rest)` (started at `B.uL`,
both leg-images agreeing) equals the `true`-face single-cube chain suffixed by `rightPush rest`
(the `refineEndG true` source of `topCofaceFirst`). -/
theorem tgtEqFirst (B : BlockRec c) (rest : List (BlockRec c)) (huLR : B.uL = B.uR)
    (h : BlockConsec (B :: rest) B.uL B.uL) (hrec : BlockConsec rest B.vL B.vR) :
    rightPush (B :: rest) B.uL B.uL h
      = (refineEndG true (c.blockQ B.cell) (B.hiR.trans huLR.symm) B.hfR).append
          (rightPush rest B.vL B.vR hrec) := by
  apply RefineObj.ext''
  simp only [rightPush_cubes, refineEndG, RefineObj.append_cubes, List.map_cons,
    List.singleton_append]

/-- **The top-level whole-chain sweep** `leftPush bs ⟶ rightPush bs` in the global fence
`RefineObj mL final`, for a block list whose first block's two leg-images agree (`mL = mR`, the
basepoint).  Lifts the first block by a top single coface, then runs `sweepTail` on the rest. -/
noncomputable def sweepFirst : (bs : List (BlockRec c)) → (mL : K.toPsh.cells 0) →
    (h : BlockConsec bs mL mL) →
    (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (leftPush bs mL mL h)
      ⟶ (FreeGroupoid.of (RefineObj (K := K) mL K.final)).obj (rightPush bs mL mL h)
  | [], mL, h =>
      eqToHom (congrArg _ (RefineObj.ext'' (by
        simp only [leftPush_cubes, rightPush_cubes, List.map_nil])))
  | B :: rest, mL, h => by
      obtain ⟨huL, huR, hEi, hEf, hmatch, hrec⟩ := h
      subst huL
      have huLR : B.uL = B.uR := huR.symm
      have hcons : BlockConsec (B :: rest) B.uL B.uL := ⟨rfl, huR, hEi, hEf, hmatch, hrec⟩
      let lifted : (FreeGroupoid.of _).obj (B.lc.append (leftPush rest B.vL B.vR hrec))
          ⟶ (FreeGroupoid.of _).obj (B.lc.append (tailTarget rest B.vL B.vR hrec)) :=
        (FreeGroupoid.map (RefineObj.appendLeft (b := K.final) B.lc)).map
          (sweepTail rest B.vL B.vR hrec)
      let topc := (FreeGroupoid.of _).map (topCofaceFirst B rest huLR hrec)
      refine eqToHom (congrArg (FreeGroupoid.of _).obj
          (leftPush_cons B rest B.uL B.uL hcons rfl hrec))
        ≫ lifted
        ≫ ?mid ≫ Groupoid.inv topc
        ≫ eqToHom (congrArg (FreeGroupoid.of _).obj (tgtEqFirst B rest huLR hcons hrec).symm)
      match rest, hmatch, hrec with
      | [], hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_nil B hmatch.1 hmatch.2 hrec))
            ≫ (FreeGroupoid.of _).map
              (ChainRefine.append (botArrowNil B hmatch.1 hmatch.2)
                (𝟙 (rightPush [] B.vL B.vR hrec)))
      | B' :: tl, hmatch, hrec =>
          exact eqToHom (congrArg (FreeGroupoid.of _).obj (midEq_cons B B' tl hmatch hrec))
            ≫ (FreeGroupoid.of _).map (botArrowCons B B' tl hmatch hrec)

/-! ### Piece 4b — the TOTAL sweep `sweepR`

For an arbitrary source chain `a : RefineObj c.src.init c.src.final`, `sweepR c a` is the homotopy
`(pushforwardBP leftLeg).obj a ⟶ (pushforwardBP rightLeg).obj a` in `DPathGrpdR K`.  It is
`sweepFirst (blocksOf c a)` (the whole-chain staircase) re-based across the two source/target
identifications `leftPush_blocksOf`/`rightPush_blocksOf` (the leg-pushforward equals the
`lc`/`rc`-push of the block decomposition, cube-wise by `blockQ_face`). -/

/-- **The total multi-block sweep** `sweepR c a : (pushforwardBP leftLeg).obj a ⟶
(pushforwardBP rightLeg).obj a` in `DPathGrpdR K` — the cylinder's homotopy on an arbitrary source
chain, the list-indexed junction-bridge staircase of §8.6. -/
noncomputable def sweepR (c : CylMapR K) (a : RefineObj (K := c.src) c.src.init c.src.final) :
    (FreeGroupoid.of (RefineObj (K := K) K.init K.final)).obj
        ((Refine.pushforwardBP c.leftLeg).obj a)
      ⟶ (FreeGroupoid.of (RefineObj (K := K) K.init K.final)).obj
          ((Refine.pushforwardBP c.rightLeg).obj a) :=
  eqToHom (congrArg (FreeGroupoid.of _).obj (leftPush_blocksOf c a).symm)
    ≫ sweepFirst (blocksOf c a) K.init (blockConsec_blocksOf c a)
    ≫ eqToHom (congrArg (FreeGroupoid.of _).obj (rightPush_blocksOf c a))

/-! ## Piece 5 — the cylinder's pointed endofunctor on the d-path groupoid

For a weak-equivalence cylinder `c : CylMapWeqR K` (left leg a groupoid equivalence), the homotopy
`sweepR` assembles into a **pointed endofunctor** of `DPathGrpdR K` via `pointedOfPaths`:

* object map `F₀ x := c.Rgrpd.obj (c.Lgrpd.inv.obj x)` (the transport `Lgrpd⁻¹ ⋙ Rgrpd` of `Rgrpd`
  along the equivalence `Lgrpd`);
* per-object point `η x := counit.inv.app x ≫ sweepR c (Lgrpd.inv.obj x)` — the cylinder's homotopy
  at the transported chain, prefixed by the equivalence counit.

`pointedOfPaths` turns this object-data into a genuine `PointedEndofunctor` with naturality *free*
(the conjugation trick), so no naturality chase is needed for the point. -/

/-- **Piece 5 (object map): the pointed endofunctor of a weak-equivalence cylinder.**  Via
`pointedOfPaths`, from the object map `Rgrpd ∘ Lgrpd⁻¹` and the per-chain homotopy `sweepR`.  This
is the action of the cylinder `c` as a coherent family of d-path homotopies on `DPathGrpdR K`. -/
noncomputable def cylToPointedObj (c : CylMapWeqR K) :
    Operations.PointedEndofunctor (DPathGrpdR K) :=
  haveI : c.obj.Lgrpd.IsEquivalence := CylMapWeqR.left_weq c
  Operations.pointedOfPaths
    (fun x => c.obj.Rgrpd.obj (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x)))
    (fun x => c.obj.Lgrpd.asEquivalence.counitIso.inv.app ((FreeGroupoid.of _).obj x)
      ≫ c.obj.sweepR (c.obj.Lgrpd.inv.obj ((FreeGroupoid.of _).obj x)).as.as)

/-- **Piece 5 (morphism map): the cylinder ⟹ pointed-functor FUNCTOR.**  Assembles the
per-cylinder pointed endofunctors `cylToPointedObj` into a functor
`CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)`.

The morphism map is *forced*: the d-path groupoid `DPathGrpdR K` is a `Groupoid`, so each
point `(cylToPointedObj c).pt` is a natural isomorphism, and the morphism axiom
`pt_c ≫ τ = pt_{c'}` determines the comparison `τ = pt_c⁻¹ ≫ pt_{c'}` uniquely
(`Operations.pointedHomOfGroupoid`).  A cylinder map `f : c ⟶ c'` is therefore sent to this
unique point-determined comparison; `map_id`/`map_comp` and the point-compatibility `w` are all
automatic (`pointedFunctorOfObj`).  No naturality chase, no deferral — this COMPLETES the
cylinder ⟹ pointed-functor functor (program step 2). -/
noncomputable def cylToPointedR (K : BPSet) :
    CylMapWeqR K ⥤ Operations.PointedEndofunctor (DPathGrpdR K) :=
  Operations.pointedFunctorOfObj CylMapR.cylToPointedObj

@[simp] theorem cylToPointedR_obj (c : CylMapWeqR K) :
    (cylToPointedR K).obj c = CylMapR.cylToPointedObj c := rfl

@[simp] theorem cylToPointedR_map {c c' : CylMapWeqR K} (f : c ⟶ c') :
    (cylToPointedR K).map f
      = Operations.pointedHomOfGroupoid (CylMapR.cylToPointedObj c)
          (CylMapR.cylToPointedObj c') := rfl

end CylMapR

/-! ## 9. Module summary — the general sweep `sweepR` and Piece 5

The cylinder ⟹ pointed-functor **functor** (program step 2) is COMPLETE, green and sorry-free:
both its object map `cylToPointedObj` and its morphism map `cylToPointedR` are built.

The pipeline: for a `k`-block source chain the junction-bridge staircase lifts the blocks `k → 1`
through prism-cube cospans, sharing each junction edge `eᵢ` between the two bridges touching `sᵢ`
(making consecutive staircase objects definitionally equal so the zigzag composes).  It is run by
the list-indexed recursion `sweepTail`/`sweepFirst` over `BlockRec`/`BlockConsec` (each local arrow
whiskered by a fixed prefix via `RefineObj.appendLeft` and a fixed suffix via inline
`ChainRefine.append · (𝟙 _)`), assembled into the total homotopy `sweepR c a :
(pushforwardBP leftLeg).obj a ⟶ (pushforwardBP rightLeg).obj a`.  Piece 5 then turns the family
`sweepR` into `cylToPointedObj` via `pointedOfPaths` (naturality free by conjugation), and—since
`DPathGrpdR K` is a groupoid—`pointedFunctorOfObj` forces the morphism map uniquely
(`cylToPointedR`).  Connectivity for the smallest multi-block cylinder is independently confirmed by
`native_decide` in `Testing/CylinderTwoBlock.lean`. -/
