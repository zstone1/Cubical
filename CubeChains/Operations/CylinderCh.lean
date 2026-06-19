import CubeChains.Operations.Cylinder
import CubeChains.Chains.Endpoints
import CubeChains.Chains.Segal
import CubeChains.Operations.PointedFunctor
import CubeChains.Operations.GroupoidTarget

/-!
# Cylinder maps over a bi-pointed `K`, and their action on the d-path groupoid (step 3)

This is the `Ch`-target analogue of `Operations/Cylinder.lean`.  Where that file builds
its cylinder maps and d-path groupoid against the **basepoint-free** chain category
`ChP = Operations.Precubical.ChP` (a `PrecubicalSet`-functor), this file mirrors the same
scaffolding against the **bi-pointed** chain category `Ch = ChainCat.Obj`
(`Chains/Category.lean`), the `BPSet`-functor.

It introduces:

* `DPathGrpdB K = FreeGroupoid (ChainCat.Obj K)` — the d-path homotopy groupoid over the
  bi-pointed chain category, i.e. the groupoid reflection `Ch(K)[Ch(K)⁻¹]`, whose arrows
  are the zigzags of `Ch K`;
* `CylMapB K` — a **cylinder map** to a bi-pointed `K`: a `BPSet` source `src` with a map
  `cyl : src.toPsh ⟶ PathOb K.toPsh` (a directed cubical homotopy), *together with the two
  legs given as `BPSet` morphisms* `leftLeg`/`rightLeg : src ⟶ K`.  Storing the legs as
  `BPSet` maps (rather than reading them off `cyl`) is precisely the **rel-interface**
  condition: the homotopy preserves the chosen basepoints at both ends;
* the induced **leg-functors** `Lgrpd`/`Rgrpd : DPathGrpdB src ⥤ DPathGrpdB K` from
  `Ch.map` on the legs;
* `CylMapWeqB K` — cylinder maps whose left leg is a groupoid-reflection weak equivalence
  (so `Lgrpd` is an equivalence), and its category.

The geometric comparison `θ = CylMapB.toTransf : Lgrpd ⟶ Rgrpd` and the resulting functor
`cylToPointedB : CylMapWeqB K ⥤ PointedEndofunctor (DPathGrpdB K)` are the **crux** and are
*not supplied here* (this is step 3 of the refactor; θ is explicitly deferred).  See the
note at the end of this file for the precise geometric obstruction and the per-block
machinery (`Chains/Endpoints.lean`'s `Ch'`) it factors through.
-/

open CategoryTheory Opposite
open Operations Operations.Precubical

variable {K : BPSet}

/-! ## 1. The bi-pointed d-path groupoid -/

/-- The **d-path homotopy groupoid** of a bi-pointed `K`: the groupoid reflection
`Ch(K)[Ch(K)⁻¹]` of the *bi-pointed* cube-chain category `Ch K = ChainCat.Obj K`, whose
morphisms are exactly the zigzags of `Ch K`.  (The `Ch`-target analogue of
`DPathGrpd = FreeGroupoid (ChP.obj K)`.) -/
abbrev DPathGrpdB (K : BPSet) := FreeGroupoid (ChainCat.Obj K)

/-! ## 2. Cylinder maps over a bi-pointed `K` (rel-interface) -/

/-- A **cylinder map** to a bi-pointed `K`: a `BPSet` source `src` carrying a map
`cyl : src.toPsh ⟶ PathOb K.toPsh` (a directed cubical homotopy `src ⊗ □¹ ⟶ K` by the
box-tensor adjunction), whose two `endpoint`-evaluations are given by *basepoint-preserving*
maps `leftLeg`/`rightLeg : src ⟶ K`.  Requiring the legs to be `BPSet` morphisms (and the
`cyl` to evaluate to them) is the **rel-interface** condition: the homotopy fixes the chosen
basepoints at both ends. -/
structure CylMapB (K : BPSet) where
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

/-! ## 3. The leg-functors on the d-path groupoid -/

/-- The **left leg-functor** on the d-path groupoid, `DPathGrpdB src ⥤ DPathGrpdB K`,
induced by post-composing chains with the left leg (`Ch.map c.leftLeg`).  Mirrors
`CylMap.Lgrpd`. -/
noncomputable def CylMapB.Lgrpd (c : CylMapB K) : DPathGrpdB c.src ⥤ DPathGrpdB K :=
  FreeGroupoid.map (Ch.map c.leftLeg).toFunctor

/-- The **right leg-functor** on the d-path groupoid, `DPathGrpdB src ⥤ DPathGrpdB K`,
induced by the right leg.  Mirrors `CylMap.Rgrpd`. -/
noncomputable def CylMapB.Rgrpd (c : CylMapB K) : DPathGrpdB c.src ⥤ DPathGrpdB K :=
  FreeGroupoid.map (Ch.map c.rightLeg).toFunctor

/-! ## 4. The weak-equivalence subcategory of cylinder maps

`CylMapB K` is a hand-rolled structure (its legs are `BPSet` morphisms and its `cyl` lives
on the underlying presheaf, so it is *not* an `Over`/comma category), so we equip it with a
`Category` instance directly: a morphism is a `BPSet` map of sources commuting with `cyl`.
Commuting with `cyl` already forces the legs to commute (they are `endpoint`-evaluations of
`cyl`), so `Lgrpd`/`Rgrpd` are functorial along these morphisms. -/

/-- A **morphism of cylinder maps**: a `BPSet` map of sources commuting with the `cyl`
classifying maps.  (The leg-commutation is then automatic.) -/
@[ext]
structure CylMapB.Hom (a b : CylMapB K) where
  /-- The underlying `BPSet` map of sources. -/
  hom : a.src ⟶ b.src
  /-- It commutes with the cylinder classifying maps. -/
  w : hom.hom ≫ b.cyl = a.cyl

namespace CylMapB

instance category (K : BPSet) : Category (CylMapB K) where
  Hom a b := CylMapB.Hom a b
  id a := ⟨𝟙 a.src, by rw [BPSet.id_hom, Category.id_comp]⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [BPSet.comp_hom, Category.assoc, g.w, f.w]⟩
  id_comp f := CylMapB.Hom.ext (Category.id_comp _)
  comp_id f := CylMapB.Hom.ext (Category.comp_id _)
  assoc f g h := CylMapB.Hom.ext (Category.assoc _ _ _)

@[simp] theorem id_hom (a : CylMapB K) : CylMapB.Hom.hom (𝟙 a) = 𝟙 a.src := rfl

@[simp] theorem comp_hom {a b c : CylMapB K} (f : a ⟶ b) (g : b ⟶ c) :
    CylMapB.Hom.hom (f ≫ g) = CylMapB.Hom.hom f ≫ CylMapB.Hom.hom g := rfl

@[ext] theorem hom_ext' {a b : CylMapB K} {f g : a ⟶ b}
    (h : CylMapB.Hom.hom f = CylMapB.Hom.hom g) : f = g := CylMapB.Hom.ext h

end CylMapB

/-- The object-property cutting out cylinder maps whose left leg is a groupoid-reflection
weak equivalence (so `Lgrpd` is an equivalence and the transport `Lgrpd⁻¹ ⋙ Rgrpd` exists).
The `Ch`-target analogue of `CylMap.leftWeq`. -/
def CylMapB.leftWeq (K : BPSet) : ObjectProperty (CylMapB K) :=
  fun c => c.Lgrpd.IsEquivalence

/-- Cylinder maps whose left leg is a weak equivalence: the full subcategory of `CylMapB K`
cut out by `Lgrpd.IsEquivalence`.  Reusing `ObjectProperty.FullSubcategory` inherits the
category and the forgetful functor `ι : CylMapWeqB K ⥤ CylMapB K`; an object's witness is
its `.property`.  Mirrors `CylMapWeq`. -/
abbrev CylMapWeqB (K : BPSet) := (CylMapB.leftWeq K).FullSubcategory

/-- The left leg-functor of a `CylMapWeqB` object is an equivalence (its defining
property). -/
theorem CylMapWeqB.left_weq (c : CylMapWeqB K) : c.obj.Lgrpd.IsEquivalence := c.property

/-! ## 5. Per-block components of `θ`, in the endpoint-indexed `Ch'`

This section ports the reusable per-block geometric heart of `Operations/Cylinder.lean`'s
`θ`-construction to the **bi-pointed** target.  The single decisive change from the
basepoint-free `ChP` case is that morphisms of the bi-pointed chain categories must
*preserve* their interface vertices.  So a block's prism homotopy is built not in the global
`Ch K` but in the **endpoint-indexed fiber** `Ch'(a, b) = ChainCat.Obj (BPSet.rebase K a b)`
(`Chains/Endpoints.lean`) over the block's own pair of junction vertices `(a, b)` —
the all-`0` and all-`1` corners of the prism cube, computed by `prism_vertex₀`/`prism_vertex₁`
(imported from `Operations/Cylinder.lean`, over the underlying presheaf `K.toPsh`).

The geometric layer itself — `CylMap.prism`, `CylMap.coface_prism`, `prism_vertex₀/₁`,
`serialWedgeSingletonIso` — is shared verbatim with the `ChP` build; only the *bundling into
a chain object* is bi-pointed-specific, and is provided by `Ch'.ofPshMap` below. -/

/-- **Bundle a presheaf wedge map into an endpoint-indexed chain object.**  A presheaf map
`f : (serialWedge dims).toPsh ⟶ K` is a `Ch'`-object over `K` re-basepointed at the *vertices
`f` itself selects* on the wedge's `init`/`final` corners, so the basepoint-preservation
conditions hold by `rfl`.  This is the bi-pointed bridge: it turns the basepoint-free prism
geometry (`CylMap.prism`, the `coface`-faces) into objects/morphisms of the interface-fixed
`Ch'`, with the interface read off the map. -/
noncomputable def Ch'.ofPshMap {K : PrecubicalSet} (dims : List ℕ+)
    (f : (BPSet.serialWedge dims).toPsh ⟶ K) :
    Ch' K (f.app (op (Box.ob 0)) (BPSet.serialWedge dims).init)
      (f.app (op (Box.ob 0)) (BPSet.serialWedge dims).final) :=
  ⟨dims, ⟨f, rfl, rfl⟩⟩

@[simp] theorem Ch'.ofPshMap_dims {K : PrecubicalSet} (dims : List ℕ+)
    (f : (BPSet.serialWedge dims).toPsh ⟶ K) : (Ch'.ofPshMap dims f).dims = dims := rfl

@[simp] theorem Ch'.ofPshMap_map_hom {K : PrecubicalSet} (dims : List ℕ+)
    (f : (BPSet.serialWedge dims).toPsh ⟶ K) : (Ch'.ofPshMap dims f).map.hom = f := rfl

/-! ### The prism cube and the block-end chains as `Ch'` objects

For a one-cube block `(m, q)` in `PathOb K`, the prism cube `R = (tauto K).prism q'`
(`q' = serialWedgeSingletonIso m ≫ q`) is an `(m+1)`-cube of `K`.  Presented as a
single-block chain via `serialWedgeSingletonIso (m+1)`, it bundles (via `Ch'.ofPshMap`)
into a `Ch'`-object over `K.toPsh` re-basepointed at its two corners; `prism_vertex₀/₁`
(over the presheaf `K.toPsh`) identify those corners with the `e₀`/`e₁` legs' corners.

These are the *objects* of the per-block fence (`R` and the two flat block ends); the prism
geometry is shared verbatim with the `ChP` build. -/

/-- The prism cube over a single-block chain `(m, q)` in `PathOb (K.toPsh)`, as a one-block
chain object `[m+1]` in the **endpoint-indexed** `Ch'` over its two corner vertices.  The
underlying `(m+1)`-cube is `(tauto K.toPsh).prism (serialWedgeSingletonIso m ≫ q)`, exactly
the `ChP`-side `singleBlockPrism`. -/
noncomputable def singleBlockPrismB (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :=
  Ch'.ofPshMap (K := K.toPsh) [m + 1]
    ((serialWedgeSingletonIso (m + 1)).inv
      ≫ (CylMap.tauto K.toPsh).prism ((serialWedgeSingletonIso m).hom ≫ q))

/-- The single block `(m, q)` evaluated at endpoint `ε`, as a one-block `Ch'`-object in `K`
re-basepointed at its own two corners (the `ChP`-side `singleBlockEnd`, bi-pointed). -/
noncomputable def singleBlockEndB (ε : Bool) (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :=
  Ch'.ofPshMap (K := K.toPsh) [m] (q ≫ (endpoint ε).app K.toPsh)

/-- The vertical prism edge over the empty chain (a vertex `v : □⁰ ⟶ PathOb K`), as a
one-block `[1]`-chain `Ch'`-object over its two endpoints `v ≫ e₀`, `v ≫ e₁` (the
`ChP`-side `emptyBlockPrism`).  This is the bridge that fixes the level mismatch at a
junction. -/
noncomputable def emptyBlockPrismB (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K.toPsh) :=
  Ch'.ofPshMap (K := K.toPsh) [1]
    ((serialWedgeSingletonIso 1).inv ≫ (CylMap.tauto K.toPsh).prism v)

/-- The empty chain `(v)` evaluated at endpoint `ε`, as the trivial `[]`-chain `Ch'`-object
over the single vertex `v ≫ eε` (the `ChP`-side `emptyBlockEnd`). -/
noncomputable def emptyBlockEndB (ε : Bool) (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K.toPsh) :=
  Ch'.ofPshMap (K := K.toPsh) [] (v ≫ (endpoint ε).app K.toPsh)

/-! ### The corner-matching kernel (the interface coherence of the fence)

The bi-pointed fence is glued from these vertex identities: the prism cube `R` shares its
**initial** corner with the `e₀`-face block and its **final** corner with the `e₁`-face
block.  These are exactly `prism_vertex₀`/`prism_vertex₁` (over the presheaf `K.toPsh`),
re-read through the `Ch'.ofPshMap` bundling.  They are the data the `P_j`/`R_j` chains glue
on at the junctions — the interface coherence the staircase consumes.

`singleBlockPrismB`/`singleBlockEndB` are bundled via `Ch'.ofPshMap`, so their interface
vertices are *definitionally* the wedge map's corner values; the lemmas below rewrite those
into the shared-corner form. -/

/-- The initial corner of the prism cube `R` equals the initial corner of its `e₀`-face
block (both are the all-`0` corner) — the `Ch'`-interface form of `prism_vertex₀`. -/
theorem singleBlockPrismB_init (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism
        ((serialWedgeSingletonIso m).hom ≫ q)))
      = K.toPsh.vertex₀ (yonedaEquiv (((serialWedgeSingletonIso m).hom ≫ q)
        ≫ (endpoint false).app K.toPsh)) :=
  prism_vertex₀ ((serialWedgeSingletonIso m).hom ≫ q)

/-- The final corner of the prism cube `R` equals the final corner of its `e₁`-face block
(both are the all-`1` corner) — the `Ch'`-interface form of `prism_vertex₁`. -/
theorem singleBlockPrismB_final (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism
        ((serialWedgeSingletonIso m).hom ≫ q)))
      = K.toPsh.vertex₁ (yonedaEquiv (((serialWedgeSingletonIso m).hom ≫ q)
        ≫ (endpoint true).app K.toPsh)) :=
  prism_vertex₁ ((serialWedgeSingletonIso m).hom ≫ q)

/-- The initial corner of the vertical prism edge equals `v ≫ e₀` (its bottom endpoint) —
the empty-block form of `prism_vertex₀`. -/
theorem emptyBlockPrismB_init (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K.toPsh) :
    K.toPsh.vertex₀ (yonedaEquiv ((CylMap.tauto K.toPsh).prism v))
      = K.toPsh.vertex₀ (yonedaEquiv (v ≫ (endpoint false).app K.toPsh)) :=
  prism_vertex₀ v

/-- The final corner of the vertical prism edge equals `v ≫ e₁` (its top endpoint) — the
empty-block form of `prism_vertex₁`. -/
theorem emptyBlockPrismB_final (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K.toPsh) :
    K.toPsh.vertex₁ (yonedaEquiv ((CylMap.tauto K.toPsh).prism v))
      = K.toPsh.vertex₁ (yonedaEquiv (v ≫ (endpoint true).app K.toPsh)) :=
  prism_vertex₁ v

/-! ### The two boundary paths of the prism cube (the irreducible combinatorics)

The per-block cospan in the bi-pointed `Ch'` cannot use the flat cofaces of `R` (they do
not preserve `R`'s final interface vertex, see `## 6.` below).  Instead it refines the two
**corner-to-corner boundary paths** of the prism cube `R = cube (m+1)`, each running from
`R`'s all-`0` corner to its all-`1` corner:

* `bdryUpIncl m : serialWedge [1, m] ⟶ cube (m+1)` — *up-then-along*: the vertical prism
  edge at the block's INIT corner (a `□¹`) followed by the TOP (`e₁`) `m`-face;
* `bdryDownIncl m : serialWedge [m, 1] ⟶ cube (m+1)` — *along-then-up*: the BOTTOM (`e₀`)
  `m`-face followed by the vertical prism edge at the block's FINAL corner.

Each is a `pushout.desc` of a flat face `yoneda.map (Box.coface ε)` against a vertical edge
`yoneda.map (Box.shift.map (cornerMap m ε))` (the last-coordinate-free edge over the corner
`□⁰ ⟶ □ᵐ`).  The corner `Box` morphism `cornerMap m ε` classifies the all-`ε` vertex of
`□ᵐ`; its shift `Box.shift.map (cornerMap m ε)` is precisely the vertical edge
`canonicalMap (snocFree (constVertex m ε))` (`shift.map` appends a free coordinate). -/

/-- The `Box` morphism `□⁰ ⟶ □ᵐ` selecting the all-`ε` vertex of the cube `□ᵐ`. -/
def cornerMap (m : ℕ) (ε : Bool) : Box.ob 0 ⟶ Box.ob m :=
  StdCube.canonicalMap (StdCube.constVertex m ε)

/-- `ev` of the corner map is the constant-`ε` vertex (it sends the top `0`-cell to it). -/
theorem ev_cornerMap (m : ℕ) (ε : Bool) :
    StdCube.ev (cornerMap m ε) = StdCube.constVertex m ε :=
  StdCube.app_topCell (K := StdCube.stdPre m) (StdCube.constVertex m ε)

/-- The **vertical prism edge** `□¹ ⟶ □^{m+1}` at the block's all-`ε` corner: the shift of
the corner map (which appends a free last coordinate to the corner vertex). -/
theorem shift_cornerMap (m : ℕ) (ε : Bool) :
    Box.shift.map (cornerMap m ε)
      = StdCube.canonicalMap (K := StdCube.stdPre (m + 1))
          (StdCube.snocFree (StdCube.constVertex m ε)) := by
  change StdCube.canonicalMap (K := StdCube.stdPre (m + 1))
      (StdCube.snocFree (StdCube.ev (cornerMap m ε))) = _
  rw [ev_cornerMap]

/-- **The vertical edge over a corner is the prism over the corner vertex.**  Precomposing
the prism cube `(tauto K).prism p` with the vertical edge at the all-`ε` corner equals the
prism (a `□¹`) over the corner vertex `cornerMap m ε ≫ p` of the block `p`.  This is the
`prism_precomp` identity at the corner, and is the geometric crux behind the boundary-path
junctions. -/
theorem vertEdge_prism {m : ℕ} (ε : Bool) (p : yoneda.obj (Box.ob m) ⟶ PathOb.obj K.toPsh) :
    yoneda.map (Box.shift.map (cornerMap m ε)) ≫ (CylMap.tauto K.toPsh).prism p
      = (CylMap.tauto K.toPsh).prism (yoneda.map (cornerMap m ε) ≫ p) :=
  (CylMap.prism_precomp (CylMap.tauto K.toPsh) (cornerMap m ε) p).symm

/-- The all-`ε` corner of `□¹` is the `ε`-end coface `□⁰ ⟶ □¹`: both classify the cell
`snocFix ε (topCell 0) = constVertex 1 ε`.  This is the bridge that turns the boundary-path
junctions into `Box.coface`-naturality squares. -/
theorem cornerMap_one (ε : Bool) : cornerMap 1 ε = (Box.coface ε).app (Box.ob 0) := by
  apply (StdCube.cubeRepr (StdCube.stdPre 1) 0).injective
  change StdCube.ev (cornerMap 1 ε) = StdCube.ev ((Box.coface ε).app (Box.ob 0))
  rw [ev_cornerMap]
  change StdCube.constVertex 1 ε = StdCube.snocFix ε (StdCube.topCell 0)
  apply Subtype.ext
  funext i
  obtain rfl : i = Fin.last 0 := Subsingleton.elim _ _
  rw [StdCube.snocFix_val, Fin.snoc_last]
  rfl

/-- The boundary-path **junction is a `Box.coface`-naturality square**: the all-`1` end of
the vertical edge over the all-`ε` corner of `□ᵐ` equals the all-`ε` corner pushed through
the `true`-end coface.  (Used for `bdryUp`; the symmetric `false` version is used for
`bdryDown`.)  Pure `coface`-naturality at `cornerMap m ε`. -/
theorem corner_coface_nat (m : ℕ) (ε δ : Bool) :
    cornerMap m ε ≫ (Box.coface δ).app (Box.ob m)
      = (Box.coface δ).app (Box.ob 0) ≫ Box.shift.map (cornerMap m ε) :=
  (Box.coface δ).naturality (cornerMap m ε)

/-- The initial vertex of the standard cube `cube n` is `yoneda.map` of the all-`0` corner
`Box` morphism `cornerMap n false = initVertexMap n`. -/
theorem cube_initVertex (n : ℕ) :
    (BPSet.cube n).initVertex = yoneda.map (cornerMap n false) := by
  rw [BPSet.initVertex, BPSet.vertexMap, Equiv.symm_apply_eq]
  exact (yonedaEquiv_yoneda_map (cornerMap n false)).symm

/-- The final vertex of the standard cube `cube n` is `yoneda.map` of the all-`1` corner
`Box` morphism `cornerMap n true = finalVertexMap n`. -/
theorem cube_finalVertex (n : ℕ) :
    (BPSet.cube n).finalVertex = yoneda.map (cornerMap n true) := by
  rw [BPSet.finalVertex, BPSet.vertexMap, Equiv.symm_apply_eq]
  exact (yonedaEquiv_yoneda_map (cornerMap n true)).symm

/-- The single-block wedge `serialWedge [m]` has the same initial vertex as the cube `cube m`
it collapses to: `(serialWedge [m]).initVertex` factors as `(cube m).initVertex ≫ singletonIso`. -/
theorem serialWedge_singleton_initVertex (m : ℕ+) :
    (BPSet.serialWedge [m]).initVertex ≫ (serialWedgeSingletonIso m).inv
      = (BPSet.cube (m : ℕ)).initVertex := by
  have h : (BPSet.serialWedge [m]).initVertex
      = (BPSet.cube (m : ℕ)).initVertex ≫ (serialWedgeSingletonIso m).hom :=
    wedge2_initVertex (BPSet.cube (m : ℕ)) (BPSet.cube 0)
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The point `cube 0` selects the same vertex at both ends. -/
theorem cube0_initVertex_eq_finalVertex :
    (BPSet.cube 0).initVertex = (BPSet.cube 0).finalVertex := by
  rw [cube0_initVertex_eq_id, cube0_finalVertex_eq_id]

/-- The single-block wedge `serialWedge [m]` has the same final vertex as the cube `cube m`. -/
theorem serialWedge_singleton_finalVertex (m : ℕ+) :
    (BPSet.serialWedge [m]).finalVertex ≫ (serialWedgeSingletonIso m).inv
      = (BPSet.cube (m : ℕ)).finalVertex := by
  rw [← cancel_mono (serialWedgeSingletonIso m).hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  -- LHS = `pushout.inr` (`final` of `cube 0` is `𝟙`); RHS = `inl`, push past the condition.
  have hL : (BPSet.serialWedge [m]).finalVertex
      = Limits.pushout.inr (BPSet.cube (m : ℕ)).finalVertex (BPSet.cube 0).initVertex :=
    (wedge2_finalVertex (BPSet.cube (m : ℕ)) (BPSet.cube 0)).trans (by
      rw [show (BPSet.cube 0).finalVertex = 𝟙 _ from cube0_finalVertex_eq_id]
      erw [Category.id_comp])
  have hR : (BPSet.cube (m : ℕ)).finalVertex ≫ (serialWedgeSingletonIso m).hom
      = Limits.pushout.inr (BPSet.cube (m : ℕ)).finalVertex (BPSet.cube 0).initVertex := by
    change (BPSet.cube (m : ℕ)).finalVertex
        ≫ Limits.pushout.inl (BPSet.cube (m : ℕ)).finalVertex (BPSet.cube 0).initVertex = _
    rw [Limits.pushout.condition, cube0_initVertex_eq_finalVertex,
      show (BPSet.cube 0).finalVertex = 𝟙 _ from cube0_finalVertex_eq_id]
    erw [Category.id_comp]
  rw [hL, hR]

/-! ### The two boundary-path inclusions of the prism cube

`bdryUpIncl m : serialWedge [1, m] ⟶ cube (m+1)` and `bdryDownIncl m : serialWedge [m, 1] ⟶
cube (m+1)`, each a `pushout.desc` of a flat coface against a vertical edge.  The cocone
condition in each is the `Box.coface`-naturality junction (`corner_coface_nat`), pushed
through Yoneda. -/

/-- **The up-then-along boundary path** `serialWedge [1, m] ⟶ cube (m+1)`: the vertical prism
edge at the INIT corner (head block, a `□¹`) followed by the TOP (`e₁`) `m`-face (tail block,
via the singleton iso).  Both blocks meet at the junction `(0,…,0,1)`. -/
noncomputable def bdryUpIncl (m : ℕ+) :
    (BPSet.serialWedge [1, m]).toPsh ⟶ (BPSet.cube ((m : ℕ) + 1)).toPsh :=
  Limits.pushout.desc
    (yoneda.map (Box.shift.map (cornerMap (m : ℕ) false)))
    ((serialWedgeSingletonIso m).inv ≫ yoneda.map ((Box.coface true).app (Box.ob (m : ℕ))))
    (by
      simp only [PNat.one_coe]
      rw [cube_finalVertex 1, cornerMap_one true, ← Category.assoc,
        serialWedge_singleton_initVertex, cube_initVertex]
      erw [← yoneda.map_comp, ← yoneda.map_comp]
      exact congrArg yoneda.map (corner_coface_nat (m : ℕ) false true).symm)

/-- **The along-then-up boundary path** `serialWedge [m, 1] ⟶ cube (m+1)`: the BOTTOM (`e₀`)
`m`-face (head block) followed by the vertical prism edge at the FINAL corner (tail block, a
`□¹`, via the singleton iso).  Both blocks meet at the junction `(1,…,1,0)`. -/
noncomputable def bdryDownIncl (m : ℕ+) :
    (BPSet.serialWedge [m, 1]).toPsh ⟶ (BPSet.cube ((m : ℕ) + 1)).toPsh :=
  Limits.pushout.desc
    (yoneda.map ((Box.coface false).app (Box.ob (m : ℕ))))
    ((serialWedgeSingletonIso 1).inv ≫ yoneda.map (Box.shift.map (cornerMap (m : ℕ) true)))
    (by
      rw [← Category.assoc, serialWedge_singleton_initVertex]
      simp only [PNat.one_coe]
      rw [cube_finalVertex (m : ℕ), cube_initVertex 1, cornerMap_one false]
      erw [← yoneda.map_comp, ← yoneda.map_comp]
      exact congrArg yoneda.map (corner_coface_nat (m : ℕ) true false))

/-! ### Corner preservation of the boundary paths

Both boundary inclusions run from `R`'s all-`0` corner to its all-`1` corner, so they
preserve the cube's init/final vertices.  The vertex-map forms below feed the
`Ch'`-interface (`app_init`/`app_final`) of the boundary-path chains. -/

/-- The all-`0` corner of `□^{m+1}` is the all-`0` corner of `□ᵐ` followed by the `false`-end
coface (`initVertexMap_succ`, in `cornerMap` form). -/
theorem cornerMap_succ_false (m : ℕ) :
    cornerMap (m + 1) false = cornerMap m false ≫ (Box.coface false).app (Box.ob m) :=
  initVertexMap_succ m

/-- The all-`1` corner of `□^{m+1}` is the all-`1` corner of `□ᵐ` followed by the `true`-end
coface (`finalVertexMap_succ`, in `cornerMap` form). -/
theorem cornerMap_succ_true (m : ℕ) :
    cornerMap (m + 1) true = cornerMap m true ≫ (Box.coface true).app (Box.ob m) :=
  finalVertexMap_succ m

/-- `bdryUpIncl` preserves the **initial** corner: the all-`0` vertex of `serialWedge [1, m]`
maps to the all-`0` vertex of `cube (m+1)`. -/
theorem bdryUpIncl_initVertex (m : ℕ+) :
    (BPSet.serialWedge [1, m]).initVertex ≫ bdryUpIncl m
      = (BPSet.cube ((m : ℕ) + 1)).initVertex := by
  have hv : (BPSet.serialWedge [1, m]).initVertex
      = (BPSet.cube ((1 : ℕ+) : ℕ)).initVertex
        ≫ Limits.pushout.inl (BPSet.cube ((1 : ℕ+) : ℕ)).finalVertex
            (BPSet.serialWedge [m]).initVertex :=
    wedge2_initVertex (BPSet.cube ((1 : ℕ+) : ℕ)) (BPSet.serialWedge [m])
  rw [hv]
  erw [Category.assoc, Limits.pushout.inl_desc]
  simp only [PNat.one_coe]
  rw [cube_initVertex, cornerMap_one false, cube_initVertex, cornerMap_succ_false]
  erw [← yoneda.map_comp]
  exact congrArg yoneda.map (corner_coface_nat (m : ℕ) false false).symm

/-- `bdryUpIncl` preserves the **final** corner: the all-`1` vertex of `serialWedge [1, m]`
maps to the all-`1` vertex of `cube (m+1)`. -/
theorem bdryUpIncl_finalVertex (m : ℕ+) :
    (BPSet.serialWedge [1, m]).finalVertex ≫ bdryUpIncl m
      = (BPSet.cube ((m : ℕ) + 1)).finalVertex := by
  have hv : (BPSet.serialWedge [1, m]).finalVertex
      = (BPSet.serialWedge [m]).finalVertex
        ≫ Limits.pushout.inr (BPSet.cube ((1 : ℕ+) : ℕ)).finalVertex
            (BPSet.serialWedge [m]).initVertex :=
    wedge2_finalVertex (BPSet.cube ((1 : ℕ+) : ℕ)) (BPSet.serialWedge [m])
  rw [hv]
  erw [Category.assoc, Limits.pushout.inr_desc]
  rw [← Category.assoc, serialWedge_singleton_finalVertex, cube_finalVertex, cube_finalVertex,
    cornerMap_succ_true]
  erw [← yoneda.map_comp]
  rfl

/-- `bdryDownIncl` preserves the **initial** corner. -/
theorem bdryDownIncl_initVertex (m : ℕ+) :
    (BPSet.serialWedge [m, 1]).initVertex ≫ bdryDownIncl m
      = (BPSet.cube ((m : ℕ) + 1)).initVertex := by
  have hv : (BPSet.serialWedge [m, 1]).initVertex
      = (BPSet.cube (m : ℕ)).initVertex
        ≫ Limits.pushout.inl (BPSet.cube (m : ℕ)).finalVertex
            (BPSet.serialWedge [1]).initVertex :=
    wedge2_initVertex (BPSet.cube (m : ℕ)) (BPSet.serialWedge [1])
  rw [hv]
  erw [Category.assoc, Limits.pushout.inl_desc]
  rw [cube_initVertex, cube_initVertex, cornerMap_succ_false]
  erw [← yoneda.map_comp]
  rfl

/-- `bdryDownIncl` preserves the **final** corner. -/
theorem bdryDownIncl_finalVertex (m : ℕ+) :
    (BPSet.serialWedge [m, 1]).finalVertex ≫ bdryDownIncl m
      = (BPSet.cube ((m : ℕ) + 1)).finalVertex := by
  have hv : (BPSet.serialWedge [m, 1]).finalVertex
      = (BPSet.serialWedge [1]).finalVertex
        ≫ Limits.pushout.inr (BPSet.cube (m : ℕ)).finalVertex
            (BPSet.serialWedge [1]).initVertex :=
    wedge2_finalVertex (BPSet.cube (m : ℕ)) (BPSet.serialWedge [1])
  rw [hv]
  erw [Category.assoc, Limits.pushout.inr_desc]
  rw [← Category.assoc, serialWedge_singleton_finalVertex]
  simp only [PNat.one_coe]
  rw [cube_finalVertex 1, cornerMap_one true, cube_finalVertex, cornerMap_succ_true]
  erw [← yoneda.map_comp]
  exact congrArg yoneda.map (corner_coface_nat (m : ℕ) true true).symm

/-! ### The per-block cospan `P_bottom → R ← P_top` and the per-block homotopy

With the boundary inclusions in hand, the per-block cospan is built directly in the
endpoint-indexed `Ch'` over the prism cube's two corners.  All three chains — the prism cube
`R` and the two boundary paths `P_bottom` (along-then-up) and `P_top` (up-then-along) — share
`R`'s all-`0` / all-`1` corners (the boundary paths run corner-to-corner of the cube), so they
are objects of *one* `Ch' K a b`, and the two boundary-path refinements give two `Ch'`
morphisms into `R`. -/

/-- The prism cube map of a single block `(m, q)` into `K`, an `(m+1)`-cube. -/
noncomputable def prismCube (m : ℕ+) (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    (BPSet.cube ((m : ℕ) + 1)).toPsh ⟶ K.toPsh :=
  (CylMap.tauto K.toPsh).prism ((serialWedgeSingletonIso m).hom ≫ q)

/-- Convert vertex-map init preservation into the cell form (`app` on the wedge's init
vertex): if `g : (serialWedge dims).toPsh ⟶ Z.toPsh` carries `initVertex` to `Z.initVertex`
then it carries the init `0`-cell to `Z.init`. -/
theorem app_init_of_initVertex {dims : List ℕ+} {Z : BPSet}
    (g : (BPSet.serialWedge dims).toPsh ⟶ Z.toPsh)
    (h : (BPSet.serialWedge dims).initVertex ≫ g = Z.initVertex) :
    g.app (op (Box.ob 0)) (BPSet.serialWedge dims).init = Z.init := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm (g.app (op (Box.ob 0)) (BPSet.serialWedge dims).init)
      = (BPSet.serialWedge dims).initVertex ≫ g from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) g (BPSet.serialWedge dims).init).symm]
  rw [h, BPSet.initVertex, BPSet.vertexMap]

/-- Cell form of corner preservation, final vertex. -/
theorem app_final_of_finalVertex {dims : List ℕ+} {Z : BPSet}
    (g : (BPSet.serialWedge dims).toPsh ⟶ Z.toPsh)
    (h : (BPSet.serialWedge dims).finalVertex ≫ g = Z.finalVertex) :
    g.app (op (Box.ob 0)) (BPSet.serialWedge dims).final = Z.final := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm (g.app (op (Box.ob 0)) (BPSet.serialWedge dims).final)
      = (BPSet.serialWedge dims).finalVertex ≫ g from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) g (BPSet.serialWedge dims).final).symm]
  rw [h, BPSet.finalVertex, BPSet.vertexMap]

/-- A boundary-path chain over the prism cube, as a `Ch'`-object **over the cube's corners**
(`prismCube … (cube N).init`, `… .final`).  Built from a corner-preserving inclusion
`g : serialWedge dims ⟶ cube (m+1)` of the boundary path; the basepoints are the prism cube's
own corners, the same for every boundary path and for `R` itself. -/
noncomputable def prismPathObj (m : ℕ+) (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh)
    (dims : List ℕ+) (g : (BPSet.serialWedge dims).toPsh ⟶ (BPSet.cube ((m : ℕ) + 1)).toPsh)
    (hi : (BPSet.serialWedge dims).initVertex ≫ g = (BPSet.cube ((m : ℕ) + 1)).initVertex)
    (hf : (BPSet.serialWedge dims).finalVertex ≫ g = (BPSet.cube ((m : ℕ) + 1)).finalVertex) :
    Ch' K.toPsh (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).init)
      (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).final) :=
  ⟨dims, ⟨g ≫ prismCube m q, by
      rw [BPSet.rebase_init]
      change (prismCube m q).app (op (Box.ob 0))
          (g.app (op (Box.ob 0)) (BPSet.serialWedge dims).init) = _
      rw [app_init_of_initVertex g hi], by
      rw [BPSet.rebase_final]
      change (prismCube m q).app (op (Box.ob 0))
          (g.app (op (Box.ob 0)) (BPSet.serialWedge dims).final) = _
      rw [app_final_of_finalVertex g hf]⟩⟩

/-- The prism cube `R` itself, as a `Ch'`-object over its own corners — the apex of the
cospan, written in the *same* corner-indexed form as the boundary paths via the identity
inclusion `(serialWedgeSingletonIso (m+1)).inv`. -/
noncomputable def prismApex (m : ℕ+) (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    Ch' K.toPsh (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).init)
      (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).final) :=
  prismPathObj m q [m + 1] (serialWedgeSingletonIso (m + 1)).inv
    (serialWedge_singleton_initVertex (m + 1)) (serialWedge_singleton_finalVertex (m + 1))

/-- The **up-then-along** boundary path `P_top` as a `Ch'`-object over the prism cube's
corners. -/
noncomputable def prismPathTop (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    Ch' K.toPsh (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).init)
      (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).final) :=
  prismPathObj m q [1, m] (bdryUpIncl m) (bdryUpIncl_initVertex m) (bdryUpIncl_finalVertex m)

/-- The **along-then-up** boundary path `P_bottom` as a `Ch'`-object over the corners. -/
noncomputable def prismPathBottom (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    Ch' K.toPsh (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).init)
      (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).final) :=
  prismPathObj m q [m, 1] (bdryDownIncl m) (bdryDownIncl_initVertex m) (bdryDownIncl_finalVertex m)

/-- A corner-preserving inclusion into `cube (m+1)`, composed with the singleton iso, preserves
the **initial** corner of the target serial wedge `serialWedge [m+1]`. -/
theorem singletonCornerInit {dims : List ℕ+} {m : ℕ+}
    (g : (BPSet.serialWedge dims).toPsh ⟶ (BPSet.cube ((m : ℕ) + 1)).toPsh)
    (hg : (BPSet.serialWedge dims).initVertex ≫ g = (BPSet.cube ((m : ℕ) + 1)).initVertex) :
    (BPSet.serialWedge dims).initVertex ≫ (g ≫ (serialWedgeSingletonIso (m + 1)).hom)
      = (BPSet.serialWedge [m + 1]).initVertex := by
  rw [← Category.assoc, hg, ← cancel_mono (serialWedgeSingletonIso (m + 1)).inv, Category.assoc,
    serialWedge_singleton_initVertex]
  erw [Iso.hom_inv_id, Category.comp_id]
  norm_cast

/-- The dual of `singletonCornerInit` for the **final** corner. -/
theorem singletonCornerFinal {dims : List ℕ+} {m : ℕ+}
    (g : (BPSet.serialWedge dims).toPsh ⟶ (BPSet.cube ((m : ℕ) + 1)).toPsh)
    (hg : (BPSet.serialWedge dims).finalVertex ≫ g = (BPSet.cube ((m : ℕ) + 1)).finalVertex) :
    (BPSet.serialWedge dims).finalVertex ≫ (g ≫ (serialWedgeSingletonIso (m + 1)).hom)
      = (BPSet.serialWedge [m + 1]).finalVertex := by
  rw [← Category.assoc, hg, ← cancel_mono (serialWedgeSingletonIso (m + 1)).inv, Category.assoc,
    serialWedge_singleton_finalVertex]
  erw [Iso.hom_inv_id, Category.comp_id]
  norm_cast

/-- The refinement `P_top ⟶ R`: the up-then-along boundary inclusion, promoted to a `Ch'`
morphism by the singleton iso (the inclusion factors through `R`'s underlying cube map). -/
noncomputable def prismRefineTop (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    prismPathTop m q ⟶ prismApex m q where
  φ := ⟨bdryUpIncl m ≫ (serialWedgeSingletonIso (m + 1)).hom,
    app_init_of_initVertex (Z := BPSet.serialWedge [m + 1]) _
      (singletonCornerInit (bdryUpIncl m) (bdryUpIncl_initVertex m)),
    app_final_of_finalVertex (Z := BPSet.serialWedge [m + 1]) _
      (singletonCornerFinal (bdryUpIncl m) (bdryUpIncl_finalVertex m))⟩
  w := by
    apply BPSet.hom_ext
    change (bdryUpIncl m ≫ (serialWedgeSingletonIso (m + 1)).hom)
        ≫ (serialWedgeSingletonIso (m + 1)).inv ≫ prismCube m q
      = bdryUpIncl m ≫ prismCube m q
    rw [Category.assoc]
    erw [Iso.hom_inv_id_assoc]

/-- The refinement `P_bottom ⟶ R`: the along-then-up boundary inclusion as a `Ch'` morphism. -/
noncomputable def prismRefineBottom (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    prismPathBottom m q ⟶ prismApex m q where
  φ := ⟨bdryDownIncl m ≫ (serialWedgeSingletonIso (m + 1)).hom,
    app_init_of_initVertex (Z := BPSet.serialWedge [m + 1]) _
      (singletonCornerInit (bdryDownIncl m) (bdryDownIncl_initVertex m)),
    app_final_of_finalVertex (Z := BPSet.serialWedge [m + 1]) _
      (singletonCornerFinal (bdryDownIncl m) (bdryDownIncl_finalVertex m))⟩
  w := by
    apply BPSet.hom_ext
    change (bdryDownIncl m ≫ (serialWedgeSingletonIso (m + 1)).hom)
        ≫ (serialWedgeSingletonIso (m + 1)).inv ≫ prismCube m q
      = bdryDownIncl m ≫ prismCube m q
    rw [Category.assoc]
    erw [Iso.hom_inv_id_assoc]

/-- **The per-block homotopy.**  In `FreeGroupoid (Ch'(a, b))` over the prism cube's two
corners, the zigzag `mk P_bottom → mk R ← mk P_top`, i.e. `of(P_bottom → R) ≫ inv(of(P_top →
R))`, connecting the along-then-up boundary path to the up-then-along boundary path.  This is
the bi-pointed analogue of `singleBlockComp`, now interface-preserving. -/
noncomputable def singleBlockCompB (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh) :
    (FreeGroupoid.of (Ch' K.toPsh _ _)).obj (prismPathBottom m q)
      ⟶ (FreeGroupoid.of (Ch' K.toPsh _ _)).obj (prismPathTop m q) :=
  (FreeGroupoid.of (Ch' K.toPsh _ _)).map (prismRefineBottom m q)
    ≫ Groupoid.inv ((FreeGroupoid.of (Ch' K.toPsh _ _)).map (prismRefineTop m q))

/-- **The empty-block (degenerate) homotopy.**  For a vertex `v : □⁰ ⟶ PathOb K` the prism
cube is the bare vertical edge `□¹` (`emptyBlockPrismB v`), whose two corner-to-corner
boundary paths *both* degenerate to the edge itself — so the per-block zigzag collapses to the
identity automorphism of the edge in `FreeGroupoid (Ch'(v≫e₀, v≫e₁))`.  This is the level-
mismatch bridge: the edge is already the d-path from `v≫e₀` to `v≫e₁`.  (Degenerate analogue
of `singleBlockCompB`; the `□¹` has no nontrivial `2`-cell, hence no zigzag.) -/
noncomputable def emptyBlockCompB (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K.toPsh) :
    (FreeGroupoid.of (Ch' K.toPsh _ _)).obj (emptyBlockPrismB v)
      ⟶ (FreeGroupoid.of (Ch' K.toPsh _ _)).obj (emptyBlockPrismB v) :=
  𝟙 _

/-! ## 5b. The context-whiskering functor (Item 1: horizontal composition of `Ch'`)

This is the precubical analogue of *horizontal composition*: given a `PrecubicalSet` `K`
and two *fixed* chains — a **prefix** `pre : Ch' K s a` and a **suffix** `suf : Ch' K b t` —
post-composing a chain `block : Ch' K a b` by gluing `pre ++ block ++ suf` along the
junction vertices `a`, `b` is a genuine functor `Ch' K a b ⥤ Ch' K s t`.  (It preserves
refinements: the identity refinement is held on the fixed `pre`/`suf` blocks and `f.φ` is
carried on the variable middle block.)  Applying `FreeGroupoid.map` to it carries a *local*
per-block homotopy in `FreeGroupoid (Ch' K a b)` up to the *global* `FreeGroupoid (Ch' K s t)`
— the promotion the staircase needs.

The construction reuses the Segal concatenation machinery `ChainCat.concatWedgeMap`/
`concatHomφ`/`concat_hom_ext`/`wedgeInclL`/`wedgeInclR` verbatim: a `Ch' K a b` object *is* a
`ConcatDesc` over the presheaf `K`, so two applications of `concatWedgeMap` glue the three
chains. -/

namespace Ch'

open ChainCat

/-- A `Ch'` object as a `ConcatDesc` over the underlying presheaf `K`: the underlying wedge
map together with its (definitional) init/final values. -/
def toConcatDesc {K : PrecubicalSet} {a b : K.cells 0} (x : Ch' K a b) :
    ConcatDesc x.dims a b where
  map := x.map.hom
  init_spec := x.map.app_init
  final_spec := x.map.app_final

/-- A `ConcatDesc` over `K` packaged back as a `Ch'` object (the inverse of `toConcatDesc`). -/
noncomputable def ofConcatDesc {K : PrecubicalSet} {a b : K.cells 0} {dims : List ℕ+}
    (d : ConcatDesc dims a b) : Ch' K a b :=
  ⟨dims, ⟨d.map, d.init_spec, d.final_spec⟩⟩

@[simp] theorem ofConcatDesc_dims {K : PrecubicalSet} {a b : K.cells 0} {dims : List ℕ+}
    (d : ConcatDesc dims a b) : (ofConcatDesc d).dims = dims := rfl

@[simp] theorem ofConcatDesc_map_hom {K : PrecubicalSet} {a b : K.cells 0} {dims : List ℕ+}
    (d : ConcatDesc dims a b) : (ofConcatDesc d).map.hom = d.map := rfl

/-- **Object-level context whisker.**  Glue `pre ++ x ++ suf` along the shared junction
vertices `a` (= `pre.final` = `x.init`) and `b` (= `x.final` = `suf.init`), producing a chain
from `s` to `t` in `K`.  Built by two applications of `ChainCat.concatWedgeMap`. -/
noncomputable def whiskerObj {K : PrecubicalSet} {s a b t : K.cells 0}
    (pre : Ch' K s a) (suf : Ch' K b t) (x : Ch' K a b) : Ch' K s t :=
  ofConcatDesc (concatWedgeMap pre.dims pre.toConcatDesc (x.dims ++ suf.dims)
    (concatWedgeMap x.dims x.toConcatDesc suf.dims suf.toConcatDesc))

@[simp] theorem whiskerObj_dims {K : PrecubicalSet} {s a b t : K.cells 0}
    (pre : Ch' K s a) (suf : Ch' K b t) (x : Ch' K a b) :
    (whiskerObj pre suf x).dims = pre.dims ++ (x.dims ++ suf.dims) := rfl

/-- **`K`-internal binary concatenation of `Ch'` *morphisms*.**  Two `Ch'` morphisms
`f : x ⟶ x'` (over `(a, b)`) and `g : y ⟶ y'` (over `(b, t)`) glue, along the shared junction
`b`, to a `Ch'` morphism between the concatenated chains `x ++ y ⟶ x' ++ y'` (over `(a, t)`),
with underlying wedge map the Segal `concatHomφ f g`.  This is the `K`-internal analogue of
`chConcat.map`; the commuting triangle is checked on the two half-inclusions via
`concat_hom_ext`. -/
noncomputable def concatMor {K : PrecubicalSet} {a b t : K.cells 0}
    {x x' : Ch' K a b} {y y' : Ch' K b t} (f : x ⟶ x') (g : y ⟶ y') :
    ofConcatDesc (concatWedgeMap x.dims x.toConcatDesc y.dims y.toConcatDesc)
      ⟶ ofConcatDesc (concatWedgeMap x'.dims x'.toConcatDesc y'.dims y'.toConcatDesc) where
  φ := concatHomφ (X := BPSet.rebase K a b) (Y := BPSet.rebase K b t) f g
  w := by
    apply BPSet.hom_ext
    rw [BPSet.comp_hom]
    refine concat_hom_ext x.dims y.dims _ _ ?_ ?_
    · -- left half: `f.φ` restricted, the triangle `f.w`.
      simp only [ofConcatDesc_map_hom]
      erw [reassoc_of% (concatHomφ_inclL f g), concatWedgeMap_inclL, concatWedgeMap_inclL]
      have hf : f.φ.hom ≫ x'.map.hom = x.map.hom := congrArg (·.hom) f.w
      exact hf
    · -- right half: `g.φ` restricted, the triangle `g.w`.
      simp only [ofConcatDesc_map_hom]
      erw [reassoc_of% (concatHomφ_inclR f g), concatWedgeMap_inclR, concatWedgeMap_inclR]
      have hg : g.φ.hom ≫ y'.map.hom = y.map.hom := congrArg (·.hom) g.w
      exact hg

@[simp] theorem concatMor_φ {K : PrecubicalSet} {a b t : K.cells 0}
    {x x' : Ch' K a b} {y y' : Ch' K b t} (f : x ⟶ x') (g : y ⟶ y') :
    (concatMor f g).φ = concatHomφ (X := BPSet.rebase K a b) (Y := BPSet.rebase K b t) f g := rfl

/-- The identity-on-identities of `concatMor` is the identity. -/
theorem concatMor_id {K : PrecubicalSet} {a b t : K.cells 0}
    (x : Ch' K a b) (y : Ch' K b t) :
    concatMor (𝟙 x) (𝟙 y) = 𝟙 _ := by
  apply ChainCat.hom_ext'
  rw [concatMor_φ]
  exact concatHomφ_id (X := BPSet.rebase K a b) (Y := BPSet.rebase K b t) x y

/-- `concatMor` of composites is the composite of `concatMor`s. -/
theorem concatMor_comp {K : PrecubicalSet} {a b t : K.cells 0}
    {x x' x'' : Ch' K a b} {y y' y'' : Ch' K b t}
    (f₁ : x ⟶ x') (f₂ : x' ⟶ x'') (g₁ : y ⟶ y') (g₂ : y' ⟶ y'') :
    concatMor (f₁ ≫ f₂) (g₁ ≫ g₂) = concatMor f₁ g₁ ≫ concatMor f₂ g₂ := by
  apply ChainCat.hom_ext'
  rw [concatMor_φ, ChainCat.comp_φ, concatMor_φ, concatMor_φ]
  exact concatHomφ_comp (X := BPSet.rebase K a b) (Y := BPSet.rebase K b t) f₁ f₂ g₁ g₂

/-- **Morphism-level context whisker.**  A `Ch'` morphism `f : x ⟶ y` (over `(a, b)`) is
whiskered by the fixed prefix `pre` and suffix `suf` to a `Ch'` morphism between the
concatenated chains, holding the identity on `pre`/`suf` and `f` on the middle block. -/
noncomputable def whiskerMap {K : PrecubicalSet} {s a b t : K.cells 0}
    (pre : Ch' K s a) (suf : Ch' K b t) {x y : Ch' K a b} (f : x ⟶ y) :
    whiskerObj pre suf x ⟶ whiskerObj pre suf y :=
  concatMor (𝟙 pre) (concatMor f (𝟙 suf))

/-- **The context-whiskering functor** `Ch' K a b ⥤ Ch' K s t` (Item 1): prepend the fixed
chain `pre : Ch' K s a` and append `suf : Ch' K b t`.  This is the precubical horizontal
composition; `FreeGroupoid.map` of it promotes a *local* per-block homotopy to the *global*
groupoid. -/
noncomputable def whisker {K : PrecubicalSet} {s a b t : K.cells 0}
    (pre : Ch' K s a) (suf : Ch' K b t) : Ch' K a b ⥤ Ch' K s t where
  obj x := whiskerObj pre suf x
  map f := whiskerMap pre suf f
  map_id x := by
    change concatMor (𝟙 pre) (concatMor (𝟙 x) (𝟙 suf)) = 𝟙 _
    rw [concatMor_id x suf, concatMor_id pre _]
  map_comp f g := by
    change concatMor (𝟙 pre) (concatMor (f ≫ g) (𝟙 suf))
      = concatMor (𝟙 pre) (concatMor f (𝟙 suf)) ≫ concatMor (𝟙 pre) (concatMor g (𝟙 suf))
    rw [← concatMor_comp, Category.comp_id, ← concatMor_comp, Category.comp_id]

end Ch'

/-! ## 5c. Item 2 — the promoted per-block homotopy in the global groupoid

`FreeGroupoid.map (Ch'.whisker pre suf)` carries the *local* per-block homotopy
`singleBlockCompB`/`emptyBlockCompB` — living in `FreeGroupoid (Ch'(block corners))` — up to
the *global* `FreeGroupoid (Ch' K s t)` by whiskering with the fixed prefix `pre` and suffix
`suf` (held at the appropriate cylinder level).  Since `FreeGroupoid.map F` agrees with `F`
on objects through `of` (`of_comp_map`, an equality by `rfl`), the source/target of the
promoted homotopy are the `of`-images of the whiskered boundary-path chains.  This is exactly
the j-th block of the staircase: blocks `< j` are held at level 1 inside `pre`, blocks `> j`
at level 0 inside `suf`, and the level-mismatch at the junction is bridged by the (degenerate)
`emptyBlockCompB`. -/

open Ch' in
/-- **Item 2: the promoted single-block homotopy.**  The per-block zigzag `singleBlockCompB
m q` (`mk P_bottom → mk R ← mk P_top` over the block's corners), whiskered by the fixed
context `pre`/`suf` into the global groupoid `FreeGroupoid (Ch' K.toPsh s t)`. -/
noncomputable def promotedBlockComp {s t : K.toPsh.cells 0} (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh)
    (pre : Ch' K.toPsh s (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).init))
    (suf : Ch' K.toPsh (prismCube m q |>.app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).final)
      t) :
    (FreeGroupoid.of (Ch' K.toPsh s t)).obj (whiskerObj pre suf (prismPathBottom m q))
      ⟶ (FreeGroupoid.of (Ch' K.toPsh s t)).obj (whiskerObj pre suf (prismPathTop m q)) :=
  (FreeGroupoid.map (Ch'.whisker pre suf)).map (singleBlockCompB m q)

/-- **Item 2 (degenerate): the promoted empty-block homotopy is an identity.**  The level-
mismatch bridge `emptyBlockCompB v` is the identity automorphism of the bare vertical edge in
its local groupoid `FreeGroupoid (Ch'(edge corners))`, so its whiskering into *any* target by
`FreeGroupoid.map W` is again an identity (image of an identity under a functor).  (The single-
block `promotedBlockComp` above is the substantive Item-2 datum; this degenerate case is the
abstract identity that the staircase uses at each junction level-mismatch.) -/
theorem promotedEmptyBlockComp_eq_id {D : Type*} [Category D]
    (v : yoneda.obj (Box.ob 0) ⟶ PathOb.obj K.toPsh)
    (W : (Ch' K.toPsh _ _) ⥤ D) :
    (FreeGroupoid.map W).map (emptyBlockCompB v) = 𝟙 _ := by
  unfold emptyBlockCompB
  exact (FreeGroupoid.map W).map_id _

/-! ## 5d. The whole-chain prism apex and its two flat ends as `Ch K` objects

**The finding, and its precise scope (`Testing/CylinderObstruction.lean`).**  The obstruction
recorded in `## 6.` is that the *direct* coface `b₀ → R` of the prism cube fails to preserve
`R`'s far interface corner.  The `native_decide` finding shows `b₀` and `b₁` ARE connected in
the **coarse face-poset** of `Ch K` (`chLe b₀ R = chLe b₁ R = true`, the Lemma-2.11(c)
"every cube is a face of a cube" order).  *However*, the program's groupoid is built on the
**wedge-map** category `ChainCat.Obj K`, whose morphisms are interface-preserving `BPSet` maps
of serial wedges — and the forward functor from the face-poset (`Chains/Correspondence.lean`
`refineToWedge`) is only defined under `NonSelfLinked + AdmitsAltitude`.  A rel-interface
cylinder forces `K` **self-linked** at its basepoints, so that gate is exactly what fails, and
the coarse connectivity does **not** lift to `ChainCat.Hom` cofaces:

* the bottom coface `b₀ → R` (`Box.coface false`, last coord `0`) sends `R`'s all-`1` corner
  preimage to the cube corner `(1,…,1,0)`, NOT to `(serialWedge [m+1]).final = (1,…,1,1)` — so
  it does not preserve the *final* interface (`finalVertexMap m ≫ coface false ≠ finalVertexMap
  (m+1)`);
* the top coface `b₁ → R` (`Box.coface true`) preserves the final corner but symmetrically
  fails the *initial* one (`initVertexMap m ≫ coface true ≠ initVertexMap (m+1)`).

So **each direct coface preserves exactly one of the two interface corners**, hence neither is a
`ChainCat.Hom`.  The connecting zigzag in the *strict* `ChainCat.Obj K` therefore still needs
the boundary-path machinery (`prismRefineTop/Bottom`, green above) for the interior, and the
closing step `b₀ ⇝ P_bottom` remains the genuine open gap (see `## 6.`).

What this section *does* contribute green and sorry-free: the prism cube `R` (`directPrismB`)
and the two flat ends `b₀`/`b₁` (`directEndB`) as honest objects of `ChainCat.Obj K` — the apex
and the two feet of the would-be direct cospan — with their basepoint interfaces verified via
`prism_initCell`/`prism_finalCell` (the prism shares the all-`0`/all-`1` corner cell with its
bottom/top face) and the singleton-iso corner lemmas.  Only the connecting *morphisms* are
absent (and provably so, by the corner computation above). -/

/-- **The prism cube and its bottom face share an init corner (cell form).**  For a block
`p : □ᵈ ⟶ PathOb K`, the all-`0` corner cell of the prism cube `(tauto).prism p` equals the
all-`0` corner cell of its bottom (`e₀`-)face `p ≫ e₀`.  Cell-level form of `prism_vertex₀`
(`(cube N).init = initVertexMap N`). -/
theorem prism_initCell {d : ℕ} (p : yoneda.obj (Box.ob d) ⟶ PathOb.obj K.toPsh) :
    ((CylMap.tauto K.toPsh).prism p).app (op (Box.ob 0)) (BPSet.cube (d + 1)).init
      = (p ≫ (endpoint false).app K.toPsh).app (op (Box.ob 0)) (BPSet.cube d).init := by
  have h := prism_vertex₀ (K := K.toPsh) p
  rw [PrecubicalSet.vertex₀_yonedaEquiv, PrecubicalSet.vertex₀_yonedaEquiv] at h
  exact h

/-- **The prism cube and its top face share a final corner (cell form)** (dual of
`prism_initCell`). -/
theorem prism_finalCell {d : ℕ} (p : yoneda.obj (Box.ob d) ⟶ PathOb.obj K.toPsh) :
    ((CylMap.tauto K.toPsh).prism p).app (op (Box.ob 0)) (BPSet.cube (d + 1)).final
      = (p ≫ (endpoint true).app K.toPsh).app (op (Box.ob 0)) (BPSet.cube d).final := by
  have h := prism_vertex₁ (K := K.toPsh) p
  rw [PrecubicalSet.vertex₁_yonedaEquiv, PrecubicalSet.vertex₁_yonedaEquiv] at h
  exact h

/-- The singleton iso carries the cube's init cell to the wedge's init cell (cell form of
`serialWedge_singleton_initVertex`, `.hom` direction). -/
theorem singletonIso_hom_init (m : ℕ+) :
    (serialWedgeSingletonIso m).hom.app (op (Box.ob 0)) (BPSet.cube (m : ℕ)).init
      = (BPSet.serialWedge [m]).init := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm ((serialWedgeSingletonIso m).hom.app (op (Box.ob 0))
        (BPSet.cube (m : ℕ)).init)
      = (BPSet.cube (m : ℕ)).initVertex ≫ (serialWedgeSingletonIso m).hom from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) (serialWedgeSingletonIso m).hom
      (BPSet.cube (m : ℕ)).init).symm]
  rw [← serialWedge_singleton_initVertex m, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    BPSet.initVertex, BPSet.vertexMap]

/-- The singleton iso carries the cube's final cell to the wedge's final cell. -/
theorem singletonIso_hom_final (m : ℕ+) :
    (serialWedgeSingletonIso m).hom.app (op (Box.ob 0)) (BPSet.cube (m : ℕ)).final
      = (BPSet.serialWedge [m]).final := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm ((serialWedgeSingletonIso m).hom.app (op (Box.ob 0))
        (BPSet.cube (m : ℕ)).final)
      = (BPSet.cube (m : ℕ)).finalVertex ≫ (serialWedgeSingletonIso m).hom from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) (serialWedgeSingletonIso m).hom
      (BPSet.cube (m : ℕ)).final).symm]
  rw [← serialWedge_singleton_finalVertex m, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    BPSet.finalVertex, BPSet.vertexMap]

/-- The inverse singleton iso carries the wedge's init cell to the cube's init cell. -/
theorem singletonIso_inv_init (m : ℕ+) :
    (serialWedgeSingletonIso m).inv.app (op (Box.ob 0)) (BPSet.serialWedge [m]).init
      = (BPSet.cube (m : ℕ)).init := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm ((serialWedgeSingletonIso m).inv.app (op (Box.ob 0))
        (BPSet.serialWedge [m]).init)
      = (BPSet.serialWedge [m]).initVertex ≫ (serialWedgeSingletonIso m).inv from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) (serialWedgeSingletonIso m).inv
      (BPSet.serialWedge [m]).init).symm]
  rw [serialWedge_singleton_initVertex m, BPSet.initVertex, BPSet.vertexMap]

/-- The inverse singleton iso carries the wedge's final cell to the cube's final cell. -/
theorem singletonIso_inv_final (m : ℕ+) :
    (serialWedgeSingletonIso m).inv.app (op (Box.ob 0)) (BPSet.serialWedge [m]).final
      = (BPSet.cube (m : ℕ)).final := by
  apply yonedaEquiv.symm.injective
  rw [show yonedaEquiv.symm ((serialWedgeSingletonIso m).inv.app (op (Box.ob 0))
        (BPSet.serialWedge [m]).final)
      = (BPSet.serialWedge [m]).finalVertex ≫ (serialWedgeSingletonIso m).inv from
    (yonedaEquiv_symm_naturality_right (Box.ob 0) (serialWedgeSingletonIso m).inv
      (BPSet.serialWedge [m]).final).symm]
  rw [serialWedge_singleton_finalVertex m, BPSet.finalVertex, BPSet.vertexMap]

/-- The `ε`-end of a single block `(m, q)` as a genuine `Ch K` object, *given* that its two
corner cells are the basepoints `K.init`/`K.final`.  (For a whole-chain single block
`a : Ch c.src`, `q = a.map.hom ≫ c.cyl`, and these corner conditions hold by construction —
they are exactly `(pushforward c.leftLeg).obj a`'s interface.) -/
noncomputable def directEndB (ε : Bool) (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh)
    (hi : (q ≫ (endpoint ε).app K.toPsh).app (op (Box.ob 0)) (BPSet.serialWedge [m]).init = K.init)
    (hf : (q ≫ (endpoint ε).app K.toPsh).app (op (Box.ob 0)) (BPSet.serialWedge [m]).final
      = K.final) :
    ChainCat.Obj K :=
  ⟨[m], ⟨q ≫ (endpoint ε).app K.toPsh, hi, hf⟩⟩

/-- The prism cube `R` over a single block `(m, q)`, as a genuine `Ch K` object — *given* the
two basepoint conditions on the `ε = false`/`true` ends (the same data feeding `directEndB`).
Its init/final corners are the basepoints because the prism cube shares them with its
bottom/top faces (`prism_initCell`/`prism_finalCell`). -/
noncomputable def directPrismB (m : ℕ+)
    (q : (BPSet.serialWedge [m]).toPsh ⟶ PathOb.obj K.toPsh)
    (hi₀ : (q ≫ (endpoint false).app K.toPsh).app (op (Box.ob 0))
        (BPSet.serialWedge [m]).init = K.init)
    (hf₁ : (q ≫ (endpoint true).app K.toPsh).app (op (Box.ob 0))
        (BPSet.serialWedge [m]).final = K.final) :
    ChainCat.Obj K :=
  ⟨[m + 1], ⟨(serialWedgeSingletonIso (m + 1)).inv ≫ prismCube m q,
    by
      -- init corner = prism init = bottom-face init = flat-end init = K.init.
      change ((serialWedgeSingletonIso (m + 1)).inv ≫ prismCube m q).app (op (Box.ob 0))
          (BPSet.serialWedge [m + 1]).init = K.init
      rw [show ((serialWedgeSingletonIso (m + 1)).inv ≫ prismCube m q).app (op (Box.ob 0))
            (BPSet.serialWedge [m + 1]).init
          = (prismCube m q).app (op (Box.ob 0)) ((serialWedgeSingletonIso (m + 1)).inv.app
              (op (Box.ob 0)) (BPSet.serialWedge [m + 1]).init) from rfl]
      rw [show (serialWedgeSingletonIso (m + 1)).inv.app (op (Box.ob 0))
            (BPSet.serialWedge [m + 1]).init = (BPSet.cube ((m : ℕ) + 1)).init from
        singletonIso_inv_init (m + 1)]
      rw [show (prismCube m q).app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).init
          = ((CylMap.tauto K.toPsh).prism ((serialWedgeSingletonIso m).hom ≫ q)).app
              (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).init from rfl]
      erw [prism_initCell ((serialWedgeSingletonIso m).hom ≫ q)]
      rw [Category.assoc]
      erw [show ((serialWedgeSingletonIso m).hom ≫ q ≫ (endpoint false).app K.toPsh).app
            (op (Box.ob 0)) (BPSet.cube (m : ℕ)).init
          = (q ≫ (endpoint false).app K.toPsh).app (op (Box.ob 0))
              ((serialWedgeSingletonIso m).hom.app (op (Box.ob 0)) (BPSet.cube (m : ℕ)).init) from
        rfl]
      rw [singletonIso_hom_init m]
      exact hi₀,
    by
      change ((serialWedgeSingletonIso (m + 1)).inv ≫ prismCube m q).app (op (Box.ob 0))
          (BPSet.serialWedge [m + 1]).final = K.final
      rw [show ((serialWedgeSingletonIso (m + 1)).inv ≫ prismCube m q).app (op (Box.ob 0))
            (BPSet.serialWedge [m + 1]).final
          = (prismCube m q).app (op (Box.ob 0)) ((serialWedgeSingletonIso (m + 1)).inv.app
              (op (Box.ob 0)) (BPSet.serialWedge [m + 1]).final) from rfl]
      rw [show (serialWedgeSingletonIso (m + 1)).inv.app (op (Box.ob 0))
            (BPSet.serialWedge [m + 1]).final = (BPSet.cube ((m : ℕ) + 1)).final from
        singletonIso_inv_final (m + 1)]
      rw [show (prismCube m q).app (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).final
          = ((CylMap.tauto K.toPsh).prism ((serialWedgeSingletonIso m).hom ≫ q)).app
              (op (Box.ob 0)) (BPSet.cube ((m : ℕ) + 1)).final from rfl]
      erw [prism_finalCell ((serialWedgeSingletonIso m).hom ≫ q)]
      rw [Category.assoc]
      erw [show ((serialWedgeSingletonIso m).hom ≫ q ≫ (endpoint true).app K.toPsh).app
            (op (Box.ob 0)) (BPSet.cube (m : ℕ)).final
          = (q ≫ (endpoint true).app K.toPsh).app (op (Box.ob 0))
              ((serialWedgeSingletonIso m).hom.app (op (Box.ob 0)) (BPSet.cube (m : ℕ)).final) from
        rfl]
      rw [singletonIso_hom_final m]
      exact hf₁⟩⟩

/-!
## 6. What is now in place, and the one remaining piece (`toTransf`, the staircase)

**Done, green, and sorry-free in this file (the irreducible reusable heart):**

* *The boundary-path geometry* (the hard combinatorics).  `bdryUpIncl`/`bdryDownIncl` —
  the two corner-to-corner boundary paths `serialWedge [1,m] ⟶ cube (m+1)` and
  `serialWedge [m,1] ⟶ cube (m+1)` of the prism cube — built by `pushout.desc` of a flat
  coface against a *vertical prism edge* `yoneda.map (Box.shift.map (cornerMap m ε))`.  The
  cocone junctions reduce to **`Box.coface`-naturality squares** (`corner_coface_nat`) once
  the all-`ε` corner of `□¹` is identified with the `ε`-end coface (`cornerMap_one`) — this
  is the lever that dissolves the would-be cell-level grind into a one-line naturality.
  Their corner preservation (`bdryUpIncl_init/finalVertex`, `bdryDownIncl_init/finalVertex`)
  uses `initVertexMap_succ`/`finalVertexMap_succ` (`cornerMap_succ_*`).

* *The per-block cospan in `Ch'`.*  All three chains — the prism cube `R` (`prismApex`) and
  the two boundary paths (`prismPathTop`/`prismPathBottom`) — are objects of *one*
  `Ch' K a b` over the cube's two corners `prismCube … (cube (m+1)).init/.final`, packaged by
  `prismPathObj` (the corner conditions discharged by `app_init/final_of_initVertex`).  The
  two boundary-path refinements `prismRefineTop`/`prismRefineBottom : P_• ⟶ R` are genuine
  `Ch'` morphisms (the singleton-iso cancels in the commuting triangle; the interface is
  preserved because both boundary paths share `R`'s corners — `singletonCornerInit/Final`).

* *The per-block homotopies.*  `singleBlockCompB = of(P_bottom→R) ≫ inv(of(P_top→R))`, the
  zigzag `mk P_bottom → mk R ← mk P_top` in `FreeGroupoid (Ch'(a,b))` (the bi-pointed,
  interface-preserving analogue of `singleBlockComp`); and `emptyBlockCompB`, the degenerate
  `m = 0` case where the prism cube is the bare edge `□¹` whose two boundary paths coincide,
  so the zigzag collapses to the identity (the level-mismatch bridge).

**§5b — Item 1 (the context-whiskering functor) is now DONE, green, sorry-free.**  For a fixed
prefix `pre : Ch' K s a` and suffix `suf : Ch' K b t`, `Ch'.whisker pre suf : Ch' K a b ⥤
Ch' K s t` glues `pre ++ block ++ suf` along the shared junction vertices `a`, `b`.  It is the
precubical *horizontal composition*, built by reusing the Segal concatenation machinery
(`ChainCat.concatWedgeMap`/`concatHomφ`/`concat_hom_ext`/`wedgeInclL`/`wedgeInclR`) verbatim
through the bridge `Ch'.toConcatDesc`/`ofConcatDesc` (a `Ch'` object *is* a `ConcatDesc` over
the presheaf `K`).  The morphism action is `Ch'.concatMor` (the `K`-internal binary
concatenation of `Ch'` morphisms, `id`-on-fixed-pieces and `f` on the middle), with
`concatMor_id`/`concatMor_comp` discharging functoriality.  `FreeGroupoid.map (Ch'.whisker
pre suf)` is the promotion functor.

**§5c — Item 2 (the promoted per-block homotopy) is now DONE, green, sorry-free.**
`promotedBlockComp m q pre suf := (FreeGroupoid.map (Ch'.whisker pre suf)).map
(singleBlockCompB m q)` carries the *local* per-block zigzag up to the *global*
`FreeGroupoid (Ch' K.toPsh s t)`; `of_comp_map` (rfl) identifies its endpoints with the
`of`-images of the whiskered boundary-path chains.  The degenerate level-mismatch bridge is
`promotedEmptyBlockComp_eq_id` (the whiskered `emptyBlockCompB` is an identity).

**§5d — the prism apex `directPrismB` and the two flat ends `directEndB` as `Ch K` objects:
green, sorry-free.**  These bundle the prism cube `R` and the flat chain ends `b₀`/`b₁` as
honest `ChainCat.Obj K` objects, with the basepoint interfaces discharged by
`prism_initCell`/`prism_finalCell` + `singletonIso_*`.  See §5d for the precise (and now
corrected) scope of the `CylinderObstruction` finding.

**Items 3–5 — the staircase fold, `toTransf`, `cylToPointedB` — remain deferred as data.**
By `FreeGroupoid.liftNatIso` + `ofCompMapIso`, `c.toTransf : c.Lgrpd ⟶ c.Rgrpd` reduces to a
natural iso `(Ch.map c.leftLeg).toFunctor ⋙ of  ≅  (Ch.map c.rightLeg).toFunctor ⋙ of` of
functors `Ch c.src ⥤ FreeGroupoid (Ch K)`, whose component at `a = (dims, p)` is the
**staircase zigzag** `zigzagB dims p : of (dims, p≫leftLeg) ⟶ of (dims, p≫rightLeg)` in
`FreeGroupoid (Ch K)`.

With Items 1–2 in hand the *interior* of the staircase — the `P_bottom → R ← P_top` cospans —
is fully expressible: the j-th step is `promotedBlockComp d_j q_j pre_j suf_j` (with
`q_j = ιⱼ ≫ p ≫ cyl`, `pre_j` the level-1 chain of blocks `<j`, `suf_j` the level-0 chain of
blocks `>j`), junction level-mismatches bridged by `promotedEmptyBlockComp_eq_id`.

**The precise remaining obstacle — and why the `CylinderObstruction` finding does NOT remove it
for the strict `ChainCat.Obj K`.**  The `native_decide` finding (`Testing/CylinderObstruction.lean`)
shows `b₀`,`b₁` are connected in the **coarse face-poset** (`chLe`, Lemma 2.11(c)).  But the
groupoid here is `FreeGroupoid (ChainCat.Obj K)`, over the **wedge-map** category, and the
forward functor face-poset → wedge-maps (`Chains/Correspondence.lean` `refineToWedge`) is gated
on `NonSelfLinked + AdmitsAltitude`.  A rel-interface cylinder forces `K` **self-linked**, so
the gate fails and the coarse connectivity does *not* lift to `ChainCat.Hom`s.  Concretely
(now verified by the §5d corner computation):

* the **direct** cofaces `b₀ → R` / `b₁ → R` each preserve exactly **one** of `R`'s two
  interface corners (bottom coface keeps init, loses final; top coface keeps final, loses init —
  `finalVertexMap m ≫ coface false ≠ finalVertexMap (m+1)`, and dually).  So neither direct
  coface is a `ChainCat.Hom`, and the direct cospan `b₀ → R ← b₁` does **not** exist strictly;
* the boundary paths dissolve this for the *interior* (`prismRefineTop/Bottom : P_• → R` ARE
  `ChainCat.Hom`s, because `P_top`/`P_bottom` run *corner-to-corner* of the cube and so share
  `R`'s interface), but the **closing step** `b₀ ⇝ P_bottom` reintroduces it: a refinement
  `b₀ → P_bottom` is a `Ch K` map `serialWedge [m] ⟶ serialWedge [m,1]`, and `wedgeInclL` sends
  `[m]`'s **final** vertex to the *junction* of `[m,1]` (not its final, across the trailing
  edge) — not interface-preserving;
* the trailing/leading edge is the prism over the chain's final/initial corner — a `□¹`-loop at
  the basepoint `K.final`/`K.init`.  The rel-interface forces its two *ends* equal (a self-loop)
  but NOT that it is *constant*; collapsing it onto the flat end needs a **degeneracy**, absent
  from `PrecubicalSet = Boxᵒᵖ ⥤ Type` (symmetry-free, no degeneracies).  So the closing step
  cannot be a single refinement.

So the honest status is: **Items 3–5 are blocked on the closing-end step, which is genuinely
obstructed in the strict wedge-map `ChainCat.Obj K` (self-linked `K` ⟹ no interface-preserving
closing map, no degeneracy to collapse the trailing self-loop).**  The `CylinderObstruction`
finding establishes coarse-poset (`chLe`/π₀) connectivity, but that is *strictly weaker* than
a zigzag of `ChainCat.Hom`s and does not transfer through the NSL-gated correspondence.  A
route to `θ` would require either (a) building the d-path groupoid on the *refinement* category
`RefineObj` (where the direct cofaces DO live, unconditionally, via `ChainRefine`) and porting
`Lgrpd`/`Rgrpd`/`pointedOfTransf` to it — a larger refactor touching `Chains/Category.lean`
and the leg-functors, outside this file's edit scope — or (b) a genuinely new closing-end
construction that this symmetry-free topos appears not to admit.

All the plumbing of the surrounding program — the d-path groupoid, the rel-interface cylinder
maps, the leg-functors, the cylinder-map category and its weak-equivalence full subcategory,
the per-block objects and corner kernel, the full boundary-path geometry, the per-block cospan
and homotopies, the context-whiskering functor (Item 1), the promoted per-block homotopy
(Item 2), and the whole-chain prism apex/feet objects (§5d) — is in place and proved.  The
single remaining gap is the **closing-end step**, obstructed as above; `toTransf` and
`cylToPointedB` remain deferred as data (NOT `sorry`'d).
-/
