import CubeChains.Chains.CoordFunctor
import CubeChains.Chains.ChainSkeletal

/-!
# Chains/CoordCorrespondence — reindexing without transport

The indexing content of `Chains/Correspondence`, reorganized so the "boring" part (which bead maps
where) separates cleanly from the mathematics (`descent_mono`, reused unchanged).

**Part 1 — the coordinate action.**  `coordWedge a : Coord↓(⋁a) ≃ Σ i, Fin aᵢ` flattens the wedge's
coordinates; a wedge map acts by the coend functoriality of `cotensorLift Coord`, and that action
*is* the block data of `BlockDecomp`:

    coordWedgeAction f ⟨i, k⟩ = ⟨blockIdx f i, faceEmb (blockFace f i) k⟩

— target block and free-coordinate embedding from one functorial gadget.  `Coord↓` cannot see a
face's fill (`faceEmb` forgets the `0/1` on collapsed coordinates); the full `blockFace` needs `K`.

**Part 2 — the `Fin`-indexed subdivision.**  `Subdiv a b` is `ChainRefine` indexed on `a.dims`
directly rather than on `wedgeToCubes` lists (whose length is only *propositionally* `dims.length`).
That single change deletes the `eqToHom`/`Fin.cast` transport that dominates
`Correspondence.wedgeToRefineMap`/`refineWedgeMap`: the backward map is `blockIdx`/`blockFace`
verbatim, the forward map is `wedgeDescHom` of the induced cells, and `Subdiv a b ≃ (a ⟶ b)` follows
from `descent_mono` (imported) plus `Ch K`-thinness.  Face uniqueness (`wedge_face_heq`) is a mono
cancellation in `⋁b.dims` — no `NonSelfLinked`, unlike `refineObj_hom_subsingleton`.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet ChainCat

namespace CubeChains

/-! ### The coordinate functor on a cube face -/

/-- **The coend functoriality of `Coord` along a cube face is `faceEmb`.**  On the coordinate
generator `(coordCube m).symm k`, the lift of `yoneda.map g` is the free-coordinate embedding —
co-Yoneda naturality made pointwise. -/
theorem coordCube_map_yoneda {m m' : ℕ} (g : ▫m ⟶ ▫m') (k : Fin m) :
    Cotensor.map Coord (yoneda.map g) ((coordCube m).symm k)
      = (coordCube m').symm (faceEmb g k) := by
  simp only [coordCube]
  refine (Cotensor.cubeEquiv Coord m').eq_symm_apply.mpr ?_
  rw [Cotensor.cubeEquiv_naturality, Coord_map_apply]
  exact congrArg (faceEmb g) ((Cotensor.cubeEquiv Coord m).apply_symm_apply k)

/-! ### The coordinate action of a wedge map -/

/-- **The coordinate action of a wedge map** `⋁a ⟶ ⋁b`: how it permutes/embeds the flattened
coordinates, `Σ i, Fin aᵢ → Σ j, Fin bⱼ`.  It is `cotensorLift Coord` conjugated by `coordWedge`. -/
def coordWedgeAction {a b : List ℕ+} (f : ⋁a ⟶ ⋁b) :
    (Σ i : Fin a.length, Fin ((a.get i : ℕ))) → Σ j : Fin b.length, Fin ((b.get j : ℕ)) :=
  fun p => coordWedge b ((cotensorLift Coord).map f ((coordWedge a).symm p))

/-- **The bridge: the coordinate action is the block data.**  Coordinate `k` of bead `i` goes to
coordinate `faceEmb (blockFace f i) k` of the target block `blockIdx f i`.  The block restriction
`blockFace_spec` transported through the coend functoriality, then re-read by co-Yoneda
(`coordCube_map_yoneda`, `coordWedge_apply_map`). -/
theorem coordWedgeAction_apply {a b : List ℕ+} (f : ⋁a ⟶ ⋁b)
    (i : Fin a.length) (k : Fin ((a.get i : ℕ))) :
    coordWedgeAction f ⟨i, k⟩ = ⟨blockIdx f.hom i, faceEmb (blockFace f.hom i) k⟩ := by
  -- The block restriction `ιᵢ ≫ f = yoneda(blockFace) ≫ ι_(blockIdx)` (`blockFace_spec`), read on
  -- the coordinate generator.  Composition steps use explicit `.trans`/`congrArg` terms (default
  -- transparency) to sidestep the `(□m).toPsh` vs `yoneda ▫m` spelling gap that blocks `rw`.
  have key : Cotensor.map Coord f.hom
        (Cotensor.map Coord (ιᵂ a i) ((coordCube (a.get i : ℕ)).symm k))
      = Cotensor.map Coord (ιᵂ b (blockIdx f.hom i))
          ((coordCube (b.get (blockIdx f.hom i) : ℕ)).symm (faceEmb (blockFace f.hom i) k)) :=
    (Cotensor.map_map Coord (ιᵂ a i) f.hom _).trans
      ((congrArg (fun m => Cotensor.map Coord m ((coordCube (a.get i : ℕ)).symm k))
          (blockFace_spec f.hom i)).trans
        (((Cotensor.map_map Coord (yoneda.map (blockFace f.hom i))
              (ιᵂ b (blockIdx f.hom i)) _).symm).trans
          (congrArg (Cotensor.map Coord (ιᵂ b (blockIdx f.hom i)))
            (coordCube_map_yoneda (blockFace f.hom i) k))))
  change coordWedge b ((cotensorLift Coord).map f ((coordWedge a).symm ⟨i, k⟩)) = _
  rw [coordWedge_symm_apply, cotensorLift_map_apply, key]
  exact coordWedge_apply_map b (blockIdx f.hom i) (faceEmb (blockFace f.hom i) k)

/-- **The block index is the first coordinate.**  The `Coord↓` reindexing recovers `blockIdx` with
no transport — the coordinate a bead carries is irrelevant to which block it lands in. -/
@[simp] theorem coordWedgeAction_fst {a b : List ℕ+} (f : ⋁a ⟶ ⋁b)
    (i : Fin a.length) (k : Fin ((a.get i : ℕ))) :
    (coordWedgeAction f ⟨i, k⟩).1 = blockIdx f.hom i := by
  rw [coordWedgeAction_apply]

/-- **Functoriality is free.**  The coordinate action is a functor into `Type`, so it respects
composition — no chain induction, just `cotensorLift Coord`'s own `map_comp`. -/
theorem coordWedgeAction_comp {a b c : List ℕ+} (f : ⋁a ⟶ ⋁b) (g : ⋁b ⟶ ⋁c) :
    coordWedgeAction (f ≫ g) = coordWedgeAction g ∘ coordWedgeAction f := by
  funext p
  simp only [coordWedgeAction, Function.comp_apply, Functor.map_comp, types_comp_apply,
    Equiv.symm_apply_apply]

/-- **The identity acts trivially.** -/
@[simp] theorem coordWedgeAction_id (a : List ℕ+) :
    coordWedgeAction (𝟙 (⋁a)) = id := by
  funext p
  simp only [coordWedgeAction, CategoryTheory.Functor.map_id, types_id_apply,
    Equiv.apply_symm_apply, id_eq]

/-- **The reindexing is monotone** — beads never reorder.  Read off the bridge: the first
coordinate of the action is `blockIdx`, monotone by the serial wedge's own altitude
(`serialWedge_blockIdx_monotone`), needing nothing about the ambient set. -/
theorem coordWedgeAction_fst_monotone {a b : List ℕ+} (f : ⋁a ⟶ ⋁b) :
    Monotone (fun i : Fin a.length => (coordWedgeAction f ⟨i, ⟨0, (a.get i).pos⟩⟩).1) := by
  simp only [coordWedgeAction_fst]
  exact serialWedge_blockIdx_monotone f.hom f.app_init

/-! ## A `Fin`-indexed subdivision — the clean form of a refinement

`Chains/Refine.ChainRefine` is phrased on `wedgeToCubes` lists, whose length is only
*propositionally* `dims.length`; every use of it in `Chains/Correspondence` pays an
`eqToHom`/`Fin.cast` transport (`wedgeToRefineMap` is ~100 lines of it).  Indexing a subdivision on
`a.dims` directly removes it wholesale: the reindexing *is* `blockIdx`, the face *is* `blockFace`,
`Fin a.dims.length`-typed on the nose.  `descent_mono` (the sole geometric input) is imported
unchanged; nothing here reproves it. -/

section Subdiv
variable {K : BPSet}

/-- The `i`-th cube of a chain, read off its classifying map. -/
def chainBead (a : Ch K) (i : Fin a.dims.length) : K.cells (a.dims.get i : ℕ) :=
  yonedaEquiv (ιᵂ a.dims i ≫ a.map.hom)

/-- A **subdivision** `a ⟶ b`: a monotone reindexing of `a`'s beads into `b`'s, and per `a`-bead a
`Box`-face into its target `b`-bead pulling that bead back — i.e. a morphism of `K`'s category of
elements.  The `Fin`-indexed `ChainRefine` (no `wedgeToCubes` transport). -/
structure Subdiv (a b : Ch K) where
  /-- Which `b`-bead each `a`-bead refines. -/
  reindex : Fin a.dims.length → Fin b.dims.length
  /-- Refinements never reorder beads. -/
  reindex_mono : Monotone reindex
  /-- The face of the target `b`-bead that the `a`-bead is. -/
  face : ∀ i, ▫(a.dims.get i : ℕ) ⟶ ▫(b.dims.get (reindex i) : ℕ)
  /-- Pulling the `b`-bead back along the face recovers the `a`-bead (compatibility in `K`). -/
  faceSpec : ∀ i, chainBead a i = K.toPsh.map (face i).op (chainBead b (reindex i))

/-- **Reading a subdivision off a chain map — the clean backward map.**  Reindexing `= blockIdx`,
face `= blockFace`, both `Fin a.dims.length`-typed with no cast; `faceSpec` is the block
factorization `blockFace_spec` fed through the triangle `g ≫ b = a`.  Replaces
`Chains/Correspondence.wedgeToRefineMap` (~106 lines). -/
def Subdiv.ofHom {a b : Ch K} (g : a ⟶ b) : Subdiv a b where
  reindex := blockIdx gᵂ
  reindex_mono := serialWedge_blockIdx_monotone gᵂ g.φ.app_init
  face := blockFace gᵂ
  faceSpec i := by
    have hw : gᵂ ≫ b.map.hom = a.map.hom := by
      have h := congrArg BPSet.Hom.hom g.w; rwa [comp_hom] at h
    have htri : ιᵂ a.dims i ≫ a.map.hom
        = yoneda.map (blockFace gᵂ i) ≫ (ιᵂ b.dims (blockIdx gᵂ i) ≫ b.map.hom) := by
      rw [← hw, ← Category.assoc, blockFace_spec gᵂ i]; exact Category.assoc _ _ _
    show yonedaEquiv (ιᵂ a.dims i ≫ a.map.hom)
      = K.toPsh.map (blockFace gᵂ i).op (yonedaEquiv (ιᵂ b.dims (blockIdx gᵂ i) ≫ b.map.hom))
    calc yonedaEquiv (ιᵂ a.dims i ≫ a.map.hom)
        = yonedaEquiv (yoneda.map (blockFace gᵂ i)
            ≫ (ιᵂ b.dims (blockIdx gᵂ i) ≫ b.map.hom)) := congrArg yonedaEquiv htri
      _ = K.toPsh.map (blockFace gᵂ i).op
            (yonedaEquiv (ιᵂ b.dims (blockIdx gᵂ i) ≫ b.map.hom)) :=
          (yonedaEquiv_naturality _ _).symm

/-! ### The forward map: a subdivision descends to a chain map

The `a`-bead's face carried into its target `b`-block gives a cell of `⋁b.dims`
(`inducedCell`); pushed through `b`'s classifying map these recover `a`'s cubes
(`descent_inducedCell`), so `descent_mono` (the sole geometric input, imported) lifts `a`'s chain
into `⋁b.dims`, and `wedgeDescHom` assembles the wedge map. -/

/-- The cell of `⋁b.dims` that `a`-bead `i` becomes: its face into block `reindex i`. -/
def Subdiv.inducedCell {a b : Ch K} (s : Subdiv a b) (i : Fin a.dims.length) :
    (⋁b.dims).cells (a.dims.get i : ℕ) :=
  yonedaEquiv (yoneda.map (s.face i) ≫ ιᵂ b.dims (s.reindex i))

/-- **The induced cell pushes to the `a`-bead** under `b`'s classifying map — `faceSpec` read
through co-Yoneda. -/
theorem Subdiv.descent_inducedCell {a b : Ch K} (s : Subdiv a b) (i : Fin a.dims.length) :
    b.map.hom⟪(a.dims.get i : ℕ)⟫ (s.inducedCell i) = chainBead a i :=
  calc b.map.hom⟪(a.dims.get i : ℕ)⟫ (s.inducedCell i)
      = yonedaEquiv ((yoneda.map (s.face i) ≫ ιᵂ b.dims (s.reindex i)) ≫ b.map.hom) :=
        (yonedaEquiv_comp _ b.map.hom).symm
    _ = yonedaEquiv (yoneda.map (s.face i) ≫ (ιᵂ b.dims (s.reindex i) ≫ b.map.hom)) :=
        congrArg yonedaEquiv (Category.assoc _ _ _)
    _ = K.toPsh.map (s.face i).op (yonedaEquiv (ιᵂ b.dims (s.reindex i) ≫ b.map.hom)) :=
        (yonedaEquiv_naturality _ _).symm
    _ = chainBead a i := (s.faceSpec i).symm

/-- The induced cells, `Fin a.dims.length`-indexed; their dimension sequence is `a.dims`. -/
def Subdiv.inducedCells {a b : Ch K} (s : Subdiv a b) :
    List (Σ n : ℕ+, (⋁b.dims).cells (n : ℕ)) :=
  List.ofFn fun i : Fin a.dims.length => ⟨a.dims.get i, s.inducedCell i⟩

theorem Subdiv.inducedCells_dims {a b : Ch K} (s : Subdiv a b) :
    s.inducedCells.map (·.1) = a.dims := by
  rw [Subdiv.inducedCells, List.map_ofFn]
  conv_rhs => rw [← List.ofFn_get a.dims]
  rfl

/-- Pushing the induced cells through `b`'s classifying map recovers `a`'s cubes. -/
theorem Subdiv.inducedCells_descent {a b : Ch K} (s : Subdiv a b) :
    s.inducedCells.map (fun c => ⟨c.1, b.map.hom⟪(c.1 : ℕ)⟫ c.2⟩)
      = wedgeToCubes ⟨a.dims, a.map.hom⟩ := by
  rw [Subdiv.inducedCells, List.map_ofFn, wedgeToCubes_eq_ofFn]
  exact congrArg List.ofFn (funext fun i => Sigma.ext rfl (heq_of_eq (s.descent_inducedCell i)))

/-- **The induced cells form a chain in `⋁b.dims`.**  Reflected through `b`'s classifying map:
that map is injective (`descent_mono` — the one hypothesis-carrying input), sends the induced cells
to `a`'s cubes, so the chain descends from `a` by `isCubeChain_of_map_injective`. -/
theorem Subdiv.inducedChain {a b : Ch K} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (s : Subdiv a b) :
    IsCubeChain (⋁b.dims).init s.inducedCells (⋁b.dims).final := by
  have hinj : ∀ n, Function.Injective (b.map.hom⟪n⟫) := fun n =>
    (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp (descent_mono h₁ h₂ b) (op ▫n))
  refine isCubeChain_of_map_injective b.map.hom hinj s.inducedCells _ _ ?_
  rw [b.map.app_init, b.map.app_final, s.inducedCells_descent]
  have h := wedgeToCubes_isCubeChain a.dims a.map.hom
  rwa [a.map.app_init, a.map.app_final] at h

/-- **A subdivision descends to a chain map — the clean forward map.**  `wedgeDescHom` assembles the
induced cells (a chain by `inducedChain`) into the wedge map; the triangle over `K` is that both
sides read off the same cubes.  Replaces `Chains/Correspondence.refineWedgeMap` (+ `inducedCell`,
`inducedChain`, `refineWedgeMap_w`, ~190 lines). -/
def Subdiv.toHom {a b : Ch K} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (s : Subdiv a b) :
    a ⟶ b where
  φ := eqToHom (congrArg BPSet.serialWedge s.inducedCells_dims.symm)
    ≫ wedgeDescHom s.inducedCells (s.inducedChain h₁ h₂)
  w := by
    apply bpset_hom_ext_of_wedgeToCubes
    simp only [comp_hom, bpset_eqToHom_hom, Category.assoc]
    refine (wedgeToCubes_eqToHom s.inducedCells_dims.symm
      ((wedgeDescHom s.inducedCells (s.inducedChain h₁ h₂)).hom ≫ b.map.hom)).trans ?_
    exact (wedgeToCubes_wedgeDesc_comp b.map.hom (⋁b.dims).init (⋁b.dims).final
      s.inducedCells (s.inducedChain h₁ h₂)).trans s.inducedCells_descent

/-! ### The two maps are inverse — the clean equivalence -/

/-- Reading the cubes off the induced wedge map recovers the induced cells. -/
theorem Subdiv.toHom_wedgeToCubes {a b : Ch K} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (s : Subdiv a b) :
    wedgeToCubes ⟨a.dims, (s.toHom h₁ h₂)ᵂ⟩ = s.inducedCells := by
  show wedgeToCubes ⟨a.dims, (eqToHom (congrArg BPSet.serialWedge s.inducedCells_dims.symm)
      ≫ wedgeDescHom s.inducedCells (s.inducedChain h₁ h₂)).hom⟩ = s.inducedCells
  rw [comp_hom, bpset_eqToHom_hom, wedgeToCubes_eqToHom s.inducedCells_dims.symm
    (wedgeDescHom s.inducedCells (s.inducedChain h₁ h₂)).hom]
  exact wedgeToCubes_wedgeDescHom s.inducedCells (s.inducedChain h₁ h₂)

/-- **The induced wedge map factors bead `i` through its target block via `s.face i`** — the
defining property of `toHom`, read back off `toHom_wedgeToCubes`. -/
theorem Subdiv.toHom_block {a b : Ch K} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (s : Subdiv a b) (i : Fin a.dims.length) :
    ιᵂ a.dims i ≫ (s.toHom h₁ h₂)ᵂ = yoneda.map (s.face i) ≫ ιᵂ b.dims (s.reindex i) := by
  apply yonedaEquiv.injective
  have hread := s.toHom_wedgeToCubes h₁ h₂
  rw [wedgeToCubes_eq_ofFn] at hread
  have hi := congrFun (List.ofFn_inj.mp hread) i
  exact eq_of_heq (Sigma.ext_iff.1 hi).2

/-- Extensionality for subdivisions: reindexing and face data (the rest are `Prop`s). -/
theorem Subdiv.ext {a b : Ch K} {s t : Subdiv a b} (hr : s.reindex = t.reindex)
    (hf : ∀ i, s.face i ≍ t.face i) : s = t := by
  obtain ⟨sr, _, sf, _⟩ := s
  obtain ⟨tr, _, tf, _⟩ := t
  obtain rfl : sr = tr := hr
  obtain rfl : sf = tf := funext fun i => eq_of_heq (hf i)
  rfl

/-- **A block-face is pinned by its image in the serial wedge.**  Two faces into the *same* block
that agree after the block inclusion are equal — cancel the mono `ιᵂ`, then `yoneda` is faithful.
No `NonSelfLinked`: the serial wedge supplies the injectivity directly (contrast
`Chains/Correspondence.refineObj_hom_subsingleton`, which needs `K`). -/
theorem wedge_face_heq {dims : List ℕ+} {m : ℕ} {j j' : Fin dims.length} (hj : j = j')
    {f : ▫m ⟶ ▫((dims.get j : ℕ))} {g : ▫m ⟶ ▫((dims.get j' : ℕ))}
    (h : yoneda.map f ≫ ιᵂ dims j = yoneda.map g ≫ ιᵂ dims j') : f ≍ g := by
  subst hj
  haveI : Mono (ιᵂ dims j) := by
    rw [NatTrans.mono_iff_mono_app]; rintro ⟨X⟩; rw [mono_iff_injective]
    exact serialWedge_ι_app_injective dims j
  exact heq_of_eq (yoneda.map_injective ((cancel_mono (ιᵂ dims j)).mp h))

/-- **Round-trip: reading a subdivision off its own descent recovers it.**  Reindex is pinned by
`blockIdx_eq_of_factor`, the face by `wedge_face_heq` — the block factorization run backwards. -/
theorem Subdiv.ofHom_toHom {a b : Ch K} (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude)
    (s : Subdiv a b) : Subdiv.ofHom (s.toHom h₁ h₂) = s := by
  have hidx : ∀ i, blockIdx (s.toHom h₁ h₂)ᵂ i = s.reindex i := fun i =>
    (blockIdx_eq_of_factor (s.toHom h₁ h₂)ᵂ i (s.reindex i) (s.face i) (s.toHom_block h₁ h₂ i)).symm
  exact Subdiv.ext (funext hidx) fun i =>
    wedge_face_heq (hidx i)
      ((blockFace_spec (s.toHom h₁ h₂)ᵂ i).symm.trans (s.toHom_block h₁ h₂ i))

/-- **The clean morphism equivalence.**  `Subdiv a b ≃ (a ⟶ b)`: `toHom`/`ofHom` are inverse —
`ofHom_toHom` one way, `Ch K`-thinness (`chainCat_hom_subsingleton`) the other.  This is the
morphism half of `equivWedgeCat`, rebuilt with no read-off-cube transport. -/
def Subdiv.equivHom (h₁ : K.NonSelfLinked) (h₂ : K.AdmitsAltitude) (a b : Ch K) :
    Subdiv a b ≃ (a ⟶ b) where
  toFun := Subdiv.toHom h₁ h₂
  invFun := Subdiv.ofHom
  left_inv := Subdiv.ofHom_toHom h₁ h₂
  right_inv _ := by haveI := chainCat_hom_subsingleton h₁ h₂ a b; exact Subsingleton.elim _ _

end Subdiv

end CubeChains
