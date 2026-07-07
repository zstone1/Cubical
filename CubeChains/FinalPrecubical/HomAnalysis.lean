import CubeChains.FinalPrecubical.SerialNSL

/-!
# FinalPrecubical/HomAnalysis — the wedge-map classification (`BRAID2_PLAN.md` §2.4)

The hom-level classification of wedge maps between serial wedges (`BRAID2_PLAN.md` §2.4),
the intended replacement for the `ev`/`ev_reconstruct`/`evValid_exists` tower of `Ev.lean`.
The target is the `Equiv`

```
homEquiv A B : (serialWedge A ⟶ serialWedge B) ≃
    Σ bm : {m : Fin A.length → Fin B.length // Monotone m},
      Π j : Fin B.length, OwnerData (fibreShape A bm.1 j) (B.get j)
```

decomposing a wedge map into a **monotone block map** `bm` (which target block each source
block lands in) plus, per target block `j`, an **ordered set partition** of `Fin (B.get j)`
of shape `fibreShape A bm j` (the sub-list of `A`'s blocks with `bm i = j`).

## What is delivered here (green, sorry-free)

* **`blockMap g` / `blockMap_spec`** — the monotone block map together with, per source block
  `i`, the face inclusion `incl : □^{A.get i} ↪ □^{B.get (blockMap g i)}` witnessing
  `ι_i ≫ g = yoneda.map incl ≫ ι_{blockMap g i}`.
* **`blockMap_monotone` / `blockMap_surjective` / `blockMap_eq_blockIdx`** — `blockMap` is a
  monotone *surjection* (hence hits every target block), reconciled with `Ev.blockIdx`.
* **`fibreShape` + `fibre` interval structure** — the per-target-block sub-shape of `A`; the
  fibre index list is strictly sorted with consecutive elements differing by `1`
  (`fibre_getElem_succ`), the geometric contiguity behind the block decomposition.
* **`serialWedge_vertex_meet`** — the **boundary-alignment structural lemma** (`§Risk R2`): two
  *distinct* blocks of a serial wedge meet on vertices only at the junction
  `final_{j₁} = init_{j₂}`.  Proved by induction on `B` from `glue0_isPullback_app` +
  `cube_init_ne_final`.  With `entry_vertex`/`exit_vertex` and `serialWedge_init_ι`/`final_ι`
  this pins the block sub-chain's endpoints.
* **`isCubeChain_pullback`** — a chain descends along a cellwise-injective map (here `ι_B j`).
* **THE OBJECT-LEVEL SEGAL DECOMPOSITION** (`BRAID2_PLAN.md` §2.4 target):
  - **`blockCubes g j`** — the block-`j` cubes of the ambient chain, pulled back through `ι_B j`
    (dims `= fibreShape A (blockMap g) j`, via `blockCubes_dims`);
  - **`blockCubes_isCubeChain g j : IsCubeChain init_j (blockCubes g j) final_j`** — the block-`j`
    cubes form an `init → final` chain *inside* `cube (B.get j)`.  Internal junctions from
    `Ev.evCell_junction`; boundaries from the vertex-meet lemma; descent by `isCubeChain_pullback`;
  - **`blockChainObj g j : RefineObj …`** and
    **`blockOwnerData g j : OwnerData (fibreShape A (blockMap g) j) (B.get j)`** (via
    `CubeChainPoset.chainOwnerData`).

## What remains (the full `Σ`-assembly `homEquiv`)

Packaging `⟨blockMap g, fun j => blockOwnerData g j⟩` into the `Equiv` `homEquiv A B` and its
inverse (assemble per-block `cornerChain`s, descend by `wedgeDescHom`) plus the two round-trips
(inheritable from `refineObjEquivOSP` + `wedgeToCubes_inj`) and functoriality
(`homEquiv_id`/`homEquiv_comp`) is future work; the object-level decomposition delivered here is
its per-target-block core.

**Layer:** FinalPrecubical.  **Imports:** `FinalPrecubical.SerialNSL` (which supplies
`serialWedge_nonSelfLinked` and transitively `CubeChainPoset`/`Correspondence`/`WedgeMap`).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace FinalPrecubical

open BPSet CubeChain PrecubicalSet

/-! ## Part 0. The top chain and a wedge map as an object of `Ch(serialWedge B)` -/

/-- The **top `B`-chain**: the identity wedge map of `serialWedge B`, viewed as an object of
`Ch(serialWedge B)` (its shape is `B`, the generic chain of one cube per block). -/
noncomputable def topChain (B : List ℕ+) : ChainCat.Obj (BPSet.serialWedge B) :=
  ⟨B, 𝟙 _⟩

@[simp] theorem topChain_dims (B : List ℕ+) : (topChain B).dims = B := rfl

/-- A wedge map `serialWedge A ⟶ serialWedge B` as an **object of `Ch(serialWedge B)`** of
shape `A` (since `serialWedge B` is terminal *within its own chain category*, a chain in it
of shape `A` is literally a map out of `serialWedge A`). -/
def objOfHom {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) :
    ChainCat.Obj (BPSet.serialWedge B) := ⟨A, g⟩

@[simp] theorem objOfHom_dims {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) : (objOfHom g).dims = A := rfl

@[simp] theorem objOfHom_map {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) : (objOfHom g).map = g := rfl

/-- The **unique morphism** from `objOfHom g` to the top chain in `Ch(serialWedge B)`: the
wedge map `g` itself, whose triangle over `serialWedge B` is `g ≫ 𝟙 = g`. -/
def homToTop {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) :
    objOfHom g ⟶ topChain B :=
  ⟨g, Category.comp_id g⟩

/-! ## Part 1. The block map and its monotonicity -/

/-- **The block map.**  Source block `i` ↦ its unique target block: the block of
`serialWedge B` that the block restriction `ι_i ≫ g` lands in (`WedgeMap.wedgeMap_block`).
By construction it comes with the face inclusion witnessing the landing (`blockMap_spec`). -/
noncomputable def blockMap {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) : Fin A.length → Fin B.length := fun i =>
  (wedgeMap_block g.hom i).choose

/-- **Block factoring of a wedge map.**  The `i`-th block restriction `ι_i ≫ g` factors as a
face inclusion `incl` into block `blockMap g i` — directly the specification of the
`wedgeMap_block` choice.  This is the raw datum the forward classification reads per block. -/
theorem blockMap_spec {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (i : Fin A.length) :
    ∃ incl : Box.ob (A.get i : ℕ) ⟶ Box.ob (B.get (blockMap g i) : ℕ),
      BPSet.serialWedge.ι A i ≫ g.hom
        = yoneda.map incl ≫ BPSet.serialWedge.ι B (blockMap g i) :=
  (wedgeMap_block g.hom i).choose_spec

/-- **The block map agrees with `wedgeToRefineMap`'s reindexing** (both are the
`wedgeMap_block` choice, definitionally, up to the read-off length recasts).  This is the
bridge that transports `refinementMono` onto `blockMap`. -/
theorem blockMap_val {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (k : Fin A.length) :
    (blockMap g k).val
      = ((wedgeToRefineMap (homToTop g) (BPSet.serialWedge_admitsAltitude B)).refinement
          (Fin.cast (wedgeToCubes_length A g.hom).symm k)).val := by
  have hidx : (Fin.cast (wedgeToCubes_length A g.hom).symm k).cast
      (wedgeToCubes_length A g.hom) = k := Fin.ext (by simp)
  change ((wedgeMap_block g.hom k).choose).val = _
  conv_rhs => rw [show
    (wedgeToRefineMap (homToTop g) (BPSet.serialWedge_admitsAltitude B)).refinement
        (Fin.cast (wedgeToCubes_length A g.hom).symm k)
      = ((wedgeMap_block g.hom ((Fin.cast (wedgeToCubes_length A g.hom).symm k).cast
          (wedgeToCubes_length A g.hom))).choose).cast
          (wedgeToCubes_length B (topChain B).map.hom).symm from rfl]
  rw [hidx]
  simp

/-- **The block map is monotone.**  Inherited from `wedgeToRefineMap`'s `refinementMono`
(needs only that `serialWedge B` admits an altitude), through `blockMap_val`. -/
theorem blockMap_monotone {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) : Monotone (blockMap g) := by
  intro i j hij
  rw [Fin.le_def, blockMap_val g i, blockMap_val g j]
  have hmono := (wedgeToRefineMap (homToTop g)
    (BPSet.serialWedge_admitsAltitude B)).refinementMono
      (Fin.cast (wedgeToCubes_length A g.hom).symm i)
      (Fin.cast (wedgeToCubes_length A g.hom).symm j)
      (by rw [Fin.le_def]; simp only [Fin.val_cast]; exact hij)
  rw [Fin.le_def] at hmono
  exact hmono

/-! ## Part 2. The fibre shape -/

/-- **Fibre of the block map over target block `j`**: the sub-list of `A`'s blocks (in order)
that land in `j`.  Its length is the number of source blocks mapping to `j`; its `l`-th entry
is the dimension of the `l`-th such source block. -/
def fibreShape (A : List ℕ+) {B : List ℕ+}
    (bm : Fin A.length → Fin B.length) (j : Fin B.length) : List ℕ+ :=
  ((List.finRange A.length).filter (fun i => decide (bm i = j))).map (fun i => A.get i)

/-- The fibre shape is `A.get` applied to the filtered index list. -/
theorem fibreShape_eq (A : List ℕ+) {B : List ℕ+}
    (bm : Fin A.length → Fin B.length) (j : Fin B.length) :
    fibreShape A bm j
      = ((List.finRange A.length).filter (fun i => decide (bm i = j))).map (fun i => A.get i) :=
  rfl

/-- The length of the fibre shape is the number of source blocks landing in `j`. -/
theorem fibreShape_length (A : List ℕ+) {B : List ℕ+}
    (bm : Fin A.length → Fin B.length) (j : Fin B.length) :
    (fibreShape A bm j).length
      = ((List.finRange A.length).filter (fun i => decide (bm i = j))).length := by
  rw [fibreShape, List.length_map]

/-! ## Part 3. Reconciling `blockMap` with `Ev.blockIdx`

`HomAnalysis.blockMap g` (the `wedgeMap_block`-choice) and `Ev.blockIdx g` (the
`serialWedge_cell_exists`-choice) are the *same* function (both are the unique target
block a source block factors into), but only *propositionally* equal (each is a distinct
`Classical.choose`).  We reconcile them once and then reuse the whole `Ev` block toolbox
(`blockFace`, `blockFace_spec`, `blockIdx_monotone`, `ev_blocks`) for the decomposition. -/

/-- **`blockMap` agrees with `Ev.blockIdx`.**  Both classify the unique target block of a
source block; `blockMap_spec`'s inclusion realises `evCell g i` in block `blockMap g i`, so
`blockIdx_eq_of` pins the two together. -/
theorem blockMap_eq_blockIdx {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (i : Fin A.length) :
    blockMap g i = blockIdx g i := by
  obtain ⟨incl, hspec⟩ := blockMap_spec g i
  symm
  refine blockIdx_eq_of g i (blockMap g i) (yonedaEquiv (yoneda.map incl)) ?_
  have key := congrArg yonedaEquiv hspec
  rw [yonedaEquiv_comp] at key
  exact key.symm

/-- **`blockMap` is surjective.**  Every target block `r` is hit: the source block of the
preimage (under the event bijection `evPerm`) of a block-`r` event maps to `r`
(`ev_blocks`). -/
theorem blockMap_surjective {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) : Function.Surjective (blockMap g) := by
  intro r
  set t := globalEquiv B ⟨r, ⟨0, (B.get r).pos⟩⟩ with ht
  refine ⟨((globalEquiv A).symm ((evPerm g).symm t)).1, ?_⟩
  rw [blockMap_eq_blockIdx]
  have h := ev_blocks g t
  rw [h, ht, Equiv.symm_apply_apply]

/-- **`blockMap` is monotone** (via `Ev.blockIdx_monotone` and the reconciliation). -/
theorem blockMap_monotone' {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) : Monotone (blockMap g) := by
  intro i i' hii'
  rw [blockMap_eq_blockIdx, blockMap_eq_blockIdx]
  exact blockIdx_monotone g hii'

/-! ## Part 4. The pulled-back block cell -/

/-- **The block-`j` cube cell of source block `i`** (valid when `blockIdx g i = j`): the
face `blockFace g i` transported along `h` into `cube (B.get j)`. -/
noncomputable def blockCellAt {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) {i : Fin A.length} {j : Fin B.length}
    (h : blockIdx g i = j) : (BPSet.cube (B.get j : ℕ)).toPsh.cells (A.get i : ℕ) :=
  cast (congrArg (fun r : Fin B.length => (BPSet.cube (B.get r : ℕ)).toPsh.cells (A.get i : ℕ)) h)
    (blockFace g i)

/-- **Defining property of `blockCellAt`**: the block inclusion `ι_B j` sends it to
`evCell g i` (the `i`-th block restriction of `g`). -/
theorem blockCellAt_spec {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) {i : Fin A.length} {j : Fin B.length}
    (h : blockIdx g i = j) :
    (BPSet.serialWedge.ι B j).app (op (Box.ob (A.get i : ℕ))) (blockCellAt g h) = evCell g i := by
  subst h
  simp only [blockCellAt, cast_eq]
  exact blockFace_spec g i

/-! ## Part 5. The block-`j` cube list -/

/-- **The block-`j` cubes of a wedge map.**  The source blocks landing in target block `j`
(in order), each pulled back through `ι_B j` to a cube of `cube (B.get j)`.  Contiguous
because `blockMap` is monotone; its dimension sequence is `fibreShape A (blockMap g) j`. -/
noncomputable def blockCubes {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length) :
    List (Σ n : ℕ+, (BPSet.cube (B.get j : ℕ)).toPsh.cells (n : ℕ)) :=
  ((List.finRange A.length).filter (fun i => decide (blockMap g i = j))).pmap
    (fun i (h : blockMap g i = j) =>
      (⟨A.get i, blockCellAt g ((blockMap_eq_blockIdx g i).symm.trans h)⟩ :
        Σ n : ℕ+, (BPSet.cube (B.get j : ℕ)).toPsh.cells (n : ℕ)))
    (fun _ hi => of_decide_eq_true (List.mem_filter.mp hi).2)

/-- The dimension sequence of `blockCubes g j` is exactly the fibre shape. -/
theorem blockCubes_dims {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length) :
    (blockCubes g j).map (·.1) = fibreShape A (blockMap g) j := by
  rw [blockCubes, fibreShape, List.map_pmap, List.pmap_eq_map]

/-! ## Part 6. The serial-wedge vertex-meet structural lemma

The genuine geometric content behind the boundary alignment of `blockCubes` (`BRAID2_PLAN.md`
§Risk R2): two **distinct** blocks of a serial wedge can only share a vertex at the junction
`final_{j₁} = init_{j₂}`, and only when they are adjacent.  We package the fact used at
boundaries: if the `ι`-images of two blocks `j₁ < j₂` coincide on vertices, the source
block's vertex is its `final`, the target block's is its `init`. -/

/-- The point map `□⁰ ⟶ X` selecting `v` sends the (unique) `0`-cell of `□⁰` to `v`. -/
theorem vertexMap_app_pt {X : PrecubicalSet} (v : X.cells 0)
    (pt : (yoneda.obj (Box.ob 0)).obj (op (Box.ob 0))) :
    (BPSet.vertexMap X v).app (op (Box.ob 0)) pt = v := by
  have hpt : pt = 𝟙 (Box.ob 0) := stdPre0_subsingleton.elim pt (𝟙 (Box.ob 0))
  rw [hpt, BPSet.vertexMap, PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply, op_id, X.map_id]
  rfl

/-- `X.finalVertex` sends the point of `□⁰` to `X.final`. -/
theorem finalVertex_app_pt (X : BPSet) (pt : (yoneda.obj (Box.ob 0)).obj (op (Box.ob 0))) :
    X.finalVertex.app (op (Box.ob 0)) pt = X.final :=
  vertexMap_app_pt X.final pt

/-- `X.initVertex` sends the point of `□⁰` to `X.init`. -/
theorem initVertex_app_pt (X : BPSet) (pt : (yoneda.obj (Box.ob 0)).obj (op (Box.ob 0))) :
    X.initVertex.app (op (Box.ob 0)) pt = X.init :=
  vertexMap_app_pt X.init pt

/-- **A cube of positive dimension has distinct `init` and `final` vertices.** -/
theorem cube_init_ne_final (n : ℕ) (hn : 0 < n) :
    (BPSet.cube n).init ≠ (BPSet.cube n).final := by
  intro h
  have h2 : StdCube.constVertex n false = StdCube.constVertex n true := by
    have hh := congrArg toStar h
    rwa [show (BPSet.cube n).init = StdCube.canonicalMap (StdCube.constVertex n false) from rfl,
      show (BPSet.cube n).final = StdCube.canonicalMap (StdCube.constVertex n true) from rfl,
      toStar_canonicalMap, toStar_canonicalMap] at hh
  have hval := congrArg (fun w : StdCube.cells n 0 => w.val ⟨0, hn⟩) h2
  simp [StdCube.constVertex] at hval

/-- **Only block `0` of a serial wedge contains its initial vertex.**  A positive-indexed
block's `ι`-image, being an `inr`-cell, can hit `init = inl`-cell only via the glued point,
forcing `final = init` of the head cube — impossible. -/
theorem serialWedge_ι_ne_init_of_pos : ∀ (B : List ℕ+) (s : Fin B.length) (_hs : 0 < (s : ℕ))
    (v : (BPSet.cube (B.get s : ℕ)).toPsh.cells 0),
    (BPSet.serialWedge.ι B s).app (op (Box.ob 0)) v ≠ (BPSet.serialWedge B).init
  | [], s, _, _ => s.elim0
  | n :: rest, s, hs, v => by
    obtain ⟨p, rfl⟩ : ∃ p : Fin rest.length, s = p.succ := by
      have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
      exact ⟨s.pred hs0, (Fin.succ_pred s hs0).symm⟩
    intro heq
    rw [serialWedge_ι_succ_app] at heq
    have hinit : (BPSet.serialWedge (n :: rest)).init
        = (pushout.inl (BPSet.cube (n : ℕ)).finalVertex
            (BPSet.serialWedge rest).initVertex).app (op (Box.ob 0)) (BPSet.cube (n : ℕ)).init := rfl
    rw [hinit] at heq
    obtain ⟨pt, hf, _hg⟩ := Types.exists_of_isPullback
      (wedge2_isPullback_app (BPSet.cube (n : ℕ)) (BPSet.serialWedge rest) 0)
      (BPSet.cube (n : ℕ)).init ((BPSet.serialWedge.ι rest p).app (op (Box.ob 0)) v) heq.symm
    rw [finalVertex_app_pt] at hf
    exact cube_init_ne_final (n : ℕ) n.pos hf.symm

/-- From `ι_B s v = init` with `s = 0`, the vertex is the head cube's `init`. -/
theorem serialWedge_ι_init_eq (B : List ℕ+) (s : Fin B.length) (hs : (s : ℕ) = 0)
    (v : (BPSet.cube (B.get s : ℕ)).toPsh.cells 0)
    (h : (BPSet.serialWedge.ι B s).app (op (Box.ob 0)) v = (BPSet.serialWedge B).init) :
    v = (BPSet.cube (B.get s : ℕ)).init := by
  have hB : 0 < B.length := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hs0 : s = ⟨0, hB⟩ := Fin.ext hs
  clear hs
  subst hs0
  rw [serialWedge_init_ι B hB] at h
  exact serialWedge_ι_app_injective B ⟨0, hB⟩ h

/-- **The vertex-meet structural lemma.**  If the `ι`-images of two blocks `j₁ < j₂` of a
serial wedge agree on vertices `u`, `v`, then `u` is the source block's `final` and `v` is the
target block's `init` (the blocks meet only at the junction).  This is the boundary-alignment
crux (`BRAID2_PLAN.md` §Risk R2). -/
theorem serialWedge_vertex_meet : ∀ (B : List ℕ+) (j₁ j₂ : Fin B.length)
    (u : (BPSet.cube (B.get j₁ : ℕ)).toPsh.cells 0)
    (v : (BPSet.cube (B.get j₂ : ℕ)).toPsh.cells 0),
    (BPSet.serialWedge.ι B j₁).app (op (Box.ob 0)) u
        = (BPSet.serialWedge.ι B j₂).app (op (Box.ob 0)) v →
    (j₁ : ℕ) < (j₂ : ℕ) →
    u = (BPSet.cube (B.get j₁ : ℕ)).final ∧ v = (BPSet.cube (B.get j₂ : ℕ)).init
  | [], j₁, _ => j₁.elim0
  | n :: rest, j₁, j₂ => by
    refine Fin.cases ?_ (fun q => ?_) j₁ <;> refine Fin.cases ?_ (fun p => ?_) j₂ <;>
      intro u v h hlt
    · -- j₁ = 0, j₂ = 0
      simp only [Fin.val_zero, lt_self_iff_false] at hlt
    · -- j₁ = 0, j₂ = p.succ
      have hB_rest : 0 < rest.length := Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt
      rw [serialWedge_ι_zero_app, serialWedge_ι_succ_app] at h
      obtain ⟨pt, hf, hg⟩ := Types.exists_of_isPullback
        (wedge2_isPullback_app (BPSet.cube (n : ℕ)) (BPSet.serialWedge rest) 0)
        u ((BPSet.serialWedge.ι rest p).app (op (Box.ob 0)) v) h
      rw [finalVertex_app_pt] at hf
      rw [initVertex_app_pt] at hg
      refine ⟨hf.symm, ?_⟩
      rcases Nat.eq_zero_or_pos (p : ℕ) with hp0 | hppos
      · exact serialWedge_ι_init_eq rest p hp0 v hg.symm
      · exfalso
        have heq' : (BPSet.serialWedge.ι rest ⟨0, hB_rest⟩).app (op (Box.ob 0))
              (BPSet.cube (rest.get ⟨0, hB_rest⟩ : ℕ)).init
            = (BPSet.serialWedge.ι rest p).app (op (Box.ob 0)) v :=
          (serialWedge_init_ι rest hB_rest).symm.trans hg
        obtain ⟨hbad, _⟩ := serialWedge_vertex_meet rest ⟨0, hB_rest⟩ p
          (BPSet.cube (rest.get ⟨0, hB_rest⟩ : ℕ)).init v heq' hppos
        exact cube_init_ne_final _ (rest.get ⟨0, hB_rest⟩).pos hbad
    · -- j₁ = q.succ, j₂ = 0
      simp only [Fin.val_zero, Fin.val_succ] at hlt
      omega
    · -- j₁ = q.succ, j₂ = p.succ
      rw [serialWedge_ι_succ_app, serialWedge_ι_succ_app] at h
      have hinr := wedge2_inr_app_injective (BPSet.cube (n : ℕ)) (BPSet.serialWedge rest) h
      have hqp : (q : ℕ) < (p : ℕ) := by simp only [Fin.val_succ] at hlt; omega
      exact serialWedge_vertex_meet rest q p u v hinr hqp

/-! ## Part 7. Pulling a chain back along an injective map -/

/-- **Pullback of a cube chain along a cellwise-injective map.**  If `F : M ↪ Z` is injective
on cells and the `F`-images of `L` form a chain from `F a` to `F b`, then `L` itself is a chain
from `a` to `b`.  (`F` is natural, so the vertex conditions transfer back through injectivity.)
This is how a block sub-chain, once known to be a chain *inside* `serialWedge B`, descends to a
chain inside the single cube. -/
theorem isCubeChain_pullback {M : BPSet} {Z : PrecubicalSet} (F : M.toPsh ⟶ Z)
    (hFinj : ∀ {m : ℕ}, Function.Injective (F.app (op (Box.ob m)))) :
    ∀ (a b : M.toPsh.cells 0) (L : List (Σ n : ℕ+, M.toPsh.cells (n : ℕ))),
      IsCubeChain (F.app (op (Box.ob 0)) a)
          (L.map (fun c => ⟨c.1, F.app (op (Box.ob (c.1 : ℕ))) c.2⟩)) (F.app (op (Box.ob 0)) b) →
      IsCubeChain a L b
  | a, b, [], h => by
      simp only [List.map_nil] at h
      exact hFinj h
  | a, b, ⟨n, c⟩ :: rest, h => by
      simp only [List.map_cons] at h
      obtain ⟨hsrc, hrest⟩ := h
      refine ⟨?_, ?_⟩
      · apply hFinj
        rw [map_vertex₀]
        exact hsrc
      · refine isCubeChain_pullback F (@hFinj) (M.toPsh.vertex₁ c) b rest ?_
        rw [map_vertex₁]
        exact hrest

/-! ## Part 8. The fibre index list and its interval structure -/

/-- The (sorted) list of source-block indices landing in target block `j`. -/
noncomputable def fibre {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (j : Fin B.length) : List (Fin A.length) :=
  (List.finRange A.length).filter (fun i => decide (blockMap g i = j))

theorem fibre_mem {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (j : Fin B.length) (i : Fin A.length) : i ∈ fibre g j ↔ blockMap g i = j := by
  rw [fibre, List.mem_filter]
  simp [List.mem_finRange]

/-- `blockCubes` is the `pmap` over the fibre index list. -/
theorem blockCubes_eq_pmap {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length) :
    blockCubes g j = (fibre g j).pmap
      (fun i (h : blockMap g i = j) =>
        (⟨A.get i, blockCellAt g ((blockMap_eq_blockIdx g i).symm.trans h)⟩ :
          Σ n : ℕ+, (BPSet.cube (B.get j : ℕ)).toPsh.cells (n : ℕ)))
      (fun _ hi => of_decide_eq_true (List.mem_filter.mp hi).2) := rfl

theorem blockCubes_length {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length) :
    (blockCubes g j).length = (fibre g j).length := by
  rw [blockCubes_eq_pmap, List.length_pmap]

/-- The fibre index list is strictly sorted. -/
theorem fibre_sortedLT {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (j : Fin B.length) : (fibre g j).SortedLT :=
  List.Pairwise.sortedLT (List.Pairwise.sublist List.filter_sublist
    (List.sortedLT_finRange A.length).pairwise)

/-- Every fibre element has block `j`. -/
theorem fibre_getElem_block {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length)
    (k : ℕ) (hk : k < (fibre g j).length) : blockMap g ((fibre g j)[k]) = j :=
  (fibre_mem g j _).mp (List.getElem_mem hk)

/-- Consecutive fibre indices differ by exactly `1` (the fibre is an interval, since
`blockMap` is monotone and surjective). -/
theorem fibre_getElem_succ {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length)
    (k : ℕ) (hk1 : k + 1 < (fibre g j).length) :
    ((fibre g j)[k + 1] : ℕ) = ((fibre g j)[k]'(Nat.lt_of_succ_lt hk1) : ℕ) + 1 := by
  have hk := Nat.lt_of_succ_lt hk1
  have hsort := fibre_sortedLT g j
  have hlt : ((fibre g j)[k]'hk : ℕ) < ((fibre g j)[k + 1] : ℕ) :=
    hsort.getElem_lt_getElem_iff.mpr (Nat.lt_succ_self k)
  by_contra hne
  have hmid : ((fibre g j)[k]'hk : ℕ) + 1 < A.length := by
    have := ((fibre g j)[k + 1] : Fin A.length).isLt; omega
  set mid : Fin A.length := ⟨((fibre g j)[k]'hk : ℕ) + 1, hmid⟩ with hmid_def
  have hmidval : (mid : ℕ) = ((fibre g j)[k]'hk : ℕ) + 1 := rfl
  have hmidb : blockMap g mid = j := by
    have h1 := fibre_getElem_block g j k hk
    have h2 := fibre_getElem_block g j (k + 1) hk1
    have hle1 : (fibre g j)[k]'hk ≤ mid := Fin.le_def.mpr (by rw [hmidval]; omega)
    have hle2 : mid ≤ (fibre g j)[k + 1] := Fin.le_def.mpr (by rw [hmidval]; omega)
    have hm1 := blockMap_monotone' g hle1
    have hm2 := blockMap_monotone' g hle2
    rw [h1] at hm1; rw [h2] at hm2
    exact le_antisymm hm2 hm1
  obtain ⟨m, hm, hmeq⟩ := List.mem_iff_getElem.mp ((fibre_mem g j mid).mpr hmidb)
  have hkm : k < m := (hsort.getElem_lt_getElem_iff (hi := hk) (hj := hm)).mp (by
    rw [hmeq]; exact Fin.lt_def.mpr (by rw [hmidval]; omega))
  have hmk1 : m < k + 1 := (hsort.getElem_lt_getElem_iff (hi := hm) (hj := hk1)).mp (by
    rw [hmeq]; exact Fin.lt_def.mpr (by rw [hmidval]; omega))
  omega

/-! ## Part 9. Block-map endpoints and ambient chain endpoints -/

theorem blockMap_zero {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (hA : 0 < A.length) (hB : 0 < B.length) : (blockMap g ⟨0, hA⟩ : ℕ) = 0 := by
  obtain ⟨i, hi⟩ := blockMap_surjective g ⟨0, hB⟩
  have hmono := blockMap_monotone' g
    (show (⟨0, hA⟩ : Fin A.length) ≤ i from Fin.le_def.mpr (Nat.zero_le _))
  rw [hi, Fin.le_def] at hmono
  have hz : ((⟨0, hB⟩ : Fin B.length) : ℕ) = 0 := rfl
  omega

theorem blockMap_last {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (hA : 0 < A.length) (hB : 0 < B.length) :
    (blockMap g ⟨A.length - 1, by omega⟩ : ℕ) = B.length - 1 := by
  obtain ⟨i, hi⟩ := blockMap_surjective g ⟨B.length - 1, by omega⟩
  have hia : ((⟨A.length - 1, by omega⟩ : Fin A.length) : ℕ) = A.length - 1 := rfl
  have hib : ((⟨B.length - 1, by omega⟩ : Fin B.length) : ℕ) = B.length - 1 := rfl
  have hmono := blockMap_monotone' g
    (show i ≤ (⟨A.length - 1, by omega⟩ : Fin A.length) from
      Fin.le_def.mpr (by have := i.isLt; omega))
  rw [hi, Fin.le_def] at hmono
  have := (blockMap g ⟨A.length - 1, by omega⟩).isLt
  omega

/-- The ambient chain of `g` starts at the initial vertex of `serialWedge B`. -/
theorem vertex₀_evCell_zero {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (hA : 0 < A.length) :
    (BPSet.serialWedge B).toPsh.vertex₀ (evCell g ⟨0, hA⟩) = (BPSet.serialWedge B).init := by
  have h1 : (BPSet.serialWedge A).toPsh.vertex₀ (yonedaEquiv (BPSet.serialWedge.ι A ⟨0, hA⟩))
      = (BPSet.serialWedge A).init := by
    rw [vertex₀_yonedaEquiv, show (PrecubicalSet.initVertexMap (A.get ⟨0, hA⟩ : ℕ))
      = (BPSet.cube (A.get ⟨0, hA⟩ : ℕ)).init from rfl]
    exact (serialWedge_init_ι A hA).symm
  rw [evCell, yonedaEquiv_comp, ← map_vertex₀, h1, g.app_init]

/-- The ambient chain of `g` ends at the final vertex of `serialWedge B`. -/
theorem vertex₁_evCell_last {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (hA : 0 < A.length) :
    (BPSet.serialWedge B).toPsh.vertex₁ (evCell g ⟨A.length - 1, by omega⟩)
      = (BPSet.serialWedge B).final := by
  have h1 : (BPSet.serialWedge A).toPsh.vertex₁
      (yonedaEquiv (BPSet.serialWedge.ι A ⟨A.length - 1, by omega⟩))
      = (BPSet.serialWedge A).final := by
    rw [vertex₁_yonedaEquiv, show (PrecubicalSet.finalVertexMap (A.get ⟨A.length - 1, by omega⟩ : ℕ))
      = (BPSet.cube (A.get ⟨A.length - 1, by omega⟩ : ℕ)).final from rfl]
    exact (serialWedge_final_ι A hA).symm
  rw [evCell, yonedaEquiv_comp, ← map_vertex₁, h1, g.app_final]

/-! ## Part 10. Boundary alignment of the block chain -/

/-- The block-`j` cube cell of source block `i`, targeted at `blockMap g i` (via the
`blockMap`/`blockIdx` reconciliation). -/
noncomputable def bcell {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (i : Fin A.length) : (BPSet.cube (B.get (blockMap g i) : ℕ)).toPsh.cells (A.get i : ℕ) :=
  blockCellAt g ((blockMap_eq_blockIdx g i).symm)

theorem bcell_spec {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (i : Fin A.length) :
    (BPSet.serialWedge.ι B (blockMap g i)).app (op (Box.ob (A.get i : ℕ))) (bcell g i)
      = evCell g i :=
  blockCellAt_spec g _

/-- **Entry alignment.**  The source vertex of the first block-`j` cube of the ambient chain is
`ι_B j` applied to the initial vertex of `cube (B.get j)`. -/
theorem entry_vertex {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (j : Fin B.length) (hpos : 0 < (fibre g j).length) :
    (BPSet.serialWedge B).toPsh.vertex₀ (evCell g ((fibre g j)[0]'hpos))
      = (BPSet.serialWedge.ι B j).app (op (Box.ob 0)) (BPSet.cube (B.get j : ℕ)).init := by
  have hB : 0 < B.length := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hlob : blockMap g ((fibre g j)[0]'hpos) = j := fibre_getElem_block g j 0 hpos
  have hlo := ((fibre g j)[0]'hpos).isLt
  have hA : 0 < A.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hlo
  rcases Nat.eq_zero_or_pos (((fibre g j)[0]'hpos : Fin A.length) : ℕ) with hlo0 | hlopos
  · -- first ambient cube: starts at the global init
    have hloeq : ((fibre g j)[0]'hpos : Fin A.length) = ⟨0, hA⟩ := Fin.ext hlo0
    have hj0 : (j : ℕ) = 0 := by rw [← hlob, hloeq]; exact blockMap_zero g hA hB
    have hjeq : j = ⟨0, hB⟩ := Fin.ext hj0
    rw [hloeq, vertex₀_evCell_zero g hA, hjeq, serialWedge_init_ι B hB]
  · -- interior boundary: use the vertex-meet lemma at the previous block
    set lo := ((fibre g j)[0]'hpos : Fin A.length) with hlo_def
    have hlo1lt : (lo : ℕ) - 1 < A.length := by omega
    set lo1 : Fin A.length := ⟨(lo : ℕ) - 1, hlo1lt⟩ with hlo1_def
    have hlo1succ : (lo1 : ℕ) + 1 < A.length := by simp only [hlo1_def]; omega
    have hidx : (⟨(lo1 : ℕ) + 1, hlo1succ⟩ : Fin A.length) = lo := Fin.ext (by
      simp only [hlo1_def]; omega)
    have hjunc : (BPSet.serialWedge B).toPsh.vertex₀ (evCell g lo)
        = (BPSet.serialWedge B).toPsh.vertex₁ (evCell g lo1) := by
      have h := evCell_junction g lo1 hlo1succ
      rw [hidx] at h
      exact h.symm
    -- `blockMap lo1 < blockMap lo = j`
    have hle : lo1 ≤ lo := Fin.le_def.mpr (by simp only [hlo1_def]; omega)
    have hmono := blockMap_monotone' g hle
    have hne : blockMap g lo1 ≠ j := by
      intro heq
      obtain ⟨m, hm, hmeq⟩ := List.mem_iff_getElem.mp ((fibre_mem g j lo1).mpr heq)
      have hle0 := (fibre_sortedLT g j).getElem_le_getElem_iff (hi := hpos) (hj := hm) |>.mpr
        (Nat.zero_le m)
      rw [hmeq, ← hlo_def] at hle0
      rw [Fin.le_def] at hle0
      simp only [hlo1_def] at hle0
      omega
    have hlt : (blockMap g lo1 : ℕ) < (blockMap g lo : ℕ) := by
      rw [hlob] at hmono ⊢
      rcases lt_or_eq_of_le (Fin.le_def.mp hmono) with h | h
      · exact h
      · exact absurd (Fin.ext h) hne
    have hL : (BPSet.serialWedge B).toPsh.vertex₁ (evCell g lo1)
        = (BPSet.serialWedge.ι B (blockMap g lo1)).app (op (Box.ob 0))
            ((BPSet.cube (B.get (blockMap g lo1) : ℕ)).toPsh.vertex₁ (bcell g lo1)) := by
      rw [← bcell_spec g lo1, map_vertex₁]
    have hR : (BPSet.serialWedge B).toPsh.vertex₀ (evCell g lo)
        = (BPSet.serialWedge.ι B (blockMap g lo)).app (op (Box.ob 0))
            ((BPSet.cube (B.get (blockMap g lo) : ℕ)).toPsh.vertex₀ (bcell g lo)) := by
      rw [← bcell_spec g lo, map_vertex₀]
    obtain ⟨_, hv⟩ := serialWedge_vertex_meet B (blockMap g lo1) (blockMap g lo)
      ((BPSet.cube (B.get (blockMap g lo1) : ℕ)).toPsh.vertex₁ (bcell g lo1))
      ((BPSet.cube (B.get (blockMap g lo) : ℕ)).toPsh.vertex₀ (bcell g lo))
      (hL.symm.trans (hjunc.symm.trans hR)) hlt
    rw [hR, hv, hlob]

/-- **Exit alignment.**  The target vertex of the last block-`j` cube of the ambient chain is
`ι_B j` applied to the final vertex of `cube (B.get j)`. -/
theorem exit_vertex {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (j : Fin B.length) (hpos : 0 < (fibre g j).length) :
    (BPSet.serialWedge B).toPsh.vertex₁
        (evCell g ((fibre g j)[(fibre g j).length - 1]'(by omega)))
      = (BPSet.serialWedge.ι B j).app (op (Box.ob 0)) (BPSet.cube (B.get j : ℕ)).final := by
  have hB : 0 < B.length := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hhib : blockMap g ((fibre g j)[(fibre g j).length - 1]'(by omega)) = j :=
    fibre_getElem_block g j _ (by omega)
  have hhi := ((fibre g j)[(fibre g j).length - 1]'(by omega) : Fin A.length).isLt
  have hA : 0 < A.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hhi
  set hi := ((fibre g j)[(fibre g j).length - 1]'(by omega) : Fin A.length) with hhi_def
  rcases Nat.lt_or_ge ((hi : ℕ) + 1) A.length with hcase | hcase
  · -- interior boundary: use the vertex-meet lemma at the next block
    set hi1 : Fin A.length := ⟨(hi : ℕ) + 1, hcase⟩ with hhi1_def
    have hjunc : (BPSet.serialWedge B).toPsh.vertex₁ (evCell g hi)
        = (BPSet.serialWedge B).toPsh.vertex₀ (evCell g hi1) := evCell_junction g hi hcase
    have hle : hi ≤ hi1 := Fin.le_def.mpr (by simp only [hhi1_def]; omega)
    have hmono := blockMap_monotone' g hle
    have hne : blockMap g hi1 ≠ j := by
      intro heq
      obtain ⟨m, hm, hmeq⟩ := List.mem_iff_getElem.mp ((fibre_mem g j hi1).mpr heq)
      have hle0 := (fibre_sortedLT g j).getElem_le_getElem_iff
        (hi := hm) (hj := (by omega : (fibre g j).length - 1 < (fibre g j).length)) |>.mpr
        (by omega)
      rw [hmeq, ← hhi_def] at hle0
      rw [Fin.le_def] at hle0
      simp only [hhi1_def] at hle0
      omega
    have hlt : (blockMap g hi : ℕ) < (blockMap g hi1 : ℕ) := by
      rw [hhib] at hmono ⊢
      rcases lt_or_eq_of_le (Fin.le_def.mp hmono) with h | h
      · exact h
      · exact absurd (Fin.ext h.symm) hne
    have hL : (BPSet.serialWedge B).toPsh.vertex₁ (evCell g hi)
        = (BPSet.serialWedge.ι B (blockMap g hi)).app (op (Box.ob 0))
            ((BPSet.cube (B.get (blockMap g hi) : ℕ)).toPsh.vertex₁ (bcell g hi)) := by
      rw [← bcell_spec g hi, map_vertex₁]
    have hR : (BPSet.serialWedge B).toPsh.vertex₀ (evCell g hi1)
        = (BPSet.serialWedge.ι B (blockMap g hi1)).app (op (Box.ob 0))
            ((BPSet.cube (B.get (blockMap g hi1) : ℕ)).toPsh.vertex₀ (bcell g hi1)) := by
      rw [← bcell_spec g hi1, map_vertex₀]
    obtain ⟨hu, _⟩ := serialWedge_vertex_meet B (blockMap g hi) (blockMap g hi1)
      ((BPSet.cube (B.get (blockMap g hi) : ℕ)).toPsh.vertex₁ (bcell g hi))
      ((BPSet.cube (B.get (blockMap g hi1) : ℕ)).toPsh.vertex₀ (bcell g hi1))
      (hL.symm.trans (hjunc.trans hR)) hlt
    rw [hL, hu, hhib]
  · -- last ambient cube: ends at the global final
    have hhieq : hi = ⟨A.length - 1, by omega⟩ := by
      apply Fin.ext
      show (hi : ℕ) = A.length - 1
      have := hi.isLt; omega
    have hjlast : (j : ℕ) = B.length - 1 := by
      rw [← hhib, hhieq]; exact blockMap_last g hA hB
    have hjeq : j = ⟨B.length - 1, by omega⟩ := Fin.ext hjlast
    rw [hhieq, vertex₁_evCell_last g hA, hjeq, serialWedge_final_ι B hB]

/-! ## Part 11. The block-`j` sub-chain -/

/-- The image of `blockCubes g j` under `ι_B j` is the list of ambient block cells
`evCell g i` for the fibre indices `i`. -/
theorem blockCubes_map_ι {A B : List ℕ+} (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B)
    (j : Fin B.length) :
    (blockCubes g j).map
        (fun c => (⟨c.1, (BPSet.serialWedge.ι B j).app (op (Box.ob (c.1 : ℕ))) c.2⟩ :
          Σ n : ℕ+, (BPSet.serialWedge B).toPsh.cells (n : ℕ)))
      = (fibre g j).map (fun i => ⟨A.get i, evCell g i⟩) := by
  rw [blockCubes_eq_pmap, List.map_pmap]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_pmap, List.getElem_map]
    exact Sigma.ext rfl (heq_of_eq (blockCellAt_spec g _))

/-- **The block-`j` cubes form an `init → final` chain inside `cube (B.get j)`** — the
object-level serial-wedge Segal decomposition (`BRAID2_PLAN.md` §2.4).  The image chain (in
`serialWedge B`) has internal junctions from `evCell_junction` and boundaries from the
vertex-meet structural lemma (`entry_vertex`/`exit_vertex`); it descends to `cube (B.get j)`
by `isCubeChain_pullback` along the mono `ι_B j`. -/
theorem blockCubes_isCubeChain {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length) :
    IsCubeChain (BPSet.cube (B.get j : ℕ)).init (blockCubes g j)
      (BPSet.cube (B.get j : ℕ)).final := by
  obtain ⟨i0, hi0⟩ := blockMap_surjective g j
  have hpos : 0 < (fibre g j).length := List.length_pos_of_mem ((fibre_mem g j i0).mpr hi0)
  -- the image chain in `serialWedge B`
  have hchain : IsCubeChain
      ((BPSet.serialWedge.ι B j).app (op (Box.ob 0)) (BPSet.cube (B.get j : ℕ)).init)
      ((fibre g j).map (fun i => (⟨A.get i, evCell g i⟩ :
        Σ m : ℕ+, (BPSet.serialWedge B).toPsh.cells (m : ℕ))))
      ((BPSet.serialWedge.ι B j).app (op (Box.ob 0)) (BPSet.cube (B.get j : ℕ)).final) := by
    rw [← List.ofFn_getElem_eq_map]
    refine isCubeChain_ofFn _ _ _
      (fun k => if h : (k : ℕ) < (fibre g j).length then
          (BPSet.serialWedge B).toPsh.vertex₀ (evCell g ((fibre g j)[(k : ℕ)]'h))
        else (BPSet.serialWedge.ι B j).app (op (Box.ob 0)) (BPSet.cube (B.get j : ℕ)).final)
      ?_ ?_ ?_ ?_
    · dsimp only
      rw [dif_pos (show ((0 : Fin ((fibre g j).length + 1)) : ℕ) < (fibre g j).length by
        simpa using hpos)]
      exact entry_vertex g j hpos
    · dsimp only
      rw [dif_neg (show ¬ ((Fin.last (fibre g j).length : Fin ((fibre g j).length + 1)) : ℕ)
        < (fibre g j).length by simp)]
    · intro k
      dsimp only
      rw [dif_pos (show ((k.castSucc : Fin ((fibre g j).length + 1)) : ℕ) < (fibre g j).length by
        simpa using k.isLt)]
      rfl
    · intro k
      dsimp only
      by_cases hkn : (k : ℕ) + 1 < (fibre g j).length
      · have hsucc := fibre_getElem_succ g j (k : ℕ) hkn
        have hj : ((fibre g j)[(k : ℕ)]'k.isLt : ℕ) + 1 < A.length := by
          rw [← hsucc]; exact ((fibre g j)[(k : ℕ) + 1]'hkn : Fin A.length).isLt
        have key : (BPSet.serialWedge B).toPsh.vertex₁ (evCell g ((fibre g j)[(k : ℕ)]'k.isLt))
            = (BPSet.serialWedge B).toPsh.vertex₀ (evCell g ((fibre g j)[(k : ℕ) + 1]'hkn)) := by
          rw [evCell_junction g ((fibre g j)[(k : ℕ)]'k.isLt) hj]
          exact congrArg
            (fun x => (BPSet.serialWedge B).toPsh.vertex₀ (evCell g x))
            (Fin.ext hsucc.symm : (⟨((fibre g j)[(k : ℕ)]'k.isLt : ℕ) + 1, hj⟩ : Fin A.length)
              = (fibre g j)[(k : ℕ) + 1]'hkn)
        rw [dif_pos (show ((k.succ : Fin ((fibre g j).length + 1)) : ℕ) < (fibre g j).length by
          simpa using hkn)]
        exact key
      · have hkeq : (k : ℕ) = (fibre g j).length - 1 := by have := k.isLt; omega
        have key : (BPSet.serialWedge B).toPsh.vertex₁ (evCell g ((fibre g j)[(k : ℕ)]'k.isLt))
            = (BPSet.serialWedge.ι B j).app (op (Box.ob 0)) (BPSet.cube (B.get j : ℕ)).final := by
          have hlast := exit_vertex g j hpos
          rw [show ((fibre g j)[(fibre g j).length - 1]'(by omega))
              = (fibre g j)[(k : ℕ)]'k.isLt from by simp only [hkeq]] at hlast
          exact hlast
        rw [dif_neg (show ¬ ((k.succ : Fin ((fibre g j).length + 1)) : ℕ) < (fibre g j).length by
          simp only [Fin.val_succ]; omega)]
        exact key
  -- pull back along the mono `ι_B j`
  refine isCubeChain_pullback (BPSet.serialWedge.ι B j)
    (fun {m} => serialWedge_ι_app_injective B j)
    (BPSet.cube (B.get j : ℕ)).init (BPSet.cube (B.get j : ℕ)).final (blockCubes g j) ?_
  rw [blockCubes_map_ι]
  exact hchain

/-- **The block chain as a refinement object** of `cube (B.get j)`. -/
noncomputable def blockChainObj {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length) :
    RefineObj (BPSet.cube (B.get j : ℕ)).init (BPSet.cube (B.get j : ℕ)).final :=
  ⟨blockCubes g j, blockCubes_isCubeChain g j⟩

/-- **The `OwnerData` of the block chain** — the ordered set partition of `Fin (B.get j)`
read off `blockChainObj g j`, transported onto the fibre shape.  This is the per-target-block
datum of the hom classification (`BRAID2_PLAN.md` §2.4). -/
noncomputable def blockOwnerData {A B : List ℕ+}
    (g : BPSet.serialWedge A ⟶ BPSet.serialWedge B) (j : Fin B.length) :
    OwnerData (fibreShape A (blockMap g) j) (B.get j : ℕ) :=
  (blockCubes_dims g j) ▸ chainOwnerData (blockChainObj g j)

end FinalPrecubical
