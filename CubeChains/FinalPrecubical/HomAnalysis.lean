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
  `ι_i ≫ g = yoneda.map incl ≫ ι_{blockMap g i}` (directly `WedgeMap.wedgeMap_block`'s choice,
  so the per-block face datum is free).
* **`blockMap_monotone`** — via `Correspondence.wedgeToRefineMap`'s `refinementMono` under the
  serial-wedge altitude, transported through `blockMap_val`.
* **`fibreShape` + length lemma** — the per-target-block sub-shape of `A`.

## What remains (the `Σ`-assembly `homEquiv`, items 3–6 of the brief)

Assembling `bm` + `blockMap_spec`'s per-block inclusions into the full `Σ`/`Π` datum requires
the **serial-wedge Segal object-decomposition**: the block-`j` sub-chain of a `serialWedge B`
chain (the cubes with `blockMap · = j`, contiguous since `blockMap` is monotone) is an
`init → final` chain *inside* `cube (B.get j)`, whose `chainOwnerData`
(`CubeChainPoset`) is the sought `OwnerData`.  Its `IsCubeChain` (junction alignment at block
boundaries + init/final matching, via `serialWedge_ι_app_injective`) is the genuine remaining
content; the inverse (assemble per-block `cornerChain`s, descend by `wedgeDescHom`) and the two
round-trips (inherited from `refineObjEquivOSP` + `wedgeToCubes_inj`) build on top of it.

**Layer:** FinalPrecubical.  **Imports:** `FinalPrecubical.SerialNSL` (which supplies
`serialWedge_nonSelfLinked` and transitively `CubeChainPoset`/`Correspondence`/`WedgeMap`).
-/

open CategoryTheory Opposite

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

end FinalPrecubical
