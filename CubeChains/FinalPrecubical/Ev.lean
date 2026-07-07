import CubeChains.Chains.SegalAltitude
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.Correspondence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith

/-!
# FinalPrecubical/Ev — event tracking for wedge maps

The morphism analyzer for `Ch Z` (Step 3 of `BRAID_CHAINS_README.md`).  A
bi-pointed map `g : serialWedge A ⟶ serialWedge B` sends the `i`-th top cube of the
source to a *face* of the `jᵢ`-th top cube of the target; the source coordinates
correspond, in serial order, to the *star* (free) positions of that face.  This
file packages that data as an *event tracking* map

  `ev g : Fin (dimSum A) → Fin (dimSum B)`

on the global coordinates ("events") of the two serial wedges, and proves the
functoriality (`ev_id`, `ev_comp`) and combinatorial consequences.

**Layer:** FinalPrecubical.  **Imports:** `Chains.SegalAltitude`, `Chains.WedgeMap`,
mathlib `BigOperators.Fin` (`finSigmaFinEquiv`), `Equiv.Fin`.

`ev g` is assembled from:
* the *block decomposition* `wedgeMap_block`/`serialWedge_cell_exists`: block `i`
  factors through a unique target block `blockIdx g i` as a face `faceCell g i`;
* the *star embedding* `StdCube.nones (faceCell g i)`: the free positions of the
  face, in order;
* the global re-indexing `finSigmaFinEquiv : (Σ i, Fin (A.get i)) ≃ Fin (dimSum A)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace FinalPrecubical

open BPSet CubeChain PrecubicalSet StdCube

/-! ## Step 0. The dimension sum `|A|` -/

/-- The total dimension of a serial wedge (the README's `|A|`): the sum of its cube
dimensions.  The global "events" of `serialWedge A` are `Fin (dimSum A)`. -/
def dimSum (A : List ℕ+) : ℕ := (A.map (fun n : ℕ+ => (n : ℕ))).sum

@[simp] theorem dimSum_nil : dimSum [] = 0 := rfl

theorem dimSum_cons (n : ℕ+) (rest : List ℕ+) :
    dimSum (n :: rest) = (n : ℕ) + dimSum rest := by
  simp [dimSum, List.map_cons, List.sum_cons]

/-- `dimSum A` as a `Finset` sum over the blocks — the shape `finSigmaFinEquiv`
consumes. -/
theorem dimSum_eq_sum (A : List ℕ+) :
    dimSum A = ∑ i : Fin A.length, (A.get i : ℕ) := by
  rw [dimSum]
  conv_lhs => rw [← List.ofFn_get A]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-! ## Step 1. `dimSum` is preserved by wedge maps

A wedge map `serialWedge A ⟶ serialWedge B` preserves total dimension.  Over the
ambient `serialWedge B`, both the source chain `⟨A, g⟩` and the target chain `⟨B, 𝟙⟩`
run `init → final`, and a chain's altitude gap equals its total dimension
(`Correspondence.isCubeChain_alt_final`), so `dimSum A = dimSum B`.  This routes through
the altitude machinery of `Chains/Correspondence`, replacing the former bespoke
`serialWedge`-altitude recursion. -/

/-- **`dimSum` is a wedge-map invariant.**  Over the ambient `serialWedge B`, both
`⟨A, g⟩` and `⟨B, 𝟙⟩` are chains `init → final`; a chain's altitude gap equals its total
dimension (`Correspondence.isCubeChain_alt_final` + `wedgeToCubes_dims`), which is
`dimSum A` resp. `dimSum B`, and the two gaps coincide. -/
theorem dimSum_eq {A B : List ℕ+} (g : serialWedge A ⟶ serialWedge B) :
    dimSum A = dimSum B := by
  obtain ⟨altB, haxB, _⟩ := serialWedge_admitsAltitude B
  -- The altitude gap of any shape-`D` chain in `serialWedge B` is `dimSum D`.
  have hgap : ∀ {D : List ℕ+} (φ : serialWedge D ⟶ serialWedge B),
      altB 0 (serialWedge B).final = altB 0 (serialWedge B).init + (dimSum D : ℤ) := by
    intro D φ
    have hchain : IsCubeChain (serialWedge B).init (wedgeToCubes ⟨D, φ.hom⟩)
        (serialWedge B).final := by
      have h := wedgeToCubes_isCubeChain D φ.hom
      rwa [φ.app_init, φ.app_final] at h
    have hmap : (wedgeToCubes ⟨D, φ.hom⟩).map (fun c => (c.1 : ℕ))
        = D.map (fun n : ℕ+ => (n : ℕ)) := by
      conv_rhs => rw [← wedgeToCubes_dims D φ.hom]
      rw [List.map_map]; rfl
    rw [isCubeChain_alt_final altB haxB (wedgeToCubes ⟨D, φ.hom⟩) _ _ hchain, hmap]
    rfl
  have hA := hgap g
  have hB := hgap (𝟙 (serialWedge B))
  rw [hA] at hB
  exact_mod_cast add_left_cancel hB

/-! ## Step 2. Block decomposition and the event map `ev`

By `serialWedge_cell_exists`, the `i`-th block of the source, restricted along `g`,
is a *face* of a unique target block.  We record that block index (`blockIdx`) and
the face (`blockFace`, a box morphism / cell), and read off its star positions
(`faceStar`).  The event map re-indexes globally. -/

variable {A B C : List ℕ+}

/-- The cell of `serialWedge B` that the `i`-th source block maps to: the Yoneda
classifier of the block restriction `ιᵢ ≫ g`. -/
noncomputable def evCell (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    (serialWedge B).toPsh.cells (A.get i : ℕ) :=
  yonedaEquiv (BPSet.serialWedge.ι A i ≫ g.hom)

/-- The target block that the `i`-th source block maps into (the `jᵢ` of the README). -/
noncomputable def blockIdx (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    Fin B.length :=
  (CubeChain.serialWedge_cell_exists B (A.get i).2 (evCell g i)).choose

/-- The face of the target block `blockIdx g i` that block `i` maps to, as a cell
(equivalently a box morphism `□^{A.get i} ⟶ □^{B.get (blockIdx g i)}`). -/
noncomputable def blockFace (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    (cube (B.get (blockIdx g i) : ℕ)).toPsh.cells (A.get i : ℕ) :=
  (CubeChain.serialWedge_cell_exists B (A.get i).2 (evCell g i)).choose_spec.choose

/-- Defining property: the block inclusion sends `blockFace g i` to `evCell g i`. -/
theorem blockFace_spec (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    (BPSet.serialWedge.ι B (blockIdx g i)).app (op (Box.ob (A.get i : ℕ))) (blockFace g i)
      = evCell g i :=
  (CubeChain.serialWedge_cell_exists B (A.get i).2 (evCell g i)).choose_spec.choose_spec

/-- Read a cube cell (= box morphism) as a concrete `StdCube.cells`.  Wrapping
`StdCube.ev` behind an argument of the *syntactic* form `(cube m).toPsh.cells k`
keeps call-site elaboration first-order (avoids repeated Yoneda whnf). -/
noncomputable def toStar {m k : ℕ} (f : (cube m).toPsh.cells k) : StdCube.cells m k :=
  StdCube.ev f

theorem toStar_eq {m k : ℕ} (f : (cube m).toPsh.cells k) : toStar f = StdCube.ev f := rfl

/-- A `□`-cell is determined by its sign vector (`toStar` is injective — the cube
Yoneda round-trip `canonicalMap ∘ ev = id`). -/
theorem toStar_injective {m k : ℕ} :
    Function.Injective (toStar : (cube m).toPsh.cells k → StdCube.cells m k) := by
  intro x y h
  rw [toStar_eq, toStar_eq] at h
  have hx := (StdCube.cubeRepr (StdCube.stdPre m) k).left_inv x
  have hy := (StdCube.cubeRepr (StdCube.stdPre m) k).left_inv y
  simp only [StdCube.cubeRepr] at hx hy
  rw [← hx, ← hy, h]

theorem toStar_canonicalMap {N k : ℕ} (x : StdCube.cells N k) :
    toStar (StdCube.canonicalMap x : (cube N).toPsh.cells k) = x := by
  rw [toStar_eq]; exact StdCube.ev_canonicalMap (K := StdCube.stdPre N) x

/-- The star (free) positions of the face `blockFace g i`, in serial order: an order
embedding `Fin (A.get i) ↪o Fin (B.get (blockIdx g i))`. -/
noncomputable def faceStar (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    StdCube.cells (B.get (blockIdx g i) : ℕ) (A.get i : ℕ) :=
  toStar (blockFace g i)

/-- The block re-indexing at the `Sigma` level: source event `(i, p)` maps to target
event `(blockIdx g i, faceStar g i p)`. -/
noncomputable def evBlk (g : serialWedge A ⟶ serialWedge B) :
    (Σ i : Fin A.length, Fin (A.get i : ℕ)) → (Σ r : Fin B.length, Fin (B.get r : ℕ)) :=
  fun p => ⟨blockIdx g p.1, StdCube.nones (faceStar g p.1) p.2⟩

/-- The global re-indexing `(Σ i, Fin (A.get i)) ≃ Fin (dimSum A)` (serial order). -/
noncomputable def globalEquiv (A : List ℕ+) :
    (Σ i : Fin A.length, Fin (A.get i : ℕ)) ≃ Fin (dimSum A) :=
  finSigmaFinEquiv.trans (finCongr (dimSum_eq_sum A).symm)

/-- **Event tracking** `ev g : Fin (dimSum A) → Fin (dimSum B)`: decode a source event
to `(i, p)`, apply the block re-indexing, re-encode. -/
noncomputable def ev (g : serialWedge A ⟶ serialWedge B) : Fin (dimSum A) → Fin (dimSum B) :=
  globalEquiv B ∘ evBlk g ∘ (globalEquiv A).symm

/-! ### Uniqueness of the block decomposition

The target block and face are pinned by the block cell (`serialWedge_block_unique`
and the block-injectivity `serialWedge_ι_app_injective`).  Packaging index + face as
a `Σ` avoids `HEq`; landing the `nones` comparison in `ℕ` (`.val`) then transports
freely. -/

/-- Two block-decompositions of the same positive cell agree (index and face
together). -/
theorem sigma_cell_ext (r r' : Fin B.length) (k : ℕ) (hk : 1 ≤ k)
    (x : (cube (B.get r : ℕ)).toPsh.cells k) (x' : (cube (B.get r' : ℕ)).toPsh.cells k)
    (z : (serialWedge B).toPsh.cells k)
    (hx : (BPSet.serialWedge.ι B r).app (op (Box.ob k)) x = z)
    (hx' : (BPSet.serialWedge.ι B r').app (op (Box.ob k)) x' = z) :
    (⟨r, x⟩ : Σ r : Fin B.length, (cube (B.get r : ℕ)).toPsh.cells k) = ⟨r', x'⟩ := by
  have hrr : r = r' :=
    serialWedge_block_unique B hk r r' z ⟨x, hx⟩ ⟨x', hx'⟩
  subst hrr
  have hxx : x = x' :=
    serialWedge_ι_app_injective B r (hx.trans hx'.symm)
  rw [hxx]

/-- The block-decomposition characterization: any face of any block realizing
`evCell g i` is *the* block decomposition. -/
theorem blockFace_unique (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length)
    (r : Fin B.length) (x : (cube (B.get r : ℕ)).toPsh.cells (A.get i : ℕ))
    (hx : (BPSet.serialWedge.ι B r).app (op (Box.ob (A.get i : ℕ))) x = evCell g i) :
    (⟨blockIdx g i, blockFace g i⟩ :
        Σ r : Fin B.length, (cube (B.get r : ℕ)).toPsh.cells (A.get i : ℕ)) = ⟨r, x⟩ :=
  sigma_cell_ext (blockIdx g i) r (A.get i : ℕ) (A.get i).2 (blockFace g i) x
    (evCell g i) (blockFace_spec g i) hx

/-- The target block is determined by any realizing face. -/
theorem blockIdx_eq_of (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length)
    (r : Fin B.length) (x : (cube (B.get r : ℕ)).toPsh.cells (A.get i : ℕ))
    (hx : (BPSet.serialWedge.ι B r).app (op (Box.ob (A.get i : ℕ))) x = evCell g i) :
    blockIdx g i = r :=
  congrArg Sigma.fst (blockFace_unique g i r x hx)

/-- Two block faces of the same positive cell read off the same star positions (in
`ℕ`).  `subst` on the block index does the transport, so `toStar` only ever appears
on the explicit arguments `y`, `y'` — never under a binder. -/
theorem nones_toStar_val_of {r r' : Fin B.length} (k : ℕ) (hk : 1 ≤ k)
    (y : (cube (B.get r : ℕ)).toPsh.cells k) (y' : (cube (B.get r' : ℕ)).toPsh.cells k)
    (z : (serialWedge B).toPsh.cells k)
    (hy : (BPSet.serialWedge.ι B r).app (op (Box.ob k)) y = z)
    (hy' : (BPSet.serialWedge.ι B r').app (op (Box.ob k)) y' = z) (p : Fin k) :
    (StdCube.nones (toStar y) p : ℕ) = (StdCube.nones (toStar y') p : ℕ) := by
  have hrr : r = r' := serialWedge_block_unique B hk r r' z ⟨y, hy⟩ ⟨y', hy'⟩
  subst hrr
  have hyy : y = y' := serialWedge_ι_app_injective B r (hy.trans hy'.symm)
  rw [hyy]

/-- The star positions of the block face are determined by any realizing face (in
`ℕ`, sidestepping the index transport). -/
theorem faceStar_nones_val (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length)
    (r : Fin B.length) (x : (cube (B.get r : ℕ)).toPsh.cells (A.get i : ℕ))
    (hx : (BPSet.serialWedge.ι B r).app (op (Box.ob (A.get i : ℕ))) x = evCell g i)
    (p : Fin (A.get i : ℕ)) :
    (StdCube.nones (faceStar g i) p : ℕ) = (StdCube.nones (toStar x) p : ℕ) :=
  nones_toStar_val_of (A.get i : ℕ) (A.get i).2 (blockFace g i) x (evCell g i)
    (blockFace_spec g i) hx p

/-- The block face read as an honest box morphism `□^{A.get i} ⟶ □^{B.get (blockIdx g i)}`. -/
noncomputable def blockMor (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    Box.ob (A.get i : ℕ) ⟶ Box.ob (B.get (blockIdx g i) : ℕ) :=
  blockFace g i

/-- Morphism form of `blockFace_spec`: block `i` factors as `blockMor g i` into
target block `blockIdx g i`. -/
theorem blockFace_spec_mor (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    yoneda.map (blockMor g i) ≫ BPSet.serialWedge.ι B (blockIdx g i)
      = BPSet.serialWedge.ι A i ≫ g.hom := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact blockFace_spec g i

/-- The identity order embedding reads off the star positions of the top cell. -/
theorem nones_topCell (k : ℕ) (p : Fin k) :
    (StdCube.nones (StdCube.topCell k) p : ℕ) = (p : ℕ) := by
  have h : StdCube.nones (StdCube.topCell k)
      = RelEmbedding.refl ((· ≤ ·) : Fin k → Fin k → Prop) :=
    (Finset.orderEmbOfFin_unique' (StdCube.topCell k).prop
      (fun x => by rw [StdCube.mem_noneSet]; rfl)).symm
  rw [h]; rfl

/-! ### Star positions compose under the iterated-face map `app`

The geometric heart of `ev_comp`: the star (free) positions of `app w v` are the
star positions of `v` transported through the star embedding of `w`.  This is the
statement that "substituting a code into the star positions of a face" composes the
two coordinate trackings. -/

/-- From the `noneSet` computation, the star embedding of `app w v` is the composite
of star embeddings (order-embedding uniqueness). -/
theorem nones_app_of_noneSet {N K1 J : ℕ} (w : StdCube.cells N K1) (v : StdCube.cells K1 J)
    (hns : StdCube.noneSet (StdCube.app (K := StdCube.stdPre N) w v).val
      = (StdCube.noneSet v.val).map (StdCube.nones w).toEmbedding) (p : Fin J) :
    StdCube.nones (StdCube.app (K := StdCube.stdPre N) w v) p
      = StdCube.nones w (StdCube.nones v p) := by
  have key : StdCube.nones (StdCube.app (K := StdCube.stdPre N) w v)
      = (StdCube.nones v).trans (StdCube.nones w) := by
    refine (Finset.orderEmbOfFin_unique'
      (StdCube.app (K := StdCube.stdPre N) w v).prop (fun y => ?_)).symm
    rw [hns]
    have hy : ((StdCube.nones v).trans (StdCube.nones w)) y
        = (StdCube.nones w).toEmbedding (StdCube.nones v y) := rfl
    rw [hy]
    exact Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem _ v.prop y)
  rw [key]; rfl

/-- **The star set of `app w v`** is the star set of `v` pushed forward along the
star embedding of `w`.  By strong induction on the fixed coordinates of `v`, peeling
the smallest with `app_unfold`. -/
theorem noneSet_app {N K1 : ℕ} (w : StdCube.cells N K1) :
    ∀ {J : ℕ} (v : StdCube.cells K1 J),
      StdCube.noneSet (StdCube.app (K := StdCube.stdPre N) w v).val
        = (StdCube.noneSet v.val).map (StdCube.nones w).toEmbedding := by
  intro J v
  induction hd : K1 - J using Nat.strong_induction_on generalizing J v with
  | _ d ih =>
    rcases Nat.lt_or_ge J K1 with hlt | hge
    · rw [StdCube.app_unfold (K := StdCube.stdPre N) w v hlt]
      change StdCube.noneSet (StdCube.face (StdCube.minFixedVal v hlt) (StdCube.minFixedIdx v hlt)
          (StdCube.app (K := StdCube.stdPre N) w (StdCube.freeMin v hlt))).val
        = (StdCube.noneSet v.val).map (StdCube.nones w).toEmbedding
      rw [StdCube.face_val, StdCube.noneSet_update]
      have ihv' := ih (K1 - (J + 1)) (by omega) (StdCube.freeMin v hlt) rfl
      rw [ihv', nones_app_of_noneSet w (StdCube.freeMin v hlt) ihv' (StdCube.minFixedIdx v hlt)]
      -- rewrite the star set of `v` as an `erase` of the freed cell's, then push `map`
      have hv : StdCube.noneSet v.val
          = (StdCube.noneSet (StdCube.freeMin v hlt).val).erase
              (StdCube.nones (StdCube.freeMin v hlt) (StdCube.minFixedIdx v hlt)) := by
        rw [StdCube.noneSet_freeMin, StdCube.nones_minFixedIdx,
          Finset.erase_insert (StdCube.minFixed_notMem v hlt)]
      rw [hv, Finset.map_erase, RelEmbedding.coe_toEmbedding]
    · have hJK : J = K1 := le_antisymm (StdCube.cells_card_le v) hge
      subst hJK
      rw [StdCube.eq_topCell v, StdCube.app_topCell]
      have hu : StdCube.noneSet (StdCube.topCell J).val = Finset.univ := by
        ext j; simp [StdCube.mem_noneSet, StdCube.topCell]
      rw [hu]
      exact (Finset.map_orderEmbOfFin_univ (StdCube.noneSet w.val) w.prop).symm

/-- **Star positions compose under `app`** (the key input to `ev_comp`). -/
theorem nones_app {N K1 J : ℕ} (w : StdCube.cells N K1) (v : StdCube.cells K1 J) (p : Fin J) :
    StdCube.nones (StdCube.app (K := StdCube.stdPre N) w v) p
      = StdCube.nones w (StdCube.nones v p) :=
  nones_app_of_noneSet w v (noneSet_app w v) p

/-! ## Step 3. Functoriality: `ev_id` and `ev_comp` -/

/-- Extensionality for `Σ i, Fin (f i)` with the first components propositionally
equal (the block index) and second components equal in `ℕ` (the star position).
`subst` on the index does the transport, keeping later proofs `HEq`-free. -/
theorem sigmaFin_ext {m : ℕ} {f : Fin m → ℕ} {a b : Fin m} (hab : a = b)
    {x : Fin (f a)} {y : Fin (f b)} (hxy : (x : ℕ) = (y : ℕ)) :
    (⟨a, x⟩ : Σ i, Fin (f i)) = ⟨b, y⟩ := by
  subst hab
  rw [Fin.ext hxy]

/-- **`ev` preserves identities** at the block level: the identity map decomposes as
each block into itself via the top-cell face. -/
theorem evBlk_id : evBlk (𝟙 (serialWedge A)) = id := by
  funext s
  obtain ⟨i, p⟩ := s
  -- the identity block-decomposition witness: block `i` maps to block `i` via `𝟙`
  have hw : (BPSet.serialWedge.ι A i).app (op (Box.ob (A.get i : ℕ)))
        (𝟙 (Box.ob (A.get i : ℕ))) = evCell (𝟙 (serialWedge A)) i := by
    have hev : evCell (𝟙 (serialWedge A)) i = yonedaEquiv (BPSet.serialWedge.ι A i) := by
      simp only [evCell, BPSet.id_hom, Category.comp_id]
    have hmor : yoneda.map (𝟙 (Box.ob (A.get i : ℕ))) ≫ BPSet.serialWedge.ι A i
        = BPSet.serialWedge.ι A i := by rw [CategoryTheory.Functor.map_id, Category.id_comp]
    have hy := congrArg yonedaEquiv hmor
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hy
    rw [hev]; exact hy
  have hbi : blockIdx (𝟙 (serialWedge A)) i = i :=
    blockIdx_eq_of (𝟙 (serialWedge A)) i i (𝟙 (Box.ob (A.get i : ℕ))) hw
  change (⟨blockIdx (𝟙 (serialWedge A)) i, StdCube.nones (faceStar (𝟙 (serialWedge A)) i) p⟩
      : Σ r : Fin A.length, Fin (A.get r : ℕ)) = ⟨i, p⟩
  refine sigmaFin_ext (f := fun r : Fin A.length => (A.get r : ℕ)) hbi ?_
  rw [faceStar_nones_val (𝟙 (serialWedge A)) i i (𝟙 (Box.ob (A.get i : ℕ))) hw p]
  exact nones_topCell (A.get i : ℕ) p

/-- **`ev (𝟙) = id`.** -/
theorem ev_id : ev (𝟙 (serialWedge A)) = id := by
  change globalEquiv A ∘ evBlk (𝟙 (serialWedge A)) ∘ (globalEquiv A).symm = id
  rw [evBlk_id]
  ext e
  simp

/-- Block-decomposition of a composite: block `i` factors through target block
`blockIdx h (blockIdx g i)` via the composite box morphism. -/
theorem evCell_comp_witness (g : serialWedge A ⟶ serialWedge B)
    (h : serialWedge B ⟶ serialWedge C) (i : Fin A.length) :
    (BPSet.serialWedge.ι C (blockIdx h (blockIdx g i))).app (op (Box.ob (A.get i : ℕ)))
        (blockMor g i ≫ blockMor h (blockIdx g i)) = evCell (g ≫ h) i := by
  have hmor : yoneda.map (blockMor g i ≫ blockMor h (blockIdx g i))
        ≫ BPSet.serialWedge.ι C (blockIdx h (blockIdx g i))
      = BPSet.serialWedge.ι A i ≫ (g ≫ h).hom := by
    rw [Functor.map_comp, BPSet.comp_hom]
    erw [Category.assoc, blockFace_spec_mor h (blockIdx g i), ← Category.assoc,
      blockFace_spec_mor g i, Category.assoc]
  have hy := congrArg yonedaEquiv hmor
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hy
  exact hy

/-- **`ev` preserves composition** at the block level (the substitution normal form:
composing block factorisations composes the star trackings, `nones_app`). -/
theorem evBlk_comp (g : serialWedge A ⟶ serialWedge B) (h : serialWedge B ⟶ serialWedge C) :
    evBlk (g ≫ h) = evBlk h ∘ evBlk g := by
  funext s
  obtain ⟨i, p⟩ := s
  have hwit := evCell_comp_witness g h i
  have hbi : blockIdx (g ≫ h) i = blockIdx h (blockIdx g i) :=
    blockIdx_eq_of (g ≫ h) i (blockIdx h (blockIdx g i))
      (blockMor g i ≫ blockMor h (blockIdx g i)) hwit
  -- the composite face reads as `app` of the two star faces
  have hW : toStar (blockMor g i ≫ blockMor h (blockIdx g i))
      = StdCube.app (K := StdCube.stdPre (C.get (blockIdx h (blockIdx g i)) : ℕ))
          (faceStar h (blockIdx g i)) (faceStar g i) := by
    change StdCube.ev (blockMor g i ≫ blockMor h (blockIdx g i))
      = StdCube.app (K := StdCube.stdPre (C.get (blockIdx h (blockIdx g i)) : ℕ))
          (faceStar h (blockIdx g i)) (faceStar g i)
    rw [StdCube.ev_comp]
    exact StdCube.app_unique (blockMor h (blockIdx g i)) rfl (StdCube.ev (blockMor g i))
  change (⟨blockIdx (g ≫ h) i, StdCube.nones (faceStar (g ≫ h) i) p⟩
      : Σ r : Fin C.length, Fin (C.get r : ℕ))
    = ⟨blockIdx h (blockIdx g i),
        StdCube.nones (faceStar h (blockIdx g i)) (StdCube.nones (faceStar g i) p)⟩
  refine sigmaFin_ext (f := fun r : Fin C.length => (C.get r : ℕ)) hbi ?_
  rw [faceStar_nones_val (g ≫ h) i (blockIdx h (blockIdx g i))
      (blockMor g i ≫ blockMor h (blockIdx g i)) hwit p, hW, nones_app]

/-- **`ev (g ≫ h) = ev h ∘ ev g`** — the largest single result (README Step 3). -/
theorem ev_comp (g : serialWedge A ⟶ serialWedge B) (h : serialWedge B ⟶ serialWedge C) :
    ev (g ≫ h) = ev h ∘ ev g := by
  change globalEquiv C ∘ evBlk (g ≫ h) ∘ (globalEquiv A).symm
    = (globalEquiv C ∘ evBlk h ∘ (globalEquiv B).symm)
      ∘ (globalEquiv B ∘ evBlk g ∘ (globalEquiv A).symm)
  rw [evBlk_comp]
  ext e
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-! ## Global-index computations and Step 3 consequences -/

/-- The underlying natural number of a re-indexed event is the raw `finSigmaFinEquiv`
value (the `finCongr` cast preserves `.val`). -/
theorem globalEquiv_val {A : List ℕ+} (s : Σ r : Fin A.length, Fin (A.get r : ℕ)) :
    (globalEquiv A s : ℕ) = (finSigmaFinEquiv s : ℕ) := by
  simp only [globalEquiv, Equiv.trans_apply, finCongr_apply_coe]

/-- Within a fixed target block the global re-indexing is strictly monotone in the
star position. -/
theorem globalEquiv_block_lt {A : List ℕ+} (r : Fin A.length)
    {q q' : Fin (A.get r : ℕ)} (h : q < q') :
    globalEquiv A ⟨r, q⟩ < globalEquiv A ⟨r, q'⟩ := by
  rw [Fin.lt_def, globalEquiv_val, globalEquiv_val, finSigmaFinEquiv_apply,
    finSigmaFinEquiv_apply]
  dsimp only
  have hq : (q : ℕ) < (q' : ℕ) := h
  omega

/-- Evaluation of `ev` on a decoded source event. -/
theorem ev_apply (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length)
    (p : Fin (A.get i : ℕ)) :
    ev g (globalEquiv A ⟨i, p⟩)
      = globalEquiv B ⟨blockIdx g i, StdCube.nones (faceStar g i) p⟩ := by
  change globalEquiv B (evBlk g ((globalEquiv A).symm (globalEquiv A ⟨i, p⟩)))
    = globalEquiv B ⟨blockIdx g i, StdCube.nones (faceStar g i) p⟩
  rw [Equiv.symm_apply_apply]; rfl

/-- **`ev` is strictly increasing on each source block** (README Step 3.2): the star
positions of a block face are read in serial order. -/
theorem ev_strictMonoOn (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length) :
    StrictMono (fun p : Fin (A.get i : ℕ) => ev g (globalEquiv A ⟨i, p⟩)) := by
  intro p p' hpp
  change ev g (globalEquiv A ⟨i, p⟩) < ev g (globalEquiv A ⟨i, p'⟩)
  rw [ev_apply, ev_apply]
  exact globalEquiv_block_lt (blockIdx g i) ((StdCube.nones (faceStar g i)).strictMono hpp)

/-- **Blocks are respected** (forward inclusion of the partition, README Step 3.3):
every event of source block `i` lands in target block `blockIdx g i`. -/
theorem ev_blockOf (g : serialWedge A ⟶ serialWedge B) (i : Fin A.length)
    (p : Fin (A.get i : ℕ)) :
    ((globalEquiv B).symm (ev g (globalEquiv A ⟨i, p⟩))).1 = blockIdx g i := by
  rw [ev_apply, Equiv.symm_apply_apply]

/-! ## Block monotonicity (inherited from `Correspondence.wedgeToRefineMap`)

`blockIdx g` is *monotone* (README Step 3; the well-definedness crux of `MainFunctor`).
Rather than re-run the altitude/prefix-sum bracketing locally, we now inherit it: `g`
packages as a `ChainCat` morphism `⟨A, g⟩ ⟶ ⟨B, 𝟙⟩` over the ambient BPSet `serialWedge B`,
and `Correspondence.wedgeToRefineMap`'s reindexing `refinement` is exactly `blockIdx g`
(identified via `wedgeToRefineMap_refinement_spec` + block uniqueness), so its
`refinementMono` gives monotonicity directly. -/

/-- **Block monotonicity of a wedge map.**  `blockIdx g` is monotone — inherited from
`Correspondence.wedgeToRefineMap`'s `refinementMono` by viewing `g` as a `ChainCat`
morphism `⟨A, g⟩ ⟶ ⟨B, 𝟙⟩` over the ambient BPSet `serialWedge B`, whose reindexing is
exactly `blockIdx g` (`wedgeToRefineMap_refinement_spec` identifies the two via the
block-uniqueness lemma `blockIdx_eq_of`).  Replaces the former standalone altitude/
prefix-sum bracketing (now factored into `wedgeToRefineMap`). -/
theorem blockIdx_monotone (g : serialWedge A ⟶ serialWedge B) :
    Monotone (blockIdx g) := by
  -- View `g` as a morphism `a ⟶ b` in `ChainCat (serialWedge B)`.
  let a : ChainCat.Obj (serialWedge B) := ⟨A, g⟩
  let b : ChainCat.Obj (serialWedge B) := ⟨B, 𝟙 _⟩
  let g' : a ⟶ b := ⟨g, Category.comp_id g⟩
  have hLlen : (wedgeToCubes ⟨a.dims, a.map.hom⟩).length = a.dims.length :=
    wedgeToCubes_length a.dims a.map.hom
  have hMlen : (wedgeToCubes ⟨b.dims, b.map.hom⟩).length = b.dims.length :=
    wedgeToCubes_length b.dims b.map.hom
  set cr := wedgeToRefineMap g' (serialWedge_admitsAltitude B) with hcr
  -- `blockIdx g` is the reindexing of `cr`: both are the target block of the source cube.
  have hid : ∀ i : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length,
      blockIdx g (i.cast hLlen) = (cr.refinement i).cast hMlen := by
    intro i
    obtain ⟨x, hx⟩ := wedgeToRefineMap_refinement_spec g' (serialWedge_admitsAltitude B) i
    exact blockIdx_eq_of g (i.cast hLlen) ((cr.refinement i).cast hMlen) x hx
  -- Transport `refinementMono` across the cube-list-length casts.
  intro i j hij
  have hij' : (i.cast hLlen.symm : Fin (wedgeToCubes ⟨a.dims, a.map.hom⟩).length)
      ≤ j.cast hLlen.symm := by rw [Fin.le_def]; simpa using Fin.le_def.mp hij
  have hmono := cr.refinementMono (i.cast hLlen.symm) (j.cast hLlen.symm) hij'
  have hi := hid (i.cast hLlen.symm)
  have hj := hid (j.cast hLlen.symm)
  rw [Fin.cast_cast, Fin.cast_eq_self] at hi hj
  rw [hi, hj, Fin.le_def]
  simpa using Fin.le_def.mp hmono

/-- A star position of a block face is a `none` (free) coordinate. -/
theorem faceStar_val_nones (g : serialWedge A ⟶ serialWedge B) (j : Fin A.length)
    (p : Fin (A.get j : ℕ)) :
    (faceStar g j).val (StdCube.nones (faceStar g j) p) = none := by
  rw [← StdCube.mem_noneSet]
  exact Finset.orderEmbOfFin_mem (StdCube.noneSet (faceStar g j).val) (faceStar g j).prop p

/-- **Value of the iterated-face map `app w v`.**  At a target coordinate `c`: a fixed
coordinate of `w` keeps `w`'s value; the `i`-th free coordinate of `w` takes `v`'s value
at source coordinate `i`.  (The value form of `noneSet_app`; the sign-vector↔corner
bridge is the `v := constVertex … ε` special case.) -/
theorem app_val {N K1 : ℕ} (w : StdCube.cells N K1) {J : ℕ} (v : StdCube.cells K1 J)
    (c : Fin N) :
    (StdCube.app (K := StdCube.stdPre N) w v).val c
      = if h : c ∈ StdCube.noneSet w.val then v.val (StdCube.nonesIdx w c h) else w.val c := by
  induction hd : K1 - J using Nat.strong_induction_on generalizing J v with
  | _ d ih =>
    rcases Nat.lt_or_ge J K1 with hlt | hge
    · rw [StdCube.app_unfold (K := StdCube.stdPre N) w v hlt]
      change (StdCube.face (StdCube.minFixedVal v hlt) (StdCube.minFixedIdx v hlt)
          (StdCube.app (K := StdCube.stdPre N) w (StdCube.freeMin v hlt))).val c = _
      rw [StdCube.face_val]
      have ihv := ih (K1 - (J + 1)) (by omega) (StdCube.freeMin v hlt) rfl
      have hnones : StdCube.nones
            (StdCube.app (K := StdCube.stdPre N) w (StdCube.freeMin v hlt))
            (StdCube.minFixedIdx v hlt)
          = StdCube.nones w (StdCube.minFixed v hlt) := by
        rw [nones_app, StdCube.nones_minFixedIdx]
      rw [hnones]
      by_cases hc : c ∈ StdCube.noneSet w.val
      · rw [dif_pos hc]
        by_cases hce : c = StdCube.nones w (StdCube.minFixed v hlt)
        · subst hce
          rw [Function.update_self]
          have hni : StdCube.nonesIdx w (StdCube.nones w (StdCube.minFixed v hlt)) hc
              = StdCube.minFixed v hlt :=
            (StdCube.nones w).injective (StdCube.nones_nonesIdx w _ hc)
          rw [hni, StdCube.minFixed_val_eq]
        · have hne : StdCube.nonesIdx w c hc ≠ StdCube.minFixed v hlt := by
            intro heq
            have hnn := StdCube.nones_nonesIdx w c hc
            rw [heq] at hnn
            exact hce hnn.symm
          rw [Function.update_of_ne hce, ihv, dif_pos hc, StdCube.freeMin_val,
            Function.update_of_ne hne]
      · rw [dif_neg hc]
        have hcne : c ≠ StdCube.nones w (StdCube.minFixed v hlt) := fun heq =>
          hc (by rw [heq]; exact Finset.orderEmbOfFin_mem _ w.prop _)
        rw [Function.update_of_ne hcne, ihv, dif_neg hc]
    · have hJK : J = K1 := le_antisymm (StdCube.cells_card_le v) hge
      subst hJK
      rw [StdCube.eq_topCell v, StdCube.app_topCell]
      by_cases hc : c ∈ StdCube.noneSet w.val
      · rw [dif_pos hc, StdCube.mem_noneSet.mp hc]
        rfl
      · rw [dif_neg hc]

/-- **Sign-vector↔corner bridge (target corner).**  `vertex₁ φ` classifies as the
`app` of `φ`'s star face at the all-`true` source vertex (`ev_comp` + `app_unique`). -/
theorem toStar_vertex₁_eq {N k : ℕ} (φ : (cube N).toPsh.cells k) :
    toStar ((cube N).toPsh.vertex₁ φ)
      = StdCube.app (K := StdCube.stdPre N) (toStar φ) (StdCube.constVertex k true) := by
  simp only [toStar_eq]
  change StdCube.ev (finalVertexMap k ≫ φ) = _
  rw [StdCube.ev_comp,
    show StdCube.ev (finalVertexMap k) = StdCube.constVertex k true from StdCube.ev_canonicalMap _]
  exact StdCube.app_unique φ rfl (StdCube.constVertex k true)

/-- **Sign-vector↔corner bridge (source corner).** -/
theorem toStar_vertex₀_eq {N k : ℕ} (φ : (cube N).toPsh.cells k) :
    toStar ((cube N).toPsh.vertex₀ φ)
      = StdCube.app (K := StdCube.stdPre N) (toStar φ) (StdCube.constVertex k false) := by
  simp only [toStar_eq]
  change StdCube.ev (initVertexMap k ≫ φ) = _
  rw [StdCube.ev_comp,
    show StdCube.ev (initVertexMap k) = StdCube.constVertex k false from StdCube.ev_canonicalMap _]
  exact StdCube.app_unique φ rfl (StdCube.constVertex k false)

/-- The target corner reads each coordinate as: `true` on the star (free) positions,
the fixed value elsewhere. -/
theorem toStar_vertex₁_val {N k : ℕ} (φ : (cube N).toPsh.cells k) (c : Fin N) :
    (toStar ((cube N).toPsh.vertex₁ φ)).val c
      = if _h : c ∈ StdCube.noneSet (toStar φ).val then some true else (toStar φ).val c := by
  rw [toStar_vertex₁_eq, app_val]
  by_cases h : c ∈ StdCube.noneSet (toStar φ).val
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]

/-- The source corner reads each coordinate as: `false` on the star positions, the fixed
value elsewhere. -/
theorem toStar_vertex₀_val {N k : ℕ} (φ : (cube N).toPsh.cells k) (c : Fin N) :
    (toStar ((cube N).toPsh.vertex₀ φ)).val c
      = if _h : c ∈ StdCube.noneSet (toStar φ).val then some false else (toStar φ).val c := by
  rw [toStar_vertex₀_eq, app_val]
  by_cases h : c ∈ StdCube.noneSet (toStar φ).val
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]

/-! ### Single-cube owner rule (cast-free `chainCoordMono`)

The residual geometry of the owner rule, on a plain directed chain in one cube `□ᴺ`
(no `ι`/`blockIdx`/`serialWedge` wrapping): coordinates only *increase* (`0 ≤ ∗ ≤ 1`)
along the chain.  The coordinate `c : Fin N` is shared by every face and the junction is
a direct cell equality in `□ᴺ`, so all block-index casts of `faceStar_val_mono` vanish. -/

/-- **Generic chain junction**: consecutive cubes of a chain share a vertex —
`vertex₁` of cube `i` equals `vertex₀` of cube `i+1` (`vtxCanon` interior identity).
Generalises `evCell_junction`; candidate to relocate to `Chains/Basic.lean`. -/
theorem isCubeChain_junction {K : BPSet} (a b : K.toPsh.cells 0)
    (cubes : List (Σ n : ℕ+, K.toPsh.cells (n : ℕ))) (h : IsCubeChain a cubes b)
    {i : ℕ} (hi : i + 1 < cubes.length) :
    K.toPsh.vertex₁ (cubes.get ⟨i, Nat.lt_of_succ_lt hi⟩).2
      = K.toPsh.vertex₀ (cubes.get ⟨i + 1, hi⟩).2 := by
  have h1 := isCubeChain_vtx_tgt a b cubes h ⟨i, Nat.lt_of_succ_lt hi⟩
  have h2 := vtxCanon_castSucc cubes b ⟨i + 1, hi⟩
  have hsucc : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin cubes.length).succ
      = (⟨i + 1, hi⟩ : Fin cubes.length).castSucc := Fin.ext rfl
  rw [h1, hsucc]; exact h2

/-- **Build a cube chain from a junction-vertex function.**  If `w : Fin (n+1) → cells 0`
has `w 0 = a`, `w (last) = b`, and each cube's source/target vertex is `w i` / `w (i+1)`,
the `ofFn` list is a chain from `a` to `b`. -/
theorem isCubeChain_ofFn {K : BPSet} :
    ∀ {n : ℕ} (f : Fin n → Σ m : ℕ+, K.toPsh.cells (m : ℕ)) (a b : K.toPsh.cells 0)
      (w : Fin (n + 1) → K.toPsh.cells 0) (_hw0 : w 0 = a) (_hwn : w (Fin.last n) = b)
      (_hsrc : ∀ i : Fin n, K.toPsh.vertex₀ (f i).2 = w i.castSucc)
      (_htgt : ∀ i : Fin n, K.toPsh.vertex₁ (f i).2 = w i.succ),
      IsCubeChain a (List.ofFn f) b
  | 0, f, a, b, w, hw0, hwn, _, _ => by
      simp only [List.ofFn_zero]
      change a = b
      rw [← hw0, ← hwn]; rfl
  | n + 1, f, a, b, w, hw0, hwn, hsrc, htgt => by
      rw [List.ofFn_succ]
      refine ⟨?_, isCubeChain_ofFn (fun i => f i.succ) (K.toPsh.vertex₁ (f 0).2) b
        (fun i => w i.succ) (htgt 0).symm ?_ (fun i => ?_) (fun i => ?_)⟩
      · rw [hsrc 0]; exact hw0
      · show w (Fin.last n).succ = b
        rw [Fin.succ_last]; exact hwn
      · show K.toPsh.vertex₀ (f i.succ).2 = w i.succ.castSucc
        rw [hsrc i.succ]
      · show K.toPsh.vertex₁ (f i.succ).2 = w i.succ.succ
        rw [htgt i.succ]

/-- The `i`-th face of a directed chain in `□ᴺ`, read as a `StdCube` sign vector. -/
noncomputable def chainFace {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ))) (i : Fin cubes.length) :
    StdCube.cells N ((cubes.get i).1 : ℕ) :=
  toStar (cubes.get i).2

/-- **One junction step of the single-cube owner rule** (cast-free `faceStar_step`):
a coordinate that is not `0` (`≠ some false`) at face `j` is `1` (`= some true`) at
face `j+1`.  Junction = direct cell equality in `□ᴺ` (`isCubeChain_junction`). -/
theorem chainCoordStep {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    {a b : (cube N).toPsh.cells 0} (h : IsCubeChain a cubes b)
    {j : ℕ} (hj1 : j + 1 < cubes.length) (c : Fin N)
    (hc : (chainFace cubes ⟨j, Nat.lt_of_succ_lt hj1⟩).val c ≠ some false) :
    (chainFace cubes ⟨j + 1, hj1⟩).val c = some true := by
  simp only [chainFace] at hc ⊢
  have hjunc := isCubeChain_junction a b cubes h hj1
  have e1 := toStar_vertex₁_val (cubes.get ⟨j, Nat.lt_of_succ_lt hj1⟩).2 c
  have e2 := toStar_vertex₀_val (cubes.get ⟨j + 1, hj1⟩).2 c
  have hval : (toStar ((cube N).toPsh.vertex₁ (cubes.get ⟨j, Nat.lt_of_succ_lt hj1⟩).2)).val c
      = (toStar ((cube N).toPsh.vertex₀ (cubes.get ⟨j + 1, hj1⟩).2)).val c := by rw [hjunc]
  rw [e1, e2] at hval
  have hLHS : (if _h : c ∈ StdCube.noneSet (toStar (cubes.get ⟨j, Nat.lt_of_succ_lt hj1⟩).2).val
      then (some true : Option Bool)
      else (toStar (cubes.get ⟨j, Nat.lt_of_succ_lt hj1⟩).2).val c) = some true := by
    by_cases hcn : c ∈ StdCube.noneSet (toStar (cubes.get ⟨j, Nat.lt_of_succ_lt hj1⟩).2).val
    · rw [dif_pos hcn]
    · rw [dif_neg hcn]
      rcases hval2 : (toStar (cubes.get ⟨j, Nat.lt_of_succ_lt hj1⟩).2).val c with _ | b
      · exact absurd (StdCube.mem_noneSet.mpr hval2) hcn
      · cases b
        · exact absurd hval2 hc
        · rfl
  rw [hLHS] at hval
  by_cases hcn' : c ∈ StdCube.noneSet (toStar (cubes.get ⟨j + 1, hj1⟩).2).val
  · rw [dif_pos hcn'] at hval
    exact absurd hval (by decide)
  · rw [dif_neg hcn'] at hval
    exact hval.symm

/-- **`chainCoordMono` — the single-cube owner rule.**  Along a directed chain in `□ᴺ`,
a coordinate `≠ 0` at an earlier face is `1` at every later face (`0 ≤ ∗ ≤ 1`, never
decreasing).  The cast-free core of `faceStar_val_mono`: `c : Fin N` is shared by all
faces, so no `blockIdx`/`Fin.cast (B.get·)` squeeze survives. -/
theorem chainCoordMono {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    {a b : (cube N).toPsh.cells 0} (h : IsCubeChain a cubes b)
    {i i' : Fin cubes.length} (hlt : (i : ℕ) < (i' : ℕ)) (c : Fin N)
    (hc : (chainFace cubes i).val c ≠ some false) :
    (chainFace cubes i').val c = some true := by
  have H : ∀ d (j : Fin cubes.length), (j : ℕ) = (i : ℕ) + d + 1 → (j : ℕ) ≤ (i' : ℕ) →
      (chainFace cubes j).val c = some true := by
    intro d
    induction d with
    | zero =>
      intro j hj0 hji'
      have hj1 : (i : ℕ) + 1 < cubes.length := by omega
      have hjeq : j = ⟨(i : ℕ) + 1, hj1⟩ := Fin.ext (by omega)
      rw [hjeq]
      have hc' : (chainFace cubes ⟨(i : ℕ), Nat.lt_of_succ_lt hj1⟩).val c ≠ some false := by
        rw [show (⟨(i : ℕ), Nat.lt_of_succ_lt hj1⟩ : Fin cubes.length) = i from Fin.ext rfl]
        exact hc
      exact chainCoordStep cubes h hj1 c hc'
    | succ d ih =>
      intro j hj0 hji'
      have hj1 : ((i : ℕ) + d + 1) + 1 < cubes.length := by omega
      have hjeq : j = ⟨((i : ℕ) + d + 1) + 1, hj1⟩ := Fin.ext (by omega)
      rw [hjeq]
      have hbound : (i : ℕ) + d + 1 ≤ (i' : ℕ) := by omega
      have ihval := ih ⟨(i : ℕ) + d + 1, Nat.lt_of_succ_lt hj1⟩ rfl hbound
      have hne : (chainFace cubes ⟨(i : ℕ) + d + 1, Nat.lt_of_succ_lt hj1⟩).val c ≠ some false := by
        rw [ihval]; decide
      exact chainCoordStep cubes h hj1 c hne
  exact H ((i' : ℕ) - (i : ℕ) - 1) i' (by omega) le_rfl

/-- **Ordered set partition of `Fin N` of shape `a`** — the combinatorial datum a
single-cube chain classifies: the block owning each coordinate (the face at which it
turns on), with each block `i` owning exactly `a.get i` coordinates. -/
structure OwnerData (a : List ℕ+) (N : ℕ) where
  /-- The block owning coordinate `c`. -/
  owner : Fin N → Fin a.length
  /-- Block `i` owns exactly `a.get i` coordinates. -/
  card : ∀ i : Fin a.length,
    (Finset.univ.filter (fun c => owner c = i)).card = (a.get i : ℕ)

/-- **Single-cube star-set disjointness** (cast-free `starSet_disjoint`): a coordinate is
free (`∗`) in at most one face of a directed `□ᴺ`-chain — immediate from `chainCoordMono`. -/
theorem chainStarSet_disjoint {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (cube N).init cubes (cube N).final)
    {i i' : Fin cubes.length} (hne : (i : ℕ) ≠ (i' : ℕ))
    {c : Fin N} (hi : (chainFace cubes i).val c = none)
    (hi' : (chainFace cubes i').val c = none) : False := by
  have key : ∀ {p q : Fin cubes.length}, (p : ℕ) < (q : ℕ) →
      (chainFace cubes p).val c = none → (chainFace cubes q).val c = none → False := by
    intro p q hpq hp hq
    have hne' : (chainFace cubes p).val c ≠ some false := by rw [hp]; decide
    have hq' := chainCoordMono cubes h hpq c hne'
    rw [hq] at hq'; exact absurd hq' (by decide)
  rcases Nat.lt_or_ge (i : ℕ) (i' : ℕ) with hlt | hge
  · exact key hlt hi hi'
  · exact key (show (i' : ℕ) < (i : ℕ) by omega) hi' hi

/-- The free (star) coordinates of face `i` of a single-cube chain. -/
noncomputable def chainStarSet {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (i : Fin cubes.length) : Finset (Fin N) :=
  StdCube.noneSet (chainFace cubes i).val

/-- Face `i` has exactly `dim(cube i)` free coordinates. -/
theorem chainStarSet_card {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ))) (i : Fin cubes.length) :
    (chainStarSet cubes i).card = ((cubes.get i).1 : ℕ) :=
  (chainFace cubes i).2

/-- The face dimensions of an `init → final` chain in `□ᴺ` sum to `N` — the altitude
gap `alt(final) − alt(init) = N` equals the chain's total dimension
(`isCubeChain_alt_final`), with `alt(final) = N` forced by the top cell. -/
theorem chainTotalDim {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (cube N).init cubes (cube N).final) :
    (cubes.map (fun c => (c.1 : ℕ))).sum = N := by
  obtain ⟨alt, hax, halt0⟩ := cube_admitsAltitude N
  have hfin := isCubeChain_alt_final alt hax cubes (cube N).init (cube N).final h
  rw [halt0, zero_add] at hfin
  have hfinN : alt 0 (cube N).final = (N : ℤ) := by
    set t : (cube N).toPsh.cells N := yonedaEquiv (𝟙 (yoneda.obj (Box.ob N))) with ht
    have h0 : (cube N).toPsh.vertex₀ t = (cube N).init := by
      rw [ht, PrecubicalSet.vertex₀_yonedaEquiv]; rfl
    have h1 : (cube N).toPsh.vertex₁ t = (cube N).final := by
      rw [ht, PrecubicalSet.vertex₁_yonedaEquiv]; rfl
    have e0 := PrecubicalSet.alt_vertex₀ alt hax t
    have e1 := PrecubicalSet.alt_vertex₁ alt hax t
    rw [h0] at e0; rw [h1] at e1
    rw [e1, ← e0, halt0, zero_add]
  rw [hfinN] at hfin
  exact_mod_cast hfin.symm

/-- The star sets of an `init → final` `□ᴺ`-chain **partition** `Fin N`: every
coordinate is free in some (by disjointness, exactly one) face — a counting argument
(`chainStarSet_disjoint` + `∑ card = N`). -/
theorem chainStarSet_cover {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (cube N).init cubes (cube N).final) (c : Fin N) :
    ∃ i, c ∈ chainStarSet cubes i := by
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin cubes.length)), ∀ j ∈ Finset.univ,
      i ≠ j → Disjoint (chainStarSet cubes i) (chainStarSet cubes j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hx hxj
    simp only [chainStarSet, StdCube.mem_noneSet] at hx hxj
    exact chainStarSet_disjoint cubes h (fun heq => hij (Fin.ext heq)) hx hxj
  have hsum : ∑ i : Fin cubes.length, (chainStarSet cubes i).card = N := by
    simp_rw [chainStarSet_card]
    have hlist : (∑ i : Fin cubes.length, ((cubes.get i).1 : ℕ))
        = (cubes.map (fun c => (c.1 : ℕ))).sum := by
      conv_rhs => rw [← List.ofFn_get cubes]
      rw [List.map_ofFn, List.sum_ofFn]
      rfl
    rw [hlist]; exact chainTotalDim cubes h
  have hcard : (Finset.univ.biUnion (chainStarSet cubes)).card = N := by
    rw [Finset.card_biUnion hdisj]; exact hsum
  have huniv : Finset.univ.biUnion (chainStarSet cubes) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
  have hmem : c ∈ Finset.univ.biUnion (chainStarSet cubes) := by
    rw [huniv]; exact Finset.mem_univ c
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  exact ⟨i, hi⟩

/-- The block owning coordinate `c`: the unique face at which `c` is free. -/
noncomputable def chainOwner {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (cube N).init cubes (cube N).final) (c : Fin N) : Fin cubes.length :=
  (chainStarSet_cover cubes h c).choose

/-- `c` is free in its owner's face. -/
theorem chainOwner_mem {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (cube N).init cubes (cube N).final) (c : Fin N) :
    c ∈ chainStarSet cubes (chainOwner cubes h c) :=
  (chainStarSet_cover cubes h c).choose_spec

/-- The owner is the unique face at which `c` is free. -/
theorem chainOwner_unique {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (cube N).init cubes (cube N).final) {c : Fin N} {i : Fin cubes.length}
    (hi : c ∈ chainStarSet cubes i) : i = chainOwner cubes h c := by
  by_contra hne
  have hi' := chainOwner_mem cubes h c
  simp only [chainStarSet, StdCube.mem_noneSet] at hi hi'
  exact chainStarSet_disjoint cubes h (fun heq => hne (Fin.ext heq)) hi hi'

/-- **The cumulative-OR corner model** (single-cube `realFaceVal`): from an `OwnerData`,
face `i` reads coordinate `c` as `∗` (free) if `i` owns it, `1` if an earlier block owns
it, `0` if a later block does. -/
def cornerFaceVal {a : List ℕ+} {N : ℕ} (o : OwnerData a N) (i : Fin a.length) :
    Fin N → Option Bool :=
  fun c => if o.owner c = i then none
    else if (o.owner c : ℕ) < (i : ℕ) then some true else some false

/-- Face `i` of the corner model has exactly `a.get i` free coordinates (the ones `i`
owns) — directly from `OwnerData.card`. -/
theorem cornerFace_card {a : List ℕ+} {N : ℕ} (o : OwnerData a N) (i : Fin a.length) :
    (StdCube.noneSet (cornerFaceVal o i)).card = (a.get i : ℕ) := by
  have hset : StdCube.noneSet (cornerFaceVal o i)
      = Finset.univ.filter (fun c => o.owner c = i) := by
    ext c
    simp only [StdCube.mem_noneSet, Finset.mem_filter, Finset.mem_univ, true_and, cornerFaceVal]
    split_ifs with hoc h2 <;> simp_all
  rw [hset, o.card i]

/-- Face `i` of the corner model as a `StdCube` cell. -/
def cornerFace {a : List ℕ+} {N : ℕ} (o : OwnerData a N) (i : Fin a.length) :
    StdCube.cells N (a.get i : ℕ) :=
  ⟨cornerFaceVal o i, cornerFace_card o i⟩

/-- The `□ᴺ`-cell corresponding to corner face `i`. -/
noncomputable def cornerCell {a : List ℕ+} {N : ℕ} (o : OwnerData a N) (i : Fin a.length) :
    (cube N).toPsh.cells (a.get i : ℕ) :=
  StdCube.canonicalMap (cornerFace o i)

/-- The stage-`i` vertex: coordinate `c` is `1` iff its owner comes strictly before `i`
(the cumulative-OR corners along the corner chain). -/
def cornerVtxVec {a : List ℕ+} {N : ℕ} (o : OwnerData a N) (i : ℕ) : StdCube.cells N 0 :=
  ⟨fun c => if (o.owner c : ℕ) < i then some true else some false, by
    rw [Finset.card_eq_zero]; ext c
    simp only [StdCube.mem_noneSet, Finset.notMem_empty, iff_false]
    split_ifs <;> simp⟩

/-- Dim-`0` cells of `□ᴺ` are determined by their sign vector (`toStar` injective). -/
theorem cellZero_ext {N : ℕ} {u v : (cube N).toPsh.cells 0}
    (hval : ∀ c, (toStar u).val c = (toStar v).val c) : u = v :=
  toStar_injective (Subtype.ext (funext hval))

/-- The corner-model chain of an `OwnerData` (the reverse map's cube list). -/
noncomputable def cornerChain {a : List ℕ+} {N : ℕ} (o : OwnerData a N) :
    List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)) :=
  List.ofFn (fun i : Fin a.length => ⟨a.get i, cornerCell o i⟩)

/-- `cornerFaceVal` is `none` (free) exactly at the coordinates block `i` owns. -/
theorem cornerFaceVal_none_iff {a : List ℕ+} {N : ℕ} (o : OwnerData a N) (i : Fin a.length)
    (c : Fin N) : cornerFaceVal o i c = none ↔ o.owner c = i := by
  simp only [cornerFaceVal]; split_ifs with h1 h2 <;> simp_all

/-- **Owner-rule reconstruction.**  Every face value is determined by the owner: `∗` at
its owner block, `1` after, `0` before.  Both directions of `chainCoordMono`; this is the
content that makes the event permutation classify the whole wedge map. -/
theorem chainFace_eq_owner {N : ℕ}
    (cubes : List (Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ)))
    (h : IsCubeChain (cube N).init cubes (cube N).final)
    (i : Fin cubes.length) (c : Fin N) :
    (chainFace cubes i).val c =
      if chainOwner cubes h c = i then none
      else if (chainOwner cubes h c : ℕ) < (i : ℕ) then some true else some false := by
  set o := chainOwner cubes h c with ho
  have hmem : c ∈ chainStarSet cubes o := chainOwner_mem cubes h c
  simp only [chainStarSet, StdCube.mem_noneSet] at hmem
  by_cases hoi : o = i
  · rw [if_pos hoi, ← hoi]; exact hmem
  · rw [if_neg hoi]
    by_cases hlt : (o : ℕ) < (i : ℕ)
    · rw [if_pos hlt]
      exact chainCoordMono cubes h hlt c (by rw [hmem]; decide)
    · rw [if_neg hlt]
      have hgt : (i : ℕ) < (o : ℕ) := by
        rcases Nat.lt_or_ge (i : ℕ) (o : ℕ) with h1 | h1
        · exact h1
        · exact absurd (Fin.ext (le_antisymm h1 (by omega))) hoi
      rcases hv : (chainFace cubes i).val c with _ | b
      · have hi_owner : i = o := chainOwner_unique cubes h (StdCube.mem_noneSet.mpr hv)
        rw [hi_owner] at hgt; exact absurd hgt (lt_irrefl _)
      · cases b
        · rfl
        · have := chainCoordMono cubes h hgt c (by rw [hv]; decide)
          rw [hmem] at this; exact absurd this (by decide)

/-- **The corner-model chain is a directed `□ᴺ`-chain** `init → final`.  Assembled via
`isCubeChain_ofFn`: the stage vertices `cornerVtxVec o i` (coords with owner `< i` set to
`1`) are the junctions, `vertex₀(face i) = stage i` and `vertex₁(face i) = stage (i+1)`. -/
theorem cornerChain_isChain {a : List ℕ+} {N : ℕ} (o : OwnerData a N) :
    IsCubeChain (cube N).init (cornerChain o) (cube N).final := by
  refine isCubeChain_ofFn (fun i : Fin a.length => (⟨a.get i, cornerCell o i⟩ :
      Σ n : ℕ+, (cube N).toPsh.cells (n : ℕ))) (cube N).init (cube N).final
    (fun i : Fin (a.length + 1) => StdCube.canonicalMap (cornerVtxVec o (i : ℕ))) ?_ ?_ ?_ ?_
  · -- w 0 = init
    apply cellZero_ext; intro c
    rw [toStar_canonicalMap,
      show (cube N).init = StdCube.canonicalMap (StdCube.constVertex N false) from rfl,
      toStar_canonicalMap]
    simp [cornerVtxVec, StdCube.constVertex]
  · -- w last = final
    apply cellZero_ext; intro c
    rw [toStar_canonicalMap,
      show (cube N).final = StdCube.canonicalMap (StdCube.constVertex N true) from rfl,
      toStar_canonicalMap]
    simp only [cornerVtxVec, StdCube.constVertex, Fin.val_last, if_pos (o.owner c).2]
  · -- vertex₀ (face i) = stage i
    intro i
    apply cellZero_ext; intro c
    show (toStar ((cube N).toPsh.vertex₀ (StdCube.canonicalMap (cornerFace o i)))).val c = _
    rw [toStar_vertex₀_val]
    simp only [toStar_canonicalMap, Fin.val_castSucc, cornerVtxVec, cornerFace]
    by_cases hoc : o.owner c = i
    · rw [dif_pos (StdCube.mem_noneSet.mpr ((cornerFaceVal_none_iff o i c).mpr hoc))]; simp [hoc]
    · rw [dif_neg (fun hm => hoc ((cornerFaceVal_none_iff o i c).mp (StdCube.mem_noneSet.mp hm)))]
      have hoc' : (o.owner c : ℕ) ≠ (i : ℕ) := fun h => hoc (Fin.ext h)
      simp only [cornerFaceVal, if_neg hoc]
      split_ifs with h1 h2 <;> first | rfl | omega
  · -- vertex₁ (face i) = stage (i+1)
    intro i
    apply cellZero_ext; intro c
    show (toStar ((cube N).toPsh.vertex₁ (StdCube.canonicalMap (cornerFace o i)))).val c = _
    rw [toStar_vertex₁_val]
    simp only [toStar_canonicalMap, Fin.val_succ, cornerVtxVec, cornerFace]
    by_cases hoc : o.owner c = i
    · rw [dif_pos (StdCube.mem_noneSet.mpr ((cornerFaceVal_none_iff o i c).mpr hoc))]; simp [hoc]
    · rw [dif_neg (fun hm => hoc ((cornerFaceVal_none_iff o i c).mp (StdCube.mem_noneSet.mp hm)))]
      simp only [cornerFaceVal, if_neg hoc]
      have hoc' : (o.owner c : ℕ) ≠ (i : ℕ) := fun h => hoc (Fin.ext h)
      split_ifs with h1 h2 <;> first | rfl | omega

/-- Two cube-`r` faces whose `ι B r`-images share a junction vertex (`vertex₁ x`
identified with `vertex₀ y`) read the same value at every coordinate — by **dim-0
injectivity** of the block inclusion (`serialWedge_ι_app_injective`). -/
theorem blockFace_junction_val {r : Fin B.length} {k1 k2 : ℕ}
    (x : (cube (B.get r : ℕ)).toPsh.cells k1) (y : (cube (B.get r : ℕ)).toPsh.cells k2)
    (hV : (BPSet.serialWedge.ι B r).app (op (Box.ob 0))
            ((cube (B.get r : ℕ)).toPsh.vertex₁ x)
          = (BPSet.serialWedge.ι B r).app (op (Box.ob 0))
            ((cube (B.get r : ℕ)).toPsh.vertex₀ y))
    (c : Fin (B.get r : ℕ)) :
    (toStar ((cube (B.get r : ℕ)).toPsh.vertex₁ x)).val c
      = (toStar ((cube (B.get r : ℕ)).toPsh.vertex₀ y)).val c := by
  have heq : (cube (B.get r : ℕ)).toPsh.vertex₁ x = (cube (B.get r : ℕ)).toPsh.vertex₀ y :=
    serialWedge_ι_app_injective B r hV
  rw [heq]

/-- **Chain junction of the event cells.**  Consecutive source blocks map to cells that
meet at a junction vertex of `□^∨(B)`: `vertex₁ (evCell g j) = vertex₀ (evCell g (j+1))`.
The event cells are the cubes of the chain `wedgeToCubes ⟨A, g⟩` (`hLchain`); the junction
is the `vtxCanon` interior identity. -/
theorem evCell_junction (g : serialWedge A ⟶ serialWedge B) (j : Fin A.length)
    (hj : (j : ℕ) + 1 < A.length) :
    (serialWedge B).toPsh.vertex₁ (evCell g j)
      = (serialWedge B).toPsh.vertex₀ (evCell g ⟨(j : ℕ) + 1, hj⟩) := by
  have hLlen : (wedgeToCubes ⟨A, g.hom⟩).length = A.length := wedgeToCubes_length A g.hom
  have hLchain : IsCubeChain (serialWedge B).init (wedgeToCubes ⟨A, g.hom⟩)
      (serialWedge B).final := by
    have h := wedgeToCubes_isCubeChain A g.hom
    rwa [g.app_init, g.app_final] at h
  have hj1L : (j : ℕ) + 1 < (wedgeToCubes ⟨A, g.hom⟩).length := by rw [hLlen]; exact hj
  -- the two `L.get`s are the event cells (cast-free once we identify the `Fin`)
  have hget : ∀ (i : Fin A.length) (hiL : (i : ℕ) < (wedgeToCubes ⟨A, g.hom⟩).length),
      (wedgeToCubes ⟨A, g.hom⟩).get ⟨(i : ℕ), hiL⟩ = ⟨A.get i, evCell g i⟩ := by
    intro i hiL
    have hcast : (⟨(i : ℕ), hiL⟩ : Fin (wedgeToCubes ⟨A, g.hom⟩).length).cast hLlen = i :=
      Fin.ext rfl
    rw [wedgeToCubes_get A g.hom ⟨(i : ℕ), hiL⟩, hcast]
    rfl
  have hjunc := isCubeChain_junction (serialWedge B).init (serialWedge B).final
    (wedgeToCubes ⟨A, g.hom⟩) hLchain hj1L
  rw [hget j (Nat.lt_of_succ_lt hj1L), hget ⟨(j : ℕ) + 1, hj⟩ hj1L] at hjunc
  exact hjunc

/-- The junction reading, with the target-block index carried as a variable so the
`Fin`/cube-type cast between blocks `r` and `r'` discharges by `subst`. -/
theorem faceStar_step_aux {k1 k2 : ℕ} {r r' : Fin B.length} (hrr : r = r')
    (x : (cube (B.get r : ℕ)).toPsh.cells k1) (y : (cube (B.get r' : ℕ)).toPsh.cells k2)
    (hV : (BPSet.serialWedge.ι B r).app (op (Box.ob 0))
            ((cube (B.get r : ℕ)).toPsh.vertex₁ x)
          = (BPSet.serialWedge.ι B r').app (op (Box.ob 0))
            ((cube (B.get r' : ℕ)).toPsh.vertex₀ y))
    (c : Fin (B.get r : ℕ)) :
    (toStar ((cube (B.get r : ℕ)).toPsh.vertex₁ x)).val c
      = (toStar ((cube (B.get r' : ℕ)).toPsh.vertex₀ y)).val
          (Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) hrr) c) := by
  subst hrr
  simpa using blockFace_junction_val x y hV c

/-- **One junction step of the owner rule.**  For consecutive source blocks `j, j+1`
mapping to the same target block, a coordinate that is not `0` at block `j` (`≠ some
false`) is `1` at block `j+1` (`= some true`).  Combines the chain junction
(`evCell_junction`), the corner bridge (`toStar_vertex₀/₁_val`), and dim-0 injectivity
(`faceStar_step_aux`). -/
theorem faceStar_step (g : serialWedge A ⟶ serialWedge B) (j : Fin A.length)
    (hj : (j : ℕ) + 1 < A.length)
    (hr : blockIdx g j = blockIdx g ⟨(j : ℕ) + 1, hj⟩)
    (c : Fin (B.get (blockIdx g j) : ℕ)) (hc : (faceStar g j).val c ≠ some false) :
    (faceStar g ⟨(j : ℕ) + 1, hj⟩).val
        (Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) hr) c) = some true := by
  have e1 : (BPSet.serialWedge.ι B (blockIdx g j)).app (op (Box.ob 0))
        ((cube (B.get (blockIdx g j) : ℕ)).toPsh.vertex₁ (blockFace g j))
      = (serialWedge B).toPsh.vertex₁ (evCell g j) := by
    rw [map_vertex₁ (BPSet.serialWedge.ι B (blockIdx g j)) (blockFace g j), blockFace_spec g j]
  have e2 : (BPSet.serialWedge.ι B (blockIdx g ⟨(j : ℕ) + 1, hj⟩)).app (op (Box.ob 0))
        ((cube (B.get (blockIdx g ⟨(j : ℕ) + 1, hj⟩) : ℕ)).toPsh.vertex₀
          (blockFace g ⟨(j : ℕ) + 1, hj⟩))
      = (serialWedge B).toPsh.vertex₀ (evCell g ⟨(j : ℕ) + 1, hj⟩) := by
    rw [map_vertex₀ (BPSet.serialWedge.ι B (blockIdx g ⟨(j : ℕ) + 1, hj⟩))
      (blockFace g ⟨(j : ℕ) + 1, hj⟩), blockFace_spec g ⟨(j : ℕ) + 1, hj⟩]
  have hV := e1.trans ((evCell_junction g j hj).trans e2.symm)
  have hval := faceStar_step_aux hr (blockFace g j) (blockFace g ⟨(j : ℕ) + 1, hj⟩) hV c
  rw [toStar_vertex₁_val, toStar_vertex₀_val] at hval
  -- the left side is `some true` (from `hc`); force the right side's else-branch.
  have hLHS : (if _h : c ∈ StdCube.noneSet (toStar (blockFace g j)).val
      then (some true : Option Bool) else (toStar (blockFace g j)).val c) = some true := by
    by_cases hcn : c ∈ StdCube.noneSet (toStar (blockFace g j)).val
    · rw [dif_pos hcn]
    · rw [dif_neg hcn]
      rcases hval2 : (toStar (blockFace g j)).val c with _ | b
      · exact absurd (StdCube.mem_noneSet.mpr hval2) hcn
      · cases b
        · exact absurd hval2 hc
        · rfl
  rw [hLHS] at hval
  by_cases hcn' : (Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) hr) c)
      ∈ StdCube.noneSet (toStar (blockFace g ⟨(j : ℕ) + 1, hj⟩)).val
  · rw [dif_pos hcn'] at hval
    exact absurd hval (by decide)
  · rw [dif_neg hcn'] at hval
    exact hval.symm

/-- Value-parametrised junction step: the target block `j'` is any `Fin` one past `j`,
and the coordinate is tracked by value (`subst` absorbs the index so no cast survives). -/
theorem faceStar_step_v (g : serialWedge A ⟶ serialWedge B) (j j' : Fin A.length)
    (hjj' : (j' : ℕ) = (j : ℕ) + 1) (hr : blockIdx g j = blockIdx g j')
    (c : Fin (B.get (blockIdx g j) : ℕ)) (hc : (faceStar g j).val c ≠ some false)
    (y : Fin (B.get (blockIdx g j') : ℕ)) (hy : (y : ℕ) = (c : ℕ)) :
    (faceStar g j').val y = some true := by
  have hj1 : (j : ℕ) + 1 < A.length := by rw [← hjj']; exact j'.2
  obtain rfl : j' = ⟨(j : ℕ) + 1, hj1⟩ := Fin.ext hjj'
  have hstep := faceStar_step g j hj1 hr c hc
  rwa [show Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) hr) c = y from
    Fin.ext (by simpa using hy.symm)] at hstep

/-- **DEFERRED — the one irreducible geometric fact (PZ Lemma 6.x, "coordinate
monotonicity along the directed junction path").**  For two source blocks `i < i'`
(serial order) mapping to the *same* target block `r`, the coordinates of the target
cube `□^{B.get r}` only *increase* along the image of the source spine: a coordinate
that is *not `0`* at the exit vertex of block `i` (i.e. `(faceStar g i).val c ≠ some
false`, so `∗` or `1` at `vertex₁ (faceStar g i)`) is *fixed to `1`* at the entry vertex
of block `i'` (i.e. `(faceStar g i').val c = some true`, `vertex₀ (faceStar g i')`).

Geometric proof (not yet formalized): `g` preserves reachability
(`PrecubicalSet.Reaches.map`); the source junctions `v_{i+1} ≼ … ≼ v_{i'}` form a
directed path whose `g`-image lands, at its block-`r` endpoints, on `vertex₁ (faceStar
g i)` and `vertex₀ (faceStar g i')`; inside a cube reachability is the componentwise
order (`0 ≤ ∗ ≤ 1`, never decreasing), so a coordinate that is `≠ 0` at the earlier
vertex is `1` at the later one.  This single monotonicity fact powers both
`starSet_disjoint` (disjointness of star sets) and `evCell_determined` (recovery of the
fixed `0/1` values), hence `ev_reconstruct`; everything else in the section is proved on
top of it. -/
theorem faceStar_val_mono (g : serialWedge A ⟶ serialWedge B) {i i' : Fin A.length}
    (hlt : (i : ℕ) < (i' : ℕ)) (hr : blockIdx g i = blockIdx g i')
    (c : Fin (B.get (blockIdx g i) : ℕ)) (hc : (faceStar g i).val c ≠ some false) :
    (faceStar g i').val (Fin.cast (congrArg (fun r : Fin B.length => (B.get r : ℕ)) hr) c)
      = some true := by
  -- all blocks in `[i, i']` equal `blockIdx g i` (block-monotone squeezed by the endpoints)
  have hsqueeze : ∀ (m : ℕ) (hm : m < A.length), (i : ℕ) ≤ m → m ≤ (i' : ℕ) →
      blockIdx g ⟨m, hm⟩ = blockIdx g i := by
    intro m hm him hmi'
    have h1 := blockIdx_monotone g (show i ≤ (⟨m, hm⟩ : Fin A.length) from Fin.le_def.mpr him)
    have h2 := blockIdx_monotone g (show (⟨m, hm⟩ : Fin A.length) ≤ i' from Fin.le_def.mpr hmi')
    rw [← hr] at h2
    exact le_antisymm h2 h1
  -- iterate the junction step; track only the coordinate's *value* so all casts collapse
  have H : ∀ d (j : Fin A.length), (j : ℕ) = (i : ℕ) + d + 1 → (j : ℕ) ≤ (i' : ℕ) →
      ∀ (y : Fin (B.get (blockIdx g j) : ℕ)), (y : ℕ) = (c : ℕ) →
      (faceStar g j).val y = some true := by
    intro d
    induction d with
    | zero =>
      intro j hj0 hji' y hy
      have hr_step : blockIdx g i = blockIdx g j := by
        have hB := hsqueeze (j : ℕ) j.2 (by omega) hji'
        rw [Fin.eta] at hB; exact hB.symm
      exact faceStar_step_v g i j (by omega) hr_step c hc y hy
    | succ d ih =>
      intro j hj0 hji' y hy
      have hlen'' : (i : ℕ) + d + 1 < A.length := by omega
      have hji'' : (i : ℕ) + d + 1 ≤ (i' : ℕ) := by omega
      have hbA : blockIdx g ⟨(i : ℕ) + d + 1, hlen''⟩ = blockIdx g i :=
        hsqueeze ((i : ℕ) + d + 1) hlen'' (by omega) hji''
      have hbB : blockIdx g j = blockIdx g i := by
        have hB := hsqueeze (j : ℕ) j.2 (by omega) hji'
        rwa [Fin.eta] at hB
      set y' : Fin (B.get (blockIdx g ⟨(i : ℕ) + d + 1, hlen''⟩) : ℕ) :=
        Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) hbA.symm) c with hy'def
      have hy'val : (y' : ℕ) = (c : ℕ) := by simp [hy'def]
      have ihval := ih ⟨(i : ℕ) + d + 1, hlen''⟩ rfl hji'' y' hy'val
      have hne : (faceStar g ⟨(i : ℕ) + d + 1, hlen''⟩).val y' ≠ some false := by
        rw [ihval]; decide
      exact faceStar_step_v g ⟨(i : ℕ) + d + 1, hlen''⟩ j (by omega) (hbA.trans hbB.symm)
        y' hne y (hy.trans hy'val.symm)
  -- specialise to the endpoint `i'`
  exact H ((i' : ℕ) - (i : ℕ) - 1) i' (by omega) le_rfl
    (Fin.cast (congrArg (fun r : Fin B.length => (B.get r : ℕ)) hr) c) (by simp)

/-- A coordinate free in an *earlier* block `i'' < i` (same target block) is fixed to
`true` in block `i` — the "already traversed" direction of the monotonicity. -/
theorem faceStar_fixed_true (g : serialWedge A ⟶ serialWedge B) {i i'' : Fin A.length}
    (hlt : (i'' : ℕ) < (i : ℕ)) (hb : blockIdx g i'' = blockIdx g i)
    (c : Fin (B.get (blockIdx g i) : ℕ)) (c'' : Fin (B.get (blockIdx g i'') : ℕ))
    (hcc : (c'' : ℕ) = (c : ℕ)) (hfree : (faceStar g i'').val c'' = none) :
    (faceStar g i).val c = some true := by
  have hmono := faceStar_val_mono g hlt hb c'' (by rw [hfree]; decide)
  have hcast : Fin.cast (congrArg (fun r : Fin B.length => (B.get r : ℕ)) hb) c'' = c := by
    apply Fin.ext; change (c'' : ℕ) = (c : ℕ); exact hcc
  rwa [hcast] at hmono

/-- A coordinate free in a *later* block `i < i''` (same target block) is fixed to
`false` in block `i` — the "not yet traversed" direction of the monotonicity. -/
theorem faceStar_fixed_false (g : serialWedge A ⟶ serialWedge B) {i i'' : Fin A.length}
    (hlt : (i : ℕ) < (i'' : ℕ)) (hb : blockIdx g i'' = blockIdx g i)
    (c : Fin (B.get (blockIdx g i) : ℕ)) (c'' : Fin (B.get (blockIdx g i'') : ℕ))
    (hcc : (c'' : ℕ) = (c : ℕ)) (hfree : (faceStar g i'').val c'' = none) :
    (faceStar g i).val c = some false := by
  by_contra hcon
  have hmono := faceStar_val_mono g hlt hb.symm c hcon
  have hcast : Fin.cast (congrArg (fun r : Fin B.length => (B.get r : ℕ)) hb.symm) c = c'' := by
    apply Fin.ext; change (c : ℕ) = (c'' : ℕ); exact hcc.symm
  rw [hcast, hfree] at hmono
  simp at hmono

/-- Extensionality for `Σ r, StdCube.cells (B.get r) k` with equal block index and
pointwise-in-`ℕ` equal values (the `subst` transports the coordinate cast). -/
theorem sigmaStar_ext {k : ℕ} {r r' : Fin B.length} (hrr : r = r')
    (x : StdCube.cells (B.get r : ℕ) k) (x' : StdCube.cells (B.get r' : ℕ) k)
    (hval : ∀ (c : Fin (B.get r : ℕ)) (c' : Fin (B.get r' : ℕ)),
        (c : ℕ) = (c' : ℕ) → x.val c = x'.val c') :
    (⟨r, x⟩ : Σ r : Fin B.length, StdCube.cells (B.get r : ℕ) k) = ⟨r', x'⟩ := by
  subst hrr
  exact congrArg (Sigma.mk r) (Subtype.ext (funext fun c => hval c c rfl))

/-- **Star-set disjointness** (PZ Lemma 6.x).  Two *distinct* source blocks that map to
the *same* target block have disjoint star sets: no target coordinate is a star of both.
Proved from the coordinate monotonicity `faceStar_val_mono`: a coordinate free in the
earlier block is fixed to `true` in the later one, hence not free there. -/
theorem starSet_disjoint (g : serialWedge A ⟶ serialWedge B) (i i' : Fin A.length)
    (hb : blockIdx g i = blockIdx g i') (hne : i ≠ i')
    (p : Fin (A.get i : ℕ)) (p' : Fin (A.get i' : ℕ)) :
    (StdCube.nones (faceStar g i) p : ℕ) ≠ (StdCube.nones (faceStar g i') p' : ℕ) := by
  -- symmetric core: for `j` strictly earlier than `j'`, their star sets are disjoint.
  have core : ∀ (j j' : Fin A.length), (j : ℕ) < (j' : ℕ) → blockIdx g j = blockIdx g j' →
      ∀ (q : Fin (A.get j : ℕ)) (q' : Fin (A.get j' : ℕ)),
      (StdCube.nones (faceStar g j) q : ℕ) ≠ (StdCube.nones (faceStar g j') q' : ℕ) := by
    intro j j' hjj hbjj q q' hval
    have hqfree : (faceStar g j).val (StdCube.nones (faceStar g j) q) = none :=
      faceStar_val_nones g j q
    have hmono := faceStar_val_mono g hjj hbjj (StdCube.nones (faceStar g j) q)
      (by rw [hqfree]; decide)
    have hcast_eq : Fin.cast (congrArg (fun r : Fin B.length => (B.get r : ℕ)) hbjj)
          (StdCube.nones (faceStar g j) q) = StdCube.nones (faceStar g j') q' := by
      apply Fin.ext
      change (StdCube.nones (faceStar g j) q : ℕ) = (StdCube.nones (faceStar g j') q' : ℕ)
      exact hval
    rw [hcast_eq, faceStar_val_nones g j' q'] at hmono
    simp at hmono
  intro hval
  rcases lt_trichotomy (i : ℕ) (i' : ℕ) with hlt | heq | hgt
  · exact core i i' hlt hb p p' hval
  · exact hne (Fin.ext heq)
  · exact core i' i hgt hb.symm p' p hval.symm

/-- **The block re-indexing is injective** — same target block + same star position
forces the same source block (`starSet_disjoint`), then `nones` is injective within a
block. -/
theorem evBlk_injective (g : serialWedge A ⟶ serialWedge B) :
    Function.Injective (evBlk g) := by
  rintro ⟨i, p⟩ ⟨i', p'⟩ h
  have hb : blockIdx g i = blockIdx g i' := congrArg Sigma.fst h
  have hv : (StdCube.nones (faceStar g i) p : ℕ)
      = (StdCube.nones (faceStar g i') p' : ℕ) :=
    congrArg (fun s : Σ r : Fin B.length, Fin (B.get r : ℕ) => (s.2 : ℕ)) h
  by_cases hii : i = i'
  · subst hii
    have hpp : p = p' := (StdCube.nones (faceStar g i)).injective (Fin.ext hv)
    subst hpp; rfl
  · exact absurd hv (starSet_disjoint g i i' hb hii p p')

/-- **`ev` is injective** — composite of the injective global re-indexings and
`evBlk_injective`. -/
theorem ev_injective (g : serialWedge A ⟶ serialWedge B) : Function.Injective (ev g) :=
  (globalEquiv B).injective.comp ((evBlk_injective g).comp (globalEquiv A).symm.injective)

/-- **`ev` is bijective** — injectivity plus `dimSum` preservation (equal cardinality). -/
theorem ev_bijective (g : serialWedge A ⟶ serialWedge B) : Function.Bijective (ev g) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨ev_injective g, by rw [Fintype.card_fin, Fintype.card_fin, dimSum_eq g]⟩

/-- **The event permutation** `evPerm g : Fin (dimSum A) ≃ Fin (dimSum B)** (README
Step 3.1) — the packaged bijection underlying the main functor. -/
noncomputable def evPerm (g : serialWedge A ⟶ serialWedge B) :
    Fin (dimSum A) ≃ Fin (dimSum B) :=
  Equiv.ofBijective (ev g) (ev_bijective g)

@[simp] theorem evPerm_apply (g : serialWedge A ⟶ serialWedge B) (e : Fin (dimSum A)) :
    evPerm g e = ev g e := rfl

/-- **The blocks partition** (README Step 3.3): every target event in block `r`
originates from a source block that maps to `r`.  Together with `ev_blockOf` (the
forward inclusion) this says the source blocks over a target segment cover exactly
that target block.  Derived from bijectivity. -/
theorem ev_blocks (g : serialWedge A ⟶ serialWedge B) (t : Fin (dimSum B)) :
    blockIdx g ((globalEquiv A).symm ((evPerm g).symm t)).1 = ((globalEquiv B).symm t).1 := by
  set s := (globalEquiv A).symm ((evPerm g).symm t) with hs
  have key := ev_blockOf g s.1 s.2
  rw [show (⟨s.1, s.2⟩ : Σ r : Fin A.length, Fin (A.get r : ℕ)) = s from rfl, hs,
    Equiv.apply_symm_apply,
    show ev g ((evPerm g).symm t) = t from (evPerm g).apply_symm_apply t] at key
  exact key.symm

/-- **The value-determination fact (PZ Definition 6.11).**  Two wedge maps with the same
event tracking classify the same block cell.  `ev g` records the target block
(`ev_blockOf`) and the *star* positions of `blockFace g i`; the remaining non-star `0/1`
coordinates are recovered by the fixed-value rule (a coordinate fixed in block `i` is
`1` iff it is the star of an *earlier* source block mapping to the same target — already
traversed — and `0` if later).  That "earlier/later" is the monotonicity
`faceStar_val_mono`; the owner block of each fixed coordinate exists by surjectivity of
`ev` (`ev_bijective`).  The full reconstruction (`ev_reconstruct`) is proved on top of
this via `serialWedge_hom_ext`. -/
theorem evCell_determined {g g' : serialWedge A ⟶ serialWedge B} (h : ev g = ev g')
    (i : Fin A.length) : evCell g i = evCell g' i := by
  -- Step 1: the block indices agree (blocks are nonempty, `ev_blockOf` reads them off).
  have hblock : ∀ j : Fin A.length, blockIdx g j = blockIdx g' j := by
    intro j
    have key := ev_blockOf g j ⟨0, (A.get j).pos⟩
    have key' := ev_blockOf g' j ⟨0, (A.get j).pos⟩
    rw [h] at key
    exact key.symm.trans key'
  -- Step 2: the star positions agree (in ℕ), block by block.
  have hnones : ∀ (j : Fin A.length) (p : Fin (A.get j : ℕ)),
      (StdCube.nones (faceStar g j) p : ℕ) = (StdCube.nones (faceStar g' j) p : ℕ) := by
    intro j p
    have key := ev_apply g j p
    have key' := ev_apply g' j p
    rw [h, key'] at key
    have hsig := (globalEquiv B).injective key
    exact (congrArg (fun s : Σ r : Fin B.length, Fin (B.get r : ℕ) => (s.2 : ℕ)) hsig).symm
  -- The pointwise value determination: `faceStar g i` and `faceStar g' i` agree.
  have hval : ∀ (c : Fin (B.get (blockIdx g i) : ℕ)) (c' : Fin (B.get (blockIdx g' i) : ℕ)),
      (c : ℕ) = (c' : ℕ) → (faceStar g i).val c = (faceStar g' i).val c' := by
    intro c c' hcc0
    by_cases hfreeC : (faceStar g i).val c = none
    · -- `c` is a star of block `i`; the same star index gives a star of block `i` for `g'`.
      have hx : c ∈ StdCube.noneSet (faceStar g i).val := by rw [StdCube.mem_noneSet]; exact hfreeC
      set idx := StdCube.nonesIdx (faceStar g i) c hx with hidx_def
      have hp : StdCube.nones (faceStar g i) idx = c := StdCube.nones_nonesIdx (faceStar g i) c hx
      have hval_c' : (StdCube.nones (faceStar g' i) idx : ℕ) = (c' : ℕ) := by
        rw [← hnones i idx]
        have h1 : (StdCube.nones (faceStar g i) idx : ℕ) = (c : ℕ) := by rw [hp]
        rw [h1, hcc0]
      have hc'eq : c' = StdCube.nones (faceStar g' i) idx := Fin.ext hval_c'.symm
      rw [hfreeC, hc'eq, faceStar_val_nones g' i]
    · -- `c` is fixed; find its owner block `i''` via surjectivity of `ev g`.
      obtain ⟨s0, hs0⟩ := (ev_bijective g).2 (globalEquiv B ⟨blockIdx g i, c⟩)
      obtain ⟨⟨i'', p''⟩, hsd⟩ : ∃ sd, globalEquiv A sd = s0 :=
        ⟨(globalEquiv A).symm s0, Equiv.apply_symm_apply _ _⟩
      rw [← hsd, ev_apply g i'' p''] at hs0
      have hsig := (globalEquiv B).injective hs0
      have hidx'' : blockIdx g i'' = blockIdx g i := congrArg Sigma.fst hsig
      have hval'' : (StdCube.nones (faceStar g i'') p'' : ℕ) = (c : ℕ) :=
        congrArg (fun s : Σ r : Fin B.length, Fin (B.get r : ℕ) => (s.2 : ℕ)) hsig
      have hfree'' : (faceStar g i'').val (StdCube.nones (faceStar g i'') p'') = none :=
        faceStar_val_nones g i'' p''
      have hne'' : i'' ≠ i := by
        rintro rfl
        rw [Fin.ext hval''] at hfree''
        exact hfreeC hfree''
      -- `g'` owns the same coordinate at the same block via `i''`.
      have hfree''' : (faceStar g' i'').val (StdCube.nones (faceStar g' i'') p'') = none :=
        faceStar_val_nones g' i'' p''
      have hidx''' : blockIdx g' i'' = blockIdx g' i :=
        (hblock i'').symm.trans (hidx''.trans (hblock i))
      have hval''' : (StdCube.nones (faceStar g' i'') p'' : ℕ) = (c' : ℕ) := by
        rw [← hnones i'' p'', hval'', hcc0]
      have hne_nat : (i'' : ℕ) ≠ (i : ℕ) := fun heq => hne'' (Fin.ext heq)
      rcases lt_or_gt_of_ne hne_nat with hlt | hgt
      · rw [faceStar_fixed_true g hlt hidx'' c (StdCube.nones (faceStar g i'') p'') hval'' hfree'',
          faceStar_fixed_true g' hlt hidx''' c'
            (StdCube.nones (faceStar g' i'') p'') hval''' hfree''']
      · rw [faceStar_fixed_false g hgt hidx'' c (StdCube.nones (faceStar g i'') p'') hval'' hfree'',
          faceStar_fixed_false g' hgt hidx''' c'
            (StdCube.nones (faceStar g' i'') p'') hval''' hfree''']
  -- Assemble: equal block index + equal faces ⟹ equal reconstructed cells.
  have hsig : (⟨blockIdx g i, faceStar g i⟩ :
        Σ r : Fin B.length, StdCube.cells (B.get r : ℕ) (A.get i : ℕ))
      = ⟨blockIdx g' i, faceStar g' i⟩ :=
    sigmaStar_ext (hblock i) (faceStar g i) (faceStar g' i) hval
  have hcanonG : StdCube.canonicalMap (faceStar g i) = blockFace g i := by
    change StdCube.canonicalMap (StdCube.ev (blockFace g i)) = blockFace g i
    exact (StdCube.cubeRepr (StdCube.stdPre (B.get (blockIdx g i) : ℕ)) (A.get i : ℕ)).left_inv
      (blockFace g i)
  have hcanonG' : StdCube.canonicalMap (faceStar g' i) = blockFace g' i := by
    change StdCube.canonicalMap (StdCube.ev (blockFace g' i)) = blockFace g' i
    exact (StdCube.cubeRepr (StdCube.stdPre (B.get (blockIdx g' i) : ℕ)) (A.get i : ℕ)).left_inv
      (blockFace g' i)
  have key := congrArg (fun s : Σ r : Fin B.length, StdCube.cells (B.get r : ℕ) (A.get i : ℕ) =>
      (BPSet.serialWedge.ι B s.1).app (op (Box.ob (A.get i : ℕ))) (StdCube.canonicalMap s.2)) hsig
  dsimp only at key
  rw [hcanonG, hcanonG', blockFace_spec g i, blockFace_spec g' i] at key
  exact key

/-- **Reconstruction** (README Step 3.4): `g` is determined by `ev g` — the analyzer
is faithful.  Assembled from `evCell_determined` (the block cells agree) via the serial
wedge's colimit uniqueness (`serialWedge_hom_ext`) and the bi-pointed extensionality. -/
theorem ev_reconstruct {g g' : serialWedge A ⟶ serialWedge B} (h : ev g = ev g') :
    g = g' := by
  apply BPSet.hom_ext
  refine serialWedge_hom_ext A g.hom g'.hom (fun i => ?_) ?_
  · exact yonedaEquiv.injective (evCell_determined h i)
  · rw [g.app_init, g'.app_init]

/-! ## Step 4. The reconstruction bijection: `evPerm` surjects onto valid permutations

For `MainFunctor`'s fullness we need not just injectivity of `evPerm` (`ev_reconstruct`)
but the characterisation of its image: a bijection `σ : Fin (dimSum A) ≃ Fin (dimSum B)`
arises as `evPerm g` iff it satisfies the PZ Def 6.11 validity conditions.  `ev_valid`
is the forward inclusion (assembled from Step 3); `evValid_exists` is the reverse
(construction) half. -/

/-- **Validity of an event permutation** (PZ Def 6.11), in the `blockIdx`/`globalEquiv`
API of this file.  `σ : Fin (dimSum A) ≃ Fin (dimSum B)` is *valid* — i.e. arises as
`evPerm g` for some wedge map `g` — when:

* **(i) block-monotonicity**: `σ` is strictly increasing on each source block (its star
  positions are read in serial order);
* **(ii) partition**: there is a block map `bm : Fin A.length → Fin B.length` under which
  every event of source block `i` lands in target block `bm i`, and the source blocks
  over each target block cover it (every target event's `σ`-preimage lies in a source
  block that `bm` sends to that event's target block). -/
def IsEvValid (σ : Fin (dimSum A) ≃ Fin (dimSum B)) : Prop :=
  (∀ i : Fin A.length, StrictMono fun p : Fin (A.get i : ℕ) => σ (globalEquiv A ⟨i, p⟩)) ∧
    ∃ bm : Fin A.length → Fin B.length,
      Monotone bm ∧
      (∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
          ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i) ∧
      (∀ t : Fin (dimSum B),
          bm (((globalEquiv A).symm (σ.symm t)).1) = ((globalEquiv B).symm t).1)

/-- **Forward inclusion**: the event permutation of any wedge map is valid.  Pure
assembly of Step 3: block-monotonicity is `ev_strictMonoOn`, the block map is `blockIdx`
(`ev_blockOf`), and the partition/covering is `ev_blocks`. -/
theorem ev_valid (g : serialWedge A ⟶ serialWedge B) : IsEvValid (evPerm g) :=
  ⟨fun i => by simpa only [evPerm_apply] using ev_strictMonoOn g i,
    blockIdx g, blockIdx_monotone g,
    fun i p => by simpa only [evPerm_apply] using ev_blockOf g i p,
    fun t => ev_blocks g t⟩

/-! ### Realization: the wedge map reconstructed from a valid event permutation

Given a valid `σ`, we build the block faces by the cumulative-OR *owner rule* (the
coordinate `c` of target block `bm i` is `∗` if block `i` owns it, `1` if an earlier
block owns it, `0` if a later one does), assemble them into a chain in `□^∨(B)`, and
descend.  All data below is parametrised by `σ`, `bm` and the validity clauses. -/

/-- The `p`-th star (free) coordinate of block `i`'s reconstructed face: the target
coordinate of `σ (event (i,p))`, cast into `Fin (B.get (bm i))` via `hplace`. -/
noncomputable def starCoord (σ : Fin (dimSum A) ≃ Fin (dimSum B)) (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) (p : Fin (A.get i : ℕ)) : Fin (B.get (bm i) : ℕ) :=
  Fin.cast (congrArg (fun r : Fin B.length => (B.get r : ℕ)) (hplace i p))
    ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).2

/-- The defining property: `⟨bm i, starCoord i p⟩` decodes to `σ (event (i,p))`. -/
theorem globalEquiv_starCoord (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) (p : Fin (A.get i : ℕ)) :
    globalEquiv B ⟨bm i, starCoord σ bm hplace i p⟩ = σ (globalEquiv A ⟨i, p⟩) := by
  have hsig : (⟨bm i, starCoord σ bm hplace i p⟩ : Σ r : Fin B.length, Fin (B.get r : ℕ))
      = (globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩)) := by
    refine sigmaFin_ext (f := fun r : Fin B.length => (B.get r : ℕ)) (hplace i p).symm ?_
    rfl
  rw [hsig, Equiv.apply_symm_apply]

/-- The owner (block of `σ`-preimage) of a target event `⟨bm i, c⟩`. -/
noncomputable def realOwner (σ : Fin (dimSum A) ≃ Fin (dimSum B)) (bm : Fin A.length → Fin B.length)
    (i : Fin A.length) (c : Fin (B.get (bm i) : ℕ)) : Fin A.length :=
  ((globalEquiv A).symm (σ.symm (globalEquiv B ⟨bm i, c⟩))).1

/-- The reconstructed sign-vector face of block `i`: coordinate `c` is `∗` if block `i`
owns it, `1` if an earlier block owns it, `0` if a later block does. -/
noncomputable def realFaceVal (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length) (i : Fin A.length) (c : Fin (B.get (bm i) : ℕ)) :
    Option Bool :=
  if realOwner σ bm i c = i then none
  else if realOwner σ bm i c < i then some true else some false

theorem realFaceVal_none_iff (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length) (i : Fin A.length) (c : Fin (B.get (bm i) : ℕ)) :
    realFaceVal σ bm i c = none ↔ realOwner σ bm i c = i := by
  unfold realFaceVal; split_ifs with h1 h2 <;> simp_all

/-- The owner of a star coordinate of block `i` is `i` itself. -/
theorem realOwner_starCoord (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) (p : Fin (A.get i : ℕ)) :
    realOwner σ bm i (starCoord σ bm hplace i p) = i := by
  rw [realOwner, globalEquiv_starCoord σ bm hplace i p, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- The star embedding is injective (from injectivity of `σ` and `globalEquiv`). -/
theorem starCoord_inj (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) : Function.Injective (starCoord σ bm hplace i) := by
  intro p p' hpp
  have hg : globalEquiv B ⟨bm i, starCoord σ bm hplace i p⟩
      = globalEquiv B ⟨bm i, starCoord σ bm hplace i p'⟩ := by rw [hpp]
  rw [globalEquiv_starCoord, globalEquiv_starCoord] at hg
  have := (globalEquiv A).injective (σ.injective hg)
  simpa using this

/-- **The reconstructed face has the right number of stars** (`A.get i`): its `∗`-set is
exactly the image of the star embedding, which is injective. -/
theorem realFace_card (σ : Fin (dimSum A) ≃ Fin (dimSum B)) (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) :
    (StdCube.noneSet (realFaceVal σ bm i)).card = (A.get i : ℕ) := by
  classical
  have hns : StdCube.noneSet (realFaceVal σ bm i)
      = Finset.image (starCoord σ bm hplace i) Finset.univ := by
    ext c
    simp only [StdCube.mem_noneSet, realFaceVal_none_iff, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · intro ho
      set p : Fin (A.get i : ℕ) :=
        Fin.cast (congrArg (fun j : Fin A.length => (A.get j : ℕ)) ho)
          ((globalEquiv A).symm (σ.symm (globalEquiv B ⟨bm i, c⟩))).2 with hpdef
      refine ⟨p, ?_⟩
      have hpre : globalEquiv A ⟨i, p⟩ = σ.symm (globalEquiv B ⟨bm i, c⟩) := by
        rw [show (⟨i, p⟩ : Σ j : Fin A.length, Fin (A.get j : ℕ))
            = (globalEquiv A).symm (σ.symm (globalEquiv B ⟨bm i, c⟩)) from
          sigmaFin_ext (f := fun j : Fin A.length => (A.get j : ℕ)) ho.symm rfl,
          Equiv.apply_symm_apply]
      have hc : globalEquiv B ⟨bm i, starCoord σ bm hplace i p⟩ = globalEquiv B ⟨bm i, c⟩ := by
        rw [globalEquiv_starCoord, hpre, Equiv.apply_symm_apply]
      simpa using (globalEquiv B).injective hc
    · rintro ⟨p, rfl⟩
      exact realOwner_starCoord σ bm hplace i p
  rw [hns, Finset.card_image_of_injective _ (starCoord_inj σ bm hplace i), Finset.card_univ,
    Fintype.card_fin]

/-- The reconstructed face of block `i` as a `StdCube` cell. -/
noncomputable def realFace (σ : Fin (dimSum A) ≃ Fin (dimSum B)) (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) : StdCube.cells (B.get (bm i) : ℕ) (A.get i : ℕ) :=
  ⟨realFaceVal σ bm i, realFace_card σ bm hplace i⟩

/-- The block face as a `□`-cell (box morphism). -/
noncomputable def blockCell (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) : (cube (B.get (bm i) : ℕ)).toPsh.cells (A.get i : ℕ) :=
  StdCube.canonicalMap (realFace σ bm hplace i)

theorem toStar_blockCell (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) : toStar (blockCell σ bm hplace i) = realFace σ bm hplace i := by
  rw [toStar_eq, blockCell]
  exact StdCube.ev_canonicalMap _

/-- The block face embedded as a cell of `□^∨(B)`. -/
noncomputable def cellFace (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) : (serialWedge B).toPsh.cells (A.get i : ℕ) :=
  (BPSet.serialWedge.ι B (bm i)).app (op (Box.ob (A.get i : ℕ))) (blockCell σ bm hplace i)

/-- `bm` is surjective (every target block is owned by some source block — covering). -/
theorem realBm_surj (σ : Fin (dimSum A) ≃ Fin (dimSum B)) (bm : Fin A.length → Fin B.length)
    (hcover : ∀ t : Fin (dimSum B),
      bm (((globalEquiv A).symm (σ.symm t)).1) = ((globalEquiv B).symm t).1) :
    Function.Surjective bm := by
  intro r
  refine ⟨((globalEquiv A).symm (σ.symm (globalEquiv B ⟨r, ⟨0, (B.get r).pos⟩⟩))).1, ?_⟩
  rw [hcover, Equiv.symm_apply_apply]


/-- The block owning any target coordinate of `bm i` maps back to `bm i` (covering). -/
theorem bm_realOwner (σ : Fin (dimSum A) ≃ Fin (dimSum B)) (bm : Fin A.length → Fin B.length)
    (hcover : ∀ t : Fin (dimSum B),
      bm (((globalEquiv A).symm (σ.symm t)).1) = ((globalEquiv B).symm t).1)
    (i : Fin A.length) (c : Fin (B.get (bm i) : ℕ)) :
    bm (realOwner σ bm i c) = bm i := by
  rw [realOwner, hcover, Equiv.symm_apply_apply]

/-- The `vertex₁` of the identity map's `r`-th event cell is `ι B r` applied to the cube's
final vertex — the wedge junction ingredient. -/
theorem vertex₁_evCell_id (B : List ℕ+) (r : Fin B.length) :
    (serialWedge B).toPsh.vertex₁ (evCell (𝟙 (BPSet.serialWedge B)) r)
      = (BPSet.serialWedge.ι B r).app (op (Box.ob 0)) (cube (B.get r : ℕ)).final := by
  simp only [evCell, BPSet.id_hom, Category.comp_id, vertex₁_yonedaEquiv]
  rfl

theorem vertex₀_evCell_id (B : List ℕ+) (r : Fin B.length) :
    (serialWedge B).toPsh.vertex₀ (evCell (𝟙 (BPSet.serialWedge B)) r)
      = (BPSet.serialWedge.ι B r).app (op (Box.ob 0)) (cube (B.get r : ℕ)).init := by
  simp only [evCell, BPSet.id_hom, Category.comp_id, vertex₀_yonedaEquiv]
  rfl

/-- A monotone surjection increases by at most `1` on consecutive inputs. -/
theorem monotone_surj_step {n m : ℕ} (f : Fin n → Fin m) (hf : Monotone f)
    (hs : Function.Surjective f) (i : Fin n) (hj : (i : ℕ) + 1 < n) :
    (f ⟨(i : ℕ) + 1, hj⟩ : ℕ) ≤ (f i : ℕ) + 1 := by
  by_contra h
  rw [not_le] at h
  have hlt : (f i : ℕ) + 1 < m := lt_of_lt_of_le h (Nat.le_of_lt_succ
    (Nat.lt_succ_of_lt (f ⟨(i : ℕ) + 1, hj⟩).2))
  obtain ⟨j, hj'⟩ := hs ⟨(f i : ℕ) + 1, hlt⟩
  rcases Nat.lt_or_ge (j : ℕ) ((i : ℕ) + 1) with hji | hji
  · have hle := hf (show j ≤ i from Fin.le_def.mpr (by omega))
    rw [hj'] at hle; simp only [Fin.le_def] at hle; omega
  · have hle := hf (show (⟨(i : ℕ) + 1, hj⟩ : Fin n) ≤ j from Fin.le_def.mpr (by omega))
    rw [hj'] at hle; simp only [Fin.le_def] at hle; omega

/-- Same-block junction: if the fill-`true` corner of `x` matches the fill-`false` corner
of `y` at every coordinate, their `ι B r`-embedded vertices coincide (target-block index
carried as a variable so the cube cast discharges by `subst`). -/
theorem blockCell_vertex_junction {r r' : Fin B.length} (hrr : r' = r) {k1 k2 : ℕ}
    (x : StdCube.cells (B.get r : ℕ) k1) (y : StdCube.cells (B.get r' : ℕ) k2)
    (hv : ∀ c : Fin (B.get r : ℕ),
        (if c ∈ StdCube.noneSet x.val then some true else x.val c)
          = (if Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) hrr.symm) c
                ∈ StdCube.noneSet y.val then some false
             else y.val (Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) hrr.symm) c))) :
    (BPSet.serialWedge.ι B r).app (op (Box.ob 0))
        ((cube (B.get r : ℕ)).toPsh.vertex₁ (StdCube.canonicalMap x))
      = (BPSet.serialWedge.ι B r').app (op (Box.ob 0))
        ((cube (B.get r' : ℕ)).toPsh.vertex₀ (StdCube.canonicalMap y)) := by
  subst hrr
  congr 1
  apply toStar_injective
  apply Subtype.ext
  funext c
  rw [toStar_vertex₁_val, toStar_vertex₀_val, toStar_canonicalMap, toStar_canonicalMap]
  simpa using hv c

/-- If every owner of block `i`'s target coordinates is `≤ i`, block `i`'s exit vertex is
the cube's final (all-`1`) vertex. -/
theorem vertex₁_blockCell_final (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) (hle : ∀ c : Fin (B.get (bm i) : ℕ), realOwner σ bm i c ≤ i) :
    (cube (B.get (bm i) : ℕ)).toPsh.vertex₁ (blockCell σ bm hplace i)
      = (cube (B.get (bm i) : ℕ)).final := by
  apply toStar_injective
  rw [show ((cube (B.get (bm i) : ℕ)).final : (cube (B.get (bm i) : ℕ)).toPsh.cells 0)
      = StdCube.canonicalMap (StdCube.constVertex (B.get (bm i) : ℕ) true) from rfl,
    toStar_canonicalMap]
  apply Subtype.ext
  funext c
  rw [toStar_vertex₁_val, toStar_blockCell]
  show (if _h : c ∈ StdCube.noneSet (realFace σ bm hplace i).val then some true
      else (realFace σ bm hplace i).val c) = some true
  by_cases hc : c ∈ StdCube.noneSet (realFace σ bm hplace i).val
  · rw [dif_pos hc]
  · rw [dif_neg hc]
    have hne : realOwner σ bm i c ≠ i := fun he =>
      hc (StdCube.mem_noneSet.mpr ((realFaceVal_none_iff σ bm i c).mpr he))
    show realFaceVal σ bm i c = some true
    rw [realFaceVal, if_neg hne, if_pos (lt_of_le_of_ne (hle c) hne)]

/-- If every owner of block `i+1`'s target coordinates is `> i`, block `i+1`'s entry vertex
is the cube's initial (all-`0`) vertex. -/
theorem vertex₀_blockCell_init (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (i : Fin A.length) (hge : ∀ c : Fin (B.get (bm i) : ℕ), i ≤ realOwner σ bm i c) :
    (cube (B.get (bm i) : ℕ)).toPsh.vertex₀ (blockCell σ bm hplace i)
      = (cube (B.get (bm i) : ℕ)).init := by
  apply toStar_injective
  rw [show ((cube (B.get (bm i) : ℕ)).init : (cube (B.get (bm i) : ℕ)).toPsh.cells 0)
      = StdCube.canonicalMap (StdCube.constVertex (B.get (bm i) : ℕ) false) from rfl,
    toStar_canonicalMap]
  apply Subtype.ext
  funext c
  rw [toStar_vertex₀_val, toStar_blockCell]
  show (if _h : c ∈ StdCube.noneSet (realFace σ bm hplace i).val then some false
      else (realFace σ bm hplace i).val c) = some false
  by_cases hc : c ∈ StdCube.noneSet (realFace σ bm hplace i).val
  · rw [dif_pos hc]
  · rw [dif_neg hc]
    have hne : realOwner σ bm i c ≠ i := fun he =>
      hc (StdCube.mem_noneSet.mpr ((realFaceVal_none_iff σ bm i c).mpr he))
    show realFaceVal σ bm i c = some false
    rw [realFaceVal, if_neg hne, if_neg (not_lt.mpr (hge c))]

/-- **The reconstructed block cells form a chain: junction step.**  `vertex₁ (cellFace i)
= vertex₀ (cellFace (i+1))`.  Same target block: the owner rule makes both corners agree
(`blockCell_vertex_junction`).  Different target block (`bm i < bm (i+1)`): block `i` exits
at `1̄` and block `i+1` enters at `0̄` (boundary lemmas), glued by the wedge junction
(`evCell_junction` of the identity). -/
theorem cellFace_junction (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length) (hbm_mono : Monotone bm)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (hcover : ∀ t : Fin (dimSum B),
      bm (((globalEquiv A).symm (σ.symm t)).1) = ((globalEquiv B).symm t).1)
    (i : Fin A.length) (hj : (i : ℕ) + 1 < A.length) :
    (serialWedge B).toPsh.vertex₁ (cellFace σ bm hplace i)
      = (serialWedge B).toPsh.vertex₀ (cellFace σ bm hplace ⟨(i : ℕ) + 1, hj⟩) := by
  have hbmle : bm i ≤ bm ⟨(i : ℕ) + 1, hj⟩ := hbm_mono (Fin.le_def.mpr (Nat.le_succ _))
  have hv1 : ((⟨(i : ℕ) + 1, hj⟩ : Fin A.length) : ℕ) = (i : ℕ) + 1 := rfl
  have hL : (serialWedge B).toPsh.vertex₁ (cellFace σ bm hplace i)
      = (BPSet.serialWedge.ι B (bm i)).app (op (Box.ob 0))
          ((cube (B.get (bm i) : ℕ)).toPsh.vertex₁ (blockCell σ bm hplace i)) := by
    rw [cellFace]; exact (map_vertex₁ (BPSet.serialWedge.ι B (bm i)) (blockCell σ bm hplace i)).symm
  have hR : (serialWedge B).toPsh.vertex₀ (cellFace σ bm hplace ⟨(i : ℕ) + 1, hj⟩)
      = (BPSet.serialWedge.ι B (bm ⟨(i : ℕ) + 1, hj⟩)).app (op (Box.ob 0))
          ((cube (B.get (bm ⟨(i : ℕ) + 1, hj⟩) : ℕ)).toPsh.vertex₀
            (blockCell σ bm hplace ⟨(i : ℕ) + 1, hj⟩)) := by
    rw [cellFace]
    exact (map_vertex₀ (BPSet.serialWedge.ι B (bm ⟨(i : ℕ) + 1, hj⟩))
      (blockCell σ bm hplace ⟨(i : ℕ) + 1, hj⟩)).symm
  rw [hL, hR]
  rcases lt_or_eq_of_le hbmle with hlt | heq
  · -- cross-block
    have hle_i : ∀ c, realOwner σ bm i c ≤ i := fun c => by
      by_contra h; rw [not_le] at h
      have h2 := hbm_mono (show (⟨(i : ℕ) + 1, hj⟩ : Fin A.length) ≤ realOwner σ bm i c from
        Fin.le_def.mpr (by rw [Fin.lt_def] at h; omega))
      rw [bm_realOwner σ bm hcover i c] at h2
      exact absurd h2 (not_le.mpr hlt)
    have hge_i1 : ∀ c, (⟨(i : ℕ) + 1, hj⟩ : Fin A.length) ≤ realOwner σ bm ⟨(i : ℕ) + 1, hj⟩ c :=
      fun c => by
        by_contra h; rw [not_le] at h
        have h2 := hbm_mono (show realOwner σ bm ⟨(i : ℕ) + 1, hj⟩ c ≤ i from
          Fin.le_def.mpr (by rw [Fin.lt_def] at h; omega))
        rw [bm_realOwner σ bm hcover ⟨(i : ℕ) + 1, hj⟩ c] at h2
        exact absurd h2 (not_le.mpr hlt)
    rw [vertex₁_blockCell_final σ bm hplace i hle_i,
      vertex₀_blockCell_init σ bm hplace ⟨(i : ℕ) + 1, hj⟩ hge_i1]
    have hbm1 : (bm ⟨(i : ℕ) + 1, hj⟩ : ℕ) = (bm i : ℕ) + 1 :=
      le_antisymm (monotone_surj_step bm hbm_mono (realBm_surj σ bm hcover) i hj)
        (by rw [Fin.lt_def] at hlt; omega)
    have hbmlt : (bm i : ℕ) + 1 < B.length := by rw [← hbm1]; exact (bm ⟨(i : ℕ) + 1, hj⟩).2
    have hjunc := evCell_junction (𝟙 (BPSet.serialWedge B)) (bm i) hbmlt
    rw [← vertex₁_evCell_id B (bm i), hjunc, vertex₀_evCell_id B ⟨(bm i : ℕ) + 1, hbmlt⟩,
      show (⟨(bm i : ℕ) + 1, hbmlt⟩ : Fin B.length) = bm ⟨(i : ℕ) + 1, hj⟩ from Fin.ext hbm1.symm]
  · -- same target block
    refine blockCell_vertex_junction heq.symm (realFace σ bm hplace i)
      (realFace σ bm hplace ⟨(i : ℕ) + 1, hj⟩) (fun c => ?_)
    set cc := Fin.cast (congrArg (fun s : Fin B.length => (B.get s : ℕ)) heq) c with hcc
    have ho_eq : realOwner σ bm ⟨(i : ℕ) + 1, hj⟩ cc = realOwner σ bm i c := by
      unfold realOwner
      congr 4
      exact (sigmaFin_ext (f := fun s : Fin B.length => (B.get s : ℕ)) heq rfl).symm
    have hoi : (realOwner σ bm ⟨(i : ℕ) + 1, hj⟩ cc : ℕ) = (realOwner σ bm i c : ℕ) := by rw [ho_eq]
    have hmemL : c ∈ StdCube.noneSet (realFace σ bm hplace i).val ↔ realOwner σ bm i c = i := by
      rw [StdCube.mem_noneSet]; exact realFaceVal_none_iff σ bm i c
    have hmemR : cc ∈ StdCube.noneSet (realFace σ bm hplace ⟨(i : ℕ) + 1, hj⟩).val
        ↔ realOwner σ bm ⟨(i : ℕ) + 1, hj⟩ cc = ⟨(i : ℕ) + 1, hj⟩ := by
      rw [StdCube.mem_noneSet]; exact realFaceVal_none_iff σ bm ⟨(i : ℕ) + 1, hj⟩ cc
    show (if _h : c ∈ StdCube.noneSet (realFace σ bm hplace i).val then some true
        else realFaceVal σ bm i c)
      = (if _h : cc ∈ StdCube.noneSet (realFace σ bm hplace ⟨(i : ℕ) + 1, hj⟩).val
          then some false else realFaceVal σ bm ⟨(i : ℕ) + 1, hj⟩ cc)
    rcases lt_trichotomy (realOwner σ bm i c : ℕ) (i : ℕ) with h | h | h
    · -- owner < i : both `some true`
      rw [dif_neg (by rw [hmemL, Fin.ext_iff]; omega),
        dif_neg (by rw [hmemR, Fin.ext_iff, hoi, hv1]; omega),
        show realFaceVal σ bm i c = some true from by
          rw [realFaceVal, if_neg (by rw [Fin.ext_iff]; omega), if_pos (by rw [Fin.lt_def]; omega)],
        show realFaceVal σ bm ⟨(i : ℕ) + 1, hj⟩ cc = some true from by
          rw [realFaceVal, if_neg (by rw [Fin.ext_iff, hoi, hv1]; omega),
            if_pos (by rw [Fin.lt_def, hoi, hv1]; omega)]]
    · -- owner = i : LHS free (`some true`); RHS fixed `< i+1` (`some true`)
      rw [dif_pos (by rw [hmemL, Fin.ext_iff]; omega),
        dif_neg (by rw [hmemR, Fin.ext_iff, hoi, hv1]; omega),
        show realFaceVal σ bm ⟨(i : ℕ) + 1, hj⟩ cc = some true from by
          rw [realFaceVal, if_neg (by rw [Fin.ext_iff, hoi, hv1]; omega),
            if_pos (by rw [Fin.lt_def, hoi, hv1]; omega)]]
    · -- owner > i : both `some false`
      rw [dif_neg (by rw [hmemL, Fin.ext_iff]; omega),
        show realFaceVal σ bm i c = some false from by
          rw [realFaceVal, if_neg (by rw [Fin.ext_iff]; omega), if_neg (by rw [Fin.lt_def]; omega)]]
      by_cases hR1 : cc ∈ StdCube.noneSet (realFace σ bm hplace ⟨(i : ℕ) + 1, hj⟩).val
      · rw [dif_pos hR1]
      · rw [dif_neg hR1, show realFaceVal σ bm ⟨(i : ℕ) + 1, hj⟩ cc = some false from by
          rw [realFaceVal, if_neg (fun he => hR1 (hmemR.mpr he)),
            if_neg (by rw [Fin.lt_def, hoi, hv1]; omega)]]

/-- The star embedding is strictly monotone (from within-block strict monotonicity of `σ`). -/
theorem starCoord_strictMono (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (hmono : ∀ i : Fin A.length,
      StrictMono fun p : Fin (A.get i : ℕ) => σ (globalEquiv A ⟨i, p⟩))
    (i : Fin A.length) : StrictMono (starCoord σ bm hplace i) := by
  intro p p' hpp
  have hsm : StrictMono (fun q : Fin (B.get (bm i) : ℕ) => globalEquiv B ⟨bm i, q⟩) :=
    fun q q' hq => globalEquiv_block_lt (bm i) hq
  have hg : globalEquiv B ⟨bm i, starCoord σ bm hplace i p⟩
      < globalEquiv B ⟨bm i, starCoord σ bm hplace i p'⟩ := by
    rw [globalEquiv_starCoord, globalEquiv_starCoord]; exact hmono i hpp
  exact hsm.lt_iff_lt.mp hg

/-- The `nones` (star-position enumeration) of the reconstructed face is exactly the star
embedding (both are the ordered enumeration of the same `∗`-set). -/
theorem nones_realFace (σ : Fin (dimSum A) ≃ Fin (dimSum B))
    (bm : Fin A.length → Fin B.length)
    (hplace : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
      ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i)
    (hmono : ∀ i : Fin A.length,
      StrictMono fun p : Fin (A.get i : ℕ) => σ (globalEquiv A ⟨i, p⟩))
    (i : Fin A.length) (p : Fin (A.get i : ℕ)) :
    StdCube.nones (realFace σ bm hplace i) p = starCoord σ bm hplace i p := by
  classical
  have hns : StdCube.noneSet (realFaceVal σ bm i)
      = Finset.image (starCoord σ bm hplace i) Finset.univ := by
    ext c
    simp only [StdCube.mem_noneSet, realFaceVal_none_iff, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · intro ho
      set q : Fin (A.get i : ℕ) :=
        Fin.cast (congrArg (fun j : Fin A.length => (A.get j : ℕ)) ho)
          ((globalEquiv A).symm (σ.symm (globalEquiv B ⟨bm i, c⟩))).2 with hqdef
      refine ⟨q, ?_⟩
      have hpre : globalEquiv A ⟨i, q⟩ = σ.symm (globalEquiv B ⟨bm i, c⟩) := by
        rw [show (⟨i, q⟩ : Σ j : Fin A.length, Fin (A.get j : ℕ))
            = (globalEquiv A).symm (σ.symm (globalEquiv B ⟨bm i, c⟩)) from
          sigmaFin_ext (f := fun j : Fin A.length => (A.get j : ℕ)) ho.symm rfl,
          Equiv.apply_symm_apply]
      have hc : globalEquiv B ⟨bm i, starCoord σ bm hplace i q⟩ = globalEquiv B ⟨bm i, c⟩ := by
        rw [globalEquiv_starCoord, hpre, Equiv.apply_symm_apply]
      simpa using (globalEquiv B).injective hc
    · rintro ⟨p', rfl⟩
      exact realOwner_starCoord σ bm hplace i p'
  have hmem : ∀ q, starCoord σ bm hplace i q ∈ StdCube.noneSet (realFaceVal σ bm i) :=
    fun q => by rw [hns]; exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
  have huniq := Finset.orderEmbOfFin_unique' (s := StdCube.noneSet (realFaceVal σ bm i))
    (k := (A.get i : ℕ)) (realFace σ bm hplace i).prop
    (f := OrderEmbedding.ofStrictMono (starCoord σ bm hplace i)
      (starCoord_strictMono σ bm hplace hmono i)) hmem
  exact congrFun (congrArg (fun e : Fin (A.get i : ℕ) ↪o Fin (B.get (bm i) : ℕ) => (e : _ → _))
    huniq.symm) p

/-- The initial vertex of a serial wedge is `ι`-block-`0` applied to the head cube's
initial vertex. -/
theorem serialWedge_init_ι : ∀ (B : List ℕ+) (hB : 0 < B.length),
    (BPSet.serialWedge B).init
      = (BPSet.serialWedge.ι B ⟨0, hB⟩).app (op (Box.ob 0)) (BPSet.cube (B.get ⟨0, hB⟩ : ℕ)).init
  | [], hB => absurd hB (by simp)
  | _ :: _, _ => rfl

/-- The final vertex of a serial wedge is `ι`-last-block applied to the last cube's final
vertex. -/
theorem serialWedge_final_ι : ∀ (B : List ℕ+) (hB : 0 < B.length),
    (BPSet.serialWedge B).final
      = (BPSet.serialWedge.ι B ⟨B.length - 1, by omega⟩).app (op (Box.ob 0))
        (BPSet.cube (B.get ⟨B.length - 1, by omega⟩ : ℕ)).final
  | [], hB => absurd hB (by simp)
  | [n], _ => by
      have hif : (BPSet.serialWedge []).final = (BPSet.serialWedge []).init :=
        Subsingleton.elim (α := (BPSet.cube 0).toPsh.cells 0) _ _
      show _ = (pushout.inl (BPSet.cube (n : ℕ)).finalVertex (BPSet.serialWedge []).initVertex).app
        (op (Box.ob 0)) (BPSet.cube (n : ℕ)).final
      rw [wedge2_glue (BPSet.cube (n : ℕ)) (BPSet.serialWedge []), ← hif]
      rfl
  | n :: m :: rest, _ => by
      have hlen : (m :: rest).length - 1 + 1 = (m :: rest).length := by simp
      have hlast : (⟨(n :: m :: rest).length - 1, by omega⟩ : Fin (n :: m :: rest).length)
          = (⟨(m :: rest).length - 1, by omega⟩ : Fin (m :: rest).length).succ := by
        apply Fin.ext; simp
      rw [hlast, serialWedge_ι_succ_app]
      show (pushout.inr (BPSet.cube (n : ℕ)).finalVertex
          (BPSet.serialWedge (m :: rest)).initVertex).app (op (Box.ob 0))
          (BPSet.serialWedge (m :: rest)).final = _
      rw [serialWedge_final_ι (m :: rest) (by simp)]
      rfl

/-- **DEFERRED — the reverse (reconstruction) half of the event bijection (PZ Def
6.11).**  Every valid event permutation `σ` is realised by a wedge map — the mirror of
the forward `ev`/`evCell` construction, and the reverse geometric input alongside
`faceStar_val_mono`.

Construction sketch.  From `σ`'s validity data read off, for each source block `i`:
* the target block `r i := bm i` (condition (ii));
* the strictly-monotone star embedding `p ↦ decode (σ (globalEquiv A ⟨i, p⟩))` into
  `Fin (B.get (r i))` (condition (i)), whose image is the star (free) set of the block
  face `f i`;
* the fixed `0/1` value of every remaining coordinate `c` of `□^{B.get (r i)}` by the
  earlier/later *owner* rule: `c` is the star of a unique source block `i''` mapping to
  `r i` (disjointness + covering from `σ` bijective), and `f i . val c = some true` iff
  `i'' < i`, `= some false` iff `i'' > i` — exactly the `faceStar_val_mono` monotonicity.

Assemble the faces `f i` into block cells `c i := ιᵣ ≫ canonicalMap (f i)` of
`serialWedge B`; the junction gluing `vertex₁ (c i) = vertex₀ (c (i+1))` holds because
the owner partition tiles each target block and the target wedge junctions
(`ιᵣ (all-true) = ιᵣ₊₁ (all-false)`) identify the block boundaries; descend to a
bi-pointed map `g` via `wedgeDesc`/`serialWedge_hom_ext` (+ `BPSet.hom_ext` for
bipointedness).  Finally `evPerm g = σ`: the block restriction `ιᵢ ≫ g.hom` classifies
`c i`, so `blockIdx g i = r i` and `faceStar g i = f i` (`blockIdx_eq_of`,
`faceStar_nones_val`), giving `evBlk g ⟨i,p⟩ = decode (σ (globalEquiv A ⟨i,p⟩))`. -/
theorem evValid_exists (σ : Fin (dimSum A) ≃ Fin (dimSum B)) (h : IsEvValid σ) :
    ∃ g : serialWedge A ⟶ serialWedge B, evPerm g = σ := by
  obtain ⟨hmono, bm, hbm_mono, hplace, hcover⟩ := h
  have hcard := Fintype.card_congr σ
  simp only [Fintype.card_fin] at hcard
  rcases Nat.eq_zero_or_pos A.length with hA0 | hA
  · -- edge case `A = []` (forces `B = []`), the permutation is trivial
    obtain rfl : A = [] := List.length_eq_zero_iff.mp hA0
    simp only [dimSum_nil] at hcard
    obtain rfl : B = [] := by
      rcases B with _ | ⟨n, rest⟩; · rfl
      rw [dimSum_cons] at hcard; have := n.pos; omega
    refine ⟨𝟙 (BPSet.serialWedge []), ?_⟩
    apply Equiv.ext; intro x; exact x.elim0
  · -- `A.length > 0`
    have hB : 0 < B.length := by
      rcases Nat.eq_zero_or_pos B.length with hB0 | hB; swap; · exact hB
      obtain rfl : B = [] := List.length_eq_zero_iff.mp hB0
      rcases A with _ | ⟨n, rest⟩; · simp at hA
      rw [dimSum_cons] at hcard; have := n.pos; simp only [dimSum_nil] at hcard; omega
    have hAL : A.length - 1 < A.length := by omega
    have hBL : B.length - 1 < B.length := by omega
    have hbm0 : bm ⟨0, hA⟩ = ⟨0, hB⟩ := by
      obtain ⟨j, hj⟩ := realBm_surj σ bm hcover ⟨0, hB⟩
      exact le_antisymm (hj ▸ hbm_mono (Fin.le_def.mpr (Nat.zero_le _)))
        (Fin.le_def.mpr (Nat.zero_le _))
    have hbmL : bm ⟨A.length - 1, hAL⟩ = ⟨B.length - 1, hBL⟩ := by
      obtain ⟨j, hj⟩ := realBm_surj σ bm hcover ⟨B.length - 1, hBL⟩
      apply Fin.ext
      apply Nat.le_antisymm
      · exact Nat.le_sub_one_of_lt (bm ⟨A.length - 1, hAL⟩).2
      · have hjle : j ≤ (⟨A.length - 1, hAL⟩ : Fin A.length) :=
          Fin.le_def.mpr (show (j : ℕ) ≤ A.length - 1 by have := j.2; omega)
        have := hbm_mono hjle
        rw [hj] at this; exact Fin.le_def.mp this
    set cubes : List (Σ n : ℕ+, (BPSet.serialWedge B).toPsh.cells (n : ℕ)) :=
      List.ofFn (fun i : Fin A.length => ⟨A.get i, cellFace σ bm hplace i⟩) with hcubes
    have hdims : cubes.map (·.1) = A := by rw [hcubes, List.map_ofFn]; exact List.ofFn_get A
    have hinit : (BPSet.serialWedge B).toPsh.vertex₀ (cellFace σ bm hplace ⟨0, hA⟩)
        = (BPSet.serialWedge B).init := by
      rw [cellFace, ← map_vertex₀,
        vertex₀_blockCell_init σ bm hplace ⟨0, hA⟩ (fun c => Fin.le_def.mpr (Nat.zero_le _)),
        serialWedge_init_ι B hB, hbm0]
    have hfinal : (BPSet.serialWedge B).toPsh.vertex₁
        (cellFace σ bm hplace ⟨A.length - 1, hAL⟩) = (BPSet.serialWedge B).final := by
      rw [cellFace, ← map_vertex₁,
        vertex₁_blockCell_final σ bm hplace ⟨A.length - 1, hAL⟩
          (fun c => Fin.le_def.mpr (show (realOwner σ bm ⟨A.length - 1, hAL⟩ c : ℕ) ≤ A.length - 1
            by have := (realOwner σ bm ⟨A.length - 1, hAL⟩ c).2; omega)),
        serialWedge_final_ι B hB, hbmL]
    have hchain : IsCubeChain (BPSet.serialWedge B).init cubes (BPSet.serialWedge B).final := by
      rw [hcubes]
      refine isCubeChain_ofFn _ _ _
        (fun k : Fin (A.length + 1) => if hk : (k : ℕ) < A.length
          then (BPSet.serialWedge B).toPsh.vertex₀ (cellFace σ bm hplace ⟨k, hk⟩)
          else (BPSet.serialWedge B).final) ?_ ?_ (fun i => ?_) (fun i => ?_)
      · simp only [Fin.val_zero]; rw [dif_pos hA]; exact hinit
      · simp only [Fin.val_last]; rw [dif_neg (lt_irrefl A.length)]
      · simp only [Fin.val_castSucc]; rw [dif_pos i.2]
      · simp only [Fin.val_succ]
        by_cases hlast : (i : ℕ) + 1 < A.length
        · rw [dif_pos hlast]
          exact cellFace_junction σ bm hbm_mono hplace hcover i hlast
        · rw [dif_neg hlast]
          rw [show i = (⟨A.length - 1, hAL⟩ : Fin A.length) from
            Fin.ext (show (i : ℕ) = A.length - 1 by have := i.2; omega)]
          exact hfinal
    let gmap := wedgeDescHom cubes
      (wedgeDesc (BPSet.serialWedge B).init (BPSet.serialWedge B).final cubes hchain)
    let g : BPSet.serialWedge A ⟶ BPSet.serialWedge B :=
      eqToHom (congrArg BPSet.serialWedge hdims.symm) ≫ gmap
    refine ⟨g, ?_⟩
    have hwtc : wedgeToCubes ⟨A, g.hom⟩ = cubes := by
      show wedgeToCubes ⟨A, (eqToHom (congrArg BPSet.serialWedge hdims.symm) ≫ gmap).hom⟩ = cubes
      rw [BPSet.comp_hom, bpset_eqToHom_hom, wedgeToCubes_eqToHom hdims.symm gmap.hom]
      exact wedgeToCubes_wedgeDesc _ _ cubes hchain
    have hevCell : ∀ i : Fin A.length, evCell g i = cellFace σ bm hplace i := by
      intro i
      have hlen : (wedgeToCubes ⟨A, g.hom⟩).length = A.length := wedgeToCubes_length A g.hom
      have hi : (i : ℕ) < (wedgeToCubes ⟨A, g.hom⟩).length := by rw [hlen]; exact i.2
      have hicu : (i : ℕ) < cubes.length := by rw [hcubes, List.length_ofFn]; exact i.2
      have hget := wedgeToCubes_get A g.hom ⟨(i : ℕ), hi⟩
      have hcast : (⟨(i : ℕ), hi⟩ : Fin (wedgeToCubes ⟨A, g.hom⟩).length).cast hlen = i :=
        Fin.ext rfl
      rw [hcast] at hget
      have hgc : cubes.get ⟨(i : ℕ), hicu⟩ = ⟨A.get i, cellFace σ bm hplace i⟩ := by
        have hbridge : cubes.get ⟨(i : ℕ), hicu⟩
            = (List.ofFn (fun j : Fin A.length =>
                (⟨A.get j, cellFace σ bm hplace j⟩ :
                  Σ n : ℕ+, (BPSet.serialWedge B).toPsh.cells (n : ℕ)))).get ⟨(i : ℕ), hicu⟩ := rfl
        rw [hbridge, List.get_ofFn]
        rfl
      have hlisteq : (wedgeToCubes ⟨A, g.hom⟩).get ⟨(i : ℕ), hi⟩ = cubes.get ⟨(i : ℕ), hicu⟩ :=
        (List.get_of_eq hwtc _).trans (congrArg cubes.get (Fin.ext rfl))
      rw [hget, hgc] at hlisteq
      simpa using hlisteq
    have hblk : ∀ i : Fin A.length, blockIdx g i = bm i := fun i =>
      blockIdx_eq_of g i (bm i) (blockCell σ bm hplace i) (by rw [hevCell i]; rfl)
    have hfsN : ∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
        (StdCube.nones (faceStar g i) p : ℕ) = (starCoord σ bm hplace i p : ℕ) := by
      intro i p
      rw [faceStar_nones_val g i (bm i) (blockCell σ bm hplace i) (by rw [hevCell i]; rfl) p,
        toStar_blockCell, nones_realFace σ bm hplace hmono i]
    apply Equiv.ext
    intro U
    apply Fin.ext
    set s := (globalEquiv A).symm U with hs
    have hUeq : globalEquiv A ⟨s.1, s.2⟩ = U := by rw [hs, Equiv.apply_symm_apply]
    rw [show U = globalEquiv A ⟨s.1, s.2⟩ from hUeq.symm, evPerm_apply, ev_apply,
      ← globalEquiv_starCoord σ bm hplace s.1 s.2]
    congr 1
    refine congrArg _ (sigmaFin_ext (f := fun r : Fin B.length => (B.get r : ℕ)) (hblk s.1) ?_)
    exact hfsN s.1 s.2

end FinalPrecubical
