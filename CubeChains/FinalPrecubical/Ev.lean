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

Via the altitude machinery: the altitude of a serial wedge's final vertex, relative
to its initial vertex, equals `dimSum`.  Since a bi-pointed map preserves both
vertices and (by pullback) the altitude, `dimSum` is an isomorphism invariant. -/

/-- Pulling an altitude back along a presheaf map is again an altitude (the map
commutes with all faces, by naturality). -/
theorem isAltitude_comp {X Y : PrecubicalSet} (φ : X ⟶ Y)
    (alt : ∀ n, Y.cells n → ℤ) (hax : Y.IsAltitude alt) :
    X.IsAltitude (fun m c => alt m (φ.app (op (Box.ob m)) c)) := by
  intro n ε i c
  have hnat : φ.app (op (Box.ob n)) (X.faceMap ε i c)
      = Y.faceMap ε i (φ.app (op (Box.ob (n + 1))) c) := by
    simp only [PrecubicalSet.faceMap]
    exact NatTrans.naturality_apply φ (PrecubicalSet.coface ε i).op c
  change alt n (φ.app _ (X.faceMap ε i c)) = alt (n + 1) (φ.app _ c) + (if ε then 1 else 0)
  rw [hnat]
  exact hax ε i (φ.app _ c)

/-- **Cube case of the altitude computation.**  For any altitude on `□ᴺ`, the final
vertex sits `N` above the initial vertex (`alt_vertex₁ - alt_vertex₀` on the top
cell, the identity `□ᴺ ⟶ □ᴺ`). -/
theorem cube_alt_final (N : ℕ) (alt : ∀ n, (cube N).toPsh.cells n → ℤ)
    (hax : (cube N).toPsh.IsAltitude alt) :
    alt 0 (cube N).final = alt 0 (cube N).init + (N : ℤ) := by
  set t : (cube N).toPsh.cells N := yonedaEquiv (𝟙 (yoneda.obj (Box.ob N))) with ht
  have h0 : (cube N).toPsh.vertex₀ t = (cube N).init := by
    rw [ht, PrecubicalSet.vertex₀_yonedaEquiv]; rfl
  have h1 : (cube N).toPsh.vertex₁ t = (cube N).final := by
    rw [ht, PrecubicalSet.vertex₁_yonedaEquiv]; rfl
  have e0 := PrecubicalSet.alt_vertex₀ alt hax t
  have e1 := PrecubicalSet.alt_vertex₁ alt hax t
  rw [h0] at e0
  rw [h1] at e1
  rw [e1, e0]

/-- **The altitude of a serial wedge's final vertex is `dimSum` above its initial
vertex**, for *any* altitude.  By recursion on the dimension sequence, restricting
the altitude to the head cube (`inl`) and the tail (`inr`). -/
theorem serialWedge_alt_final :
    ∀ (A : List ℕ+) (alt : ∀ n, (serialWedge A).toPsh.cells n → ℤ)
      (_ : (serialWedge A).toPsh.IsAltitude alt),
    alt 0 (serialWedge A).final = alt 0 (serialWedge A).init + (dimSum A : ℤ)
  | [], alt, _ => by
      rw [show (serialWedge ([] : List ℕ+)).final = (serialWedge ([] : List ℕ+)).init from
        Subsingleton.elim (α := (BPSet.cube 0).toPsh.cells 0) _ _]
      simp
  | n :: rest, alt, hax => by
      -- restrict `alt` to the two blocks (inlined via the wedge `faceMap` lemmas,
      -- avoiding a `serialWedge`/`pushout` defeq boundary that trips unification)
      have haxHead : (cube (n : ℕ)).toPsh.IsAltitude
          (fun m x => alt m ((pushout.inl (cube (n : ℕ)).finalVertex
            (serialWedge rest).initVertex).app (op (Box.ob m)) x)) := by
        intro k ε i x
        dsimp only
        rw [← BPSet.wedge2_inl_faceMap]
        exact hax ε i _
      have haxTail : (serialWedge rest).toPsh.IsAltitude
          (fun m y => alt m ((pushout.inr (cube (n : ℕ)).finalVertex
            (serialWedge rest).initVertex).app (op (Box.ob m)) y)) := by
        intro k ε i y
        dsimp only
        rw [← BPSet.wedge2_inr_faceMap]
        exact hax ε i _
      have hC := cube_alt_final (n : ℕ)
        (fun m x => alt m ((pushout.inl (cube (n : ℕ)).finalVertex
          (serialWedge rest).initVertex).app (op (Box.ob m)) x)) haxHead
      have hR := serialWedge_alt_final rest
        (fun m y => alt m ((pushout.inr (cube (n : ℕ)).finalVertex
          (serialWedge rest).initVertex).app (op (Box.ob m)) y)) haxTail
      dsimp only at hC hR
      have hglue := congrArg (alt 0) (CubeChain.wedge2_glue (cube (n : ℕ)) (serialWedge rest)).symm
      -- `(serialWedge (n::rest)).final`/`.init` are defeq to the `inr`/`inl` block vertices
      change alt 0 ((pushout.inr (cube (n : ℕ)).finalVertex
            (serialWedge rest).initVertex).app (op (Box.ob 0)) (serialWedge rest).final)
          = alt 0 ((pushout.inl (cube (n : ℕ)).finalVertex
            (serialWedge rest).initVertex).app (op (Box.ob 0)) (cube (n : ℕ)).init)
            + (dimSum (n :: rest) : ℤ)
      rw [dimSum_cons]; push_cast
      linarith [hC, hR, hglue]

/-- **`dimSum` is a wedge-map invariant.**  Pull the target altitude back along `g`
to get an altitude on the source with the same final/initial values; both sides then
equal the common altitude gap. -/
theorem dimSum_eq {A B : List ℕ+} (g : serialWedge A ⟶ serialWedge B) :
    dimSum A = dimSum B := by
  obtain ⟨altB, haxB, _⟩ := serialWedge_admitsAltitude B
  have haxA' : (serialWedge A).toPsh.IsAltitude
      (fun m c => altB m (g.hom.app (op (Box.ob m)) c)) :=
    isAltitude_comp g.hom altB haxB
  have hLA := serialWedge_alt_final A
    (fun m c => altB m (g.hom.app (op (Box.ob m)) c)) haxA'
  have hLB := serialWedge_alt_final B altB haxB
  have hinit : altB 0 (g.hom.app (op (Box.ob 0)) (serialWedge A).init)
      = altB 0 (serialWedge B).init := by rw [g.app_init]
  have hfinal : altB 0 (g.hom.app (op (Box.ob 0)) (serialWedge A).final)
      = altB 0 (serialWedge B).final := by rw [g.app_final]
  dsimp only at hLA
  rw [hinit, hfinal] at hLA
  have key : (altB 0 (serialWedge B).init + (dimSum A : ℤ))
      = altB 0 (serialWedge B).init + (dimSum B : ℤ) := hLA.symm.trans hLB
  have : (dimSum A : ℤ) = (dimSum B : ℤ) := by linarith
  exact_mod_cast this

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
    serialWedge_ι_app_injective B hk r (hx.trans hx'.symm)
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
  have hyy : y = y' := serialWedge_ι_app_injective B hk r (hy.trans hy'.symm)
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

/-! ## Block monotonicity (via the altitude counting of `Chains/Correspondence`)

`blockIdx g` is *monotone* (README Step 3; the well-definedness crux of `MainFunctor`):
the source spine's junction altitudes strictly increase, so the target blocks are
visited in weakly increasing order (no junction re-crossing).  This is exactly the
computation that powers `Correspondence.wedgeToRefineMap`'s `refinementMono`, here
specialised to a map of serial wedges and read off directly on `blockIdx`/`blockFace`.
It reuses the chain-altitude arithmetic (`isCubeChain_alt_get`, `dimPrefixSum_*`) — an
altitude-only argument, needing no reachability geometry. -/

/-- **Block monotonicity of a wedge map.**  `blockIdx g` is monotone.

Both the source cube list `wedgeToCubes ⟨A, g.hom⟩` and the target's own cube list
`wedgeToCubes ⟨B, 𝟙⟩` are chains from `init` to `final` in `□^∨(B)`; the `i`-th source
cube is a face of target block `blockIdx g i` (`blockFace_spec`).  Comparing altitudes
(`alt_cubeMap`) pins the source prefix-sum into the `blockIdx g i`-th target block:
`psum_B (blockIdx g i) ≤ psum_A i < psum_B (blockIdx g i + 1)`.  Since `psum_A` is
monotone in `i`, the block index is monotone. -/
theorem blockIdx_monotone (g : serialWedge A ⟶ serialWedge B) :
    Monotone (blockIdx g) := by
  obtain ⟨alt, hax, halt0⟩ := serialWedge_admitsAltitude B
  -- The two chains in `□^∨(B)`: the source cube list `L` (read off `g`) and the
  -- target's own cube list `M` (read off `𝟙`).
  have hLlen : (wedgeToCubes ⟨A, g.hom⟩).length = A.length := wedgeToCubes_length A g.hom
  have hMlen : (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩).length = B.length :=
    wedgeToCubes_length B (𝟙 (serialWedge B).toPsh)
  have hLchain : IsCubeChain (serialWedge B).init (wedgeToCubes ⟨A, g.hom⟩)
      (serialWedge B).final := by
    have h := wedgeToCubes_isCubeChain A g.hom
    rwa [g.app_init, g.app_final] at h
  have hMchain : IsCubeChain (serialWedge B).init (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩)
      (serialWedge B).final := by
    have h := wedgeToCubes_isCubeChain B (𝟙 (serialWedge B).toPsh)
    simpa only [BPSet.id_hom, NatTrans.id_app, types_id_apply] using h
  -- Source altitude: `alt (evCell g i) = psum_A i` (chain-altitude arithmetic).
  have hsrc : ∀ i : Fin A.length,
      alt (A.get i : ℕ) (evCell g i) = dimPrefixSum (wedgeToCubes ⟨A, g.hom⟩) (i : ℕ) := by
    intro i
    have hi : (i : ℕ) < (wedgeToCubes ⟨A, g.hom⟩).length := by rw [hLlen]; exact i.2
    have halt := isCubeChain_alt_get alt hax (wedgeToCubes ⟨A, g.hom⟩) (serialWedge B).init
      (serialWedge B).final hLchain (i : ℕ) hi
    rw [halt0, zero_add] at halt
    have hcast : (⟨(i : ℕ), hi⟩ : Fin (wedgeToCubes ⟨A, g.hom⟩).length).cast hLlen = i :=
      Fin.ext rfl
    have hget := wedgeToCubes_get A g.hom ⟨(i : ℕ), hi⟩
    rw [hcast] at hget
    exact (congrArg (fun s : Σ n : ℕ+, (serialWedge B).toPsh.cells (n : ℕ) =>
      alt (s.1 : ℕ) s.2) hget).symm.trans halt
  -- Target altitude: `alt (top cell of block r) = psum_B r`.
  have htgt : ∀ r : Fin B.length,
      alt (B.get r : ℕ) (yonedaEquiv (BPSet.serialWedge.ι B r))
        = dimPrefixSum (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩) (r : ℕ) := by
    intro r
    have hr : (r : ℕ) < (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩).length := by
      rw [hMlen]; exact r.2
    have halt := isCubeChain_alt_get alt hax (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩)
      (serialWedge B).init (serialWedge B).final hMchain (r : ℕ) hr
    rw [halt0, zero_add] at halt
    have hcast : (⟨(r : ℕ), hr⟩ :
        Fin (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩).length).cast hMlen = r := Fin.ext rfl
    have hget := wedgeToCubes_get B (𝟙 (serialWedge B).toPsh) ⟨(r : ℕ), hr⟩
    rw [hcast] at hget
    simp only [BPSet.id_hom, Category.comp_id] at hget
    exact (congrArg (fun s : Σ n : ℕ+, (serialWedge B).toPsh.cells (n : ℕ) =>
      alt (s.1 : ℕ) s.2) hget).symm.trans halt
  -- The prefix-sum bracketing of `blockIdx g i`.
  have hbound : ∀ i : Fin A.length,
      dimPrefixSum (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩) (blockIdx g i : ℕ)
          ≤ dimPrefixSum (wedgeToCubes ⟨A, g.hom⟩) (i : ℕ)
        ∧ dimPrefixSum (wedgeToCubes ⟨A, g.hom⟩) (i : ℕ)
          < dimPrefixSum (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩) ((blockIdx g i : ℕ) + 1) := by
    intro i
    -- `evCell g i` is a face of target block `blockIdx g i` (`blockFace_spec`); comparing
    -- altitudes via `alt_cubeMap` gives `psum_A i = psum_B (blockIdx g i) + trueCount`.
    have hstar : alt (A.get i : ℕ) (evCell g i)
        = alt (B.get (blockIdx g i) : ℕ) (yonedaEquiv (BPSet.serialWedge.ι B (blockIdx g i)))
          + (StdCube.trueCount (faceStar g i) : ℤ) := by
      have h := PrecubicalSet.alt_cubeMap alt hax
        (yonedaEquiv (BPSet.serialWedge.ι B (blockIdx g i))) (blockMor g i)
      have hcm : (serialWedge B).toPsh.cubeMap
            (yonedaEquiv (BPSet.serialWedge.ι B (blockIdx g i)))
          = BPSet.serialWedge.ι B (blockIdx g i) :=
        Equiv.symm_apply_apply yonedaEquiv _
      rw [hcm] at h
      -- rewrite `evCell g i` back into its block-face form (`blockFace_spec`); then `h`
      -- closes up to `StdCube.ev (blockMor g i) = faceStar g i` (definitional).
      rw [show evCell g i
          = (BPSet.serialWedge.ι B (blockIdx g i)).app (op (Box.ob (A.get i : ℕ))) (blockMor g i)
          from (blockFace_spec g i).symm]
      exact h
    have hcount : dimPrefixSum (wedgeToCubes ⟨A, g.hom⟩) (i : ℕ)
        = dimPrefixSum (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩) (blockIdx g i : ℕ)
          + (StdCube.trueCount (faceStar g i) : ℤ) := by
      have e3 := htgt (blockIdx g i)
      linarith [hsrc i, hstar, e3]
    have hnn : (0 : ℤ) ≤ (StdCube.trueCount (faceStar g i) : ℤ) :=
      Int.natCast_nonneg _
    have hrlt : (blockIdx g i : ℕ) < (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩).length := by
      rw [hMlen]; exact (blockIdx g i).2
    have hgetfst : ((wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩).get
        ⟨(blockIdx g i : ℕ), hrlt⟩).1 = B.get (blockIdx g i) := by
      have hcast : (⟨(blockIdx g i : ℕ), hrlt⟩ :
          Fin (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩).length).cast hMlen = blockIdx g i :=
        Fin.ext rfl
      rw [congrArg Sigma.fst (wedgeToCubes_get B (𝟙 (serialWedge B).toPsh)
        ⟨(blockIdx g i : ℕ), hrlt⟩), hcast]
    have hsucc := dimPrefixSum_succ (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩) hrlt
    rw [hgetfst] at hsucc
    -- The face is positive, so it fixes `< B.get r` coordinates to `true`.
    have htlt : (StdCube.trueCount (faceStar g i) : ℤ) < (B.get (blockIdx g i) : ℕ) := by
      have hle := StdCube.trueCount_le (faceStar g i)
      have hkpos := (A.get i).pos
      have hNpos := (B.get (blockIdx g i)).pos
      have hlt : StdCube.trueCount (faceStar g i) < (B.get (blockIdx g i) : ℕ) := by omega
      exact_mod_cast hlt
    exact ⟨by rw [hcount]; linarith, by rw [hcount, hsucc]; linarith⟩
  -- Monotonicity: bracket both `i` and `j`, use prefix-sum monotonicity, `omega`.
  intro i j hij
  rw [Fin.le_def]
  by_contra hcon
  rw [not_le] at hcon
  have hijval : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
  have hmL := dimPrefixSum_mono (wedgeToCubes ⟨A, g.hom⟩) hijval
  have hmM := dimPrefixSum_mono (wedgeToCubes ⟨B, (𝟙 (serialWedge B).toPsh)⟩)
    (show (blockIdx g j : ℕ) + 1 ≤ (blockIdx g i : ℕ) by omega)
  have b1 := (hbound i).1
  have b2 := (hbound j).2
  omega

/-- A star position of a block face is a `none` (free) coordinate. -/
theorem faceStar_val_nones (g : serialWedge A ⟶ serialWedge B) (j : Fin A.length)
    (p : Fin (A.get j : ℕ)) :
    (faceStar g j).val (StdCube.nones (faceStar g j) p) = none := by
  rw [← StdCube.mem_noneSet]
  exact Finset.orderEmbOfFin_mem (StdCube.noneSet (faceStar g j).val) (faceStar g j).prop p

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
      = some true :=
  sorry

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
      (∀ (i : Fin A.length) (p : Fin (A.get i : ℕ)),
          ((globalEquiv B).symm (σ (globalEquiv A ⟨i, p⟩))).1 = bm i) ∧
      (∀ t : Fin (dimSum B),
          bm (((globalEquiv A).symm (σ.symm t)).1) = ((globalEquiv B).symm t).1)

/-- **Forward inclusion**: the event permutation of any wedge map is valid.  Pure
assembly of Step 3: block-monotonicity is `ev_strictMonoOn`, the block map is `blockIdx`
(`ev_blockOf`), and the partition/covering is `ev_blocks`. -/
theorem ev_valid (g : serialWedge A ⟶ serialWedge B) : IsEvValid (evPerm g) :=
  ⟨fun i => by simpa only [evPerm_apply] using ev_strictMonoOn g i,
    blockIdx g,
    fun i p => by simpa only [evPerm_apply] using ev_blockOf g i p,
    fun t => ev_blocks g t⟩

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
    ∃ g : serialWedge A ⟶ serialWedge B, evPerm g = σ :=
  sorry

end FinalPrecubical
