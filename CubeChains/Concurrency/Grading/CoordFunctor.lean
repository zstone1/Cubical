import CubeChains.Concurrency.Grading.BlockDecomp
import CubeChains.Precubical.Chains.CubeVtx
import CubeChains.Precubical.Segal.Split
import CubeChains.Precubical.Wedge.CubeMerge
import CubeChains.Precubical.Basic.Reachability
import CubeChains.Machinery.SortPerm
import Mathlib.Data.Fintype.Inv
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Concurrency/Grading/CoordFunctor — coordinates of a serial wedge

A cube face `g : ▫n ⟶ ▫m` acts on coordinates by its free-coordinate embedding `faceEmb g :
Fin n ↪ Fin m`, and a serial wedge's coordinates are its beads' coordinates tagged by bead
(`beadEvent`).  A wedge map carries `⟨i, k⟩` to `⟨blockIdx φ i, faceEmb (blockFace φ i) k⟩`
(`coordMap`) and a chain to the coordinate its bead flips (`coordFlip`) — the bead data of
`Precubical/Chains/WedgeMap`, nothing else.

`coordMap` is functorial because bead data composes (`beadFace_comp`, `blockFace_spec` twice with
`yoneda` faithful), and `coordFlip` is bijective because distinct beads flip disjoint coordinates.
On top sits the event order: `pos` (counted by `dimSum`), `strand` (`pos` at a chosen count), and
`flatten` (the chain's own order compared with `strand`).
-/

open CategoryTheory CubeChain ChainCat BPSet StdCube Opposite PrecubicalSet

namespace CubeChains

/-! ## The coordinate bijection of a serial-wedge map into a cube

For `f : ⋁a ⟶ □m`, the coordinate `⟨i, k⟩` (the `k`-th coordinate of bead `i`) goes to the
coordinate of `□m` that bead `i` flips.  Distinct beads flip **disjoint** coordinates
(`coord_beads_disjoint`), so this map is injective for *any* presheaf `f` (`coord_sigma_injective`);
the engine is `readVec_mono`, a potential along `Reaches` read through `cubeVtx`.  For a bi-pointed
`χ` the count `dimSum a = m` upgrades injectivity to a bijection (`coord_sigma_bijective`). -/

/-- Bead `i`'s image face in `□m`: `beadCell` at a representable target, read as a `Box` hom. -/
def beadFace {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length) :
    ▫((a.get i : ℕ)) ⟶ ▫m := beadCell f i

/-- `beadFace` is the Yoneda cell of the bead restriction, in `Box`-hom spelling. -/
theorem yoneda_map_beadFace {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i : Fin a.length) : yoneda.map (beadFace f i) = ιᵂ a i ≫ f :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map (beadFace f i))

/-- The **`⊥`-vertex reading** of a cube face.  At `n = 0` a face *is* a vertex and this is cube
Yoneda; above that it is the potential `readVec_mono` runs on. -/
def readVec {n m : ℕ} (g : ▫n ⟶ ▫m) : Fin m → Bool := cubeVtx g (fun _ => false)

/-- A cube map acts on a `0`-cell by precomposition with its Yoneda cell (cube Yoneda). -/
theorem cube_app_zero {b m : ℕ} (f : (□b).toPsh ⟶ (□m).toPsh) (x : ▫0 ⟶ ▫b) :
    f⟪0⟫ x = x ≫ yonedaEquiv f := (map_yonedaEquiv f x).symm

/-- Reading a face extended along a `Box` hom is `cubeVtx` of that hom — `cubeVtx_comp` at `⊥`. -/
theorem readVec_vertex_comp {c m n : ℕ} (v : ▫n ⟶ ▫c) (g : ▫c ⟶ ▫m) :
    readVec (v ≫ g) = cubeVtx g (readVec v) :=
  congrArg (fun t : (Fin n → Bool) →o (Fin m → Bool) => t (fun _ => false)) (cubeVtx_comp v g)

/-- Reading a map at a cube-borne `0`-cell factors through `cubeVtx` of the Yoneda cell. -/
theorem readVec_app_zero {b m : ℕ} (f : (□b).toPsh ⟶ (□m).toPsh) (x : ▫0 ⟶ ▫b) :
    readVec (f⟪0⟫ x) = cubeVtx (yonedaEquiv f) (readVec x) := by
  rw [cube_app_zero f x, readVec_vertex_comp]

/-- Reading `f` at bead `i`'s vertices factors through `cubeVtx` of bead `i`'s face. -/
theorem readVec_bead {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length)
    (v : ▫0 ⟶ ▫(a.get i : ℕ)) :
    readVec (f⟪0⟫ ((ιᵂ a i)⟪0⟫ v)) = cubeVtx (beadFace f i) (readVec v) :=
  (congrArg readVec (comp_app_cell (f := ιᵂ a i) (g := f) (h := ιᵂ a i ≫ f) rfl 0 v)).trans
    (readVec_app_zero (ιᵂ a i ≫ f) v)

/-- `readVec` of `□m`'s `ε`-extremal vertex is constant `ε`. -/
theorem readVec_endVertexMap (ε : Bool) (m : ℕ) (q : Fin m) :
    readVec (endVertexMap ε m) q = ε := cubeVtx_bot_getD (endVertexMap ε m) q

/-! ### Reachability monotonicity of `readVec`

A face of `c` *is* `c` precomposed with a coface, so `readVec` of it is `cubeVtx c` of that
coface's own `⊥`-vertex: `⊥` again at a source face, and `cubeVtx c` is monotone.  That makes
`readVec` a potential along `Reaches`, and reading a coordinate through `f` cannot go from `true` to
`false` as the wedge is traversed. -/

/-- **The `⊥`-vertex of a source face is the `⊥`-vertex.** -/
theorem readVec_coface_false {n : ℕ} (i : Fin (n + 1)) :
    readVec (coface false i) = fun _ => false := by
  funext q
  refine (cubeVtx_bot_getD (coface false i) q).trans ?_
  rw [Box.sign_coface, face_val, nones_topCell]
  by_cases h : q = i
  · rw [h, Function.update_self]; rfl
  · rw [Function.update_of_ne h]; rfl

/-- **The `⊥`-vertex reading is monotone along reachability.** -/
theorem readVec_cell_mono {m : ℕ} {x y : (□m).toPsh.TotalCell} (h : Reaches (□m).toPsh x y) :
    readVec x.2 ≤ readVec y.2 := by
  have key : ∀ (ε : Bool) (n : ℕ) (i : Fin (n + 1)) (c : (□m).cells (n + 1)),
      readVec ((□m).toPsh.faceMap ε i c) = cubeVtx c (readVec (coface ε i)) :=
    fun ε n i c => readVec_vertex_comp (coface ε i) c
  have step : ∀ {u v : (□m).toPsh.TotalCell}, PrecubicalSet.Face (□m).toPsh u v →
      readVec u.2 ≤ readVec v.2 := by
    rintro u v hf
    cases hf with
    | @source n i c => rw [key false n i c, readVec_coface_false]; exact le_refl _
    | @target n i c => rw [key true n i c]; exact (cubeVtx c).monotone' fun _ => Bool.false_le _
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (step hbc)

/-- **`readVec` is monotone along vertex-reachability**, transported through a presheaf map `f`. -/
theorem readVec_mono {X : BPSet} {m : ℕ} (f : X.toPsh ⟶ (□m).toPsh) {v w : X.cells 0}
    (h : VertexReaches X.toPsh v w) : readVec (f⟪0⟫ v) ≤ readVec (f⟪0⟫ w) :=
  readVec_cell_mono ((h : Reaches X.toPsh ⟨0, v⟩ ⟨0, w⟩).map f)

/-- Within a single cube, the initial vertex reaches the final (bottom-to-top of the top cell). -/
theorem cube_reaches_init_final (n : ℕ) :
    Reaches (□n).toPsh ⟨0, (□n).init⟩ ⟨0, (□n).final⟩ := by
  have key : ∀ ε : Bool, (□n).toPsh.vertexEnd ε (𝟙 ▫n) = endVertexMap ε n :=
    fun ε => Category.comp_id (endVertexMap ε n)
  have h0 := reaches_vertexEnd (X := (□n).toPsh) false (𝟙 ▫n)
  have h1 := reaches_vertexEnd (X := (□n).toPsh) true (𝟙 ▫n)
  rw [key false] at h0
  rw [key true] at h1
  exact Relation.ReflTransGen.trans h0 h1

/-- Bead `s`'s `ε`-extremal vertex, as a `0`-cell of `⋁a`: `false` its bottom, `true` its top. -/
def beadEnd (ε : Bool) (a : List ℕ+) (s : Fin a.length) : (⋁a).toPsh.cells 0 :=
  (ιᵂ a s)⟪0⟫ (endVertexMap ε (a.get s : ℕ))

/-- Bead `s`'s extremal vertices are those of its tautological cube. -/
theorem beadEnd_eq_vertexEnd (ε : Bool) (a : List ℕ+) (s : Fin a.length) :
    beadEnd ε a s = (⋁a).toPsh.vertexEnd ε (tautBead a s) :=
  (vertexEnd_yonedaEquiv ε (ιᵂ a s)).symm

/-- **The wedge spine's junction**, an instance of the chain junction principle
(`isCubeChain_junction`): bead `s`'s top is bead `t = s+1`'s bottom.  The tautological chain
`(beadCell 𝟙).toList` reads bead `i`'s cube as `tautBead a i`. -/
theorem junction_eq (a : List ℕ+) (s t : Fin a.length) (h : (t : ℕ) = (s : ℕ) + 1) :
    beadEnd true a s = beadEnd false a t := by
  have hlen := Beads.length_toList (beadCell (𝟙 (⋁a).toPsh))
  have hcell : ∀ i : Fin a.length,
      (beadCell (𝟙 (⋁a).toPsh)).toList.get (i.cast hlen.symm) = ⟨a.get i, tautBead a i⟩ :=
    fun i => by
      rw [Beads.toList_get, beadCell_id, Fin.cast_cast, Fin.cast_eq_self]
  have hkey := isCubeChain_junction _ _ _ (beadCell_isCubeChain a (𝟙 (⋁a).toPsh))
    (s := s.cast hlen.symm) (t := t.cast hlen.symm) (by simp only [Fin.val_cast]; omega)
  rw [hcell s, hcell t] at hkey
  rw [beadEnd_eq_vertexEnd, beadEnd_eq_vertexEnd]
  exact hkey

/-- Bead `s`'s bottom reaches bead `t = s+k`'s bottom — the generic fold of the junction adjacency,
by recursion on the gap `k` (no wedge structure). -/
theorem beadBot_reaches_up (a : List ℕ+) (s : Fin a.length) :
    ∀ (k : ℕ) (t : Fin a.length), (t : ℕ) = (s : ℕ) + k →
      VertexReaches (⋁a).toPsh (beadEnd false a s) (beadEnd false a t)
  | 0, t, ht => by rw [show t = s from Fin.ext (by omega)]; exact Relation.ReflTransGen.refl
  | k + 1, t, ht => by
      have hk : s.val + k < a.length := by have := t.isLt; omega
      refine Relation.ReflTransGen.trans (beadBot_reaches_up a s k ⟨s.val + k, hk⟩ rfl) ?_
      rw [← junction_eq a ⟨s.val + k, hk⟩ t (by change (t : ℕ) = (s.val + k) + 1; omega)]
      exact Reaches.map (ιᵂ a ⟨s.val + k, hk⟩) (cube_reaches_init_final _)

/-- **Spine, bottom-to-bottom.**  If `s ≤ t` then bead `s`'s bottom reaches bead `t`'s bottom. -/
theorem beadBot_reaches_beadBot (a : List ℕ+) (s t : Fin a.length) (h : (s : ℕ) ≤ (t : ℕ)) :
    VertexReaches (⋁a).toPsh (beadEnd false a s) (beadEnd false a t) :=
  beadBot_reaches_up a s (t.val - s.val) t (by omega)

/-- **Spine, top-to-bottom.**  If `s < t` then bead `s`'s top reaches bead `t`'s bottom. -/
theorem beadTop_reaches_beadBot (a : List ℕ+) (s t : Fin a.length) (h : (s : ℕ) < (t : ℕ)) :
    VertexReaches (⋁a).toPsh (beadEnd true a s) (beadEnd false a t) := by
  have hsucc : s.val + 1 < a.length := by have := t.isLt; omega
  rw [junction_eq a s ⟨s.val + 1, hsucc⟩ rfl]
  exact beadBot_reaches_beadBot a ⟨s.val + 1, hsucc⟩ t (by change s.val + 1 ≤ (t : ℕ); omega)

/-- Bead `i` flips `q` ⟹ `q` reads `ε` at bead `i`'s `ε`-end (its free coords are all `ε`). -/
theorem readVec_beadEnd_flip (ε : Bool) {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i : Fin a.length) {q : Fin m} (hq : q ∈ Set.range (faceEmb (beadFace f i))) :
    readVec (f⟪0⟫ (beadEnd ε a i)) q = ε := by
  obtain ⟨k, rfl⟩ := hq
  rw [beadEnd, readVec_bead, cubeVtx_faceEmb]
  exact readVec_endVertexMap ε _ k

/-- An earlier and a later bead cannot both flip `q`: `q` is `true` at the earlier bead's top, which
reaches the later one's bottom (`readVec_mono`), where flipping would read `q` as `false`. -/
theorem not_flip_of_fst_lt {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    {i i' : Fin a.length} (hlt : (i : ℕ) < (i' : ℕ)) {q : Fin m}
    (hi : q ∈ Set.range (faceEmb (beadFace f i)))
    (hi' : q ∈ Set.range (faceEmb (beadFace f i'))) : False := by
  have hle := readVec_mono f (beadTop_reaches_beadBot a i i' hlt) q
  rw [readVec_beadEnd_flip true f i hi, readVec_beadEnd_flip false f i' hi'] at hle
  exact Bool.noConfusion (le_antisymm hle (Bool.false_le true))

/-- **Cross-bead disjointness.**  Distinct beads flip disjoint coordinates — whichever of the two
comes first has its top reach the other's bottom. -/
theorem coord_beads_disjoint (a : List ℕ+) {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i i' : Fin a.length) (q : Fin m) (hi : q ∈ Set.range (faceEmb (beadFace f i)))
    (hi' : q ∈ Set.range (faceEmb (beadFace f i'))) : i = i' := by
  rcases lt_trichotomy (i : ℕ) (i' : ℕ) with h | h | h
  · exact (not_flip_of_fst_lt f h hi hi').elim
  · exact Fin.ext h
  · exact (not_flip_of_fst_lt f h hi' hi).elim

/-- **The bead-flip sigma-map is injective** — within a bead `faceEmb` is an embedding, across beads
the flipped coordinates are disjoint. -/
theorem coord_sigma_injective {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
    Function.Injective (fun p : beadEvent a => faceEmb (beadFace f p.1) p.2) := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ hp
  obtain rfl : i = i' := coord_beads_disjoint a f i i' _ ⟨k, rfl⟩ ⟨k', hp.symm⟩
  obtain rfl : k = k' := (faceEmb (beadFace f i)).injective hp
  rfl

/-- `dimSum` in the `Fin`-indexed shape the event flattening `pos` counts in. -/
theorem dimSum_eq_sum_get (a : List ℕ+) : ∑ i : Fin a.length, (a.get i : ℕ) = dimSum a :=
  (List.sum_map_eq_sum_get a (fun d : ℕ+ => (d : ℕ))).symm.trans (dimSum_sum a).symm

/-- **The count.**  Total bead dimension equals the target dimension. -/
theorem wedgeDimSum_eq {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) : dimSum a = m := by
  rcases m with _ | m
  · have h := serialWedge_dimSum_eq (ad := a) (cd := ([] : List ℕ+)) χ
    simpa [dimSum] using h
  · have h := serialWedge_dimSum_eq (ad := a) (cd := [⟨m + 1, m.succ_pos⟩])
      (χ ≫ (serialWedge1 ⟨m + 1, m.succ_pos⟩).inv)
    have hd : dimSum [⟨m + 1, m.succ_pos⟩] = m + 1 := by simp [dimSum]
    rw [hd] at h; exact h

/-- **The bead-flip sigma-map is bijective** — injective (disjoint beads) plus equal cardinality
(count = dimension). -/
theorem coord_sigma_bijective {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    Function.Bijective (fun p : beadEvent a => faceEmb (beadFace χ.hom p.1) p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨coord_sigma_injective χ.hom, ?_⟩
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [← List.sum_map_eq_sum_get a (fun d : ℕ+ => (d : ℕ)), ← dimSum_sum]
  exact wedgeDimSum_eq χ


/-- **The coordinate bijection** of a bipointed wedge map into a cube: `⟨i,k⟩ ↦` the coordinate of
`□m` that bead `i` flips — computable, its inverse a `Fintype.bijInv`. -/
def coordFlip {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) : beadEvent a ≃ Fin m where
  toFun p := faceEmb (beadFace χ.hom p.1) p.2
  invFun := Fintype.bijInv (coord_sigma_bijective χ)
  left_inv := Fintype.leftInverse_bijInv (coord_sigma_bijective χ)
  right_inv := Fintype.rightInverse_bijInv (coord_sigma_bijective χ)

/-- **Escape hatch to the concrete machinery**: `coordFlip χ ⟨i,k⟩` is the coordinate of `□m` that
bead `i` flips — `faceEmb` of bead `i`'s face at `k`. -/
@[simp] theorem coordFlip_eq {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) (p : beadEvent a) :
    coordFlip χ p = faceEmb (beadFace χ.hom p.1) p.2 := rfl

/-- The **wedge coordinate map** of a serial-wedge map: bead data, coordinate by coordinate.
Functorial (`coordMap_id`, `coordMap_comp`). -/
def coordMap {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) : beadEvent a → beadEvent b :=
  fun p => ⟨blockIdx φ.hom p.1, faceEmb (blockFace φ.hom p.1) p.2⟩

/-- **The block form of `coordMap`** — definitional. -/
theorem coordMap_eq {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) (k : Fin (a.get i : ℕ)) :
    coordMap φ ⟨i, k⟩ = ⟨blockIdx φ.hom i, faceEmb (blockFace φ.hom i) k⟩ := rfl

/-- **`coordMap` from any bead factorization** — a bead inclusion is a mono
(`serialWedge_ι_mono`) and `yoneda` is faithful, so a factorization through bead `i` *is* the
block data.  Callers with a factorization of their own (a concatenation, an identity) need not
compute `blockFace`. -/
theorem coordMap_of_factor {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (s : Fin a.length) (i : Fin b.length)
    (g : ▫((a.get s : ℕ)) ⟶ ▫((b.get i : ℕ)))
    (hfac : ιᵂ a s ≫ φ.hom = yoneda.map g ≫ ιᵂ b i) (k : Fin (a.get s : ℕ)) :
    coordMap φ ⟨s, k⟩ = ⟨i, faceEmb g k⟩ := by
  obtain rfl : i = blockIdx φ.hom s := blockIdx_eq_of_factor φ.hom s i g hfac
  obtain rfl : blockFace φ.hom s = g :=
    yoneda.map_injective ((cancel_mono (ιᵂ b (blockIdx φ.hom s))).mp
      ((blockFace_spec φ.hom s).symm.trans hfac))
  rfl

@[simp] theorem coordMap_id {a : List ℕ+} : coordMap (𝟙 (⋁a)) = id := by
  funext p
  obtain ⟨i, k⟩ := p
  rw [coordMap_of_factor (𝟙 (⋁a)) i i (𝟙 _) (by simp) k, faceEmb_id]
  rfl

/-- **A composite restricted to a bead** factors through the block that `φ` puts the bead in —
`blockFace_spec` reassociated, and the one step behind both composition laws below. -/
theorem ι_comp_blockFace {a b : List ℕ+} {X : PrecubicalSet} (φ : (⋁a).toPsh ⟶ (⋁b).toPsh)
    (ψ : (⋁b).toPsh ⟶ X) (i : Fin a.length) :
    ιᵂ a i ≫ φ ≫ ψ = yoneda.map (blockFace φ i) ≫ ιᵂ b (blockIdx φ i) ≫ ψ := by
  rw [← Category.assoc, blockFace_spec φ i]
  exact Category.assoc _ _ _

/-- **Bead data composes.**  Bead `i` of `φ ≫ ψ` is bead `blockIdx φ i` of `ψ` restricted along
`φ`'s own block face — `yoneda` faithful. -/
theorem beadFace_comp {a b : List ℕ+} {m : ℕ} (φ : (⋁a).toPsh ⟶ (⋁b).toPsh)
    (ψ : (⋁b).toPsh ⟶ (□m).toPsh) (i : Fin a.length) :
    beadFace (φ ≫ ψ) i = blockFace φ i ≫ beadFace ψ (blockIdx φ i) :=
  yoneda.map_injective (by
    rw [yoneda_map_beadFace, Functor.map_comp, yoneda_map_beadFace, ι_comp_blockFace]
    rfl)

theorem coordMap_comp {a b c : List ℕ+} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ ⋁c) :
    coordMap (φ ≫ ψ) = coordMap ψ ∘ coordMap φ := by
  funext p
  obtain ⟨s, k⟩ := p
  have hfac : ιᵂ a s ≫ (φ ≫ ψ).hom
      = yoneda.map (blockFace φ.hom s ≫ blockFace ψ.hom (blockIdx φ.hom s))
        ≫ ιᵂ c (blockIdx ψ.hom (blockIdx φ.hom s)) := by
    rw [comp_hom, ι_comp_blockFace, Functor.map_comp, Category.assoc,
      ← blockFace_spec ψ.hom (blockIdx φ.hom s)]
    rfl
  rw [coordMap_of_factor (φ ≫ ψ) s _ _ hfac k]
  exact congrArg (fun t => (⟨blockIdx ψ.hom (blockIdx φ.hom s), t⟩ : beadEvent c))
    (faceEmb_comp (blockFace φ.hom s) (blockFace ψ.hom (blockIdx φ.hom s)) k)

/-- **Functoriality of `coordFlip`** — precomposing with a wedge map `φ` reindexes coordinates by
`coordMap φ`; `beadFace_comp` with `faceEmb` functorial. -/
theorem coordFlip_comp_apply {a b : List ℕ+} {m : ℕ} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ □m)
    (p : beadEvent a) : coordFlip (φ ≫ ψ) p = coordFlip ψ (coordMap φ p) := by
  obtain ⟨i, k⟩ := p
  change faceEmb (beadFace (φ.hom ≫ ψ.hom) i) k = _
  rw [beadFace_comp, faceEmb_comp]
  rfl

/-- **The bead a coordinate lands in reads off `coordMap`** — `proj₁ ∘ coordMap` is `blockIdx` of
the source bead. -/
@[simp] theorem coordMap_fst {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (p : beadEvent a) :
    (coordMap φ p).1 = blockIdx φ.hom p.1 := by
  obtain ⟨i, k⟩ := p; rw [coordMap_eq]

/-- **`proj₁ ∘ coordMap` is monotone** — a coordinate's bead index moves monotonically under a
bi-pointed wedge map, being `blockIdx` of the source bead (`serialWedge_blockIdx_monotone`). -/
theorem coordMap_fst_monotone {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) {p q : beadEvent a} (h : p.1 ≤ q.1) :
    (coordMap φ p).1 ≤ (coordMap φ q).1 := by
  simp only [coordMap_fst]
  exact serialWedge_blockIdx_monotone φ.hom φ.app_init h

/-! ## The coordinate map of a wedge map is bijective

A wedge becomes a cube by gluing its beads together (`nonempty_toCube`), and a wedge map composed
with such a chain is one again — so both readings of `coordMap φ` are `coordFlip`, which is a
bijection because each cube coordinate is flipped by exactly one bead. -/

/-- **A serial wedge merges into the cube of its own total dimension** — glue the beads together
one at a time. -/
theorem nonempty_toCube : ∀ b : List ℕ+, Nonempty (⋁b ⟶ □(dimSum b))
  | [] => ⟨𝟙 (□0)⟩
  | c :: rest => (nonempty_toCube rest).map fun t =>
      wedge2Map (𝟙 (□(c : ℕ))) t ≫ cubeMerge (c : ℕ) (dimSum rest)

/-- **The wedge coordinate map is bijective** — `coordFlip` at a chain of the target, cancelled. -/
theorem coordMap_bijective {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) :
    Function.Bijective (coordMap φ) := by
  obtain ⟨χ⟩ := nonempty_toCube b
  rw [show coordMap φ = ⇑(coordFlip χ).symm ∘ ⇑(coordFlip (φ ≫ χ)) from
    funext fun p => ((coordFlip χ).symm_apply_eq.mpr (coordFlip_comp_apply φ χ p)).symm]
  exact (coordFlip χ).symm.bijective.comp (coordFlip (φ ≫ χ)).bijective

/-- The wedge coordinate map as an `Equiv`, with `_apply = rfl`.  Computable: the inverse is the
`Fintype.bijInv` of the coend bijection, not `Equiv.ofBijective`'s choice. -/
def coordMapEquiv {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) : beadEvent a ≃ beadEvent b where
  toFun := coordMap φ
  invFun := Fintype.bijInv (coordMap_bijective φ)
  left_inv := Fintype.leftInverse_bijInv (coordMap_bijective φ)
  right_inv := Fintype.rightInverse_bijInv (coordMap_bijective φ)

@[simp] theorem coordMapEquiv_apply {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (p : beadEvent a) :
    coordMapEquiv φ p = coordMap φ p := rfl

@[simp] theorem coordMapEquiv_id {a : List ℕ+} : coordMapEquiv (𝟙 (⋁a)) = Equiv.refl _ :=
  Equiv.ext fun p => by rw [coordMapEquiv_apply, coordMap_id, id_eq, Equiv.refl_apply]

/-- **A chain precomposed is the chain reindexed** — `coordFlip_comp_apply`, as an `Equiv`.  This is
what makes a chain morphism the comparison of the two chains' firing orders
(`conjPerm_mul_pullback`). -/
theorem coordFlip_comp {a b : List ℕ+} {m : ℕ} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ □m) :
    coordFlip (φ ≫ ψ) = (coordMapEquiv φ).trans (coordFlip ψ) :=
  Equiv.ext (coordFlip_comp_apply φ ψ)

/-- **`coordMapEquiv` is a functor to bijections** — `coordMap_comp`, as an `Equiv`. -/
theorem coordMapEquiv_comp {a b c : List ℕ+} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ ⋁c) :
    coordMapEquiv (φ ≫ ψ) = (coordMapEquiv φ).trans (coordMapEquiv ψ) :=
  Equiv.ext fun p => by
    rw [coordMapEquiv_apply, coordMap_comp, Function.comp_apply, Equiv.trans_apply,
      coordMapEquiv_apply, coordMapEquiv_apply]

/-- **The inverse relabelling reflects the bead order strictly** — `coordMap_fst_monotone` read
backwards through the bijection, which is what every "an event of an earlier bead is performed
earlier" argument needs. -/
theorem coordMapEquiv_symm_fst_lt {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) {p q : beadEvent b}
    (h : (p.1 : ℕ) < (q.1 : ℕ)) :
    (((coordMapEquiv φ).symm p).1 : ℕ) < (((coordMapEquiv φ).symm q).1 : ℕ) := by
  by_contra hcon
  have hmono := coordMap_fst_monotone φ (Fin.le_def.mpr (not_lt.mp hcon))
  rw [show coordMap φ ((coordMapEquiv φ).symm q) = q from (coordMapEquiv φ).apply_symm_apply q,
    show coordMap φ ((coordMapEquiv φ).symm p) = p from
      (coordMapEquiv φ).apply_symm_apply p] at hmono
  exact absurd h (not_lt.mpr (Fin.le_def.mp hmono))

/-! ## The event flattening `pos`

`finSigmaFinEquiv` enumerates the lex order on events, counted by `dimSum`.  Its only computation is
`pos_val`, which says `pos` is the bead's start plus the offset inside it — so every order fact
below is `beadStart_succ` and `beadStart_mono`, on the ordered partition, and the raw `Fin` prefix
sums never escape. -/

/-- `beadStart` in the `Fin`-indexed shape `finSigmaFinEquiv_apply` produces. -/
theorem beadStart_eq_sum (dims : List ℕ+) :
    ∀ (i : ℕ) (h : i ≤ dims.length),
      beadStart dims i = ∑ u : Fin i, ((dims.get (u.castLE h)) : ℕ)
  | 0, _ => by simp
  | i + 1, h => by
      rw [beadStart_succ dims ⟨i, h⟩, beadStart_eq_sum dims i (Nat.le_of_succ_le h),
        Fin.sum_univ_castSucc]
      rfl

/-- The canonical, run-free event order: flatten the beads lexicographically.  Counted by `dimSum`,
the spelling every consumer uses — `finSigmaFinEquiv`'s own `∑ i : Fin _` never escapes. -/
def pos {dims : List ℕ+} : beadEvent dims ≃ Fin (dimSum dims) :=
  finSigmaFinEquiv.trans (finCongr (dimSum_eq_sum_get dims))

/-- **`pos` is `beadStart` plus the within-bead offset** — the bridge to the ordered partition, and
the one computation underneath every order fact about the flattening. -/
theorem pos_val {dims : List ℕ+} (e : beadEvent dims) :
    (pos e : ℕ) = beadStart dims e.1 + (e.2 : ℕ) := by
  rw [beadStart_eq_sum dims e.1 e.1.2.le]
  exact finSigmaFinEquiv_apply e

theorem pos_mk {dims : List ℕ+} (i : Fin dims.length) (x : Fin ((dims.get i : ℕ))) :
    (pos (⟨i, x⟩ : beadEvent dims) : ℕ) = beadStart dims i + (x : ℕ) :=
  pos_val ⟨i, x⟩

/-- Earlier bead ⇒ earlier in the flattening: bead `e.1` ends where bead `e.1 + 1` starts, which is
at or below where `e'.1` starts. -/
theorem pos_lt_of_fst_lt {dims : List ℕ+} {e e' : beadEvent dims} (h : (e.1 : ℕ) < e'.1) :
    pos e < pos e' := by
  have hsucc := beadStart_succ dims e.1
  have hmono := beadStart_mono dims (show (e.1 : ℕ) + 1 ≤ (e'.1 : ℕ) from h)
  have hoff := e.2.isLt
  rw [Fin.lt_def, pos_val, pos_val]
  omega

/-- Inside a bead, the flattening is the coordinate order. -/
theorem pos_lt_iff_of_fst_eq {dims : List ℕ+} {i : Fin dims.length} {k k' : Fin (dims.get i : ℕ)} :
    pos (⟨i, k⟩ : beadEvent dims) < pos ⟨i, k'⟩ ↔ k < k' := by
  rw [Fin.lt_def, pos_mk, pos_mk, Fin.lt_def]
  omega

/-- The flattening reflects the bead order: an earlier event sits in a bead no later. -/
theorem fst_le_of_pos_lt {dims : List ℕ+} {e e' : beadEvent dims} (h : pos e < pos e') :
    (e.1 : ℕ) ≤ e'.1 :=
  le_of_not_gt fun hc => absurd (pos_lt_of_fst_lt hc) (asymm h)

/-! ### Inside a bead the event order survives

Within one bead a chain is `faceEmb` of that bead's block face (`coordFlip_eq`), and `faceEmb` is an
order embedding — so it cannot invert a within-bead pair. -/

/-- **Inside a bead a chain preserves the event order** — the same fact at a cube target. -/
theorem coordFlip_lt_iff_pos_lt {d : List ℕ+} {N : ℕ} (χ : ⋁d ⟶ □N) {u v : beadEvent d}
    (h : u.1 = v.1) : coordFlip χ u < coordFlip χ v ↔ pos u < pos v := by
  obtain ⟨j, l⟩ := u
  obtain ⟨j', l'⟩ := v
  obtain rfl : j = j' := h
  rw [coordFlip_eq, coordFlip_eq, pos_lt_iff_of_fst_eq]
  exact (faceEmb (beadFace χ.hom j)).lt_iff_lt


/-! ### `strand` — `pos` at a chosen count

A strand count is *derived* from a shape (`dimSum`), so a permutation of the strands has to be read
at some count the shape meets.  Carrying that count as an argument — rather than transporting
afterwards — is what makes the cocycle law of `crossPerm` a plain anti-homomorphism: the target
numbering of `g` and the source numbering of `h` differ only in their proofs, hence not at all. -/

/-- The strand an event occupies, at a strand count the shape meets — the events, flattened
lexicographically. -/
def strand (d : List ℕ+) {N : ℕ} (h : dimSum d = N) : beadEvent d ≃ Fin N :=
  pos.trans (finCongr h)

@[simp] theorem strand_val (d : List ℕ+) {N : ℕ} (h : dimSum d = N) (e : beadEvent d) :
    (strand d h e : ℕ) = (pos e : ℕ) := rfl

/-- **The event of another shape at the same rank.**  Two shapes of one total dimension have their
events matched by the flattening alone — which is all a comparison of the two ever needs. -/
def strandTransfer {d d' : List ℕ+} {N : ℕ} (h : dimSum d = N) (h' : dimSum d' = N) :
    beadEvent d ≃ beadEvent d' :=
  (strand d h).trans (strand d' h').symm

theorem pos_strandTransfer {d d' : List ℕ+} {N : ℕ} (h : dimSum d = N) (h' : dimSum d' = N)
    (e : beadEvent d) : (pos (strandTransfer h h' e) : ℕ) = (pos e : ℕ) :=
  (strand_val d' h' _).symm.trans
    (congrArg Fin.val ((strand d' h').apply_symm_apply (strand d h e)))

/-! ### `flatten` — the firing order of a chain

A chain `⋁d ⟶ □N` identifies the events of `d` with the coordinates of `□N` (`coordFlip`), so the
cube's coordinates acquire two orderings: their own, and the lexicographic `strand`.  `flatten` is
the comparison — the `φ = 1` case of `conjPerm`, and the order in which the chain fires the
coordinates.  A run of `□N` is a chain of an all-edges shape, so its step order is this same map. -/

/-- **The firing order of a chain**: the rank of the event that flips a coordinate. -/
def flatten {N : ℕ} (A : Ch (□N)) : Equiv.Perm (Fin N) :=
  conjPerm (coordFlip A.map) (strand A.dims (wedgeDimSum_eq A.map)) (Equiv.refl _)

theorem flatten_val {N : ℕ} (A : Ch (□N)) (q : Fin N) :
    (flatten A q : ℕ) = (pos ((coordFlip A.map).symm q) : ℕ) := rfl

/-- **A chain carries the event order to its own**: the chain's `flatten` *is* `strand`. -/
theorem flatten_coordFlip {d : List ℕ+} {N : ℕ} (χ : ⋁d ⟶ □N) (e : beadEvent d) :
    flatten (⟨d, χ⟩ : Ch (□N)) (coordFlip χ e) = strand d (wedgeDimSum_eq χ) e :=
  conjPerm_apply _ _ _ e

/-! ### `pos` on a cons and on an all-edges shape -/

theorem pos_cons_zero (c : ℕ+) (rest : List ℕ+) (x : Fin (((c :: rest).get 0 : ℕ))) :
    (pos (⟨0, x⟩ : beadEvent (c :: rest)) : ℕ) = (x : ℕ) := by
  simpa using pos_mk (dims := c :: rest) 0 x

theorem pos_cons_succ (c : ℕ+) (rest : List ℕ+) (j : Fin rest.length)
    (x : Fin (((c :: rest).get j.succ : ℕ))) :
    (pos (⟨j.succ, x⟩ : beadEvent (c :: rest)) : ℕ)
      = (c : ℕ) + (pos (⟨j, x⟩ : beadEvent rest) : ℕ) := by
  rw [pos_mk, pos_mk, Fin.val_succ, beadStart_cons_succ]
  exact Nat.add_assoc _ _ _

/-- On an all-edges shape every bead starts at its own index. -/
theorem beadStart_ones {dims : List ℕ+} (h : ∀ d ∈ dims, d = 1) {i : ℕ} (hi : i ≤ dims.length) :
    beadStart dims i = i := by
  rw [beadStart, dimSum_eq_length_of_ones (fun d hd => h d (List.mem_of_mem_take hd)),
    List.length_take, min_eq_left hi]

/-- **On an all-edges shape the flattening is the bead index** — one event per bead. -/
theorem pos_ones {dims : List ℕ+} (h : ∀ d ∈ dims, d = 1) (e : beadEvent dims) :
    (pos e : ℕ) = (e.1 : ℕ) := by
  have hd : ((dims.get e.1 : ℕ)) = 1 := congrArg PNat.val (h _ (List.get_mem _ _))
  have h2 : (e.2 : ℕ) = 0 := by have := e.2.isLt; omega
  rw [pos_val, beadStart_ones h e.1.2.le, h2, Nat.add_zero]

/-! ### Events of a concatenated word

`beadEvent (a ++ b)` is the disjoint union `beadEvent a ⊕ beadEvent b`, and `pos` shifts the
second summand past `dimSum a`.  Only the two inclusions are named — the `Fin`-index casts that a
full `Equiv` would carry are exactly what the callers do not want to see. -/

theorem beadStart_append_left (a b : List ℕ+) {i : ℕ} (h : i ≤ a.length) :
    beadStart (a ++ b) i = beadStart a i := by
  rw [beadStart, beadStart, List.take_append_of_le_length h]

theorem beadStart_append_right (a b : List ℕ+) (j : ℕ) :
    beadStart (a ++ b) (a.length + j) = dimSum a + beadStart b j := by
  rw [beadStart, beadStart, List.take_append, dimSum_append, Nat.add_sub_cancel_left,
    List.take_of_length_le (Nat.le_add_right _ _)]

theorem get_append_left {a b : List ℕ+} {i : Fin a.length} {s : Fin (a ++ b).length}
    (hs : (s : ℕ) = (i : ℕ)) : ((a ++ b).get s : ℕ) = (a.get i : ℕ) := by
  simp only [List.get_eq_getElem, hs, List.getElem_append_left i.isLt]

theorem get_append_right {a b : List ℕ+} {j : Fin b.length} {s : Fin (a ++ b).length}
    (hs : (s : ℕ) = a.length + (j : ℕ)) : ((a ++ b).get s : ℕ) = (b.get j : ℕ) := by
  simp only [List.get_eq_getElem, hs, List.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- An event of the first factor, read in the concatenation. -/
def eventInl (a b : List ℕ+) (e : beadEvent a) : beadEvent (a ++ b) :=
  ⟨⟨(e.1 : ℕ), by rw [List.length_append]; omega⟩, Fin.cast (get_append_left rfl).symm e.2⟩

/-- An event of the second factor, read in the concatenation. -/
def eventInr (a b : List ℕ+) (e : beadEvent b) : beadEvent (a ++ b) :=
  ⟨⟨a.length + (e.1 : ℕ), by rw [List.length_append]; omega⟩,
    Fin.cast (get_append_right rfl).symm e.2⟩

/-- Events are determined by their bead index and offset. -/
theorem beadEvent_ext {d : List ℕ+} {e e' : beadEvent d} (h1 : (e.1 : ℕ) = (e'.1 : ℕ))
    (h2 : (e.2 : ℕ) = (e'.2 : ℕ)) : e = e' := by
  obtain ⟨i, k⟩ := e
  obtain ⟨i', k'⟩ := e'
  obtain rfl : i = i' := Fin.ext h1
  exact congrArg _ (Fin.ext h2)

/-- **Every event of a concatenation lies in one of the two factors.** -/
theorem eventAppendCases {a b : List ℕ+} {P : beadEvent (a ++ b) → Prop}
    (hl : ∀ x, P (eventInl a b x)) (hr : ∀ y, P (eventInr a b y)) (e : beadEvent (a ++ b)) :
    P e := by
  have hlen : (e.1 : ℕ) < a.length + b.length := by
    have := e.1.isLt; simpa using this
  rcases Nat.lt_or_ge (e.1 : ℕ) a.length with h | h
  · have key : eventInl a b ⟨⟨(e.1 : ℕ), h⟩, Fin.cast (get_append_left rfl) e.2⟩ = e :=
      beadEvent_ext rfl rfl
    exact key ▸ hl _
  · have hj : (e.1 : ℕ) - a.length < b.length := by omega
    have hs : (e.1 : ℕ) = a.length + ((e.1 : ℕ) - a.length) := by omega
    have key : eventInr a b ⟨⟨(e.1 : ℕ) - a.length, hj⟩, Fin.cast (get_append_right hs) e.2⟩ = e :=
      beadEvent_ext (by simpa using hs.symm) rfl
    exact key ▸ hr _

@[simp] theorem eventInl_fst_val (a b : List ℕ+) (e : beadEvent a) :
    ((eventInl a b e).1 : ℕ) = (e.1 : ℕ) := rfl

@[simp] theorem eventInr_fst_val (a b : List ℕ+) (e : beadEvent b) :
    ((eventInr a b e).1 : ℕ) = a.length + (e.1 : ℕ) := rfl

@[simp] theorem eventInl_snd_val (a b : List ℕ+) (e : beadEvent a) :
    ((eventInl a b e).2 : ℕ) = (e.2 : ℕ) := rfl

@[simp] theorem eventInr_snd_val (a b : List ℕ+) (e : beadEvent b) :
    ((eventInr a b e).2 : ℕ) = (e.2 : ℕ) := rfl

/-- The first factor's events keep their strand. -/
theorem pos_eventInl (a b : List ℕ+) (e : beadEvent a) :
    (pos (eventInl a b e) : ℕ) = (pos e : ℕ) := by
  rw [pos_val, pos_val, eventInl_fst_val, eventInl_snd_val,
    beadStart_append_left a b e.1.2.le]

/-- The second factor's events are shifted past the first factor's coordinates. -/
theorem pos_eventInr (a b : List ℕ+) (e : beadEvent b) :
    (pos (eventInr a b e) : ℕ) = dimSum a + (pos e : ℕ) := by
  rw [pos_val, pos_val, eventInr_fst_val, eventInr_snd_val, beadStart_append_right]
  omega

/-! ## The coordinate map along a bead-inclusion square

A bead of the source that sits inside a sub-wedge, carried by `Φ` into a bead of the target that
sits inside another, moves its coordinates by whatever cube face joins the two sub-wedges.  Every
`coordMap` computation on a wedge built from pieces — the two half-inclusions of `++`, the two
legs of a chain concatenation — is this one square. -/

/-- **`coordMap` along a bead-inclusion square.**  With `hσ`/`hτ` placing bead `s` inside `σ` and
bead `s'` inside `τ`, and `g` the cube face joining them:

      □n  --σ-->  ⋁c
      |            |
      g            Φ
      v            v
      □n' --τ--> ⋁c'

`Φ` sends bead `s`'s coordinate `x` to bead `s'`'s coordinate `faceEmb g k`.  The bead casts make
the two `Fin`s only equal on values, so the conclusion is stated on values. -/
theorem coordMap_of_beadFactor {c c' : List ℕ+} (Φ : ⋁c ⟶ ⋁c')
    {s : Fin c.length} {n : ℕ} {σ : (□n).toPsh ⟶ (⋁c).toPsh} (hσ : IsBeadFactor s σ)
    {s' : Fin c'.length} {n' : ℕ} {τ : (□n').toPsh ⟶ (⋁c').toPsh} (hτ : IsBeadFactor s' τ)
    {g : (▫n : Box) ⟶ ▫n'} (hg : σ ≫ Φ.hom = yoneda.map g ≫ τ)
    (x : Fin ((c.get s : ℕ))) (k : Fin n) (hx : (k : ℕ) = (x : ℕ)) :
    (coordMap Φ ⟨s, x⟩).1 = s'
      ∧ ((coordMap Φ ⟨s, x⟩).2 : ℕ) = ((faceEmb g k : Fin n') : ℕ) := by
  obtain ⟨e₁, he₁, hfac₁⟩ := hσ
  obtain ⟨e₂, he₂, hfac₂⟩ := hτ
  have hτ' : yoneda.map e₂.inv ≫ ιᵂ c' s' = τ := by
    rw [hfac₂]; exact (yoneda.mapIso e₂).inv_hom_id_assoc τ
  have hfac : ιᵂ c s ≫ Φ.hom = yoneda.map (e₁.hom ≫ g ≫ e₂.inv) ≫ ιᵂ c' s' := by
    refine Eq.trans ?_ ?_ (b := yoneda.map e₁.hom ≫ yoneda.map g ≫ τ)
    · rw [hfac₁]
      exact (Category.assoc _ _ _).trans (congrArg (fun t => yoneda.map e₁.hom ≫ t) hg)
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      refine ((Category.assoc _ _ _).trans
        (congrArg (fun t => yoneda.map e₁.hom ≫ t) ?_)).symm
      exact (Category.assoc _ _ _).trans (congrArg (fun t => yoneda.map g ≫ t) hτ')
  rw [coordMap_of_factor Φ s s' _ hfac x]
  refine ⟨rfl, ?_⟩
  rw [faceEmb_comp, faceEmb_comp, faceEmb_iso_inv_val e₂ he₂]
  exact congrArg (fun t : Fin n => ((faceEmb g t : Fin n') : ℕ))
    (Fin.ext ((he₁ x).trans hx.symm))

/-! ## The coordinate map is monoidal over `++`

A wedge map of appended words that restricts along the half-inclusions `wedgeInclL`/`wedgeInclR`
moves each block's coordinates by the corresponding restriction: `coordMap` is a map of
coproducts.  The half-inclusion square is the only input, so `chConcat`'s tensorator inherits it
from `concatHomφ_inclL`/`_inclR`. -/

/-- **A commuting square restricted to one bead.**  The two readings below differ only in how the
right-hand leg factors — `blockFace_spec` at a wedge target, `yoneda_map_beadFace` at a cube. -/
theorem incl_sq {a : List ℕ+} {P Q R : PrecubicalSet} {v : (⋁a).toPsh ⟶ P}
    {w : (⋁a).toPsh ⟶ Q} {Φ : Q ⟶ R} {w' : P ⟶ R} (h : w ≫ Φ = v ≫ w') (i : Fin a.length) :
    (ιᵂ a i ≫ w) ≫ Φ = (ιᵂ a i ≫ v) ≫ w' :=
  ((Category.assoc _ _ _).trans (congrArg (ιᵂ a i ≫ ·) h)).trans (Category.assoc _ _ _).symm

/-- **The bead leg of an inclusion square, at a wedge target.**  It restricts, at bead `i`, to
`ψ`'s own block factorization — the only input the two half-inclusions need. -/
theorem incl_sq_bead {a a' c c' : List ℕ+} (Φ : ⋁c ⟶ ⋁c') {ψ : ⋁a ⟶ ⋁a'}
    {w : (⋁a).toPsh ⟶ (⋁c).toPsh} {w' : (⋁a').toPsh ⟶ (⋁c').toPsh}
    (h : w ≫ Φ.hom = ψ.hom ≫ w') (i : Fin a.length) :
    (ιᵂ a i ≫ w) ≫ Φ.hom
      = yoneda.map (blockFace ψ.hom i) ≫ (ιᵂ a' (blockIdx ψ.hom i) ≫ w') :=
  (incl_sq h i).trans
    ((congrArg (· ≫ w') (blockFace_spec ψ.hom i)).trans (Category.assoc _ _ _))

/-- **…and at a cube target**, where the factorization is the bead cell itself. -/
theorem incl_sq_beadFace {a c c' : List ℕ+} {m : ℕ} (Φ : ⋁c ⟶ ⋁c') {χ : ⋁a ⟶ □m}
    {w : (⋁a).toPsh ⟶ (⋁c).toPsh} {w' : (□m).toPsh ⟶ (⋁c').toPsh}
    (h : w ≫ Φ.hom = χ.hom ≫ w') (i : Fin a.length) :
    (ιᵂ a i ≫ w) ≫ Φ.hom = yoneda.map (beadFace χ.hom i) ≫ w' :=
  (incl_sq h i).trans (congrArg (· ≫ w') (yoneda_map_beadFace χ.hom i).symm)

/-- **Left block.**  A wedge map restricting to `ψ` on the first block moves that block's
coordinates by `coordMap ψ`. -/
theorem coordMap_inclL {a b a' b' : List ℕ+} (Φ : ⋁(a ++ b) ⟶ ⋁(a' ++ b')) {ψ : ⋁a ⟶ ⋁a'}
    (h : wedgeInclL a b ≫ Φ.hom = ψ.hom ≫ wedgeInclL a' b') (e : beadEvent a) :
    coordMap Φ (eventInl a b e) = eventInl a' b' (coordMap ψ e) := by
  obtain ⟨i, k⟩ := e
  obtain ⟨h1, h2⟩ := coordMap_of_beadFactor Φ (ι_appendL b a i (eventInl a b ⟨i, k⟩).1 rfl)
    (ι_appendL b' a' (blockIdx ψ.hom i) (eventInl a' b' (coordMap ψ ⟨i, k⟩)).1
      (congrArg Fin.val (coordMap_fst ψ ⟨i, k⟩))) (incl_sq_bead Φ h i)
    (eventInl a b ⟨i, k⟩).2 k rfl
  exact beadEvent_ext (congrArg Fin.val h1)
    (h2.trans (congrArg (fun z : beadEvent a' => (z.2 : ℕ)) (coordMap_eq ψ i k)).symm)

/-- **Right block.**  A wedge map restricting to `ψ` on the second block moves that block's
coordinates by `coordMap ψ`. -/
theorem coordMap_inclR {a b a' b' : List ℕ+} (Φ : ⋁(a ++ b) ⟶ ⋁(a' ++ b')) {ψ : ⋁b ⟶ ⋁b'}
    (h : wedgeInclR a b ≫ Φ.hom = ψ.hom ≫ wedgeInclR a' b') (e : beadEvent b) :
    coordMap Φ (eventInr a b e) = eventInr a' b' (coordMap ψ e) := by
  obtain ⟨j, k⟩ := e
  obtain ⟨h1, h2⟩ := coordMap_of_beadFactor Φ (ι_appendR b a j (eventInr a b ⟨j, k⟩).1 rfl)
    (ι_appendR b' a' (blockIdx ψ.hom j) (eventInr a' b' (coordMap ψ ⟨j, k⟩)).1
      (congrArg (fun z : Fin b'.length => a'.length + (z : ℕ)) (coordMap_fst ψ ⟨j, k⟩)))
    (incl_sq_bead Φ h j) (eventInr a b ⟨j, k⟩).2 k rfl
  exact beadEvent_ext (congrArg Fin.val h1)
    (h2.trans (congrArg (fun z : beadEvent b' => (z.2 : ℕ)) (coordMap_eq ψ j k)).symm)

/-- **The tensorator on coordinates, left block** — `concatHomφ_inclL`. -/
theorem coordMap_concatHomφ_left {K L : BPSet} {a a' : Ch K} {b b' : Ch L} (f : a ⟶ a')
    (g : b ⟶ b') (e : beadEvent a.dims) :
    coordMap (concatHomφ f g) (eventInl a.dims b.dims e)
      = eventInl a'.dims b'.dims (coordMap f.φ e) :=
  coordMap_inclL _ (concatHomφ_inclL f g) e

/-- **The tensorator on coordinates, right block** — `concatHomφ_inclR`. -/
theorem coordMap_concatHomφ_right {K L : BPSet} {a a' : Ch K} {b b' : Ch L} (f : a ⟶ a')
    (g : b ⟶ b') (e : beadEvent b.dims) :
    coordMap (concatHomφ f g) (eventInr a.dims b.dims e)
      = eventInr a'.dims b'.dims (coordMap g.φ e) :=
  coordMap_inclR _ (concatHomφ_inclR f g) e

end CubeChains
