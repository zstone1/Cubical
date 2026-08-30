import CubeChains.Concurrency.Grading.BlockDecomp
import CubeChains.Precubical.Segal.WedgeExtend
import CubeChains.Precubical.Chains.CubeVtx
import CubeChains.Precubical.Segal.Segal
import CubeChains.Precubical.Segal.Split
import CubeChains.Precubical.Basic.Reachability
import CubeChains.Machinery.SortPerm
import Mathlib.Data.Fintype.Inv
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Concurrency/Grading/CoordFunctor — the coordinate copresheaf `▫n ↦ Fin n`

A cube face `g : ▫n ⟶ ▫m` acts on coordinates by its free-coordinate embedding `faceEmb g :
Fin n ↪ Fin m`.  It is **empty at `▫0`**, so its cubical coend `cotensorLift Coord`
(`Precubical/Segal/WedgeExtend`) sends a serial wedge to the *coproduct* of its beads' coordinate
sets — the ordered partition of the coordinates a cube chain realises (`coordWedge`), and a cube to
its own coordinate set (`coordCube`).
-/

open CategoryTheory CubeChain ChainCat BPSet StdCube Opposite PrecubicalSet

namespace CubeChains

/-- The **coordinate copresheaf** `▫n ↦ Fin n`, a cube face acting by `faceEmb`. -/
def Coord : Box ⥤ Type where
  obj b := Fin b.dim
  map g := ↾fun i => faceEmb g i
  map_id b := by
    apply ConcreteCategory.hom_ext
    intro i
    rw [TypeCat.ofHom_apply, types_id_apply]
    exact faceEmb_id b.dim i
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro i
    rw [TypeCat.ofHom_apply, types_comp_apply, TypeCat.ofHom_apply, TypeCat.ofHom_apply]
    exact faceEmb_comp g h i

@[simp] theorem Coord_obj (b : Box) : Coord.obj b = Fin b.dim := rfl

@[simp] theorem Coord_map_apply {b b' : Box} (g : b ⟶ b') (i : Fin b.dim) :
    Coord.map g i = faceEmb g i :=
  rfl

/-- `Coord` is **empty at the point** `▫0` — what turns its coend into a coproduct. -/
instance : IsEmpty (Coord.obj ▫0) := inferInstanceAs (IsEmpty (Fin 0))

/-! ## The coend of `Coord` -/

/-- **A cube's coend is its coordinate set** `Coord↓ □m ≃ Fin m` — co-Yoneda. -/
def coordCube (m : ℕ) : (cotensorLift Coord).obj (□m) ≃ Fin m :=
  Cotensor.cubeEquiv Coord m

/-- **A serial wedge's coend is its beads' coordinate sets, indexed by bead**
`Coord↓ (⋁a) ≃ Σ i : Fin a.length, Fin (a.get i)` — a coordinate's bead is the first component. -/
def coordWedge (a : List ℕ+) :
    (cotensorLift Coord).obj (⋁a) ≃ Σ i : Fin a.length, Fin ((a.get i : ℕ)) :=
  cotensorSigmaEquiv Coord inferInstance a

/-- **A bead coordinate assembles from its bead inclusion.**  `coordWedge` reads bead `i`'s
inclusion, decorated by the `k`-th coordinate of `□(aᵢ)`, back to `⟨i, k⟩`. -/
theorem coordWedge_apply_map (a : List ℕ+) (i : Fin a.length) (k : Fin ((a.get i : ℕ))) :
    coordWedge a (Cotensor.map Coord (ιᵂ a i) ((coordCube (a.get i : ℕ)).symm k)) = ⟨i, k⟩ :=
  cotensorSigmaEquiv_apply_map Coord inferInstance a i k

/-- **A bead coordinate is its bead inclusion decorated by the coordinate.**  `coordWedge.symm`
sends `⟨i, k⟩` to bead `i`'s inclusion pushed onto the `k`-th coordinate of `□(aᵢ)`. -/
theorem coordWedge_symm_apply (a : List ℕ+) (i : Fin a.length) (k : Fin ((a.get i : ℕ))) :
    (coordWedge a).symm ⟨i, k⟩
      = Cotensor.map Coord (ιᵂ a i) ((coordCube (a.get i : ℕ)).symm k) :=
  cotensorSigmaEquiv_symm_apply Coord inferInstance a i k

/-- **Pushing a cube coordinate along a cube map** reads off `faceEmb` of the Yoneda cell. -/
theorem coordCube_map_symm {m b : ℕ} (g : (□m).toPsh ⟶ (□b).toPsh) (k : Fin m) :
    coordCube b (Cotensor.map Coord g ((coordCube m).symm k)) = faceEmb (yonedaEquiv g) k := rfl

/-! ## The coordinate bijection of a serial-wedge map into a cube

For `f : ⋁a ⟶ □m`, its coend `Coord↓(f)` sends the coordinate `⟨i, k⟩` (the `k`-th coordinate of
bead `i`) to the coordinate of `□m` bead `i` flips.  Distinct beads flip **disjoint** coordinates
(`coord_beads_disjoint`), so this map is injective for *any* presheaf `f` (`coord_sigma_injective`);
the "once true stays true" vertex induction (`coord_stays_true`, read through `cubeVtx`) is the
engine.  For a bi-pointed `χ` the count `dimSum a = m` upgrades injectivity to a bijection
(`coordLift_map_bijective`). -/

/-- Bead `i`'s image face in `□m`: `beadCell` at a representable target, read as a `Box` hom. -/
def beadFace {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length) :
    ▫((a.get i : ℕ)) ⟶ ▫m := beadCell f i

/-- `beadFace` is the Yoneda cell of the bead restriction, in `Box`-hom spelling. -/
theorem yoneda_map_beadFace {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i : Fin a.length) : yoneda.map (beadFace f i) = ιᵂ a i ≫ f :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map (beadFace f i))

/-- The coordinate coend map `Coord↓(f)` of a serial-wedge map into a cube. -/
abbrev coordFlip' {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
    Cotensor Coord (⋁a).toPsh → Cotensor Coord (□m).toPsh := Cotensor.map Coord f

/-- The `0`-cell reader: a vertex of `□m` (a `Box` hom `▫0 ⟶ ▫m`) as a sign vector, via `cubeVtx`
at the empty input. -/
def readVec {m : ℕ} (u : ▫0 ⟶ ▫m) : Fin m → Bool := cubeVtx u (fun i => i.elim0)

/-- A cube map acts on a `0`-cell by precomposition with its Yoneda cell (cube Yoneda). -/
theorem cube_app_zero {b m : ℕ} (f : (□b).toPsh ⟶ (□m).toPsh) (x : ▫0 ⟶ ▫b) :
    f⟪0⟫ x = x ≫ yonedaEquiv f := (map_yonedaEquiv f x).symm

/-- Reading a vertex extended along a `Box` hom is `cubeVtx` of that hom (transport law). -/
theorem readVec_vertex_comp {c m : ℕ} (v : ▫0 ⟶ ▫c) (g : ▫c ⟶ ▫m) :
    readVec (v ≫ g) = cubeVtx g (readVec v) := by
  change cubeVtx (v ≫ g) (fun i => i.elim0) = cubeVtx g (cubeVtx v (fun i => i.elim0))
  rw [cubeVtx_comp]; rfl

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

/-- `readVec` of `□m`'s initial vertex is constant `false`. -/
theorem readVec_init (m : ℕ) (q : Fin m) : readVec ((□m).init) q = false := by
  have hev : toStar ((□m).init : (□m).cells 0) = constVertex m false := by
    rw [toStar_eq]; exact ev_canonicalMap (K := stdPre m) (constVertex m false)
  change cubeVtxOfCell (toStar ((□m).init : (□m).cells 0)) (fun i => i.elim0) q = false
  rw [hev, cubeVtxOfCell_apply,
    dif_neg (by simp [constVertex] : q ∉ noneSet (constVertex m false).val)]
  rfl

/-- `readVec` of `□m`'s final vertex is constant `true`. -/
theorem readVec_final (m : ℕ) (q : Fin m) : readVec ((□m).final) q = true := by
  have hev : toStar ((□m).final : (□m).cells 0) = constVertex m true := by
    rw [toStar_eq]; exact ev_canonicalMap (K := stdPre m) (constVertex m true)
  change cubeVtxOfCell (toStar ((□m).final : (□m).cells 0)) (fun i => i.elim0) q = true
  rw [hev, cubeVtxOfCell_apply,
    dif_neg (by simp [constVertex] : q ∉ noneSet (constVertex m true).val)]
  rfl

/-! ### Reachability monotonicity of `readVec`

`readVec` is monotone along vertex-reachability: reading a coordinate through `f` cannot go from
`true` to `false` as the wedge is traversed.  The potential is `low`, the `⊥`-vertex vector of a
decorated cell, monotone along `Reaches` (a source face fixes it, a target face raises it). -/

/-- `ev` of a face is the corresponding face of the sign vector. -/
theorem ev_faceMap {m n : ℕ} (ε : Bool) (i : Fin (n + 1)) (c : (□m).cells (n + 1)) :
    ev ((□m).toPsh.faceMap ε i c) = faceCell ε i (ev c) := by
  have h1 : ev ((□m).toPsh.faceMap ε i c)
      = PrecubicalConstructions.Hom.app c n (ev (PrecubicalSet.coface ε i)) :=
    ev_comp (PrecubicalSet.coface ε i) c
  rw [h1, ev_coface, app_unique (c := ev c) c rfl (faceCell ε i (topCell (n + 1))), app_face,
    app_topCell]
  rfl

/-- A `false`-face leaves the `⊥`-vertex reading unchanged (the freed coord was already `false`). -/
theorem getD_faceCell_false {m k : ℕ} (i : Fin (k + 1)) (b : Cell m (k + 1)) (q : Fin m) :
    ((faceCell false i b).val q).getD false = (b.val q).getD false := by
  rw [face_val]
  by_cases hq : q = nones b i
  · subst hq; rw [Function.update_self, mem_noneSet.mp (nones_mem b i)]; rfl
  · rw [Function.update_of_ne hq]

/-- A `true`-face can only raise the `⊥`-vertex reading (the freed coord flips `false → true`). -/
theorem getD_faceCell_true_ge {m k : ℕ} (i : Fin (k + 1)) (b : Cell m (k + 1)) (q : Fin m) :
    (b.val q).getD false ≤ ((faceCell true i b).val q).getD false := by
  rw [face_val]
  by_cases hq : q = nones b i
  · subst hq; rw [Function.update_self, mem_noneSet.mp (nones_mem b i)]; exact Bool.false_le _
  · rw [Function.update_of_ne hq]

/-- The `⊥`-vertex vector of a decorated total cell — a monotone potential along `Reaches`. -/
def low {m : ℕ} (x : (□m).toPsh.TotalCell) : Fin m → Bool :=
  cubeVtxOfCell (toStar x.2) (fun _ => false)

/-- **`low` is monotone along reachability** — a source face fixes it, a target raises it. -/
theorem low_mono {m : ℕ} {x y : (□m).toPsh.TotalCell} (h : Reaches (□m).toPsh x y) :
    low x ≤ low y := by
  induction h with
  | refl x => exact le_refl _
  | @source n i c =>
      intro q
      change cubeVtxOfCell (toStar ((□m).toPsh.faceMap false i c)) (fun _ => false) q
        ≤ cubeVtxOfCell (toStar c) (fun _ => false) q
      rw [cubeVtxOfCell_bot, cubeVtxOfCell_bot,
        show toStar ((□m).toPsh.faceMap false i c) = faceCell false i (toStar c)
          from ev_faceMap false i c]
      exact le_of_eq (getD_faceCell_false i (toStar c) q)
  | @target n i c =>
      intro q
      change cubeVtxOfCell (toStar c) (fun _ => false) q
        ≤ cubeVtxOfCell (toStar ((□m).toPsh.faceMap true i c)) (fun _ => false) q
      rw [cubeVtxOfCell_bot, cubeVtxOfCell_bot,
        show toStar ((□m).toPsh.faceMap true i c) = faceCell true i (toStar c)
          from ev_faceMap true i c]
      exact getD_faceCell_true_ge i (toStar c) q
  | trans _ _ ih₁ ih₂ => exact le_trans ih₁ ih₂

/-- At dimension `0`, `low` is `readVec` (a vertex has no free coordinates). -/
theorem low_zero {m : ℕ} (u : ▫0 ⟶ ▫m) : low ⟨0, u⟩ = readVec u := by
  have he : (fun _ => false : Fin 0 → Bool) = (fun i => i.elim0) := funext (fun i => i.elim0)
  change cubeVtxOfCell (toStar u) (fun _ => false) = cubeVtx u (fun i => i.elim0)
  rw [he, cubeVtx_eq]

/-- **`readVec` is monotone along cube reachability of vertices.** -/
theorem readVec_cube_mono {m : ℕ} {u u' : ▫0 ⟶ ▫m}
    (h : Reaches (□m).toPsh ⟨0, u⟩ ⟨0, u'⟩) : readVec u ≤ readVec u' := by
  rw [← low_zero u, ← low_zero u']
  exact low_mono h

/-- **`readVec` is monotone along vertex-reachability**, transported through a presheaf map `f`. -/
theorem readVec_mono {X : BPSet} {m : ℕ} (f : X.toPsh ⟶ (□m).toPsh) {v w : X.cells 0}
    (h : VertexReaches X.toPsh v w) : readVec (f⟪0⟫ v) ≤ readVec (f⟪0⟫ w) :=
  readVec_cube_mono ((h : Reaches X.toPsh ⟨0, v⟩ ⟨0, w⟩).map f)

/-- Within a single cube, the initial vertex reaches the final (bottom-to-top of the top cell). -/
theorem cube_reaches_init_final (n : ℕ) :
    Reaches (□n).toPsh ⟨0, (□n).init⟩ ⟨0, (□n).final⟩ := by
  have e0 : (□n).toPsh.vertex₀ (𝟙 ▫n) = (□n).init := Category.comp_id (initVertexMap n)
  have e1 : (□n).toPsh.vertex₁ (𝟙 ▫n) = (□n).final := Category.comp_id (finalVertexMap n)
  have h0 := reaches_vertex₀ (X := (□n).toPsh) (𝟙 ▫n)
  have h1 := reaches_vertex₁ (X := (□n).toPsh) (𝟙 ▫n)
  rw [e0] at h0
  rw [e1] at h1
  exact h0.trans h1

/-- Bead `s`'s bottom vertex, as a `0`-cell of `⋁a`. -/
def beadBot (a : List ℕ+) (s : Fin a.length) : (⋁a).toPsh.cells 0 :=
  (ιᵂ a s)⟪0⟫ ((□(a.get s : ℕ)).init)

/-- Bead `s`'s top vertex, as a `0`-cell of `⋁a`. -/
def beadTop (a : List ℕ+) (s : Fin a.length) : (⋁a).toPsh.cells 0 :=
  (ιᵂ a s)⟪0⟫ ((□(a.get s : ℕ)).final)

/-- Bead `s`'s bottom vertex is `vertex₀` of its tautological cube (`(□n).init` is defeq
`initVertexMap n`). -/
theorem beadBot_eq_vertex₀ (a : List ℕ+) (s : Fin a.length) :
    beadBot a s = (⋁a).toPsh.vertex₀ (tautBead a s) :=
  (vertex₀_yonedaEquiv (ιᵂ a s)).symm

/-- Bead `s`'s top vertex is `vertex₁` of its tautological cube. -/
theorem beadTop_eq_vertex₁ (a : List ℕ+) (s : Fin a.length) :
    beadTop a s = (⋁a).toPsh.vertex₁ (tautBead a s) :=
  (vertex₁_yonedaEquiv (ιᵂ a s)).symm

/-- **The wedge spine's junction**, an instance of the chain junction principle
(`isCubeChain_junction`): bead `s`'s top is bead `t = s+1`'s bottom.  The tautological chain
`wedgeToCubes ⟨a, 𝟙⟩` reads bead `i`'s cube as `tautBead a i`. -/
theorem junction_eq (a : List ℕ+) (s t : Fin a.length) (h : (t : ℕ) = (s : ℕ) + 1) :
    beadTop a s = beadBot a t := by
  have hlen := wedgeToCubes_length a (𝟙 (⋁a).toPsh)
  have hcell : ∀ i : Fin a.length,
      (wedgeToCubes ⟨a, 𝟙 (⋁a).toPsh⟩).get (i.cast hlen.symm) = ⟨a.get i, tautBead a i⟩ :=
    fun i => by
      rw [wedgeToCubes_get, beadCell_id, Fin.cast_cast, Fin.cast_eq_self]
  have hkey := isCubeChain_junction _ _ _ (wedgeToCubes_isCubeChain a (𝟙 (⋁a).toPsh))
    (s := s.cast hlen.symm) (t := t.cast hlen.symm) (by simp only [Fin.val_cast]; omega)
  rw [hcell s, hcell t] at hkey
  rw [beadTop_eq_vertex₁, beadBot_eq_vertex₀]
  exact hkey

/-- Bead `s`'s bottom reaches bead `t = s+k`'s bottom — the generic fold of the junction adjacency,
by recursion on the gap `k` (no wedge structure). -/
theorem beadBot_reaches_up (a : List ℕ+) (s : Fin a.length) :
    ∀ (k : ℕ) (t : Fin a.length), (t : ℕ) = (s : ℕ) + k →
      VertexReaches (⋁a).toPsh (beadBot a s) (beadBot a t)
  | 0, t, ht => by rw [show t = s from Fin.ext (by omega)]; exact Reaches.refl _
  | k + 1, t, ht => by
      have hk : s.val + k < a.length := by have := t.isLt; omega
      refine Reaches.trans (beadBot_reaches_up a s k ⟨s.val + k, hk⟩ rfl) ?_
      rw [← junction_eq a ⟨s.val + k, hk⟩ t (by change (t : ℕ) = (s.val + k) + 1; omega)]
      exact Reaches.map (ιᵂ a ⟨s.val + k, hk⟩) (cube_reaches_init_final _)

/-- **Spine, bottom-to-bottom.**  If `s ≤ t` then bead `s`'s bottom reaches bead `t`'s bottom. -/
theorem beadBot_reaches_beadBot (a : List ℕ+) (s t : Fin a.length) (h : (s : ℕ) ≤ (t : ℕ)) :
    VertexReaches (⋁a).toPsh (beadBot a s) (beadBot a t) :=
  beadBot_reaches_up a s (t.val - s.val) t (by omega)

/-- **Spine, top-to-bottom.**  If `s < t` then bead `s`'s top reaches bead `t`'s bottom. -/
theorem beadTop_reaches_beadBot (a : List ℕ+) (s t : Fin a.length) (h : (s : ℕ) < (t : ℕ)) :
    VertexReaches (⋁a).toPsh (beadTop a s) (beadBot a t) := by
  have hsucc : s.val + 1 < a.length := by have := t.isLt; omega
  rw [junction_eq a s ⟨s.val + 1, hsucc⟩ rfl]
  exact beadBot_reaches_beadBot a ⟨s.val + 1, hsucc⟩ t (by change s.val + 1 ≤ (t : ℕ); omega)

/-- Bead `i` flips `q` ⟹ `q` reads `true` at bead `i`'s top (its free coords are all `true`). -/
theorem readVec_beadTop_flip {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i : Fin a.length) {q : Fin m} (hq : q ∈ Set.range (faceEmb (beadFace f i))) :
    readVec (f⟪0⟫ ((ιᵂ a i)⟪0⟫ (□(a.get i : ℕ)).final)) q = true := by
  obtain ⟨k, rfl⟩ := hq; rw [readVec_bead, cubeVtx_faceEmb]; exact readVec_final _ k

/-- Bead `i` flips `q` ⟹ `q` reads `false` at bead `i`'s bottom (free coords all `false`). -/
theorem readVec_beadBot_flip {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh)
    (i : Fin a.length) {q : Fin m} (hq : q ∈ Set.range (faceEmb (beadFace f i))) :
    readVec (f⟪0⟫ ((ιᵂ a i)⟪0⟫ (□(a.get i : ℕ)).init)) q = false := by
  obtain ⟨k, rfl⟩ := hq; rw [readVec_bead, cubeVtx_faceEmb]; exact readVec_init _ k

/-- Bead `0` and a later bead cannot both flip `q`: `q` is `true` at bead `0`'s top, which reaches
the later bead's bottom (`readVec_mono`), where flipping would read `q` as `false`. -/
theorem beadTop0_not_flip_below {c : ℕ+} {rest : List ℕ+} {m : ℕ}
    (f : (⋁(c :: rest)).toPsh ⟶ (□m).toPsh) (j' : Fin rest.length) {q : Fin m}
    (h0 : q ∈ Set.range (faceEmb (beadFace f 0)))
    (hs : q ∈ Set.range (faceEmb (beadFace f j'.succ))) : False := by
  have hle := readVec_mono f (beadTop_reaches_beadBot (c :: rest) 0 j'.succ (by simp)) q
  have htop : readVec (f⟪0⟫ (beadTop (c :: rest) 0)) q = true := readVec_beadTop_flip f 0 h0
  have hbot : readVec (f⟪0⟫ (beadBot (c :: rest) j'.succ)) q = false :=
    readVec_beadBot_flip f j'.succ hs
  rw [htop, hbot] at hle
  exact Bool.noConfusion (le_antisymm hle (Bool.false_le true))

/-- **Cross-bead disjointness.**  Distinct beads flip disjoint coordinates.  If beads `i < i'` both
flip `q`, then `q` is `true` at bead `i`'s top which reaches bead `i'`'s bottom (`readVec_mono`),
contradicting that bead `i'` reads `q` as `false` there. -/
theorem coord_beads_disjoint :
    ∀ (a : List ℕ+) {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i i' : Fin a.length) (q : Fin m),
      q ∈ Set.range (faceEmb (beadFace f i)) →
      q ∈ Set.range (faceEmb (beadFace f i')) → i = i'
  | [], _, _, i, _, _, _, _ => i.elim0
  | c :: rest, m, f, i, i', q, hi, hi' => by
      have hrange : ∀ (j : Fin rest.length),
          Set.range (faceEmb (beadFace f j.succ))
            = Set.range (faceEmb
                (beadFace (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex ≫ f) j)) :=
        fun j => congrArg (fun w => Set.range (faceEmb w)) (beadCell_succ f j)
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨j', rfl⟩
      · rfl
      · exact (beadTop0_not_flip_below f j' hi hi').elim
      · exact (beadTop0_not_flip_below f j hi' hi).elim
      · exact congrArg Fin.succ (coord_beads_disjoint rest
          (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex ≫ f) j j' q
          ((hrange j) ▸ hi) ((hrange j') ▸ hi'))

/-- The coend map on the coordinate `⟨i, k⟩`: bead `i` flips the coordinate `faceEmb (beadFace f i)`
reads off. -/
theorem coordWedgeCube_apply {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length)
    (k : Fin (a.get i : ℕ)) :
    coordCube m (coordFlip' f ((coordWedge a).symm ⟨i, k⟩)) = faceEmb (beadFace f i) k := by
  change coordCube m (Cotensor.map Coord f ((coordWedge a).symm ⟨i, k⟩)) = faceEmb (beadFace f i) k
  rw [coordWedge_symm_apply, Cotensor.map_map]
  exact coordCube_map_symm _ _

/-- **The bead-flip sigma-map is injective** — within a bead `faceEmb` is an embedding, across beads
the flipped coordinates are disjoint. -/
theorem coord_sigma_injective {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
    Function.Injective
      (fun p : Σ i : Fin a.length, Fin (a.get i : ℕ) => faceEmb (beadFace f p.1) p.2) := by
  rintro ⟨i, k⟩ ⟨i', k'⟩ hp
  obtain rfl : i = i' := coord_beads_disjoint a f i i' _ ⟨k, rfl⟩ ⟨k', hp.symm⟩
  obtain rfl : k = k' := (faceEmb (beadFace f i)).injective hp
  rfl

/-- `coordFlip' f` conjugated by the coordinate equivs is the bead-flip sigma-map. -/
theorem coordFlip'_eq {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
    coordFlip' f
      = ⇑(coordCube m).symm
        ∘ (fun p : Σ i : Fin a.length, Fin (a.get i : ℕ) => faceEmb (beadFace f p.1) p.2)
        ∘ ⇑(coordWedge a) := by
  funext t
  simp only [Function.comp_apply]
  apply (coordCube m).injective
  rw [Equiv.apply_symm_apply]
  have hthis := coordWedgeCube_apply f (coordWedge a t).1 (coordWedge a t).2
  rw [Sigma.eta, Equiv.symm_apply_apply] at hthis
  exact hthis

/-- `dimSum` in the `Fin`-indexed shape the event flattening `pos` counts in. -/
theorem dimSum_eq_sum_get (a : List ℕ+) : ∑ i : Fin a.length, (a.get i : ℕ) = dimSum a :=
  (sum_get_eq_sum_map a (fun d : ℕ+ => (d : ℕ))).trans (dimSum_sum a).symm

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
    Function.Bijective
      (fun p : Σ i : Fin a.length, Fin (a.get i : ℕ) => faceEmb (beadFace χ.hom p.1) p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨coord_sigma_injective χ.hom, ?_⟩
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [sum_get_eq_sum_map a (fun d : ℕ+ => (d : ℕ)), ← dimSum_sum]
  exact wedgeDimSum_eq χ


/-! ### The coend map bijections (bipointed)

`(cotensorLift Coord).map χ` is `coordFlip' χ.hom` (`cotensorLift_map_apply`), which conjugates to
the bead-flip sigma-map — bijective by disjointness + the dimension count. -/

/-- The coend map underlying `(cotensorLift Coord).map χ` is `coordFlip' χ.hom`. -/
theorem cotensorLift_map_eq_coordFlip' {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    ⇑((cotensorLift Coord).map χ) = coordFlip' χ.hom := by
  funext t; exact cotensorLift_map_apply Coord χ t

/-- **The coend map is bijective** — each coordinate of `□m` is flipped by exactly one bead. -/
theorem coordLift_map_bijective {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    Function.Bijective ((cotensorLift Coord).map χ) := by
  rw [cotensorLift_map_eq_coordFlip' χ, coordFlip'_eq χ.hom]
  exact (coordCube m).symm.bijective.comp
    ((coord_sigma_bijective χ).comp (coordWedge a).bijective)

/-- Coend classes of a serial wedge are finite (via `coordWedge`). -/
instance coordWedgeObjFintype (a : List ℕ+) : Fintype ((cotensorLift Coord).obj (⋁a)) :=
  Fintype.ofEquiv _ (coordWedge a).symm

/-- Coend classes of a cube have decidable equality (via `coordCube`). -/
instance coordCubeObjDecEq (m : ℕ) : DecidableEq ((cotensorLift Coord).obj (□m)) :=
  (coordCube m).injective.decidableEq

/-- **The coordinate bijection** of a bipointed wedge map into a cube: `⟨i,k⟩ ↦` the coordinate of
`□m` that bead `i` flips.  Built through the coend map `(cotensorLift Coord).map χ` (conjugated by
`coordWedge`/`coordCube`); computable, its inverse the coend map's `Fintype.bijInv`. -/
def coordFlip {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    (Σ i : Fin a.length, Fin (a.get i : ℕ)) ≃ Fin m where
  toFun := coordCube m ∘ (cotensorLift Coord).map χ ∘ (coordWedge a).invFun
  invFun := coordWedge a ∘ Fintype.bijInv (coordLift_map_bijective χ) ∘ (coordCube m).invFun
  left_inv p := by
    simp only [Function.comp_apply, Equiv.invFun_as_coe, Equiv.symm_apply_apply]
    rw [Fintype.leftInverse_bijInv (coordLift_map_bijective χ), Equiv.apply_symm_apply]
  right_inv q := by
    simp only [Function.comp_apply, Equiv.invFun_as_coe, Equiv.symm_apply_apply]
    rw [Fintype.rightInverse_bijInv (coordLift_map_bijective χ), Equiv.apply_symm_apply]

/-- **Escape hatch to the concrete machinery**: `coordFlip χ ⟨i,k⟩` is the coordinate of `□m` that
bead `i` flips — `faceEmb` of bead `i`'s face at `k`. -/
@[simp] theorem coordFlip_eq {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m)
    (p : Σ i : Fin a.length, Fin (a.get i : ℕ)) :
    coordFlip χ p = faceEmb (beadFace χ.hom p.1) p.2 := by
  obtain ⟨i, k⟩ := p
  simp only [coordFlip, Equiv.coe_fn_mk, Function.comp_apply, Equiv.invFun_as_coe,
    cotensorLift_map_eq_coordFlip']
  exact coordWedgeCube_apply χ.hom i k

/-- The **wedge coordinate map** of a serial-wedge map — the coend functor `cotensorLift Coord`
acting on `φ`, read through `coordWedge`.  Functorial (`coordMap_id`, `coordMap_comp`). -/
def coordMap {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) :
    (Σ i : Fin a.length, Fin (a.get i : ℕ)) → Σ j : Fin b.length, Fin (b.get j : ℕ) :=
  coordWedge b ∘ (cotensorLift Coord).map φ ∘ (coordWedge a).invFun

@[simp] theorem coordMap_id {a : List ℕ+} : coordMap (𝟙 (⋁a)) = id := by
  funext p
  simp only [coordMap, Function.comp_apply, CategoryTheory.Functor.map_id, types_id_apply,
    Equiv.invFun_as_coe, Equiv.apply_symm_apply, id_eq]

/-- **Coend functoriality in wedge coordinates** — the shared step of `coordMap_comp` (`Y = ⋁c`)
and `coordFlip_comp` (`Y = □m`). -/
theorem cotensorLift_map_coordWedge_comp {a b : List ℕ+} {Y : BPSet} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ Y)
    (p : Σ i : Fin a.length, Fin (a.get i : ℕ)) :
    (cotensorLift Coord).map (φ ≫ ψ) ((coordWedge a).invFun p)
      = (cotensorLift Coord).map ψ ((coordWedge b).invFun (coordMap φ p)) := by
  rw [Functor.map_comp_apply]
  congr 2
  simp only [coordMap, Function.comp_apply, Equiv.invFun_as_coe, Equiv.symm_apply_apply]

theorem coordMap_comp {a b c : List ℕ+} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ ⋁c) :
    coordMap (φ ≫ ψ) = coordMap ψ ∘ coordMap φ :=
  funext fun p => congrArg (coordWedge c) (cotensorLift_map_coordWedge_comp φ ψ p)

/-- **Functoriality of `coordFlip`** — the coend functor law: precomposing with a wedge map `φ`
reindexes coordinates by `coordMap φ`. -/
theorem coordFlip_comp {a b : List ℕ+} {m : ℕ} (φ : ⋁a ⟶ ⋁b) (ψ : ⋁b ⟶ □m)
    (p : Σ i : Fin a.length, Fin (a.get i : ℕ)) :
    coordFlip (φ ≫ ψ) p = coordFlip ψ (coordMap φ p) :=
  congrArg (coordCube m) (cotensorLift_map_coordWedge_comp φ ψ p)

/-- **`coordMap` from any bead factorization** — `blockIdx`/`blockFace` is one (`coordMap_eq`), but
a concatenation supplies its own more cheaply. -/
theorem coordMap_of_factor {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (s : Fin a.length) (i : Fin b.length)
    (g : ▫((a.get s : ℕ)) ⟶ ▫((b.get i : ℕ)))
    (hfac : ιᵂ a s ≫ φ.hom = yoneda.map g ≫ ιᵂ b i) (k : Fin (a.get s : ℕ)) :
    coordMap φ ⟨s, k⟩ = ⟨i, faceEmb g k⟩ := by
  have e1 : (cotensorLift Coord).map φ ((coordWedge a).invFun ⟨s, k⟩)
      = Cotensor.map Coord (ιᵂ a s ≫ φ.hom) ((coordCube (a.get s : ℕ)).symm k) := by
    rw [Equiv.invFun_as_coe, coordWedge_symm_apply, cotensorLift_map_apply, Cotensor.map_map]
  have hinner : Cotensor.map Coord (yoneda.map g) ((coordCube (a.get s : ℕ)).symm k)
      = (coordCube (b.get i : ℕ)).symm (faceEmb g k) := by
    apply (coordCube _).injective
    rw [Equiv.apply_symm_apply]
    exact (coordCube_map_symm (yoneda.map g) k).trans
      (congrArg (fun w => faceEmb w k) (yonedaEquiv_yoneda_map g))
  have hstep : (cotensorLift Coord).map φ ((coordWedge a).invFun ⟨s, k⟩)
      = Cotensor.map Coord (ιᵂ b i) ((coordCube (b.get i : ℕ)).symm (faceEmb g k)) := by
    rw [e1, hfac, ← hinner]
    exact (Cotensor.map_map Coord (yoneda.map g) (ιᵂ b i) _).symm
  change coordWedge b ((cotensorLift Coord).map φ ((coordWedge a).invFun ⟨s, k⟩)) = _
  rw [hstep]
  exact coordWedge_apply_map b i (faceEmb g k)

/-- **The block form of `coordMap`** — the factorization is `blockFace_spec`. -/
theorem coordMap_eq {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) (i : Fin a.length) (k : Fin (a.get i : ℕ)) :
    coordMap φ ⟨i, k⟩ = ⟨blockIdx φ.hom i, faceEmb (blockFace φ.hom i) k⟩ :=
  coordMap_of_factor φ i _ _ (blockFace_spec φ.hom i) k

/-- **The bead a coordinate lands in reads off `coordMap`** — `proj₁ ∘ coordMap` is `blockIdx` of
the source bead. -/
@[simp] theorem coordMap_fst {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b)
    (p : Σ i : Fin a.length, Fin (a.get i : ℕ)) :
    (coordMap φ p).1 = blockIdx φ.hom p.1 := by
  obtain ⟨i, k⟩ := p; rw [coordMap_eq]

/-- **`proj₁ ∘ coordMap` is monotone** — a coordinate's bead index moves monotonically under a
bi-pointed wedge map, being `blockIdx` of the source bead (`serialWedge_blockIdx_monotone`). -/
theorem coordMap_fst_monotone {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b)
    {p q : Σ i : Fin a.length, Fin (a.get i : ℕ)} (h : p.1 ≤ q.1) :
    (coordMap φ p).1 ≤ (coordMap φ q).1 := by
  simp only [coordMap_fst]
  exact serialWedge_blockIdx_monotone φ.hom φ.app_init h

/-! ## The coend map of a wedge map is bijective

Route to `coordMap_bijective`: reduce to the coend map `Cotensor.map Coord φ.hom`, then induct on
the target word `b`.  The cons step splits `φ` at the head bead (`splitWedgeMorphism`) into a
cube-target chain `L` and a wedge-target chain `R`, and the tensorator of the lax-monoidal coend
(`Cotensor.wedge2Equiv`) turns the concatenation into a coproduct `coordFlip L ⊕ coordMap R` —
bijective by the cube base case (`coordLift_map_bijective`) and the inductive hypothesis on the
tail. -/

/-- The coend map of a **cube-target** wedge map is bijective — the base case, from
`coordLift_map_bijective` (each cube coordinate is flipped by exactly one bead). -/
theorem cotensorMap_cube_bijective {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    Function.Bijective (Cotensor.map Coord χ.hom) := by
  have h := coordLift_map_bijective χ
  rwa [cotensorLift_map_eq_coordFlip'] at h

/-- Coend functoriality: bijectivity is closed under composition. -/
theorem cotensorMap_comp_bijective (F : Box ⥤ Type) {X Y Z : PrecubicalSet} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hg : Function.Bijective (Cotensor.map F g)) (hh : Function.Bijective (Cotensor.map F h)) :
    Function.Bijective (Cotensor.map F (g ≫ h)) := by
  rw [Cotensor.map_comp]; exact hh.comp hg

/-- The coend map of an **isomorphism** is bijective (functoriality: two-sided inverse is the coend
map of the inverse iso). -/
theorem cotensorMap_bpIso_bijective (F : Box ⥤ Type) {X Y : BPSet} (e : X ≅ Y) :
    Function.Bijective (Cotensor.map F e.hom.hom) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨Cotensor.map F e.inv.hom, ?_, ?_⟩
  · intro t
    rw [Cotensor.map_map, ← comp_hom, e.hom_inv_id, id_hom]
    exact congrFun (Cotensor.map_id F X.toPsh) t
  · intro t
    rw [Cotensor.map_map, ← comp_hom, e.inv_hom_id, id_hom]
    exact congrFun (Cotensor.map_id F Y.toPsh) t

/-- Monoidality: the coend map of a wedge tensor is the coproduct of the factors' coend maps.
`Cotensor.wedge2Equiv` (the tensorator of the lax-monoidal `cotensorLift F`) conjugates
`Cotensor.map (wedge2MapPsh f g)` to `Sum.map (Cotensor.map f) (Cotensor.map g)`, so it is bijective
iff both factors are. -/
theorem cotensorMap_wedge2MapPsh_bijective (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0))
    {X₁ X₂ Y₁ Y₂ : BPSet} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (hf : Function.Bijective (Cotensor.map F f.hom))
    (hg : Function.Bijective (Cotensor.map F g.hom)) :
    Function.Bijective (Cotensor.map F (wedge2MapPsh f g)) := by
  have hPl : ∀ a, (Cotensor.wedge2Equiv hF X₁ Y₁).symm (Sum.inl a)
      = Cotensor.map F (wedgeInl X₁ Y₁) a := fun a =>
    (Equiv.symm_apply_eq _).mpr (Cotensor.wedge2Equiv_map_inl hF X₁ Y₁ a).symm
  have hPr : ∀ b, (Cotensor.wedge2Equiv hF X₁ Y₁).symm (Sum.inr b)
      = Cotensor.map F (wedgeInr X₁ Y₁) b := fun b =>
    (Equiv.symm_apply_eq _).mpr (Cotensor.wedge2Equiv_map_inr hF X₁ Y₁ b).symm
  have hQl : ∀ a, (Cotensor.wedge2Equiv hF X₂ Y₂).symm (Sum.inl a)
      = Cotensor.map F (wedgeInl X₂ Y₂) a := fun a =>
    (Equiv.symm_apply_eq _).mpr (Cotensor.wedge2Equiv_map_inl hF X₂ Y₂ a).symm
  have hQr : ∀ b, (Cotensor.wedge2Equiv hF X₂ Y₂).symm (Sum.inr b)
      = Cotensor.map F (wedgeInr X₂ Y₂) b := fun b =>
    (Equiv.symm_apply_eq _).mpr (Cotensor.wedge2Equiv_map_inr hF X₂ Y₂ b).symm
  have hconj : Cotensor.map F (wedge2MapPsh f g)
      = ⇑(Cotensor.wedge2Equiv hF X₂ Y₂).symm
        ∘ Sum.map (Cotensor.map F f.hom) (Cotensor.map F g.hom)
        ∘ ⇑(Cotensor.wedge2Equiv hF X₁ Y₁) := by
    funext t
    simp only [Function.comp_apply]
    rcases hs : Cotensor.wedge2Equiv hF X₁ Y₁ t with a | b
    · have ht : t = Cotensor.map F (wedgeInl X₁ Y₁) a := by
        rw [← hPl, ← hs, Equiv.symm_apply_apply]
      rw [ht, Cotensor.map_map, wedge2MapPsh_inl, ← Cotensor.map_map, Sum.map_inl, hQl]
    · have ht : t = Cotensor.map F (wedgeInr X₁ Y₁) b := by
        rw [← hPr, ← hs, Equiv.symm_apply_apply]
      rw [ht, Cotensor.map_map, wedge2MapPsh_inr, ← Cotensor.map_map, Sum.map_inr, hQr]
  rw [hconj]
  exact (Cotensor.wedge2Equiv hF X₂ Y₂).symm.bijective.comp
    ((Function.Bijective.sumMap hf hg).comp (Cotensor.wedge2Equiv hF X₁ Y₁).bijective)

/-- **The coend map of any wedge map is bijective.**  Induction on `b`: `[]` is the cube case
(`⋁[] = □0`); the cons step splits at the head bead and uses monoidality
(`cotensorMap_wedge2MapPsh_bijective`) with the cube base (`cotensorMap_cube_bijective`, the head)
and the inductive hypothesis (the tail). -/
theorem cotensorMap_wedge_bijective (b : List ℕ+) :
    ∀ {a : List ℕ+} (φ : ⋁a ⟶ ⋁b), Function.Bijective (Cotensor.map Coord φ.hom) := by
  induction b with
  | nil => intro a φ; exact cotensorMap_cube_bijective φ
  | cons c rest ih =>
      intro a φ
      obtain ⟨L, R, heq, hφ⟩ := splitWedgeMorphism
        (wedge2_admitsAltitude (cube_admitsAltitude (c : ℕ)) (serialWedge_admitsAltitude rest)) a φ
      have hR : Function.Bijective (Cotensor.map Coord R.map.hom) := ih R.map
      have hL : Function.Bijective (Cotensor.map Coord L.map.hom) :=
        cotensorMap_cube_bijective L.map
      have hφhom : φ.hom
          = (eqToHom (congrArg BPSet.serialWedge heq)).hom
            ≫ (concatChainMap (□(c : ℕ)) (⋁rest) L R).hom := by
        rw [← comp_hom]; exact congrArg BPSet.Hom.hom hφ
      rw [hφhom]
      refine cotensorMap_comp_bijective Coord _ _
        (cotensorMap_bpIso_bijective Coord (eqToIso (congrArg BPSet.serialWedge heq))) ?_
      rw [concatChainMap_hom]
      exact cotensorMap_comp_bijective Coord _ _
        (cotensorMap_bpIso_bijective Coord (serialWedgeAppend L.dims R.dims).symm)
        (cotensorMap_wedge2MapPsh_bijective Coord inferInstance L.map R.map hL hR)

/-- **The wedge coordinate map is bijective.**  `coordMap φ` is `Cotensor.map Coord φ.hom` read
through the `coordWedge` equivalences, so it inherits the coend map's bijectivity. -/
theorem coordMap_bijective {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) :
    Function.Bijective (coordMap φ) := by
  have hfun : ⇑((cotensorLift Coord).map φ) = Cotensor.map Coord φ.hom :=
    funext (fun x => cotensorLift_map_apply Coord φ x)
  have hmid : Function.Bijective ⇑((cotensorLift Coord).map φ) := by
    rw [hfun]; exact cotensorMap_wedge_bijective b φ
  exact (coordWedge b).bijective.comp (hmid.comp (coordWedge a).symm.bijective)

/-- The wedge coordinate map as an `Equiv`, with `_apply = rfl`.  Computable: the inverse is the
`Fintype.bijInv` of the coend bijection, not `Equiv.ofBijective`'s choice. -/
def coordMapEquiv {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b) :
    (Σ i : Fin a.length, Fin (a.get i : ℕ)) ≃ Σ j : Fin b.length, Fin (b.get j : ℕ) where
  toFun := coordMap φ
  invFun := Fintype.bijInv (coordMap_bijective φ)
  left_inv := Fintype.leftInverse_bijInv (coordMap_bijective φ)
  right_inv := Fintype.rightInverse_bijInv (coordMap_bijective φ)

@[simp] theorem coordMapEquiv_apply {a b : List ℕ+} (φ : ⋁a ⟶ ⋁b)
    (p : Σ i : Fin a.length, Fin (a.get i : ℕ)) : coordMapEquiv φ p = coordMap φ p := rfl

/-! ## The event flattening `pos`

`finSigmaFinEquiv : (Σ i, Fin (n i)) ≃ Fin (∑ n)` is the monotone enumeration of the lex order on
events: an earlier bead flattens strictly below a later one, and inside a bead the flattening is
the coordinate order. -/

/-- Prefix sums of a `Fin m`-indexed family are monotone in the cut point. -/
private theorem sum_castLE_mono {m : ℕ} (n : Fin m → ℕ) {s t : ℕ} (hs : s ≤ m) (ht : t ≤ m)
    (hst : s ≤ t) : ∑ i : Fin s, n (Fin.castLE hs i) ≤ ∑ i : Fin t, n (Fin.castLE ht i) := by
  have hval : ∀ (u : ℕ) (hu : u ≤ m), (∑ i : Fin u, n (Fin.castLE hu i))
      = ∑ x ∈ Finset.range u, (if h : x < m then n ⟨x, h⟩ else 0) := by
    intro u hu
    rw [← Fin.sum_univ_eq_sum_range (fun x => if h : x < m then n ⟨x, h⟩ else 0) u]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos (lt_of_lt_of_le j.2 hu)]
    rfl
  rw [hval s hs, hval t ht]
  exact Finset.sum_le_sum_of_subset fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hst)

/-- **`finSigmaFinEquiv` respects the block order.**  If `p`'s block precedes `q`'s, its whole block
flattens strictly below `q`. -/
theorem finSigmaFinEquiv_lt_of_fst_lt {m : ℕ} {n : Fin m → ℕ}
    {p q : (i : Fin m) × Fin (n i)} (h : (p.1 : ℕ) < (q.1 : ℕ)) :
    finSigmaFinEquiv p < finSigmaFinEquiv q := by
  rw [Fin.lt_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply]
  have hstep : (∑ i : Fin (p.1 : ℕ), n (Fin.castLE p.1.2.le i)) + n p.1
      ≤ ∑ i : Fin (q.1 : ℕ), n (Fin.castLE q.1.2.le i) := by
    have hle := sum_castLE_mono n (s := (p.1 : ℕ) + 1) (t := (q.1 : ℕ)) p.1.2 q.1.2.le (by omega)
    refine le_trans (le_of_eq ?_) hle
    rw [Fin.sum_univ_castSucc]
    exact congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun j _ => congrArg n (Fin.ext rfl)) (congrArg n (Fin.ext rfl))
  have hk := p.2.isLt
  omega

/-- **`finSigmaFinEquiv` is the coordinate order inside a block.** -/
theorem finSigmaFinEquiv_lt_iff_of_fst_eq {m : ℕ} {n : Fin m → ℕ} {i : Fin m} {k k' : Fin (n i)} :
    finSigmaFinEquiv ⟨i, k⟩ < finSigmaFinEquiv ⟨i, k'⟩ ↔ k < k' := by
  rw [Fin.lt_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply, Fin.lt_def]
  exact Nat.add_lt_add_iff_left

/-- The canonical, run-free event order: flatten the beads lexicographically. -/
def pos {dims : List ℕ+} : beadEvent dims ≃ Fin (∑ i : Fin dims.length, (dims.get i : ℕ)) :=
  finSigmaFinEquiv

/-- Earlier bead ⇒ earlier in the flattening. -/
theorem pos_lt_of_fst_lt {dims : List ℕ+} {e e' : beadEvent dims} (h : (e.1 : ℕ) < e'.1) :
    pos e < pos e' :=
  finSigmaFinEquiv_lt_of_fst_lt h

/-- Inside a bead, the flattening is the coordinate order. -/
theorem pos_lt_iff_of_fst_eq {dims : List ℕ+} {i : Fin dims.length} {k k' : Fin (dims.get i : ℕ)} :
    pos (⟨i, k⟩ : beadEvent dims) < pos ⟨i, k'⟩ ↔ k < k' :=
  finSigmaFinEquiv_lt_iff_of_fst_eq

/-- The flattening reflects the bead order: an earlier event sits in a bead no later. -/
theorem fst_le_of_pos_lt {dims : List ℕ+} {e e' : beadEvent dims} (h : pos e < pos e') :
    (e.1 : ℕ) ≤ e'.1 :=
  le_of_not_gt fun hc => absurd (pos_lt_of_fst_lt hc) (asymm h)

/-! ### The event order

The lexicographic order on events, with `pos` as its monotone enumeration: `pos_lt_of_fst_lt` and
`pos_lt_iff_of_fst_eq` are its two clauses.  `pos` is then the *unique* monotone bijection, which is
what makes "monotone" a definition rather than a condition (`pos_eq_of_monotone`). -/

/-- The lexicographic event order: bead first, coordinate inside a bead. -/
instance beadOrder (dims : List ℕ+) : LinearOrder (beadEvent dims) :=
  LinearOrder.lift' pos pos.injective

theorem le_iff_pos {dims : List ℕ+} {e e' : beadEvent dims} : e ≤ e' ↔ pos e ≤ pos e' := Iff.rfl

theorem lt_iff_pos {dims : List ℕ+} {e e' : beadEvent dims} : e < e' ↔ pos e < pos e' := Iff.rfl

/-- A bijection of events forces the two flattenings to have the same length. -/
theorem sum_get_eq_of_bijective {a b : List ℕ+} {f : beadEvent a → beadEvent b}
    (hf : Function.Bijective f) :
    (∑ i : Fin a.length, (a.get i : ℕ)) = ∑ j : Fin b.length, (b.get j : ℕ) := by
  have h := Fintype.card_of_bijective hf
  rwa [Fintype.card_congr (pos (dims := a)), Fintype.card_congr (pos (dims := b)),
    Fintype.card_fin, Fintype.card_fin] at h

/-- **There is at most one monotone bijection of events**: conjugated by `pos` it is a monotone
permutation of `Fin N`, hence the identity, so it preserves the flattening. -/
theorem pos_eq_of_monotone {a b : List ℕ+} {f : beadEvent a → beadEvent b} (hm : Monotone f)
    (hf : Function.Bijective f) (e : beadEvent a) : (pos (f e) : ℕ) = (pos e : ℕ) := by
  have hsum := sum_get_eq_of_bijective hf
  set σ : Equiv.Perm (Fin (∑ i : Fin a.length, (a.get i : ℕ))) :=
    pos.symm.trans ((Equiv.ofBijective f hf).trans (pos.trans (finCongr hsum.symm))) with hσ
  have hmono : Monotone σ := fun x y hxy =>
    hm (le_iff_pos.mpr (by rwa [pos.apply_symm_apply, pos.apply_symm_apply]))
  have h1 : (σ (pos e) : ℕ) = (pos e : ℕ) :=
    congrArg Fin.val (Equiv.ext_iff.mp (Equiv.Perm.eq_one_of_monotone hmono) (pos e))
  simpa [hσ, pos.symm_apply_apply] using h1

/-! ### `pos` as bead start plus offset -/

/-- `beadStart` in the `Fin`-indexed shape `finSigmaFinEquiv_apply` produces. -/
theorem beadStart_eq_sum (dims : List ℕ+) :
    ∀ (i : ℕ) (h : i ≤ dims.length),
      beadStart dims i = ∑ u : Fin i, ((dims.get (u.castLE h)) : ℕ)
  | 0, _ => by simp
  | i + 1, h => by
      rw [beadStart_succ dims ⟨i, h⟩, beadStart_eq_sum dims i (Nat.le_of_succ_le h),
        Fin.sum_univ_castSucc]
      rfl

/-- `pos` is `beadStart` plus the within-bead offset. -/
theorem pos_val {dims : List ℕ+} (e : beadEvent dims) :
    (pos e : ℕ) = beadStart dims e.1 + (e.2 : ℕ) := by
  rw [beadStart_eq_sum dims e.1 e.1.2.le]
  exact finSigmaFinEquiv_apply e

theorem pos_mk {dims : List ℕ+} (i : Fin dims.length) (x : Fin ((dims.get i : ℕ))) :
    (pos (⟨i, x⟩ : beadEvent dims) : ℕ) = beadStart dims i + (x : ℕ) :=
  pos_val ⟨i, x⟩

theorem pos_cons_zero (c : ℕ+) (rest : List ℕ+) (x : Fin (((c :: rest).get 0 : ℕ))) :
    (pos (⟨0, x⟩ : beadEvent (c :: rest)) : ℕ) = (x : ℕ) := by
  simpa using pos_mk (dims := c :: rest) 0 x

theorem pos_cons_succ (c : ℕ+) (rest : List ℕ+) (j : Fin rest.length)
    (x : Fin (((c :: rest).get j.succ : ℕ))) :
    (pos (⟨j.succ, x⟩ : beadEvent (c :: rest)) : ℕ)
      = (c : ℕ) + (pos (⟨j, x⟩ : beadEvent rest) : ℕ) := by
  rw [pos_mk, pos_mk, Fin.val_succ, beadStart_cons_succ]
  exact Nat.add_assoc _ _ _

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

/-! ## The coordinate map is monoidal over `++`

A wedge map of appended words that restricts along the half-inclusions `wedgeInclL`/`wedgeInclR`
moves each block's coordinates by the corresponding restriction: `coordMap` is a map of
coproducts.  The half-inclusion square is the only input, so `chConcat`'s tensorator inherits it
from `concatHomφ_inclL`/`_inclR`. -/

/-- **Left block.**  A wedge map restricting to `ψ` on the first block moves that block's
coordinates by `coordMap ψ`. -/
theorem coordMap_inclL {a b a' b' : List ℕ+} (Φ : ⋁(a ++ b) ⟶ ⋁(a' ++ b')) {ψ : ⋁a ⟶ ⋁a'}
    (h : wedgeInclL a b ≫ Φ.hom = ψ.hom ≫ wedgeInclL a' b') (e : beadEvent a) :
    coordMap Φ (eventInl a b e) = eventInl a' b' (coordMap ψ e) := by
  obtain ⟨i, k⟩ := e
  obtain ⟨e₁, he₁, hfac₁⟩ := ι_appendL b a i (eventInl a b ⟨i, k⟩).1 rfl
  obtain ⟨e₂, he₂, hfac₂⟩ := ι_appendL b' a' (blockIdx ψ.hom i)
    (eventInl a' b' (coordMap ψ ⟨i, k⟩)).1 (congrArg Fin.val (coordMap_fst ψ ⟨i, k⟩))
  have hfac₂' : ιᵂ a' (blockIdx ψ.hom i) ≫ wedgeInclL a' b'
      = yoneda.map e₂.inv ≫ ιᵂ (a' ++ b') (eventInl a' b' (coordMap ψ ⟨i, k⟩)).1 := by
    rw [hfac₂]
    exact ((yoneda.mapIso e₂).inv_hom_id_assoc _).symm
  have step1 : ιᵂ (a ++ b) (eventInl a b ⟨i, k⟩).1 ≫ Φ.hom
      = yoneda.map e₁.hom ≫ (ιᵂ a i ≫ ψ.hom) ≫ wedgeInclL a' b' := by
    rw [hfac₁]
    refine (Category.assoc _ _ _).trans (congrArg (fun t => yoneda.map e₁.hom ≫ t) ?_)
    refine (Category.assoc _ _ _).trans ?_
    rw [h]
    exact (Category.assoc _ _ _).symm
  have step2 : yoneda.map (e₁.hom ≫ blockFace ψ.hom i ≫ e₂.inv)
        ≫ ιᵂ (a' ++ b') (eventInl a' b' (coordMap ψ ⟨i, k⟩)).1
      = yoneda.map e₁.hom ≫ (yoneda.map (blockFace ψ.hom i) ≫ ιᵂ a' (blockIdx ψ.hom i))
          ≫ wedgeInclL a' b' := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    refine (Category.assoc _ _ _).trans (congrArg (fun t => yoneda.map e₁.hom ≫ t) ?_)
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun t => yoneda.map (blockFace ψ.hom i) ≫ t) hfac₂'.symm).trans
      (Category.assoc _ _ _).symm
  rw [coordMap_of_factor Φ (eventInl a b ⟨i, k⟩).1 (eventInl a' b' (coordMap ψ ⟨i, k⟩)).1
    (e₁.hom ≫ blockFace ψ.hom i ≫ e₂.inv)
    ((step1.trans (congrArg (fun t => yoneda.map e₁.hom ≫ t ≫ wedgeInclL a' b')
      (blockFace_spec ψ.hom i))).trans step2.symm) (eventInl a b ⟨i, k⟩).2]
  refine congrArg (fun z => (⟨_, z⟩ : beadEvent (a' ++ b'))) (Fin.ext ?_)
  rw [faceEmb_comp, faceEmb_comp, faceEmb_iso_inv_val e₂ he₂,
    show faceEmb e₁.hom (eventInl a b ⟨i, k⟩).2 = k from Fin.ext (he₁ _),
    Fin.val_cast, coordMap_eq]

/-- **Right block.**  A wedge map restricting to `ψ` on the second block moves that block's
coordinates by `coordMap ψ`. -/
theorem coordMap_inclR {a b a' b' : List ℕ+} (Φ : ⋁(a ++ b) ⟶ ⋁(a' ++ b')) {ψ : ⋁b ⟶ ⋁b'}
    (h : wedgeInclR a b ≫ Φ.hom = ψ.hom ≫ wedgeInclR a' b') (e : beadEvent b) :
    coordMap Φ (eventInr a b e) = eventInr a' b' (coordMap ψ e) := by
  obtain ⟨j, k⟩ := e
  obtain ⟨e₁, he₁, hfac₁⟩ := ι_appendR b a j (eventInr a b ⟨j, k⟩).1 rfl
  obtain ⟨e₂, he₂, hfac₂⟩ := ι_appendR b' a' (blockIdx ψ.hom j)
    (eventInr a' b' (coordMap ψ ⟨j, k⟩)).1
    (congrArg (fun z : Fin b'.length => a'.length + (z : ℕ)) (coordMap_fst ψ ⟨j, k⟩))
  have hfac₂' : ιᵂ b' (blockIdx ψ.hom j) ≫ wedgeInclR a' b'
      = yoneda.map e₂.inv ≫ ιᵂ (a' ++ b') (eventInr a' b' (coordMap ψ ⟨j, k⟩)).1 := by
    rw [hfac₂]
    exact ((yoneda.mapIso e₂).inv_hom_id_assoc _).symm
  have step1 : ιᵂ (a ++ b) (eventInr a b ⟨j, k⟩).1 ≫ Φ.hom
      = yoneda.map e₁.hom ≫ (ιᵂ b j ≫ ψ.hom) ≫ wedgeInclR a' b' := by
    rw [hfac₁]
    refine (Category.assoc _ _ _).trans (congrArg (fun t => yoneda.map e₁.hom ≫ t) ?_)
    refine (Category.assoc _ _ _).trans ?_
    rw [h]
    exact (Category.assoc _ _ _).symm
  have step2 : yoneda.map (e₁.hom ≫ blockFace ψ.hom j ≫ e₂.inv)
        ≫ ιᵂ (a' ++ b') (eventInr a' b' (coordMap ψ ⟨j, k⟩)).1
      = yoneda.map e₁.hom ≫ (yoneda.map (blockFace ψ.hom j) ≫ ιᵂ b' (blockIdx ψ.hom j))
          ≫ wedgeInclR a' b' := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    refine (Category.assoc _ _ _).trans (congrArg (fun t => yoneda.map e₁.hom ≫ t) ?_)
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun t => yoneda.map (blockFace ψ.hom j) ≫ t) hfac₂'.symm).trans
      (Category.assoc _ _ _).symm
  rw [coordMap_of_factor Φ (eventInr a b ⟨j, k⟩).1 (eventInr a' b' (coordMap ψ ⟨j, k⟩)).1
    (e₁.hom ≫ blockFace ψ.hom j ≫ e₂.inv)
    ((step1.trans (congrArg (fun t => yoneda.map e₁.hom ≫ t ≫ wedgeInclR a' b')
      (blockFace_spec ψ.hom j))).trans step2.symm) (eventInr a b ⟨j, k⟩).2]
  refine congrArg (fun z => (⟨_, z⟩ : beadEvent (a' ++ b'))) (Fin.ext ?_)
  rw [faceEmb_comp, faceEmb_comp, faceEmb_iso_inv_val e₂ he₂,
    show faceEmb e₁.hom (eventInr a b ⟨j, k⟩).2 = k from Fin.ext (he₁ _),
    Fin.val_cast, coordMap_eq]

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
