import CubeChains.Chains.BlockDecomp
import CubeChains.Chains.WedgeExtend
import CubeChains.Chains.CubeVtx
import CubeChains.Chains.ChainSkeletal
import CubeChains.Chains.Segal
import CubeChains.Foundations.Reachability

/-!
# Chains/CoordFunctor — the coordinate copresheaf `▫n ↦ Fin n`

A cube face `g : ▫n ⟶ ▫m` acts on coordinates by its free-coordinate embedding `faceEmb g :
Fin n ↪ Fin m`.  It is **empty at `▫0`**, so its cubical coend `cotensorLift Coord`
(`Chains/WedgeExtend`) sends a serial wedge to the *coproduct* of its beads' coordinate sets — the
ordered partition of the coordinates a cube chain realises (`coordWedge`), and a cube to its own
coordinate set (`coordCube`).
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

/-- The coordinate `k` of `□m`, as a coend class. -/
theorem coordCube_symm_apply (m : ℕ) (k : Fin m) :
    (coordCube m).symm k = Cotensor.mk Coord m (𝟙 ▫m) k := rfl

/-- **Reading a decorated cube cell**: the coend collapses to the free-coordinate embedding of the
cell.  `coordCube` sends `⟨x, k⟩` to the coordinate `x` sends `k`. -/
theorem coordCube_mk {b m : ℕ} (x : (□b).cells m) (k : Fin m) :
    coordCube b (Cotensor.mk Coord m x k) = faceEmb x k := rfl

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
(`coord_beads_disjoint`), so this map is injective for *any* presheaf `f` (`coord_map_injective`);
the "once true stays true" vertex induction (`coord_stays_true`, read through `cubeVtx`) is the
engine.  For a bi-pointed `χ` the count `dimSum a = m` upgrades injectivity to a bijection
(`coordLift_map_bijective`). -/

/-- Bead `i`'s image face in `□m`: the `Box` hom `▫(aᵢ) ⟶ ▫m` the bead inclusion `ιᵂ a i ≫ f`
Yoneda-classifies (`□m` representable). -/
def beadFace {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) (i : Fin a.length) :
    ▫((a.get i : ℕ)) ⟶ ▫m := yonedaEquiv (ιᵂ a i ≫ f)

/-- The coordinate coend map `Coord↓(f)` of a serial-wedge map into a cube. -/
abbrev coordFlip {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
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

/-- The `⊥`-vertex vector reads a cell coordinatewise: free coords `false`, fixed coords their
value. -/
theorem cubeVtxOfCell_bot {m k : ℕ} (b : Cell m k) (q : Fin m) :
    cubeVtxOfCell b (fun _ => false) q = (b.val q).getD false := by
  rw [cubeVtxOfCell_apply]
  by_cases h : q ∈ noneSet b.val
  · rw [dif_pos h, mem_noneSet.mp h]; rfl
  · rw [dif_neg h]

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

/-- The junction vertex of `□c ∨ ⋁rest`: bead `0`'s final vertex glues to the tail's initial. -/
theorem serialWedge_junction (c : ℕ+) (rest : List ℕ+) :
    (Glue.inl (□(c : ℕ)).finalVertex (⋁rest).initVertex)⟪0⟫ (□(c : ℕ)).final
      = (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex)⟪0⟫ (⋁rest).init := by
  have hf : yonedaEquiv ((□(c : ℕ)).finalVertex) = (□(c : ℕ)).final :=
    Equiv.apply_symm_apply yonedaEquiv (□(c : ℕ)).final
  have hi : yonedaEquiv ((⋁rest).initVertex) = (⋁rest).init :=
    Equiv.apply_symm_apply yonedaEquiv (⋁rest).init
  have hcond := congrArg yonedaEquiv (Glue.condition (□(c : ℕ)).finalVertex (⋁rest).initVertex)
  rw [yonedaEquiv_comp, yonedaEquiv_comp, hf, hi] at hcond
  exact hcond

/-- Bead `s`'s bottom vertex, as a `0`-cell of `⋁a`. -/
def beadBot (a : List ℕ+) (s : Fin a.length) : (⋁a).toPsh.cells 0 :=
  (ιᵂ a s)⟪0⟫ ((□(a.get s : ℕ)).init)

/-- Bead `s`'s top vertex, as a `0`-cell of `⋁a`. -/
def beadTop (a : List ℕ+) (s : Fin a.length) : (⋁a).toPsh.cells 0 :=
  (ιᵂ a s)⟪0⟫ ((□(a.get s : ℕ)).final)

/-- Peeling the head: bead `s.succ` of `c :: rest` is bead `s` of `rest`, right-included. -/
theorem beadBot_succ (c : ℕ+) (rest : List ℕ+) (s : Fin rest.length) :
    beadBot (c :: rest) s.succ
      = (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex)⟪0⟫ (beadBot rest s) :=
  (comp_app_cell (f := ιᵂ rest s)
    (g := Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex)
    (h := ιᵂ (c :: rest) s.succ) rfl 0 ((□(rest.get s : ℕ)).init)).symm

theorem beadTop_succ (c : ℕ+) (rest : List ℕ+) (s : Fin rest.length) :
    beadTop (c :: rest) s.succ
      = (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex)⟪0⟫ (beadTop rest s) :=
  (comp_app_cell (f := ιᵂ rest s)
    (g := Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex)
    (h := ιᵂ (c :: rest) s.succ) rfl 0 ((□(rest.get s : ℕ)).final)).symm

/-- Bead `0`'s bottom vertex is the wedge's initial vertex. -/
theorem beadBot_zero (a : List ℕ+) (h : 0 < a.length) : beadBot a ⟨0, h⟩ = (⋁a).init := by
  cases a with
  | nil => exact absurd h (by simp)
  | cons c rest => rfl

/-- **The one wedge-structural recursion of the spine.**  Consecutive beads meet at a junction:
bead `s`'s top is bead `t = s+1`'s bottom.  Head junction is `serialWedge_junction`; tail junctions
map down the right inclusion. -/
theorem junction_eq : ∀ (a : List ℕ+) (s t : Fin a.length), (t : ℕ) = (s : ℕ) + 1 →
    beadTop a s = beadBot a t
  | [], s, _, _ => s.elim0
  | c :: rest, s, t, h => by
      rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t', rfl⟩
      · exfalso; simp only [Fin.val_zero] at h; omega
      · rw [beadBot_succ]
        rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
        · rw [show t' = (⟨0, t'.pos⟩ : Fin rest.length) from
              Fin.ext (by simp only [Fin.val_succ, Fin.val_zero] at h ⊢; omega), beadBot_zero]
          exact serialWedge_junction c rest
        · rw [beadTop_succ]
          exact congrArg (fun v => (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex)⟪0⟫ v)
            (junction_eq rest s' t' (by simp only [Fin.val_succ] at h; omega))

/-- Bead `s`'s bottom reaches bead `t = s+k`'s bottom — the generic fold of the junction adjacency,
by recursion on the gap `k` (no wedge structure). -/
theorem beadBot_reaches_up (a : List ℕ+) (s : Fin a.length) :
    ∀ (k : ℕ) (t : Fin a.length), (t : ℕ) = (s : ℕ) + k →
      VertexReaches (⋁a).toPsh (beadBot a s) (beadBot a t)
  | 0, t, ht => by rw [show t = s from Fin.ext (by omega)]; exact Reaches.refl _
  | k + 1, t, ht => by
      have hk : s.val + k < a.length := by have := t.isLt; omega
      refine Reaches.trans (beadBot_reaches_up a s k ⟨s.val + k, hk⟩ rfl) ?_
      rw [← junction_eq a ⟨s.val + k, hk⟩ t (by show (t : ℕ) = (s.val + k) + 1; omega)]
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
  exact beadBot_reaches_beadBot a ⟨s.val + 1, hsucc⟩ t (by show s.val + 1 ≤ (t : ℕ); omega)

/-- **The wedge spine:** the initial vertex reaches every bead's bottom vertex.  Now a corollary of
`beadBot_reaches_beadBot` (bead `0` = the initial vertex). -/
theorem init_reaches_beadBot (a : List ℕ+) (j : Fin a.length) :
    VertexReaches (⋁a).toPsh (⋁a).init ((ιᵂ a j)⟪0⟫ (□(a.get j : ℕ)).init) := by
  rw [show (⋁a).init = beadBot a ⟨0, j.pos⟩ from (beadBot_zero a j.pos).symm]
  exact beadBot_reaches_beadBot a ⟨0, j.pos⟩ j (Nat.zero_le _)

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
        fun j => congrArg (fun w => Set.range (faceEmb w)) (congrArg yonedaEquiv
          (Category.assoc (ιᵂ rest j) (Glue.inr (□(c : ℕ)).finalVertex (⋁rest).initVertex) f))
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
    coordCube m (coordFlip f ((coordWedge a).symm ⟨i, k⟩)) = faceEmb (beadFace f i) k := by
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

/-- `coordFlip f` conjugated by the coordinate equivs is the bead-flip sigma-map. -/
theorem coordFlip_eq {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
    coordFlip f
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

/-- **Injectivity of the coend map, for a general presheaf map** — no base-point hypothesis. -/
theorem coordFlip_injective {a : List ℕ+} {m : ℕ} (f : (⋁a).toPsh ⟶ (□m).toPsh) :
    Function.Injective (coordFlip f) := by
  rw [coordFlip_eq f]
  exact (coordCube m).symm.injective.comp
    ((coord_sigma_injective f).comp (coordWedge a).injective)

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

`(cotensorLift Coord).map χ` is `coordFlip χ.hom` (`cotensorLift_map_apply`), which conjugates to
the bead-flip sigma-map — bijective by disjointness + the dimension count. -/

/-- The coend map underlying `(cotensorLift Coord).map χ` is `coordFlip χ.hom`. -/
theorem cotensorLift_map_eq_coordFlip {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    ⇑((cotensorLift Coord).map χ) = coordFlip χ.hom := by
  funext t; exact cotensorLift_map_apply Coord χ t

/-- **The coend map is bijective** — each coordinate of `□m` is flipped by exactly one bead. -/
theorem coordLift_map_bijective {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    Function.Bijective ((cotensorLift Coord).map χ) := by
  rw [cotensorLift_map_eq_coordFlip χ, coordFlip_eq χ.hom]
  exact (coordCube m).symm.bijective.comp
    ((coord_sigma_bijective χ).comp (coordWedge a).bijective)

theorem coordLift_map_injective {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    Function.Injective ((cotensorLift Coord).map χ) :=
  (coordLift_map_bijective χ).injective

theorem coordLift_map_surjective {a : List ℕ+} {m : ℕ} (χ : ⋁a ⟶ □m) :
    Function.Surjective ((cotensorLift Coord).map χ) :=
  (coordLift_map_bijective χ).surjective

end CubeChains
