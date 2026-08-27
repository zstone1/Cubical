import CubeChains.Chains.Category
import CubeChains.Chains.WedgeMap
import CubeChains.Chains.CubeNonSelfLinked
import CubeChains.Chains.SegalAltitude
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Chains/BlockDecomp — block decomposition of a serial-wedge map

For a bi-pointed wedge map `φ : ⋁ad ⟶ ⋁cd`, each source bead `i` factors through a
unique target block `blockIdx φ i` via a `Box`-face `blockFace φ i`; `faceEmb` reads off that
face's free coordinates as an order embedding.  This is pure cube-chain data — shared by the
run presheaf (`Lines`) and the `Ch(K)`-skeletality proof.

Where that block sits is `serialWedge_beadStart_blockIdx`, whence `blockIdx` is monotone
(`serialWedge_blockIdx_monotone`) and `∑ ad = ∑ cd` (`serialWedge_dimSum_eq`).
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChain

/-- The `Fin`-indexed sum over a list's entries is the sum of the mapped list. -/
theorem sum_get_eq_sum_map {α : Type*} {M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    ∑ i : Fin l.length, g (l.get i) = (l.map g).sum := by
  rw [← List.sum_ofFn (f := fun i => g (l.get i)), List.ofFn_comp', List.ofFn_get]

/-! ### Block data of a wedge map

`serialWedgeCell` reads a positive cell of `⋁dims` off the `Glue` `Quot`: the block it lies in,
and the face of that block's cube it is (`serialWedgeCell_spec`).  `blockIdx`/`blockFace` are its
two projections at the source-bead restriction `ι_i ≫ φ`, so a wedge map's block data is genuinely
computable (no `.choose`).  `blockFace`'s codomain matches `blockIdx φ i` with no cast: it *is* the
cube-face projection, whose type reduces to `▫(ad.get i) ⟶ ▫(cd.get (blockIdx φ i))`. -/

-- The block a positive cell of `⋁dims` lies in, together with the face of that block's cube it is,
-- read off the `Glue` `Quot`.
unseal Glue.gluePsh Glue.inl Glue.inr in
def serialWedgeCell : (dims : List ℕ+) → {m : ℕ} → 1 ≤ m → (⋁dims).cells m →
    Σ i : Fin dims.length, (□((dims.get i) : ℕ)).cells m
  | [], _, hm, c => ((cube0_cells_isEmpty hm).false c).elim
  | _ :: rest, m, hm, c =>
      Quot.lift
        (fun x => match x with
          | Sum.inl a => ⟨0, a⟩
          | Sum.inr b => let r := serialWedgeCell rest hm b; ⟨r.1.succ, r.2⟩)
        (by intro _ _ r; obtain ⟨s⟩ := r
            exact ((cube0_cells_isEmpty hm).false s).elim)
        c

theorem serialWedgeCell_zero {n : ℕ+} {rest : List ℕ+} {m : ℕ} (hm : 1 ≤ m)
    (x : (□(n : ℕ)).cells m) :
    serialWedgeCell (n :: rest) hm
        ((Glue.inl (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ x)
      = ⟨0, x⟩ := by
  show serialWedgeCell (n :: rest) hm ((Glue.inl _ _).app (op ▫m) x) = ⟨0, x⟩
  rw [Glue.inl_app]; rfl

theorem serialWedgeCell_succ {n : ℕ+} {rest : List ℕ+} {m : ℕ} (hm : 1 ≤ m)
    (y : (⋁rest).cells m) :
    serialWedgeCell (n :: rest) hm
        ((Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫ y)
      = ⟨(serialWedgeCell rest hm y).1.succ, (serialWedgeCell rest hm y).2⟩ := by
  show serialWedgeCell (n :: rest) hm ((Glue.inr _ _).app (op ▫m) y) = _
  rw [Glue.inr_app]; rfl

/-- **`serialWedgeCell` is a genuine decomposition**: the reported face of the reported block
recovers the cell. -/
theorem serialWedgeCell_spec :
    ∀ (dims : List ℕ+) {m : ℕ} (hm : 1 ≤ m) (c : (⋁dims).cells m),
      (ιᵂ dims (serialWedgeCell dims hm c).1)⟪m⟫ (serialWedgeCell dims hm c).2 = c
  | [], _, hm, c => ((cube0_cells_isEmpty hm).false c).elim
  | n :: rest, m, hm, c => by
      rcases wedge2_cell_cases (□(n : ℕ)) (⋁rest) m c with ⟨x, hx⟩ | ⟨y, hy⟩
      · rw [← hx, serialWedgeCell_zero]
        exact serialWedge_ι_zero_app n rest x
      · rw [← hy, serialWedgeCell_succ,
          serialWedge_ι_succ_app n rest (serialWedgeCell rest hm y).1
            (serialWedgeCell rest hm y).2]
        exact congrArg
          ((Glue.inr (□(n : ℕ)).finalVertex (⋁rest).initVertex)⟪m⟫)
          (serialWedgeCell_spec rest hm y)

/-- The **target block index** of source bead `i` under a wedge map `φ`: the `cd`-block that the
restriction `ι_i ≫ φ` factors through. -/
def blockIdx {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    Fin cd.length :=
  (serialWedgeCell cd (ad.get i).pos (beadCell φ i)).1

/-- The **face inclusion** of source bead `i` under a wedge map `φ`: the `Box`
morphism `□^{ad.get i} ⟶ □^{cd.get (blockIdx φ i)}` witnessing that `ι_i ≫ φ` lands
in a face of the target block. -/
def blockFace {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ▫((ad.get i) : ℕ) ⟶ ▫((cd.get (blockIdx φ i)) : ℕ) :=
  (serialWedgeCell cd (ad.get i).pos (beadCell φ i)).2

/-- Defining factorization of the block data (`r := blockIdx φ i`):

      □^{ad.get i}  --ι_i-->  □^∨(ad)
           |                     |
   blockFace φ i                 φ
           v                     v
      □^{cd.get r}  --ι_r-->  □^∨(cd)
-/
theorem blockFace_spec {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ιᵂ ad i ≫ φ
      = yoneda.map (blockFace φ i) ≫ ιᵂ cd (blockIdx φ i) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact (serialWedgeCell_spec cd (ad.get i).pos (beadCell φ i)).symm

/-- …read on cells: **post-composition happens in the target bead.**  Bead `i` of `φ ≫ ψ` is
bead `blockIdx φ i` of `ψ`, restricted along the block face. -/
theorem beadCell_comp_block {ad cd : List ℕ+} {X : PrecubicalSet}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (ψ : (⋁cd).toPsh ⟶ X) (i : Fin ad.length) :
    beadCell (φ ≫ ψ) i = X.map (blockFace φ i).op (beadCell ψ (blockIdx φ i)) := by
  have h : ιᵂ ad i ≫ (φ ≫ ψ)
      = yoneda.map (blockFace φ i) ≫ (ιᵂ cd (blockIdx φ i) ≫ ψ) := by
    rw [← Category.assoc, blockFace_spec φ i]; exact Category.assoc _ _ _
  exact (congrArg yonedaEquiv h).trans
    (yonedaEquiv_naturality (ιᵂ cd (blockIdx φ i) ≫ ψ) (blockFace φ i)).symm

/-- …and at `ψ = 𝟙`: **a wedge map's bead is a face of the target bead it lands in.** -/
theorem blockFace_spec_cell {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    beadCell φ i = (⋁cd).toPsh.map (blockFace φ i).op (taut cd (blockIdx φ i)) := by
  simpa only [Category.comp_id, beadCell_id] using beadCell_comp_block φ (𝟙 _) i

/-- If `ι_i ≫ φ = g ≫ ι_r` for any face `g`, then `r = blockIdx φ i`. -/
theorem blockIdx_eq_of_factor {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length)
    (r : Fin cd.length) (g : ▫((ad.get i) : ℕ) ⟶ ▫((cd.get r) : ℕ))
    (h : ιᵂ ad i ≫ φ = yoneda.map g ≫ ιᵂ cd r) :
    r = blockIdx φ i := by
  refine serialWedge_block_unique cd (ad.get i).2 r (blockIdx φ i)
    (beadCell φ i)
    ⟨yonedaEquiv (yoneda.map g),
      (yonedaEquiv_comp (yoneda.map g) (ιᵂ cd r)).symm.trans
        (congrArg yonedaEquiv h.symm)⟩
    ⟨yonedaEquiv (yoneda.map (blockFace φ i)),
      (yonedaEquiv_comp (yoneda.map (blockFace φ i))
        (ιᵂ cd (blockIdx φ i))).symm.trans
        (congrArg yonedaEquiv (blockFace_spec φ i).symm)⟩

/-- The two-step block factorization of `ι_i ≫ (φ ≫ ψ)` (`r := blockIdx φ i`, `r' := blockIdx ψ r`):

      □^{ad.get i}   --ι-->  □^∨(ad)
           |                    |
   blockFace φ i                φ
           v                    v
      □^{bd.get r}   --ι-->  □^∨(bd)
           |                    |
   blockFace ψ r                ψ
           v                    v
      □^{cd.get r'}  --ι-->  □^∨(cd)
-/
theorem blockFace_spec_comp {ad bd cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁bd).toPsh)
    (ψ : (⋁bd).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    ιᵂ ad i ≫ (φ ≫ ψ)
      = yoneda.map (blockFace φ i ≫ blockFace ψ (blockIdx φ i))
        ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)) :=
  calc ιᵂ ad i ≫ (φ ≫ ψ)
      = (ιᵂ ad i ≫ φ) ≫ ψ := (Category.assoc _ _ _).symm
    _ = (yoneda.map (blockFace φ i) ≫ ιᵂ bd (blockIdx φ i)) ≫ ψ :=
        congrArg (· ≫ ψ) (blockFace_spec φ i)
    _ = yoneda.map (blockFace φ i) ≫ (ιᵂ bd (blockIdx φ i) ≫ ψ) :=
        Category.assoc _ _ _
    _ = yoneda.map (blockFace φ i) ≫ (yoneda.map (blockFace ψ (blockIdx φ i))
          ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i))) :=
        congrArg (yoneda.map (blockFace φ i) ≫ ·) (blockFace_spec ψ (blockIdx φ i))
    _ = (yoneda.map (blockFace φ i) ≫ yoneda.map (blockFace ψ (blockIdx φ i)))
          ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)) := (Category.assoc _ _ _).symm
    _ = yoneda.map (blockFace φ i ≫ blockFace ψ (blockIdx φ i))
          ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)) :=
        congrArg (· ≫ ιᵂ cd (blockIdx ψ (blockIdx φ i)))
          (yoneda.map_comp (blockFace φ i) (blockFace ψ (blockIdx φ i))).symm

/-- `blockIdx` of an identity map is the identity. -/
theorem blockIdx_id {dims : List ℕ+} (i : Fin dims.length) :
    blockIdx (𝟙 (⋁dims).toPsh) i = i :=
  (blockIdx_eq_of_factor (𝟙 (⋁dims).toPsh) i i
    (𝟙 ▫(dims.get i : ℕ)) (by
      rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp])).symm

/-- `blockIdx (φ ≫ ψ) i = blockIdx ψ (blockIdx φ i)`. -/
theorem blockIdx_comp {ad bd cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁bd).toPsh)
    (ψ : (⋁bd).toPsh ⟶ (⋁cd).toPsh) (i : Fin ad.length) :
    blockIdx (φ ≫ ψ) i = blockIdx ψ (blockIdx φ i) :=
  (blockIdx_eq_of_factor (φ ≫ ψ) i (blockIdx ψ (blockIdx φ i))
    (blockFace φ i ≫ blockFace ψ (blockIdx φ i)) (blockFace_spec_comp φ ψ i)).symm

/-! ### Where a block sits: the prefix-sum sandwich

`blockIdx` is pinned numerically by dimension prefix sums.  Everything here runs on the serial
wedge's *own* tautological altitude (`serialWedge_admitsAltitude`), which always exists — no
hypothesis on any ambient `K`. -/

/-- The taut chain of a serial wedge: its own beads, read off the identity. -/
theorem serialWedge_isCubeChain_id (cd : List ℕ+) :
    IsCubeChain (⋁cd).init (wedgeToCubes ⟨cd, 𝟙 (⋁cd).toPsh⟩) (⋁cd).final := by
  simpa using wedgeToCubes_isCubeChain (K := ⋁cd) cd (𝟙 (⋁cd).toPsh)

/-- The chain a wedge map into `⋁cd` pushes forward, for any map fixing the initial vertex. -/
theorem serialWedge_isCubeChain_push {ed cd : List ℕ+} (hom : (⋁ed).toPsh ⟶ (⋁cd).toPsh)
    (hinit : hom⟪0⟫ (⋁ed).init = (⋁cd).init) :
    IsCubeChain (⋁cd).init (wedgeToCubes ⟨ed, hom⟩) (hom⟪0⟫ (⋁ed).final) := by
  have h := wedgeToCubes_isCubeChain (K := ⋁cd) ed hom
  rwa [hinit] at h

/-- The altitude of bead `k` of a wedge map into `⋁cd` is where that bead starts.
A packaging of `isCubeChain_alt_get` through `wedgeToCubes_get`. -/
theorem serialWedge_bead_alt {ed cd : List ℕ+}
    (alt : ∀ n, (⋁cd).cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude (⋁cd).toPsh alt)
    (h0 : alt 0 (⋁cd).init = 0)
    (hom : (⋁ed).toPsh ⟶ (⋁cd).toPsh)
    (hinit : hom⟪0⟫ (⋁ed).init = (⋁cd).init)
    (k : Fin ed.length) :
    alt (ed.get k : ℕ) (beadCell hom k) = (beadStart ed k.val : ℤ) := by
  have hlt : k.val < (wedgeToCubes ⟨ed, hom⟩).length := by
    rw [wedgeToCubes_length]; exact k.isLt
  have hcast : (⟨k.val, hlt⟩ : Fin (wedgeToCubes ⟨ed, hom⟩).length).cast
      (wedgeToCubes_length ed hom) = k := Fin.ext rfl
  have hget := wedgeToCubes_get ed hom ⟨k.val, hlt⟩
  have hg := isCubeChain_alt_get alt hax (wedgeToCubes ⟨ed, hom⟩) (⋁cd).init _
    (serialWedge_isCubeChain_push hom hinit) k.val hlt
  rw [h0, zero_add, wedgeToCubes_dims] at hg
  rw [hget, hcast] at hg
  exact hg

/-- **A source bead sits inside its target block**, offset by the block face's `trueCount`:
bead `i` of `ad` starts `trueCount (ev (blockFace φ i))` into block `blockIdx φ i` of `cd`.
Uses **only** `serialWedge_admitsAltitude cd`. -/
theorem serialWedge_beadStart_blockIdx {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    beadStart ad i.val
      = beadStart cd (blockIdx φ i).val + trueCount (ev (blockFace φ i)) := by
  obtain ⟨alt, hax, h0⟩ := BPSet.serialWedge_admitsAltitude cd
  have hP := serialWedge_bead_alt alt hax h0 φ hinit i
  have hT := serialWedge_bead_alt alt hax h0 (𝟙 (⋁cd).toPsh) (by simp) (blockIdx φ i)
  rw [beadCell_id] at hT
  have hc := PrecubicalSet.alt_cubeMap alt hax (taut cd (blockIdx φ i)) (blockFace φ i)
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply] at hc
  have hz : (beadStart ad i.val : ℤ)
      = (beadStart cd (blockIdx φ i).val : ℤ) + (trueCount (ev (blockFace φ i)) : ℤ) := by
    rw [← hP, ← hT, blockFace_spec_cell φ i]; exact hc
  exact_mod_cast hz

/-- **Prefix-sum sandwich for `blockIdx`**: bead `i` of `ad` starts inside the half-open
interval of block `blockIdx φ i` of `cd`. -/
theorem serialWedge_blockIdx_prefix_bound {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init)
    (i : Fin ad.length) :
    beadStart cd (blockIdx φ i).val ≤ beadStart ad i.val
      ∧ beadStart ad i.val < beadStart cd ((blockIdx φ i).val + 1) := by
  have heq := serialWedge_beadStart_blockIdx φ hinit i
  have hsucc := beadStart_succ cd (blockIdx φ i)
  have hle : (ad.get i : ℕ) ≤ (cd.get (blockIdx φ i) : ℕ) :=
    cells_card_le (ev (blockFace φ i))
  have htle : trueCount (ev (blockFace φ i))
      ≤ (cd.get (blockIdx φ i) : ℕ) - (ad.get i : ℕ) :=
    trueCount_le (ev (blockFace φ i))
  have hipos : 0 < (ad.get i : ℕ) := (ad.get i).2
  omega

/-- **`blockIdx` of a bi-pointed wedge map is monotone** — from the prefix-sum sandwich. -/
theorem serialWedge_blockIdx_monotone {ad cd : List ℕ+}
    (φ : (⋁ad).toPsh ⟶ (⋁cd).toPsh)
    (hinit : φ⟪0⟫ (⋁ad).init = (⋁cd).init) :
    Monotone (blockIdx φ) := by
  intro i i' hii
  rw [Fin.le_def]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨hb1, _⟩ := serialWedge_blockIdx_prefix_bound φ hinit i
  obtain ⟨_, hb2'⟩ := serialWedge_blockIdx_prefix_bound φ hinit i'
  have hmA := beadStart_mono ad (Fin.le_def.mp hii)
  have hmB := beadStart_mono cd (show (blockIdx φ i').val + 1 ≤ (blockIdx φ i).val by omega)
  omega

/-- **`∑ ad = ∑ cd` for a bi-pointed serial-wedge map**: the pushed chain has dimension list
`ad`, the taut chain has `cd`, and both span the same altitude gap in `⋁cd`. -/
theorem serialWedge_dimSum_eq {ad cd : List ℕ+} (φ : ⋁ad ⟶ ⋁cd) :
    BPSet.dimSum ad = BPSet.dimSum cd := by
  obtain ⟨alt, hax, _⟩ := BPSet.serialWedge_admitsAltitude cd
  have hT := isCubeChain_alt_final alt hax _ _ _ (serialWedge_isCubeChain_id cd)
  have hP := isCubeChain_alt_final alt hax _ _ _
    (serialWedge_isCubeChain_push φ.hom φ.app_init)
  rw [φ.app_final] at hP
  rw [wedgeToCubes_dims] at hT hP
  exact_mod_cast add_left_cancel (hP.symm.trans hT)

end CubeChain
