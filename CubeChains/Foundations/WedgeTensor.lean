import CubeChains.Foundations.GeoTensor.BP
import CubeChains.Foundations.WedgeMonoidal

/-!
# Foundations/WedgeTensor — the two wedge-to-tensor comparisons

`X ∨ Y` glues `X.final` to `Y.init`; inside `X ⊗ᵍ Y` the slices `X ⊗ init Y` and `final X ⊗ Y`
meet at exactly that vertex, so the wedge descends (`wedgeToTensor`).  Sending each leaf to the
*other* factor descends it to `Y ⊗ᵍ X` instead (`wedgeSwapTensor`).  At cubes the two are the two
staircases out of `□m ∨ □n`: `cubeMerge` runs the first bead through the first coordinate block,
`cubeReorder` through the second.
-/

open CategoryTheory Opposite StdCube BPSet

namespace GeoTensor

/-! ### Slices of the tensor through a vertex -/

/-- Maps into the tensor unit are unique — `▫0` is terminal in `Box`. -/
theorem hom_unit_ext {Z : PrecubicalSet} (a b : Z ⟶ tensorUnit) : a = b :=
  NatTrans.ext_apply fun B z =>
    Box.hom_ext (X := B.unop) (Y := ▫0) (f := a.app B z) (g := b.app B z)
      (Subtype.ext (funext fun j => j.elim0))

/-- The unit is self-dual: its two unitors coincide (both are maps into `tensorUnit`). -/
theorem rightUnitor_tensorUnit : rightUnitor tensorUnit = leftUnitor tensorUnit :=
  Iso.ext (hom_unit_ext _ _)

theorem rightUnitor_inv_naturality {X Y : PrecubicalSet} (f : X ⟶ Y) :
    f ≫ (rightUnitor Y).inv = (rightUnitor X).inv ≫ tensorHom f (𝟙 tensorUnit) := by
  rw [Iso.comp_inv_eq, Category.assoc, show tensorHom f (𝟙 tensorUnit) = whiskerRight f tensorUnit
      from rfl, rightUnitor_naturality f, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem leftUnitor_inv_naturality {X Y : PrecubicalSet} (f : X ⟶ Y) :
    f ≫ (leftUnitor Y).inv = (leftUnitor X).inv ≫ tensorHom (𝟙 tensorUnit) f := by
  rw [Iso.comp_inv_eq, Category.assoc, show tensorHom (𝟙 tensorUnit) f = whiskerLeft tensorUnit f
      from rfl, leftUnitor_naturality f, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The slice `X ⊗ v` of `X ⊗ Y` through a vertex `v` of `Y`. -/
def rightSlice (X : PrecubicalSet) {Y : PrecubicalSet} (v : tensorUnit ⟶ Y) :
    X ⟶ tensorObj X Y :=
  (rightUnitor X).inv ≫ tensorHom (𝟙 X) v

/-- The slice `u ⊗ Y` of `X ⊗ Y` through a vertex `u` of `X`. -/
def leftSlice {X : PrecubicalSet} (u : tensorUnit ⟶ X) (Y : PrecubicalSet) :
    Y ⟶ tensorObj X Y :=
  (leftUnitor Y).inv ≫ tensorHom u (𝟙 Y)

theorem rightSlice_app {X Y : PrecubicalSet} (v : tensorUnit ⟶ Y) {B : Boxᵒᵖ} (x : X.obj B) :
    (rightSlice X v).app B x
      = ⟨B.unop.dim, 0, Nat.add_zero _, x, v.app (op ▫0) unitVertex⟩ := by
  simp only [rightSlice, NatTrans.comp_app, types_comp_apply, rightUnitor_inv_app,
    tensorHom_app, NatTrans.id_app, types_id_apply]
  rfl

theorem leftSlice_app {X Y : PrecubicalSet} (u : tensorUnit ⟶ X) {B : Boxᵒᵖ} (y : Y.obj B) :
    (leftSlice u Y).app B y
      = ⟨0, B.unop.dim, Nat.zero_add _, u.app (op ▫0) unitVertex, y⟩ := by
  simp only [leftSlice, NatTrans.comp_app, types_comp_apply, leftUnitor_inv_app,
    tensorHom_app, NatTrans.id_app, types_id_apply]
  rfl

/-- **The corner of the two slices**: they meet exactly at `u ⊗ v`. -/
theorem slice_corner {X Y : PrecubicalSet} (u : tensorUnit ⟶ X) (v : tensorUnit ⟶ Y) :
    u ≫ rightSlice X v = v ≫ leftSlice u Y := by
  rw [rightSlice, leftSlice, ← Category.assoc, ← Category.assoc,
    rightUnitor_inv_naturality u, leftUnitor_inv_naturality v, Category.assoc, Category.assoc,
    ← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, rightUnitor_tensorUnit,
    Category.comp_id, Category.id_comp, Category.comp_id, Category.id_comp]

/-! ### The cube slices are the two coordinate blocks

Read off as raw sign vectors (`.val`), so no dependent transport of cell dimensions appears. -/

/-- The `X`-slice of `□m ⊗ □n` at a vertex `v` is the face `(∗ᵐ, v)`. -/
theorem sign_rightSlice_cube {m n : ℕ} {w : (□m).toPsh ⟶ (□(m + n)).toPsh}
    {v : (yoneda.obj ▫0) ⟶ (□n).toPsh}
    (hw : w = rightSlice (□m).toPsh v ≫ (cubeTensorIso m n).hom) :
    (Box.sign (yonedaEquiv w)).val
      = Fin.append (topCell m).val (Box.sign (yonedaEquiv v : (▫0 : Box) ⟶ ▫n)).val := by
  subst hw
  have hcell : (rightSlice (□m).toPsh v).app (op ▫m) (𝟙 (▫m))
      = (⟨m, 0, Nat.add_zero m, 𝟙 (▫m), yonedaEquiv v⟩ :
          tensorCells (□m).toPsh (□n).toPsh (▫m).dim) := by
    refine (rightSlice_app (X := (□m).toPsh) (B := op ▫m) v (𝟙 (▫m))).trans ?_
    exact tensorCells_ext rfl rfl HEq.rfl HEq.rfl
  change (Box.sign ((cubeTensorIso m n).hom.app (op ▫m)
    ((rightSlice (□m).toPsh v).app (op ▫m) (𝟙 (▫m))))).val = _
  rw [hcell, cubeTensorIso_hom_app, tensorCubeFun, Box.sign_ofSign, castCellDim_val,
    appendCell_val, Box.sign_id]

/-- The `Y`-slice of `□m ⊗ □n` at a vertex `u` is the face `(u, ∗ⁿ)`. -/
theorem sign_leftSlice_cube {m n : ℕ} {w : (□n).toPsh ⟶ (□(m + n)).toPsh}
    {u : (yoneda.obj ▫0) ⟶ (□m).toPsh}
    (hw : w = leftSlice u (□n).toPsh ≫ (cubeTensorIso m n).hom) :
    (Box.sign (yonedaEquiv w)).val
      = Fin.append (Box.sign (yonedaEquiv u : (▫0 : Box) ⟶ ▫m)).val (topCell n).val := by
  subst hw
  have hcell : (leftSlice u (□n).toPsh).app (op ▫n) (𝟙 (▫n))
      = (⟨0, n, Nat.zero_add n, yonedaEquiv u, 𝟙 (▫n)⟩ :
          tensorCells (□m).toPsh (□n).toPsh (▫n).dim) := by
    refine (leftSlice_app (Y := (□n).toPsh) (B := op ▫n) u (𝟙 (▫n))).trans ?_
    exact tensorCells_ext rfl rfl HEq.rfl HEq.rfl
  change (Box.sign ((cubeTensorIso m n).hom.app (op ▫n)
    ((leftSlice u (□n).toPsh).app (op ▫n) (𝟙 (▫n))))).val = _
  rw [hcell, cubeTensorIso_hom_app, tensorCubeFun, Box.sign_ofSign, castCellDim_val,
    appendCell_val, Box.sign_id]

end GeoTensor

namespace ChainCat

open GeoTensor

/-! ### The comparison maps -/

/-- The wedge descends to the tensor: `X` at `Y`'s start, `Y` at `X`'s end. -/
def wedgeToTensorPsh (X Y : BPSet) : (X ∨ Y).toPsh ⟶ tensorObj X.toPsh Y.toPsh :=
  wedge2Desc (rightSlice X.toPsh Y.initVertex) (leftSlice X.finalVertex Y.toPsh)
    (slice_corner X.finalVertex Y.initVertex)

/-- The wedge descends to the flipped tensor: each leaf takes the *other* factor. -/
def wedgeSwapTensorPsh (X Y : BPSet) : (X ∨ Y).toPsh ⟶ tensorObj Y.toPsh X.toPsh :=
  wedge2Desc (leftSlice Y.initVertex X.toPsh) (rightSlice Y.toPsh X.finalVertex)
    (slice_corner Y.initVertex X.finalVertex).symm

@[reassoc] theorem wedgeInl_wedgeToTensorPsh (X Y : BPSet) :
    wedgeInl X Y ≫ wedgeToTensorPsh X Y = rightSlice X.toPsh Y.initVertex :=
  wedge2Desc_inl _ _ _

@[reassoc] theorem wedgeInr_wedgeToTensorPsh (X Y : BPSet) :
    wedgeInr X Y ≫ wedgeToTensorPsh X Y = leftSlice X.finalVertex Y.toPsh :=
  wedge2Desc_inr _ _ _

@[reassoc] theorem wedgeInl_wedgeSwapTensorPsh (X Y : BPSet) :
    wedgeInl X Y ≫ wedgeSwapTensorPsh X Y = leftSlice Y.initVertex X.toPsh :=
  wedge2Desc_inl _ _ _

@[reassoc] theorem wedgeInr_wedgeSwapTensorPsh (X Y : BPSet) :
    wedgeInr X Y ≫ wedgeSwapTensorPsh X Y = rightSlice Y.toPsh X.finalVertex :=
  wedge2Desc_inr _ _ _

theorem yonedaEquiv_initVertex (K : BPSet) : yonedaEquiv K.initVertex = K.init :=
  yonedaEquiv.apply_symm_apply K.init

theorem yonedaEquiv_finalVertex (K : BPSet) : yonedaEquiv K.finalVertex = K.final :=
  yonedaEquiv.apply_symm_apply K.final

/-- **The wedge-to-tensor comparison** `X ∨ Y ⟶ X ⊗ᵍ Y`. -/
def wedgeToTensor (X Y : BPSet) : X ∨ Y ⟶ X ⊗ᵍ Y where
  hom := wedgeToTensorPsh X Y
  app_init :=
    (comp_app_cell (wedge2Desc_inl _ _ _) 0 X.init).trans
      ((rightSlice_app _ X.init).trans
        (tensorCells_ext rfl rfl HEq.rfl (heq_of_eq (yonedaEquiv_initVertex Y))))
  app_final :=
    (comp_app_cell (wedge2Desc_inr _ _ _) 0 Y.final).trans
      ((leftSlice_app _ Y.final).trans
        (tensorCells_ext rfl rfl (heq_of_eq (yonedaEquiv_finalVertex X)) HEq.rfl))

/-- The comparison into the flipped tensor `X ∨ Y ⟶ Y ⊗ᵍ X`. -/
def wedgeSwapTensor (X Y : BPSet) : X ∨ Y ⟶ Y ⊗ᵍ X where
  hom := wedgeSwapTensorPsh X Y
  app_init :=
    (comp_app_cell (wedge2Desc_inl _ _ _) 0 X.init).trans
      ((leftSlice_app _ X.init).trans
        (tensorCells_ext rfl rfl (heq_of_eq (yonedaEquiv_initVertex Y)) HEq.rfl))
  app_final :=
    (comp_app_cell (wedge2Desc_inr _ _ _) 0 Y.final).trans
      ((rightSlice_app _ Y.final).trans
        (tensorCells_ext rfl rfl HEq.rfl (heq_of_eq (yonedaEquiv_finalVertex X))))

/-! ### The two staircases at cubes -/

/-- **The bead merge** `□m ∨ □n ⟶ □(m+n)`: the first bead runs the first `m` coordinates (the
rest at `0`), the second the last `n` (the rest at `1`). -/
def cubeMerge (m n : ℕ) : □m ∨ □n ⟶ □(m + n) :=
  wedgeToTensor (□m) (□n) ≫ (cubeTensorIsoBP m n).hom

/-- **The bead reordering** `□m ∨ □n ⟶ □(n+m)`: the same two beads in the opposite blocks. -/
def cubeReorder (m n : ℕ) : □m ∨ □n ⟶ □(n + m) :=
  wedgeSwapTensor (□m) (□n) ≫ (cubeTensorIsoBP n m).hom

theorem sign_cubeMerge_inl (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom))).val
      = Fin.append (topCell m).val (constVertex n false).val := by
  have h : wedgeInl (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom
      = rightSlice (□m).toPsh ((□n).initVertex) ≫ (cubeTensorIso m n).hom :=
    wedgeInl_wedgeToTensorPsh_assoc (□m) (□n) _
  refine (sign_rightSlice_cube h).trans ?_
  rw [yonedaEquiv_initVertex, cube_init_sign n]

theorem sign_cubeMerge_inr (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom))).val
      = Fin.append (constVertex m true).val (topCell n).val := by
  have h : wedgeInr (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom
      = leftSlice ((□m).finalVertex) (□n).toPsh ≫ (cubeTensorIso m n).hom :=
    wedgeInr_wedgeToTensorPsh_assoc (□m) (□n) _
  refine (sign_leftSlice_cube h).trans ?_
  rw [yonedaEquiv_finalVertex, cube_final_sign m]

theorem sign_cubeReorder_inl (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom))).val
      = Fin.append (constVertex n false).val (topCell m).val := by
  have h : wedgeInl (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom
      = leftSlice ((□n).initVertex) (□m).toPsh ≫ (cubeTensorIso n m).hom :=
    wedgeInl_wedgeSwapTensorPsh_assoc (□m) (□n) _
  refine (sign_leftSlice_cube h).trans ?_
  rw [yonedaEquiv_initVertex, cube_init_sign n]

theorem sign_cubeReorder_inr (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom))).val
      = Fin.append (topCell n).val (constVertex m true).val := by
  have h : wedgeInr (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom
      = rightSlice (□n).toPsh ((□m).finalVertex) ≫ (cubeTensorIso n m).hom :=
    wedgeInr_wedgeSwapTensorPsh_assoc (□m) (□n) _
  refine (sign_rightSlice_cube h).trans ?_
  rw [yonedaEquiv_finalVertex, cube_final_sign m]

/-! ### The coordinate blocks of the two staircases

Each bead of a staircase frees a contiguous run of coordinates, so its `faceEmb` is the
corresponding `Fin` inclusion: `cubeMerge` keeps the block order, `cubeReorder` exchanges it. -/

/-- A face whose free coordinates are enumerated by a strictly monotone `f` **is** `f`. -/
theorem faceEmb_eq_of_none {k N : ℕ} (g : ▫k ⟶ ▫N) {f : Fin k → Fin N} (hf : StrictMono f)
    (hnone : ∀ i, (Box.sign g).val (f i) = none) (i : Fin k) : faceEmb g i = f i :=
  congrFun (Finset.orderEmbOfFin_unique (Box.sign g).prop
    (fun z => StdCube.mem_noneSet.mpr (hnone z)) hf).symm i

/-- The first bead of `cubeMerge m n` runs the coordinate block `[0, m)`. -/
theorem faceEmb_cubeMerge_inl (m n : ℕ) (k : Fin m) :
    (faceEmb (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom)) k : ℕ)
      = (k : ℕ) := by
  refine congrArg Fin.val (faceEmb_eq_of_none _ (f := fun i => Fin.castAdd n i)
    (fun _ _ hab => hab) (fun i => ?_) k)
  rw [sign_cubeMerge_inl m n, Fin.append_left]
  rfl

/-- The second bead of `cubeMerge m n` runs the coordinate block `[m, m + n)`. -/
theorem faceEmb_cubeMerge_inr (m n : ℕ) (k : Fin n) :
    (faceEmb (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom)) k : ℕ)
      = m + (k : ℕ) := by
  refine congrArg Fin.val (faceEmb_eq_of_none _ (f := fun i => Fin.natAdd m i)
    (fun _ _ hab => Nat.add_lt_add_left hab m) (fun i => ?_) k)
  rw [sign_cubeMerge_inr m n, Fin.append_right]
  rfl

/-- The first bead of `cubeReorder m n` runs the *last* coordinate block `[n, n + m)`. -/
theorem faceEmb_cubeReorder_inl (m n : ℕ) (k : Fin m) :
    (faceEmb (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom)) k : ℕ)
      = n + (k : ℕ) := by
  refine congrArg Fin.val (faceEmb_eq_of_none _ (f := fun i => Fin.natAdd n i)
    (fun _ _ hab => Nat.add_lt_add_left hab n) (fun i => ?_) k)
  rw [sign_cubeReorder_inl m n, Fin.append_right]
  rfl

/-- The second bead of `cubeReorder m n` runs the *first* coordinate block `[0, n)`. -/
theorem faceEmb_cubeReorder_inr (m n : ℕ) (k : Fin n) :
    (faceEmb (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom)) k : ℕ)
      = (k : ℕ) := by
  refine congrArg Fin.val (faceEmb_eq_of_none _ (f := fun i => Fin.castAdd m i)
    (fun _ _ hab => hab) (fun i => ?_) k)
  rw [sign_cubeReorder_inr m n, Fin.append_left]
  rfl

/-- **Merging is not reordering**: the first bead of `cubeMerge 1 1` runs coordinate `0`, that of
`cubeReorder 1 1` coordinate `1`. -/
theorem cubeMerge_ne_cubeReorder : cubeMerge 1 1 ≠ cubeReorder 1 1 := by
  intro h
  have h0 : Fin.append (topCell 1).val (constVertex 1 false).val
      = Fin.append (constVertex 1 false).val (topCell 1).val :=
    (sign_cubeMerge_inl 1 1).symm.trans (by rw [h]; exact sign_cubeReorder_inl 1 1)
  have h1 := congrFun h0 (Fin.castAdd 1 (0 : Fin 1))
  rw [Fin.append_left, Fin.append_left] at h1
  exact absurd h1 (by decide)

end ChainCat
