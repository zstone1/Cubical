import CubeChains.Precubical.Wedge.GeoTensor.BP
import CubeChains.Precubical.Wedge.WedgeMonoidal

/-!
# Precubical/Wedge/WedgeTensor — the two wedge-to-tensor comparisons

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

/-- **Both cube slices at once.**  A map `□k ⟶ □m ⊗ □n` whose top cell is `c`, read through the
tensor iso, has for sign vector the concatenation of `c`'s two half signs. -/
theorem sign_slice_cube {m n k : ℕ} {σ : (□k).toPsh ⟶ tensorObj (□m).toPsh (□n).toPsh}
    {c : tensorCells (□m).toPsh (□n).toPsh k} (hc : σ.app (op ▫k) (𝟙 (▫k)) = c) :
    (Box.sign (yonedaEquiv (σ ≫ (cubeTensorIso m n).hom))).val
      = Fin.append (Box.sign c.x).val (Box.sign c.y).val := by
  change (Box.sign ((cubeTensorIso m n).hom.app (op ▫k) (σ.app (op ▫k) (𝟙 (▫k))))).val = _
  rw [hc, cubeTensorIso_hom_app, sign_tensorCubeFun]

/-- The `X`-slice of `□m ⊗ □n` at the `ε`-vertex is the face `(∗ᵐ, εⁿ)`. -/
theorem sign_rightSlice_cube {m n : ℕ} (ε : Bool) {w : (□m).toPsh ⟶ (□(m + n)).toPsh}
    (hw : w = rightSlice (□m).toPsh ((□n).vertexOf ε) ≫ (cubeTensorIso m n).hom) :
    (Box.sign (yonedaEquiv w)).val
      = Fin.append (topCell m).val (constVertex n ε).val := by
  subst hw
  refine (sign_slice_cube (rightSlice_app (X := (□m).toPsh) (B := op ▫m) _ (𝟙 (▫m)))).trans ?_
  change Fin.append (Box.sign (𝟙 (▫m))).val (Box.sign ((□n).vtx ε : (▫0 : Box) ⟶ ▫n)).val = _
  rw [Box.sign_id, cube_sign n]

/-- The `Y`-slice of `□m ⊗ □n` at the `ε`-vertex is the face `(εᵐ, ∗ⁿ)`. -/
theorem sign_leftSlice_cube {m n : ℕ} (ε : Bool) {w : (□n).toPsh ⟶ (□(m + n)).toPsh}
    (hw : w = leftSlice ((□m).vertexOf ε) (□n).toPsh ≫ (cubeTensorIso m n).hom) :
    (Box.sign (yonedaEquiv w)).val
      = Fin.append (constVertex m ε).val (topCell n).val := by
  subst hw
  refine (sign_slice_cube (leftSlice_app (Y := (□n).toPsh) (B := op ▫n) _ (𝟙 (▫n)))).trans ?_
  change Fin.append (Box.sign ((□m).vtx ε : (▫0 : Box) ⟶ ▫m)).val (Box.sign (𝟙 (▫n))).val = _
  rw [Box.sign_id, cube_sign m]

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

/-! ### At a unit factor there is nothing to compare

`□0` is the unit of both the wedge and `⊗ᵍ`, so there the comparison is a pair of unitors — an
isomorphism, and the Segal condition is vacuous. -/

/-- A slice through the unit's own vertex is the unitor. -/
private theorem leftSlice_unit (Y : PrecubicalSet) (u : tensorUnit ⟶ tensorUnit) :
    leftSlice u Y = (leftUnitor Y).inv := by
  rw [leftSlice, hom_unit_ext u (𝟙 tensorUnit), tensorHom_id, Category.comp_id]

private theorem rightSlice_unit (X : PrecubicalSet) (v : tensorUnit ⟶ tensorUnit) :
    rightSlice X v = (rightUnitor X).inv := by
  rw [rightSlice, hom_unit_ext v (𝟙 tensorUnit), tensorHom_id, Category.comp_id]

theorem wedgeToTensorPsh_unit_left (Y : BPSet) :
    wedgeToTensorPsh (□0) Y = wedge2LeftUnitPsh Y ≫ (leftUnitor Y.toPsh).inv := by
  refine wedge2_hom_ext ?_ ?_
  -- `exact`, not `rw`: `(□0).toPsh` and `tensorUnit` are `rfl`-equal but `kabstract` will not
  -- unfold either to see it
  · refine ((wedgeInl_wedgeToTensorPsh (□0) Y).trans ?_).trans
      (wedge2LeftUnitPsh_inl_assoc Y _).symm
    exact (congrArg (fun e : _ ≅ _ => e.inv ≫ tensorHom (𝟙 tensorUnit) Y.initVertex)
      rightUnitor_tensorUnit).trans (leftUnitor_inv_naturality Y.initVertex).symm
  · exact ((wedgeInr_wedgeToTensorPsh (□0) Y).trans (leftSlice_unit Y.toPsh _)).trans
      (wedge2LeftUnitPsh_inr_assoc Y _).symm

theorem wedgeToTensorPsh_unit_right (X : BPSet) :
    wedgeToTensorPsh X (□0) = wedge2RightUnitPsh X ≫ (rightUnitor X.toPsh).inv := by
  refine wedge2_hom_ext ?_ ?_
  · exact ((wedgeInl_wedgeToTensorPsh X (□0)).trans (rightSlice_unit X.toPsh _)).trans
      (wedge2RightUnitPsh_inl_assoc X _).symm
  · refine ((wedgeInr_wedgeToTensorPsh X (□0)).trans ?_).trans
      (wedge2RightUnitPsh_inr_assoc X _).symm
    exact (congrArg (fun e : _ ≅ _ => e.inv ≫ tensorHom X.finalVertex (𝟙 tensorUnit))
      rightUnitor_tensorUnit.symm).trans (rightUnitor_inv_naturality X.finalVertex).symm

instance isIso_wedgeToTensorPsh_unit_left (Y : BPSet) : IsIso (wedgeToTensorPsh (□0) Y) := by
  rw [wedgeToTensorPsh_unit_left]
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso (BPSet.toPshFunctor.map (wedge2LeftUnit Y).hom))) inferInstance

instance isIso_wedgeToTensorPsh_unit_right (X : BPSet) : IsIso (wedgeToTensorPsh X (□0)) := by
  rw [wedgeToTensorPsh_unit_right]
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso (BPSet.toPshFunctor.map (wedge2RightUnit X).hom))) inferInstance

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

/-- At a unit bead the merge is a pair of unitors — there is nothing to merge. -/
instance isIso_cubeMerge_unit_left (n : ℕ) : IsIso (cubeMerge 0 n : BPSet.Hom _ _).hom :=
  IsIso.comp_isIso' (isIso_wedgeToTensorPsh_unit_left (□n))
    (inferInstanceAs (IsIso (BPSet.toPshFunctor.map (cubeTensorIsoBP 0 n).hom)))

instance isIso_cubeMerge_unit_right (m : ℕ) : IsIso (cubeMerge m 0 : BPSet.Hom _ _).hom :=
  IsIso.comp_isIso' (isIso_wedgeToTensorPsh_unit_right (□m))
    (inferInstanceAs (IsIso (BPSet.toPshFunctor.map (cubeTensorIsoBP m 0).hom)))

theorem sign_cubeMerge_inl (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom))).val
      = Fin.append (topCell m).val (constVertex n false).val :=
  sign_rightSlice_cube false (wedgeInl_wedgeToTensorPsh_assoc (□m) (□n) _)

theorem sign_cubeMerge_inr (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom))).val
      = Fin.append (constVertex m true).val (topCell n).val :=
  sign_leftSlice_cube true (wedgeInr_wedgeToTensorPsh_assoc (□m) (□n) _)

theorem sign_cubeReorder_inl (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom))).val
      = Fin.append (constVertex n false).val (topCell m).val :=
  sign_leftSlice_cube false (wedgeInl_wedgeSwapTensorPsh_assoc (□m) (□n) _)

theorem sign_cubeReorder_inr (m n : ℕ) :
    (Box.sign (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom))).val
      = Fin.append (topCell n).val (constVertex m true).val :=
  sign_rightSlice_cube true (wedgeInr_wedgeSwapTensorPsh_assoc (□m) (□n) _)

/-! ### The coordinate blocks of the two staircases

Each bead of a staircase frees a contiguous run of coordinates, so its `faceEmb` is the
corresponding `Fin` inclusion: `cubeMerge` keeps the block order, `cubeReorder` exchanges it. -/

/-- A face whose free coordinates are enumerated by a strictly monotone `f` **is** `f`. -/
theorem faceEmb_eq_of_none {k N : ℕ} (g : ▫k ⟶ ▫N) {f : Fin k → Fin N} (hf : StrictMono f)
    (hnone : ∀ i, (Box.sign g).val (f i) = none) (i : Fin k) : faceEmb g i = f i :=
  congrFun (Finset.orderEmbOfFin_unique (Box.sign g).prop
    (fun z => StdCube.mem_noneSet.mpr (hnone z)) hf).symm i

/-- A leg free on the **low** block: its sign is the top cell appended to a vertex. -/
theorem faceEmb_of_sign_append_left {k N : ℕ} (g : ▫k ⟶ ▫(k + N)) {v : Fin N → Option Bool}
    (h : (Box.sign g).val = Fin.append (topCell k).val v) (i : Fin k) :
    (faceEmb g i : ℕ) = (i : ℕ) :=
  congrArg Fin.val (faceEmb_eq_of_none g (f := Fin.castAdd N) (fun _ _ hab => hab)
    (fun z => by rw [h, Fin.append_left]; rfl) i)

/-- A leg free on the **high** block: its sign is a vertex appended to the top cell. -/
theorem faceEmb_of_sign_append_right {k N : ℕ} (g : ▫N ⟶ ▫(k + N)) {v : Fin k → Option Bool}
    (h : (Box.sign g).val = Fin.append v (topCell N).val) (i : Fin N) :
    (faceEmb g i : ℕ) = k + (i : ℕ) :=
  congrArg Fin.val (faceEmb_eq_of_none g (f := Fin.natAdd k)
    (fun _ _ hab => Nat.add_lt_add_left hab k) (fun z => by rw [h, Fin.append_right]; rfl) i)

/-- The first bead of `cubeMerge m n` runs the coordinate block `[0, m)`. -/
theorem faceEmb_cubeMerge_inl (m n : ℕ) (k : Fin m) :
    (faceEmb (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom)) k : ℕ)
      = (k : ℕ) :=
  faceEmb_of_sign_append_left _ (sign_cubeMerge_inl m n) k

/-- The second bead of `cubeMerge m n` runs the coordinate block `[m, m + n)`. -/
theorem faceEmb_cubeMerge_inr (m n : ℕ) (k : Fin n) :
    (faceEmb (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeMerge m n : BPSet.Hom _ _).hom)) k : ℕ)
      = m + (k : ℕ) :=
  faceEmb_of_sign_append_right _ (sign_cubeMerge_inr m n) k

/-- The first bead of `cubeReorder m n` runs the *last* coordinate block `[n, n + m)`. -/
theorem faceEmb_cubeReorder_inl (m n : ℕ) (k : Fin m) :
    (faceEmb (yonedaEquiv (wedgeInl (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom)) k : ℕ)
      = n + (k : ℕ) :=
  faceEmb_of_sign_append_right _ (sign_cubeReorder_inl m n) k

/-- The second bead of `cubeReorder m n` runs the *first* coordinate block `[0, n)`. -/
theorem faceEmb_cubeReorder_inr (m n : ℕ) (k : Fin n) :
    (faceEmb (yonedaEquiv (wedgeInr (□m) (□n) ≫ (cubeReorder m n : BPSet.Hom _ _).hom)) k : ℕ)
      = (k : ℕ) :=
  faceEmb_of_sign_append_left _ (sign_cubeReorder_inr m n) k

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
