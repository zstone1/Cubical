import CubeChains.Foundations.GeoTensor

/-!
# Foundations/GeoTensor/Cube — the computable cube tensor iso

`□m ⊗ □n ≅ □(m+n)` at the representable level, computably: the geometric tensor of two
representables `yoneda ▫m`, `yoneda ▫n` is the representable `yoneda ▫(m+n)`.  A tensor cell
`⟨p, q, f, g⟩` (a `p`-cell of `▫m` and a `q`-cell of `▫n`) is sent to the sign-vector
concatenation `appendCell (sign f) (sign g)`; the inverse splits a cell of `▫(m+n)` into its
`Fin m`/`Fin n` coordinate blocks.
-/

open CategoryTheory Opposite StdCube

namespace GeoTensor

/-- Reindex the *cell* dimension (number of free coordinates) of a cell along `k = k'`.  The
underlying sign vector is unchanged. -/
def castCellDim {N k k' : ℕ} (h : k = k') (s : Cell N k) : Cell N k' := ⟨s.val, s.prop.trans h⟩

@[simp] theorem castCellDim_val {N k k' : ℕ} (h : k = k') (s : Cell N k) :
    (castCellDim h s).val = s.val := rfl

theorem castCellDim_heq {N k k' : ℕ} (h : k = k') (s : Cell N k) : HEq (castCellDim h s) s :=
  cell_heq_of_val rfl

/-- `ofSign` is a congruence for heterogeneous equality of its sign vector. -/
theorem ofSign_heq {t p p' : ℕ} {a : Cell t p} {b : Cell t p'} (hp : p = p') (hab : HEq a b) :
    HEq (Box.ofSign a : ▫p ⟶ ▫t) (Box.ofSign b : ▫p' ⟶ ▫t) := by
  cases hp
  cases eq_of_heq hab
  rfl

theorem ofSign_sign {A B : Box} (f : A ⟶ B) : Box.ofSign (Box.sign f) = f :=
  Box.hom_ext (by rw [Box.sign_ofSign])

/-- Restricting a cell of the representable `yoneda ▫m` is precomposition in `Box`. -/
theorem restr_yoneda {m p a : ℕ} (f : (yoneda.obj ▫m).obj (op ▫p)) (c : Cell p a) :
    restr (yoneda.obj ▫m) f c = Box.ofSign c ≫ (f : ▫p ⟶ ▫m) := rfl

theorem sign_restr_yoneda {m p a : ℕ} (f : (yoneda.obj ▫m).obj (op ▫p)) (c : Cell p a) :
    Box.sign (restr (yoneda.obj ▫m) f c : ▫a ⟶ ▫m) = subst (Box.sign f) c := by
  rw [restr_yoneda, Box.sign_comp, Box.sign_ofSign]

/-! ### The degreewise bijection -/

variable (m n : ℕ)

/-- Forward: a tensor cell `⟨p, q, f, g⟩` of `yoneda ▫m ⊗ yoneda ▫n` in degree `B.dim` becomes the
`Box` map `B ⟶ ▫(m+n)` whose sign concatenates the signs of `f` and `g`. -/
def tensorCubeFun (B : Box)
    (c : tensorCells (yoneda.obj ▫m) (yoneda.obj ▫n) B.dim) : (B ⟶ ▫(m + n)) :=
  Box.ofSign (castCellDim c.hpq (appendCell (Box.sign c.x) (Box.sign c.y)))

/-- Inverse: split the sign vector of `h : B ⟶ ▫(m+n)` into its `Fin m`/`Fin n` blocks. -/
def tensorCubeInv (B : Box) (h : B ⟶ ▫(m + n)) :
    tensorCells (yoneda.obj ▫m) (yoneda.obj ▫n) B.dim where
  p := (noneSet (fun i => (Box.sign h).val (Fin.castAdd n i))).card
  q := (noneSet (fun i => (Box.sign h).val (Fin.natAdd m i))).card
  hpq := splitLeft_dim_add (Box.sign h)
  x := Box.ofSign (splitLeft (Box.sign h))
  y := Box.ofSign (splitRight (Box.sign h))

theorem tensorCubeInv_hom (B : Box) (c : tensorCells (yoneda.obj ▫m) (yoneda.obj ▫n) B.dim) :
    tensorCubeInv m n B (tensorCubeFun m n B c) = c := by
  set H := castCellDim c.hpq (appendCell (Box.sign c.x) (Box.sign c.y)) with hH
  have hsign : Box.sign (tensorCubeFun m n B c) = H := by
    rw [tensorCubeFun, Box.sign_ofSign]
  have hleft : (fun i => (Box.sign (tensorCubeFun m n B c)).val (Fin.castAdd n i))
      = (Box.sign c.x).val := by
    funext i
    rw [hsign, hH, castCellDim_val, appendCell_val, Fin.append_left]
  have hright : (fun i => (Box.sign (tensorCubeFun m n B c)).val (Fin.natAdd m i))
      = (Box.sign c.y).val := by
    funext i
    rw [hsign, hH, castCellDim_val, appendCell_val, Fin.append_right]
  refine tensorCells_ext ?_ ?_ ?_ ?_
  · change (noneSet (fun i => (Box.sign (tensorCubeFun m n B c)).val (Fin.castAdd n i))).card = c.p
    rw [hleft]; exact (Box.sign c.x).prop
  · change (noneSet (fun i => (Box.sign (tensorCubeFun m n B c)).val (Fin.natAdd m i))).card = c.q
    rw [hright]; exact (Box.sign c.y).prop
  · refine HEq.trans (ofSign_heq (by rw [hleft]; exact (Box.sign c.x).prop)
      (cell_heq_of_val hleft)) (heq_of_eq (ofSign_sign c.x))
  · refine HEq.trans (ofSign_heq (by rw [hright]; exact (Box.sign c.y).prop)
      (cell_heq_of_val hright)) (heq_of_eq (ofSign_sign c.y))

theorem tensorCubeFun_inv (B : Box) (h : B ⟶ ▫(m + n)) :
    tensorCubeFun m n B (tensorCubeInv m n B h) = h := by
  apply Box.hom_ext
  rw [tensorCubeFun, Box.sign_ofSign]
  apply Subtype.ext
  change (appendCell (Box.sign (Box.ofSign (splitLeft (Box.sign h))))
      (Box.sign (Box.ofSign (splitRight (Box.sign h))))).val = (Box.sign h).val
  rw [appendCell_val, Box.sign_ofSign, Box.sign_ofSign, splitLeft_val, splitRight_val]
  exact append_split (Box.sign h)

/-- The degreewise bijection `tensorCells (yoneda ▫m) (yoneda ▫n) B.dim ≃ (B ⟶ ▫(m+n))`. -/
def tensorCubeEquiv (B : Box) :
    tensorCells (yoneda.obj ▫m) (yoneda.obj ▫n) B.dim ≃ (B ⟶ ▫(m + n)) where
  toFun := tensorCubeFun m n B
  invFun := tensorCubeInv m n B
  left_inv := tensorCubeInv_hom m n B
  right_inv := tensorCubeFun_inv m n B

/-! ### The natural isomorphism -/

/-- **`□m ⊗ □n ≅ □(m+n)`** for the geometric tensor of representables. -/
def cubeTensorIso :
    tensorObj (yoneda.obj ▫m) (yoneda.obj ▫n) ≅ yoneda.obj ▫(m + n) :=
  NatIso.ofComponents (fun B => (tensorCubeEquiv m n B.unop).toIso) fun {B B'} φ => by
    apply ConcreteCategory.hom_ext
    intro c
    change tensorCubeFun m n B'.unop ((tensorObj (yoneda.obj ▫m) (yoneda.obj ▫n)).map φ c)
      = (yoneda.obj ▫(m + n)).map φ (tensorCubeFun m n B.unop c)
    apply Box.hom_ext
    rw [show (yoneda.obj ▫(m + n)).map φ (tensorCubeFun m n B.unop c)
        = φ.unop ≫ tensorCubeFun m n B.unop c from rfl,
      tensorObj_map, Box.sign_comp, tensorCubeFun, tensorCubeFun, Box.sign_ofSign, Box.sign_ofSign]
    set s := recast c.hpq (Box.sign φ.unop) with hs
    -- rewrite the two half-signs of the restricted cell as `subst`s
    have hdx : Box.sign (restrictAux (yoneda.obj ▫m) (yoneda.obj ▫n) s c.x c.y).x
        = subst (Box.sign c.x) (splitLeft s) := sign_restr_yoneda c.x (splitLeft s)
    have hdy : Box.sign (restrictAux (yoneda.obj ▫m) (yoneda.obj ▫n) s c.x c.y).y
        = subst (Box.sign c.y) (splitRight s) := sign_restr_yoneda c.y (splitRight s)
    rw [hdx, hdy]
    -- both sides equal `subst (appendCell .. ..) (appendCell (splitLeft s) (splitRight s))`
    apply eq_of_heq
    have hLM := (castCellDim_heq (splitLeft_dim_add s) (appendCell
        (subst (Box.sign c.x) (splitLeft s)) (subst (Box.sign c.y) (splitRight s)))).trans
      (heq_of_eq (subst_appendCell (Box.sign c.x) (Box.sign c.y) (splitLeft s) (splitRight s)).symm)
    have hRM : HEq (subst (castCellDim c.hpq (appendCell (Box.sign c.x) (Box.sign c.y)))
          (Box.sign φ.unop))
        (subst (appendCell (Box.sign c.x) (Box.sign c.y))
          (appendCell (splitLeft s) (splitRight s))) := by
      refine subst_heq c.hpq.symm (splitLeft_dim_add s).symm (castCellDim_heq c.hpq _) ?_
      refine HEq.symm (HEq.trans ?_ (recast_heq c.hpq (Box.sign φ.unop)))
      exact cell_heq_of_val (by
        rw [appendCell_val, splitLeft_val, splitRight_val]; exact append_split s)
    exact hLM.trans hRM.symm

@[simp] theorem cubeTensorIso_hom_app (B : Boxᵒᵖ)
    (c : tensorCells (yoneda.obj ▫m) (yoneda.obj ▫n) B.unop.dim) :
    (cubeTensorIso m n).hom.app B c = tensorCubeFun m n B.unop c := rfl

@[simp] theorem cubeTensorIso_inv_app (B : Boxᵒᵖ) (h : B.unop ⟶ ▫(m + n)) :
    (cubeTensorIso m n).inv.app B h = tensorCubeInv m n B.unop h := rfl

end GeoTensor
