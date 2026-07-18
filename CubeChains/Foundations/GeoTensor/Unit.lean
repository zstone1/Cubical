import CubeChains.Foundations.GeoTensor.Hom
import Mathlib.CategoryTheory.Yoneda

/-!
# Foundations/GeoTensor/Unit — the tensor unit and both unitors

The unit of the computable geometric tensor is the representable at dimension `0`,
`tensorUnit = yoneda.obj ▫0`.  A cell of `tensorUnit` in degree `p` is a `Box` map `▫p ⟶ ▫0`,
whose sign vector lives on `Fin 0`; so it forces `p = 0` (`unitCell_dim_zero`) and is unique
(`unitCell_unique`).  Hence in `tensorObj tensorUnit X` the left half collapses (`p = 0`,
`q = n`) and the projection to the surviving `X`-cell is an iso `leftUnitor`; symmetrically
`rightUnitor` collapses the right half.  The transports along the forced `q = n` (resp. `p = n`)
are `eqToHom`; the `p = 0` half-cell manipulations run through the `restr`/split HEq API.
-/

open CategoryTheory Opposite StdCube

namespace GeoTensor

/-- The tensor unit: the representable precubical set at dimension `0`. -/
def tensorUnit : PrecubicalSet := yoneda.obj ▫0

/-- The unique unit cell in degree `0`, the identity of `▫0`. -/
def unitVertex : tensorUnit.obj (op ▫0) := 𝟙 (▫0 : Box)

/-! ### The unit cells force dimension `0` and are unique -/

/-- A cell of `Cell 0 p` forces `p = 0` (its sign vector lives on the empty `Fin 0`). -/
theorem cell_zero_dim {p : ℕ} (c : Cell 0 p) : p = 0 := by
  have h := c.prop
  rw [Finset.eq_empty_of_isEmpty (noneSet c.val), Finset.card_empty] at h
  exact h.symm

/-- A unit cell in degree `p` forces `p = 0`. -/
theorem unitCell_dim_zero {p : ℕ} (u : tensorUnit.obj (op ▫p)) : p = 0 :=
  cell_zero_dim (Box.sign (u : ▫p ⟶ ▫0))

/-- Unit cells in a fixed degree are unique (maps into `▫0` are unique). -/
theorem unitCell_unique {p : ℕ} (u v : tensorUnit.obj (op ▫p)) : u = v := by
  show (u : ▫p ⟶ ▫0) = v
  apply Box.hom_ext
  apply Subtype.ext
  funext j
  exact j.elim0

/-- Unit cells across (propositionally equal) degrees are heterogeneously equal. -/
theorem unitCell_heq {p p' : ℕ} (u : tensorUnit.obj (op ▫p)) (v : tensorUnit.obj (op ▫p'))
    (h : p = p') : HEq u v := by
  subst h
  exact heq_of_eq (unitCell_unique u v)

/-! ### Transport of a cell along a degree equation -/

/-- Transporting a presheaf cell along an object equation is heterogeneously the identity. -/
theorem map_eqToHom_heq {X : PrecubicalSet} {A A' : Boxᵒᵖ} (h : A = A') (x : X.obj A) :
    HEq (X.map (eqToHom h) x) x := by
  subst h
  rw [eqToHom_refl]
  exact heq_of_eq (by rw [Functor.map_id_apply])

/-- Restriction by the sign vector of a `Box` map is the presheaf map. -/
theorem restr_sign_unop {X : PrecubicalSet} {B B' : Boxᵒᵖ} (φ : B ⟶ B') (z : X.obj B) :
    restr X z (Box.sign φ.unop) = X.map φ z := by
  have hof : Box.ofSign (Box.sign φ.unop) = φ.unop := Box.hom_ext (by rw [Box.sign_ofSign])
  change X.map (Box.ofSign (Box.sign φ.unop)).op z = X.map φ z
  rw [hof, Quiver.Hom.op_unop]

/-! ### Restricting a product cell with a trivial unit half -/

/-- `restrictAux` with the left half a unit cell: the left block vanishes. -/
theorem restrictAux_unitLeft (X : PrecubicalSet) {M K : ℕ} (σ : Cell M K) (z : X.obj (op ▫M)) :
    restrictAux tensorUnit X (recast (Nat.zero_add M) σ) unitVertex z
      = ⟨0, K, Nat.zero_add K, unitVertex, restr X z σ⟩ := by
  set s := recast (Nat.zero_add M) σ with hs
  have hfun : (fun i : Fin M => s.val (Fin.natAdd 0 i)) = σ.val := by
    funext i
    have hcast : Fin.cast (Nat.zero_add M) (Fin.natAdd 0 i) = i := by apply Fin.ext; simp
    rw [hs, recast_val, Function.comp_apply, hcast]
  have hq : (noneSet (fun i : Fin M => s.val (Fin.natAdd 0 i))).card = K := by
    rw [hfun]; exact σ.prop
  have hAll : AllNone (splitLeft s) := fun j => j.elim0
  refine tensorCells_ext (cell_zero_dim (splitLeft s)) hq
    (restr_allNone tensorUnit hAll unitVertex) ?_
  refine restr_heq X z hq (cell_heq_of_val ?_)
  rw [splitRight_val]; exact hfun

/-- `restrictAux` with the right half a unit cell: the right block vanishes. -/
theorem restrictAux_unitRight (X : PrecubicalSet) {M K : ℕ} (σ : Cell M K) (z : X.obj (op ▫M)) :
    restrictAux X tensorUnit (recast (Nat.add_zero M) σ) z unitVertex
      = ⟨K, 0, Nat.add_zero K, restr X z σ, unitVertex⟩ := by
  set s := recast (Nat.add_zero M) σ with hs
  have hfun : (fun i : Fin M => s.val (Fin.castAdd 0 i)) = σ.val := by
    funext i
    have hcast : Fin.cast (Nat.add_zero M) (Fin.castAdd 0 i) = i := by apply Fin.ext; simp
    rw [hs, recast_val, Function.comp_apply, hcast]
  have hp : (noneSet (fun i : Fin M => s.val (Fin.castAdd 0 i))).card = K := by
    rw [hfun]; exact σ.prop
  have hAll : AllNone (splitRight s) := fun j => j.elim0
  refine tensorCells_ext hp (cell_zero_dim (splitRight s)) ?_
    (restr_allNone tensorUnit hAll unitVertex)
  refine restr_heq X z hp (cell_heq_of_val ?_)
  rw [splitLeft_val]; exact hfun

/-! ### The left unitor -/

/-- The surviving `X`-dimension of a `tensorObj tensorUnit X` cell is the total degree. -/
theorem leftDim {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells tensorUnit X B.unop.dim) :
    c.q = B.unop.dim := by
  have h0 := unitCell_dim_zero c.x
  have hpq := c.hpq
  omega

/-- The object equation transporting the surviving `X`-half to the ambient degree. -/
theorem leftHomEq {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells tensorUnit X B.unop.dim) :
    (op ▫c.q : Boxᵒᵖ) = op ▫(B.unop.dim) :=
  congrArg (fun n => (op ▫n : Boxᵒᵖ)) (leftDim c)

/-- Forward map of the left unitor: keep the `X`-half, transported to the ambient degree. -/
def leftHomApp (X : PrecubicalSet) (B : Boxᵒᵖ) (c : tensorCells tensorUnit X B.unop.dim) :
    X.obj B :=
  X.map (eqToHom (leftHomEq c)) c.y

/-- Inverse map of the left unitor: the `X`-cell with a trivial unit half. -/
def invCell (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    tensorCells tensorUnit X B.unop.dim :=
  ⟨0, B.unop.dim, Nat.zero_add _, unitVertex, z⟩

theorem leftHom_invCell (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    leftHomApp X B (invCell X B z) = z :=
  eq_of_heq (map_eqToHom_heq (leftHomEq (invCell X B z)) z)

theorem invCell_leftHom (X : PrecubicalSet) (B : Boxᵒᵖ) (c : tensorCells tensorUnit X B.unop.dim) :
    invCell X B (leftHomApp X B c) = c :=
  tensorCells_ext (unitCell_dim_zero c.x).symm (leftDim c).symm
    (unitCell_heq unitVertex c.x (unitCell_dim_zero c.x).symm)
    (map_eqToHom_heq (leftHomEq c) c.y)

/-- Naturality of the inverse cell in the presheaf variable. -/
theorem invNat (X : PrecubicalSet) {B B' : Boxᵒᵖ} (φ : B ⟶ B') (z : X.obj B) :
    (tensorObj tensorUnit X).map φ (invCell X B z) = invCell X B' (X.map φ z) := by
  change restrictAux tensorUnit X (recast (Nat.zero_add B.unop.dim) (Box.sign φ.unop)) unitVertex z
      = invCell X B' (X.map φ z)
  rw [restrictAux_unitLeft X (Box.sign φ.unop) z]
  refine tensorCells_ext rfl rfl HEq.rfl (heq_of_eq ?_)
  exact restr_sign_unop φ z

/-- The inverse half of the left unitor as a presheaf map. -/
def leftUnitorInv (X : PrecubicalSet) : X ⟶ tensorObj tensorUnit X where
  app B := TypeCat.ofHom (invCell X B)
  naturality := by
    intro B B' φ
    apply ConcreteCategory.hom_ext
    intro x
    simp only [types_comp_apply, TypeCat.ofHom_apply]
    exact (invNat X φ x).symm

/-- The forward half of the left unitor as a presheaf map. -/
def leftUnitorHom (X : PrecubicalSet) : tensorObj tensorUnit X ⟶ X where
  app B := TypeCat.ofHom (leftHomApp X B)
  naturality := by
    intro B B' φ
    apply ConcreteCategory.hom_ext
    intro c
    change leftHomApp X B' ((tensorObj tensorUnit X).map φ c) = X.map φ (leftHomApp X B c)
    calc leftHomApp X B' ((tensorObj tensorUnit X).map φ c)
        = leftHomApp X B' ((tensorObj tensorUnit X).map φ (invCell X B (leftHomApp X B c))) := by
            rw [invCell_leftHom]
      _ = leftHomApp X B' (invCell X B' (X.map φ (leftHomApp X B c))) := by rw [invNat]
      _ = X.map φ (leftHomApp X B c) := leftHom_invCell X B' _

/-- **Left unitor** for the geometric tensor: `tensorUnit ⊗ X ≅ X`. -/
def leftUnitor (X : PrecubicalSet) : tensorObj tensorUnit X ≅ X where
  hom := leftUnitorHom X
  inv := leftUnitorInv X
  hom_inv_id := by
    apply NatTrans.ext; funext B
    apply ConcreteCategory.hom_ext; intro c
    simp only [NatTrans.comp_app, NatTrans.id_app, types_comp_apply, types_id_apply]
    exact invCell_leftHom X B c
  inv_hom_id := by
    apply NatTrans.ext; funext B
    apply ConcreteCategory.hom_ext; intro z
    simp only [NatTrans.comp_app, NatTrans.id_app, types_comp_apply, types_id_apply]
    exact leftHom_invCell X B z

@[simp] theorem leftUnitor_hom_app (X : PrecubicalSet) (B : Boxᵒᵖ)
    (c : tensorCells tensorUnit X B.unop.dim) :
    (leftUnitor X).hom.app B c = X.map (eqToHom (leftHomEq c)) c.y := rfl

@[simp] theorem leftUnitor_inv_app (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    (leftUnitor X).inv.app B z = invCell X B z := rfl

/-- Naturality of the left unitor in the presheaf variable. -/
theorem leftUnitor_naturality {X Y : PrecubicalSet} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply NatTrans.ext; funext B
  apply ConcreteCategory.hom_ext; intro c
  simp only [NatTrans.comp_app, types_comp_apply, whiskerLeft,
    tensorHom_app, NatTrans.id_app, types_id_apply, leftUnitor_hom_app]
  rw [NatTrans.naturality_apply]

/-! ### The right unitor -/

/-- The surviving `X`-dimension of a `tensorObj X tensorUnit` cell is the total degree. -/
theorem rightDim {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells X tensorUnit B.unop.dim) :
    c.p = B.unop.dim := by
  have h0 := unitCell_dim_zero c.y
  have hpq := c.hpq
  omega

/-- The object equation transporting the surviving `X`-half to the ambient degree. -/
theorem rightHomEq {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells X tensorUnit B.unop.dim) :
    (op ▫c.p : Boxᵒᵖ) = op ▫(B.unop.dim) :=
  congrArg (fun n => (op ▫n : Boxᵒᵖ)) (rightDim c)

/-- Forward map of the right unitor: keep the `X`-half, transported to the ambient degree. -/
def rightHomApp (X : PrecubicalSet) (B : Boxᵒᵖ) (c : tensorCells X tensorUnit B.unop.dim) :
    X.obj B :=
  X.map (eqToHom (rightHomEq c)) c.x

/-- Inverse map of the right unitor: the `X`-cell with a trivial unit half. -/
def rightInvCell (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    tensorCells X tensorUnit B.unop.dim :=
  ⟨B.unop.dim, 0, Nat.add_zero _, z, unitVertex⟩

theorem rightHom_invCell (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    rightHomApp X B (rightInvCell X B z) = z :=
  eq_of_heq (map_eqToHom_heq (rightHomEq (rightInvCell X B z)) z)

theorem invCell_rightHom (X : PrecubicalSet) (B : Boxᵒᵖ)
    (c : tensorCells X tensorUnit B.unop.dim) :
    rightInvCell X B (rightHomApp X B c) = c :=
  tensorCells_ext (rightDim c).symm (unitCell_dim_zero c.y).symm
    (map_eqToHom_heq (rightHomEq c) c.x)
    (unitCell_heq unitVertex c.y (unitCell_dim_zero c.y).symm)

/-- Naturality of the inverse cell in the presheaf variable. -/
theorem rightInvNat (X : PrecubicalSet) {B B' : Boxᵒᵖ} (φ : B ⟶ B') (z : X.obj B) :
    (tensorObj X tensorUnit).map φ (rightInvCell X B z) = rightInvCell X B' (X.map φ z) := by
  change restrictAux X tensorUnit (recast (Nat.add_zero B.unop.dim) (Box.sign φ.unop)) z unitVertex
      = rightInvCell X B' (X.map φ z)
  rw [restrictAux_unitRight X (Box.sign φ.unop) z]
  refine tensorCells_ext rfl rfl (heq_of_eq ?_) HEq.rfl
  exact restr_sign_unop φ z

/-- The inverse half of the right unitor as a presheaf map. -/
def rightUnitorInv (X : PrecubicalSet) : X ⟶ tensorObj X tensorUnit where
  app B := TypeCat.ofHom (rightInvCell X B)
  naturality := by
    intro B B' φ
    apply ConcreteCategory.hom_ext
    intro x
    simp only [types_comp_apply, TypeCat.ofHom_apply]
    exact (rightInvNat X φ x).symm

/-- The forward half of the right unitor as a presheaf map. -/
def rightUnitorHom (X : PrecubicalSet) : tensorObj X tensorUnit ⟶ X where
  app B := TypeCat.ofHom (rightHomApp X B)
  naturality := by
    intro B B' φ
    apply ConcreteCategory.hom_ext
    intro c
    change rightHomApp X B' ((tensorObj X tensorUnit).map φ c) = X.map φ (rightHomApp X B c)
    calc rightHomApp X B' ((tensorObj X tensorUnit).map φ c)
        = rightHomApp X B' ((tensorObj X tensorUnit).map φ (rightInvCell X B (rightHomApp X B c)))
            := by rw [invCell_rightHom]
      _ = rightHomApp X B' (rightInvCell X B' (X.map φ (rightHomApp X B c))) := by rw [rightInvNat]
      _ = X.map φ (rightHomApp X B c) := rightHom_invCell X B' _

/-- **Right unitor** for the geometric tensor: `X ⊗ tensorUnit ≅ X`. -/
def rightUnitor (X : PrecubicalSet) : tensorObj X tensorUnit ≅ X where
  hom := rightUnitorHom X
  inv := rightUnitorInv X
  hom_inv_id := by
    apply NatTrans.ext; funext B
    apply ConcreteCategory.hom_ext; intro c
    simp only [NatTrans.comp_app, NatTrans.id_app, types_comp_apply, types_id_apply]
    exact invCell_rightHom X B c
  inv_hom_id := by
    apply NatTrans.ext; funext B
    apply ConcreteCategory.hom_ext; intro z
    simp only [NatTrans.comp_app, NatTrans.id_app, types_comp_apply, types_id_apply]
    exact rightHom_invCell X B z

@[simp] theorem rightUnitor_hom_app (X : PrecubicalSet) (B : Boxᵒᵖ)
    (c : tensorCells X tensorUnit B.unop.dim) :
    (rightUnitor X).hom.app B c = X.map (eqToHom (rightHomEq c)) c.x := rfl

@[simp] theorem rightUnitor_inv_app (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    (rightUnitor X).inv.app B z = rightInvCell X B z := rfl

/-- Naturality of the right unitor in the presheaf variable. -/
theorem rightUnitor_naturality {X Y : PrecubicalSet} (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply NatTrans.ext; funext B
  apply ConcreteCategory.hom_ext; intro c
  simp only [NatTrans.comp_app, types_comp_apply, whiskerRight,
    tensorHom_app, NatTrans.id_app, types_id_apply, rightUnitor_hom_app]
  rw [NatTrans.naturality_apply]

end GeoTensor
