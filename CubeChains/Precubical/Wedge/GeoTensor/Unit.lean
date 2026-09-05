import CubeChains.Precubical.Wedge.GeoTensor.Hom
import Mathlib.CategoryTheory.Yoneda

/-!
# Precubical/Wedge/GeoTensor/Unit — the tensor unit and both unitors

The unit is the representable at dimension `0`, `tensorUnit = yoneda.obj ▫0`: a cell of it in
degree `p` has its sign vector on `Fin 0`, so `p = 0` (`unitCell_dim_zero`) and it is unique
(`unitCell_unique`).  A unit half of a product cell is therefore redundant and the surviving half
carries the whole degree — an equivalence (`leftUnitorEquiv`) whose naturality is `leftUnitor`.
`Box` has no symmetry, but a unit half occupies no coordinates, so swapping the two halves *is*
natural once one of them is the unit (`unitSwap`); the right unitor is the left one conjugated by
that swap, and every right-hand statement follows.
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

/-- The `Boxᵒᵖ` equation induced by a degree equation. -/
theorem degEq {p n : ℕ} (h : p = n) : (op ▫p : Boxᵒᵖ) = op ▫n :=
  congrArg (fun k => (op ▫k : Boxᵒᵖ)) h

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

/-! ### The left unitor -/

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

/-- The surviving `X`-dimension of a `tensorObj tensorUnit X` cell is the total degree. -/
theorem leftDim {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells tensorUnit X B.unop.dim) :
    c.q = B.unop.dim := by
  have h0 := unitCell_dim_zero c.x
  have hpq := c.hpq
  omega

/-- The object equation transporting the surviving `X`-half to the ambient degree. -/
theorem leftHomEq {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells tensorUnit X B.unop.dim) :
    (op ▫c.q : Boxᵒᵖ) = op ▫(B.unop.dim) :=
  degEq (leftDim c)

/-- A unit left half is redundant data: the `X`-half, transported to the ambient degree. -/
def leftUnitorEquiv (X : PrecubicalSet) (B : Boxᵒᵖ) :
    X.obj B ≃ tensorCells tensorUnit X B.unop.dim where
  toFun z := ⟨0, B.unop.dim, Nat.zero_add _, unitVertex, z⟩
  invFun c := X.map (eqToHom (leftHomEq c)) c.y
  left_inv z := eq_of_heq (map_eqToHom_heq _ z)
  right_inv c := tensorCells_ext (unitCell_dim_zero c.x).symm (leftDim c).symm
    (unitCell_heq _ _ (unitCell_dim_zero c.x).symm) (map_eqToHom_heq _ c.y)

theorem leftUnitorEquiv_naturality (X : PrecubicalSet) {B B' : Boxᵒᵖ} (φ : B ⟶ B') (z : X.obj B) :
    (tensorObj tensorUnit X).map φ (leftUnitorEquiv X B z) = leftUnitorEquiv X B' (X.map φ z) := by
  change restrictAux tensorUnit X (recast (Nat.zero_add B.unop.dim) (Box.sign φ.unop)) unitVertex z
      = leftUnitorEquiv X B' (X.map φ z)
  rw [restrictAux_unitLeft X (Box.sign φ.unop) z]
  exact tensorCells_ext rfl rfl HEq.rfl (heq_of_eq (restr_sign_unop φ z))

/-- **Left unitor** for the geometric tensor: `tensorUnit ⊗ X ≅ X`. -/
def leftUnitor (X : PrecubicalSet) : tensorObj tensorUnit X ≅ X :=
  (NatIso.ofComponents (fun B => (leftUnitorEquiv X B).toIso) fun φ => by
    apply ConcreteCategory.hom_ext
    intro z
    exact (leftUnitorEquiv_naturality X φ z).symm).symm

@[simp] theorem leftUnitor_hom_app (X : PrecubicalSet) (B : Boxᵒᵖ)
    (c : tensorCells tensorUnit X B.unop.dim) :
    (leftUnitor X).hom.app B c = X.map (eqToHom (leftHomEq c)) c.y := rfl

@[simp] theorem leftUnitor_inv_app (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    (leftUnitor X).inv.app B z = leftUnitorEquiv X B z := rfl

/-- Naturality of the left unitor in the presheaf variable. -/
theorem leftUnitor_naturality {X Y : PrecubicalSet} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  refine NatTrans.ext_apply fun B c => ?_
  simp only [NatTrans.comp_app, types_comp_apply, whiskerLeft,
    tensorHom_app, NatTrans.id_app, types_id_apply, leftUnitor_hom_app]
  rw [NatTrans.naturality_apply]

/-! ### Swapping the halves past a unit -/

/-- Swapping the two halves of a product cell. -/
def swapCells (X Y : PrecubicalSet) (n : ℕ) : tensorCells X Y n ≃ tensorCells Y X n where
  toFun c := ⟨c.q, c.p, (Nat.add_comm _ _).trans c.hpq, c.y, c.x⟩
  invFun c := ⟨c.q, c.p, (Nat.add_comm _ _).trans c.hpq, c.y, c.x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `0`-dimensional block occupies no coordinates, so both readings of a restricting sign vector
reach the surviving half through the same coordinates. -/
theorem swapCells_naturality (X : PrecubicalSet) {B B' : Boxᵒᵖ} (φ : B ⟶ B')
    (c : tensorCells tensorUnit X B.unop.dim) :
    swapCells tensorUnit X B'.unop.dim ((tensorObj tensorUnit X).map φ c)
      = (tensorObj X tensorUnit).map φ (swapCells tensorUnit X B.unop.dim c) := by
  obtain ⟨p, q, hpq, u, y⟩ := c
  obtain rfl := unitCell_dim_zero u
  have hfun : (fun i : Fin q => (recast hpq (Box.sign φ.unop)).val (Fin.natAdd 0 i))
      = fun i : Fin q =>
          (recast ((Nat.add_comm q 0).trans hpq) (Box.sign φ.unop)).val (Fin.castAdd 0 i) := by
    funext i
    exact congrArg (Box.sign φ.unop).val (Fin.ext (by simp))
  have hp := congrArg (fun f => (noneSet f).card) hfun
  have hq := (cell_zero_dim (splitLeft (recast hpq (Box.sign φ.unop)))).trans
    (cell_zero_dim (splitRight (recast ((Nat.add_comm q 0).trans hpq) (Box.sign φ.unop)))).symm
  exact tensorCells_ext hp hq (restr_heq X y hp (cell_heq_of_val hfun)) (unitCell_heq _ _ hq)

/-- The unit factor may be moved across: `tensorUnit ⊗ X ≅ X ⊗ tensorUnit`. -/
def unitSwap (X : PrecubicalSet) : tensorObj tensorUnit X ≅ tensorObj X tensorUnit :=
  NatIso.ofComponents (fun B => (swapCells tensorUnit X B.unop.dim).toIso) fun φ => by
    apply ConcreteCategory.hom_ext
    intro c
    exact swapCells_naturality X φ c

theorem unitSwap_inv_naturality {X Y : PrecubicalSet} (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (unitSwap Y).inv = (unitSwap X).inv ≫ whiskerLeft tensorUnit f :=
  NatTrans.ext_apply fun _ _ => rfl

/-! ### The right unitor -/

/-- The surviving `X`-dimension of a `tensorObj X tensorUnit` cell is the total degree. -/
theorem rightDim {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells X tensorUnit B.unop.dim) :
    c.p = B.unop.dim :=
  leftDim (swapCells X tensorUnit B.unop.dim c)

/-- The object equation transporting the surviving `X`-half to the ambient degree. -/
theorem rightHomEq {X : PrecubicalSet} {B : Boxᵒᵖ} (c : tensorCells X tensorUnit B.unop.dim) :
    (op ▫c.p : Boxᵒᵖ) = op ▫(B.unop.dim) :=
  degEq (rightDim c)

/-- A unit right half is redundant data. -/
def rightUnitorEquiv (X : PrecubicalSet) (B : Boxᵒᵖ) :
    X.obj B ≃ tensorCells X tensorUnit B.unop.dim :=
  (leftUnitorEquiv X B).trans (swapCells tensorUnit X B.unop.dim)

/-- **Right unitor** for the geometric tensor: `X ⊗ tensorUnit ≅ X`. -/
def rightUnitor (X : PrecubicalSet) : tensorObj X tensorUnit ≅ X :=
  (unitSwap X).symm ≪≫ leftUnitor X

@[simp] theorem rightUnitor_hom_app (X : PrecubicalSet) (B : Boxᵒᵖ)
    (c : tensorCells X tensorUnit B.unop.dim) :
    (rightUnitor X).hom.app B c = X.map (eqToHom (rightHomEq c)) c.x := rfl

@[simp] theorem rightUnitor_inv_app (X : PrecubicalSet) (B : Boxᵒᵖ) (z : X.obj B) :
    (rightUnitor X).inv.app B z = rightUnitorEquiv X B z := rfl

/-- Naturality of the right unitor in the presheaf variable. -/
theorem rightUnitor_naturality {X Y : PrecubicalSet} (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  change whiskerRight f tensorUnit ≫ (unitSwap Y).inv ≫ (leftUnitor Y).hom
      = ((unitSwap X).inv ≫ (leftUnitor X).hom) ≫ f
  rw [← Category.assoc, unitSwap_inv_naturality, Category.assoc, leftUnitor_naturality,
    Category.assoc]

end GeoTensor
