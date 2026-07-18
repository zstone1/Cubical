import CubeChains.Foundations.GeoTensor.Hom

/-!
# Foundations/GeoTensor/Assoc — the associator of the geometric tensor

Reassociation `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`: both sides are the same triple split `x ⊗ y ⊗ z`, so
the component maps reassociate the nested `tensorCells` via `(p+q)+r = p+(q+r)`.  Naturality is the
associativity of the triple coordinate split of a sign vector.
-/

open CategoryTheory Opposite StdCube

namespace GeoTensor

/-- Structure HEq for `tensorCells` across differing total dimension. -/
theorem tensorCells_heq {X Y : PrecubicalSet} {n n' : ℕ} {c : tensorCells X Y n}
    {d : tensorCells X Y n'} (hp : c.p = d.p) (hq : c.q = d.q) (hx : HEq c.x d.x)
    (hy : HEq c.y d.y) : HEq c d := by
  have hn : n = n' := by rw [← c.hpq, ← d.hpq, hp, hq]
  subst hn
  exact heq_of_eq (tensorCells_ext hp hq hx hy)

/-- The `X`-half is a heterogeneous congruence for equality of `tensorCells`. -/
theorem congr_x {X Y : PrecubicalSet} {n : ℕ} {a b : tensorCells X Y n} (h : a = b) :
    HEq a.x b.x := by subst h; rfl

/-- The `Y`-half is a heterogeneous congruence for equality of `tensorCells`. -/
theorem congr_y {X Y : PrecubicalSet} {n : ℕ} {a b : tensorCells X Y n} (h : a = b) :
    HEq a.y b.y := by subst h; rfl

/-- Forward reassociation `((x,y),z) ↦ (x,(y,z))`. -/
def assocFwd (X Y Z : PrecubicalSet) {n : ℕ}
    (c : tensorCells (tensorObj X Y) Z n) : tensorCells X (tensorObj Y Z) n where
  p := c.x.p
  q := c.x.q + c.q
  hpq := by have h1 : c.x.p + c.x.q = c.p := c.x.hpq; have h2 := c.hpq; omega
  x := c.x.x
  y := ⟨c.x.q, c.q, rfl, c.x.y, c.y⟩

/-- Backward reassociation `(x,(y,z)) ↦ ((x,y),z)`. -/
def assocBwd (X Y Z : PrecubicalSet) {n : ℕ}
    (d : tensorCells X (tensorObj Y Z) n) : tensorCells (tensorObj X Y) Z n where
  p := d.p + d.y.p
  q := d.y.q
  hpq := by have h1 : d.y.p + d.y.q = d.q := d.y.hpq; have h2 := d.hpq; omega
  x := ⟨d.p, d.y.p, rfl, d.x, d.y.x⟩
  y := d.y.y

@[simp] theorem assocFwd_p (X Y Z : PrecubicalSet) {n : ℕ} (c : tensorCells (tensorObj X Y) Z n) :
    (assocFwd X Y Z c).p = c.x.p := rfl
@[simp] theorem assocFwd_q (X Y Z : PrecubicalSet) {n : ℕ} (c : tensorCells (tensorObj X Y) Z n) :
    (assocFwd X Y Z c).q = c.x.q + c.q := rfl
@[simp] theorem assocFwd_x (X Y Z : PrecubicalSet) {n : ℕ} (c : tensorCells (tensorObj X Y) Z n) :
    (assocFwd X Y Z c).x = c.x.x := rfl
@[simp] theorem assocFwd_y (X Y Z : PrecubicalSet) {n : ℕ} (c : tensorCells (tensorObj X Y) Z n) :
    (assocFwd X Y Z c).y = pair Y Z c.x.y c.y := rfl

@[simp] theorem assocBwd_p (X Y Z : PrecubicalSet) {n : ℕ} (d : tensorCells X (tensorObj Y Z) n) :
    (assocBwd X Y Z d).p = d.p + d.y.p := rfl
@[simp] theorem assocBwd_q (X Y Z : PrecubicalSet) {n : ℕ} (d : tensorCells X (tensorObj Y Z) n) :
    (assocBwd X Y Z d).q = d.y.q := rfl
@[simp] theorem assocBwd_x (X Y Z : PrecubicalSet) {n : ℕ} (d : tensorCells X (tensorObj Y Z) n) :
    (assocBwd X Y Z d).x = pair X Y d.x d.y.x := rfl
@[simp] theorem assocBwd_y (X Y Z : PrecubicalSet) {n : ℕ} (d : tensorCells X (tensorObj Y Z) n) :
    (assocBwd X Y Z d).y = d.y.y := rfl

/-- Pointwise reassociation iso. -/
def assocIso (X Y Z : PrecubicalSet) (B : Boxᵒᵖ) :
    (tensorObj (tensorObj X Y) Z).obj B ≅ (tensorObj X (tensorObj Y Z)).obj B where
  hom := TypeCat.ofHom (assocFwd X Y Z)
  inv := TypeCat.ofHom (assocBwd X Y Z)
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro c
    simp only [types_comp_apply, TypeCat.ofHom_apply, types_id_apply]
    exact tensorCells_ext c.x.hpq rfl (tensorCells_heq rfl rfl HEq.rfl HEq.rfl) HEq.rfl
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro d
    simp only [types_comp_apply, TypeCat.ofHom_apply, types_id_apply]
    exact tensorCells_ext rfl d.y.hpq HEq.rfl (tensorCells_heq rfl rfl HEq.rfl HEq.rfl)

/-- The reassociation natural iso `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. -/
def associator (X Y Z : PrecubicalSet) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  NatIso.ofComponents (assocIso X Y Z) (by
    intro B B' φ
    apply ConcreteCategory.hom_ext
    intro c
    simp only [assocIso, types_comp_apply, TypeCat.ofHom_apply, tensorObj_map]
    -- The two coordinate re-splits of `Box.sign φ.unop` agree block-by-block.
    -- LHS restricts `((x,y),z)` then reassociates; RHS reassociates then restricts.
    -- `t` : the `((·,·),·)` split; `dx` : its inner left resplit; `s'` : the `(·,(·,·))` split.
    have hRy : restr (tensorObj Y Z) (pair Y Z c.x.y c.y)
          (splitRight (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))
        = restrictAux Y Z (splitRight (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))
          c.x.y c.y := by
      unfold restr
      rw [map_pair]
      simp only [Quiver.Hom.unop_op, Box.sign_ofSign]
    have hRHSy : (restrictAux X (tensorObj Y Z) (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop))
          (assocFwd X Y Z c).x (pair Y Z c.x.y c.y)).y
        = restrictAux Y Z (splitRight (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))
          c.x.y c.y := hRy
    have hdx : (restrictAux (tensorObj X Y) Z (recast c.hpq (Box.sign φ.unop)) c.x c.y).x
        = restrictAux X Y (recast c.x.hpq (splitLeft (recast c.hpq (Box.sign φ.unop))))
          c.x.x c.x.y := by
      change restr (tensorObj X Y) c.x (splitLeft (recast c.hpq (Box.sign φ.unop))) = _
      unfold restr
      rw [tensorObj_map]
      simp only [Quiver.Hom.unop_op, Box.sign_ofSign]
    -- block index equalities: the three coordinate blocks agree as raw vectors
    have hvA :
        (splitLeft (recast c.x.hpq (splitLeft (recast c.hpq (Box.sign φ.unop))))).val
          = (splitLeft (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop))).val := by
      funext i
      simp only [recast_val, Function.comp_apply]
      refine congrArg _ (Fin.ext ?_)
      simp
    have hvB :
        (splitRight (recast c.x.hpq (splitLeft (recast c.hpq (Box.sign φ.unop))))).val
          = (splitLeft (splitRight
              (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))).val := by
      funext i
      simp only [splitLeft_val, splitRight_val, recast_val, Function.comp_apply]
      refine congrArg _ (Fin.ext ?_)
      simp
    have hvC :
        (splitRight (recast c.hpq (Box.sign φ.unop))).val
          = (splitRight (splitRight
              (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))).val := by
      funext i
      have h : c.x.p + c.x.q = c.p := c.x.hpq
      simp only [splitRight_val, recast_val, Function.comp_apply]
      refine congrArg _ (Fin.ext ?_)
      simp only [Fin.val_cast, Fin.val_natAdd, assocFwd_p]
      omega
    -- card equalities derived from the block equalities
    have hcA : (noneSet (splitLeft (recast c.x.hpq
          (splitLeft (recast c.hpq (Box.sign φ.unop))))).val).card
        = (noneSet (splitLeft (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop))).val).card :=
      congrArg (fun v => (noneSet v).card) hvA
    have hcB : (noneSet (splitRight (recast c.x.hpq
          (splitLeft (recast c.hpq (Box.sign φ.unop))))).val).card
        = (noneSet (splitLeft (splitRight
            (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))).val).card :=
      congrArg (fun v => (noneSet v).card) hvB
    have hcC : (noneSet (splitRight (recast c.hpq (Box.sign φ.unop))).val).card
        = (noneSet (splitRight (splitRight
            (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))).val).card :=
      congrArg (fun v => (noneSet v).card) hvC
    have hq : (noneSet (splitRight (recast c.x.hpq
            (splitLeft (recast c.hpq (Box.sign φ.unop))))).val).card
          + (noneSet (splitRight (recast c.hpq (Box.sign φ.unop))).val).card
        = (noneSet (splitRight (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop))).val).card := by
      rw [hcB, hcC]
      exact splitLeft_dim_add (splitRight (recast (assocFwd X Y Z c).hpq (Box.sign φ.unop)))
    refine tensorCells_ext ?_ ?_ ?_ ?_
    · simp only [assocFwd_p]
      rw [hdx]
      exact hcA
    · simp only [assocFwd_q]
      rw [hdx]
      exact hq
    · simp only [assocFwd_x]
      exact (congr_x hdx).trans (restr_heq X c.x.x hcA (cell_heq_of_val hvA))
    · simp only [assocFwd_y]
      rw [hRHSy]
      exact tensorCells_heq ((congrArg (fun w => w.q) hdx).trans hcB) hcC
        ((congr_y hdx).trans (restr_heq Y c.x.y hcB (cell_heq_of_val hvB)))
        (restr_heq Z c.y hcC (cell_heq_of_val hvC)))

@[simp] theorem associator_hom_app (X Y Z : PrecubicalSet) (B : Boxᵒᵖ)
    (c : tensorCells (tensorObj X Y) Z B.unop.dim) :
    (associator X Y Z).hom.app B c = assocFwd X Y Z c := rfl

@[simp] theorem associator_inv_app (X Y Z : PrecubicalSet) (B : Boxᵒᵖ)
    (d : tensorCells X (tensorObj Y Z) B.unop.dim) :
    (associator X Y Z).inv.app B d = assocBwd X Y Z d := rfl

/-- Naturality of the associator in all three arguments. -/
theorem associator_naturality {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : PrecubicalSet}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂) :
    tensorHom (tensorHom f g) h ≫ (associator X₂ Y₂ Z₂).hom
      = (associator X₁ Y₁ Z₁).hom ≫ tensorHom f (tensorHom g h) := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro c
  simp only [NatTrans.comp_app, types_comp_apply, associator_hom_app, tensorHom_app]
  exact tensorCells_ext rfl rfl HEq.rfl (tensorCells_heq rfl rfl HEq.rfl HEq.rfl)

/-- The pentagon coherence for the associator. -/
theorem pentagon (W X Y Z : PrecubicalSet) :
    tensorHom (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensorObj X Y) Z).hom
        ≫ tensorHom (𝟙 W) (associator X Y Z).hom
      = (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro c
  simp only [NatTrans.comp_app, types_comp_apply, associator_hom_app, tensorHom_app,
    NatTrans.id_app, types_id_apply]
  refine tensorCells_ext rfl ?_ HEq.rfl (tensorCells_heq rfl rfl HEq.rfl HEq.rfl)
  simp only [assocFwd_p, assocFwd_q, assocFwd_x]
  omega

end GeoTensor
