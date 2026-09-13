import CubeChains.Precubical.Basic.Representable
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Machinery/Cube/BoxMonoidal

The **parallel tensor** on the box category: `▫m ⊗ ▫n = ▫(m + n)`, on morphisms the
*concatenation of sign vectors* (`Fin.append`), so the whole monoidal structure is sign-vector
algebra.

The associator and both unitors are `eqToIso` of `ℕ`-transports, and a `Box` map that does not
drop dimension is unique (`Box.hom_ext_dim`, from `allNone_of_dim`) — that is what discharges
pentagon and triangle, while the three naturalities need `comp_ext_allNone`.

**`Box` is not braided.**  A `Box` morphism cannot permute coordinates (the symmetry-free
convention), so there is no block swap `▫(m+n) ⟶ ▫(n+m)`; do not look for one.  The braiding
of the geometric product lives one level up, between *cube chains* of `K ⊗ L`, not here.
-/

open CategoryTheory MonoidalCategory

namespace StdCube

variable {N n k : ℕ}

/-! ### Concatenation of sign vectors -/

variable {N₁ N₂ n₁ n₂ k₁ k₂ : ℕ}

theorem card_noneSet_append (u : Fin N₁ → Option Bool) (v : Fin N₂ → Option Bool) :
    (noneSet (Fin.append u v)).card = (noneSet u).card + (noneSet v).card := by
  simp only [noneSet, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp

/-- Concatenation of sign vectors: the tensor of `Box` morphisms. -/
def appendCell (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) : Cell (N₁ + N₂) (n₁ + n₂) :=
  ⟨Fin.append c₁.val c₂.val, by rw [card_noneSet_append, c₁.prop, c₂.prop]⟩

@[simp] theorem appendCell_val (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) :
    (appendCell c₁ c₂).val = Fin.append c₁.val c₂.val := rfl

/-- Concatenating two cells that are constantly `v` gives the constantly-`v` cell. -/
theorem appendCell_const {v : Option Bool} {c₁ : Cell N₁ n₁} {c₂ : Cell N₂ n₂}
    {c : Cell (N₁ + N₂) (n₁ + n₂)} (h₁ : c₁.val = fun _ => v) (h₂ : c₂.val = fun _ => v)
    (h : c.val = fun _ => v) : appendCell c₁ c₂ = c := by
  refine Subtype.ext ?_
  rw [appendCell_val, h₁, h₂, h]
  funext j
  exact Fin.addCases (fun i => Fin.append_left _ _ i) (fun i => Fin.append_right _ _ i) j

/-- Block concatenation of two order embeddings, as a plain function. -/
def addFun (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) : Fin (n₁ + n₂) → Fin (N₁ + N₂) :=
  Fin.addCases (fun i₁ => Fin.castAdd N₂ (e₁ i₁)) (fun i₂ => Fin.natAdd N₁ (e₂ i₂))

@[simp] theorem addFun_castAdd (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) (i : Fin n₁) :
    addFun e₁ e₂ (Fin.castAdd n₂ i) = Fin.castAdd N₂ (e₁ i) := Fin.addCases_left _

@[simp] theorem addFun_natAdd (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) (i : Fin n₂) :
    addFun e₁ e₂ (Fin.natAdd n₁ i) = Fin.natAdd N₁ (e₂ i) := Fin.addCases_right _

theorem addFun_strictMono (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) :
    StrictMono (addFun e₁ e₂) := by
  have h₁ : ∀ a b : Fin n₁, (a : ℕ) < b → ((e₁ a : Fin N₁) : ℕ) < e₁ b :=
    fun _ _ h => e₁.strictMono h
  have h₂ : ∀ a b : Fin n₂, (a : ℕ) < b → ((e₂ a : Fin N₂) : ℕ) < e₂ b :=
    fun _ _ h => e₂.strictMono h
  intro i j hij
  rw [Fin.lt_def] at hij ⊢
  cases i using Fin.addCases with
  | left a =>
    cases j using Fin.addCases with
    | left b => simpa using h₁ a b (by simpa using hij)
    | right b =>
      simp only [addFun_castAdd, addFun_natAdd, Fin.val_castAdd, Fin.val_natAdd]
      have := (e₁ a).isLt; omega
  | right a =>
    cases j using Fin.addCases with
    | left b =>
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hij
      have := b.isLt; omega
    | right b =>
      simp only [addFun_natAdd, Fin.val_natAdd]
      simp only [Fin.val_natAdd] at hij
      have := h₂ a b (by omega); omega

/-- Block concatenation of order embeddings, `Fin (n₁+n₂) ↪o Fin (N₁+N₂)`. -/
def addOrderEmb (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) :
    Fin (n₁ + n₂) ↪o Fin (N₁ + N₂) :=
  OrderEmbedding.ofStrictMono (addFun e₁ e₂) (addFun_strictMono e₁ e₂)

@[simp] theorem addOrderEmb_apply (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂)
    (i : Fin (n₁ + n₂)) : addOrderEmb e₁ e₂ i = addFun e₁ e₂ i := rfl

theorem nones_appendCell (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) :
    nones (appendCell c₁ c₂) = addOrderEmb (nones c₁) (nones c₂) := by
  symm
  refine Finset.orderEmbOfFin_unique' (appendCell c₁ c₂).prop (fun x => ?_)
  rw [mem_noneSet, addOrderEmb_apply]
  cases x using Fin.addCases with
  | left i =>
    rw [addFun_castAdd, appendCell_val, Fin.append_left]
    exact val_nones c₁ i
  | right i =>
    rw [addFun_natAdd, appendCell_val, Fin.append_right]
    exact val_nones c₂ i

theorem nones_appendCell_left (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) (i : Fin n₁) :
    nones (appendCell c₁ c₂) (Fin.castAdd n₂ i) = Fin.castAdd N₂ (nones c₁ i) := by
  rw [nones_appendCell, addOrderEmb_apply, addFun_castAdd]

theorem nones_appendCell_right (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) (i : Fin n₂) :
    nones (appendCell c₁ c₂) (Fin.natAdd n₁ i) = Fin.natAdd N₁ (nones c₂ i) := by
  rw [nones_appendCell, addOrderEmb_apply, addFun_natAdd]

theorem nonesIdx_appendCell_left (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) (j : Fin N₁)
    (h : Fin.castAdd N₂ j ∈ noneSet (appendCell c₁ c₂).val) (h₁ : j ∈ noneSet c₁.val) :
    nonesIdx (appendCell c₁ c₂) (Fin.castAdd N₂ j) h = Fin.castAdd n₂ (nonesIdx c₁ j h₁) := by
  apply (nones (appendCell c₁ c₂)).injective
  rw [nones_nonesIdx, nones_appendCell_left, nones_nonesIdx]

theorem nonesIdx_appendCell_right (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) (j : Fin N₂)
    (h : Fin.natAdd N₁ j ∈ noneSet (appendCell c₁ c₂).val) (h₂ : j ∈ noneSet c₂.val) :
    nonesIdx (appendCell c₁ c₂) (Fin.natAdd N₁ j) h = Fin.natAdd n₁ (nonesIdx c₂ j h₂) := by
  apply (nones (appendCell c₁ c₂)).injective
  rw [nones_nonesIdx, nones_appendCell_right, nones_nonesIdx]

/-- Substitution is computed blockwise: this is functoriality of the tensor. -/
theorem subst_appendCell (c₁ : Cell N₁ n₁) (c₂ : Cell N₂ n₂) (a₁ : Cell n₁ k₁)
    (a₂ : Cell n₂ k₂) :
    subst (appendCell c₁ c₂) (appendCell a₁ a₂) = appendCell (subst c₁ a₁) (subst c₂ a₂) := by
  apply Subtype.ext
  funext j
  rw [appendCell_val, subst_val]
  cases j using Fin.addCases with
  | left j₁ =>
    rw [Fin.append_left]
    by_cases hc : c₁.val j₁ = none
    · have hc' : (appendCell c₁ c₂).val (Fin.castAdd N₂ j₁) = none := by
        rw [appendCell_val, Fin.append_left]; exact hc
      rw [substFun_of_none _ _ hc',
        nonesIdx_appendCell_left c₁ c₂ j₁ (mem_noneSet.mpr hc') (mem_noneSet.mpr hc),
        appendCell_val, Fin.append_left, subst_val, substFun_of_none c₁ a₁ hc]
    · have hc' : (appendCell c₁ c₂).val (Fin.castAdd N₂ j₁) ≠ none := by
        rw [appendCell_val, Fin.append_left]; exact hc
      rw [substFun_of_some _ _ hc', subst_val, substFun_of_some c₁ a₁ hc, appendCell_val,
        Fin.append_left]
  | right j₂ =>
    rw [Fin.append_right]
    by_cases hc : c₂.val j₂ = none
    · have hc' : (appendCell c₁ c₂).val (Fin.natAdd N₁ j₂) = none := by
        rw [appendCell_val, Fin.append_right]; exact hc
      rw [substFun_of_none _ _ hc',
        nonesIdx_appendCell_right c₁ c₂ j₂ (mem_noneSet.mpr hc') (mem_noneSet.mpr hc),
        appendCell_val, Fin.append_right, subst_val, substFun_of_none c₂ a₂ hc]
    · have hc' : (appendCell c₁ c₂).val (Fin.natAdd N₁ j₂) ≠ none := by
        rw [appendCell_val, Fin.append_right]; exact hc
      rw [substFun_of_some _ _ hc', subst_val, substFun_of_some c₂ a₂ hc, appendCell_val,
        Fin.append_right]

theorem appendCell_topCell (m n : ℕ) :
    appendCell (topCell m) (topCell n) = topCell (m + n) :=
  appendCell_const rfl rfl rfl

/-! ### All-`none` sign vectors (the shape of every coherence morphism) -/

/-- A sign vector with no fixed coordinate: the sign of an identity or of an `eqToHom`. -/
def AllNone (c : Cell N n) : Prop := ∀ j, c.val j = none

theorem allNone_topCell (n : ℕ) : AllNone (topCell n) := fun _ => rfl

theorem allNone_dim {c : Cell N n} (h : AllNone c) : N = n := by
  have huniv : noneSet c.val = Finset.univ := by
    ext j; simp [mem_noneSet, h j]
  have hc := c.prop
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hc
  exact hc

/-- **…and conversely**: a cell that drops no dimension frees every coordinate.  This is what
makes a dimension-preserving `Box` map unique. -/
theorem allNone_of_dim {c : Cell N n} (h : N = n) : AllNone c := fun j =>
  mem_noneSet.mp (Finset.eq_univ_of_card _ (by rw [c.prop, Fintype.card_fin, h]) ▸
    Finset.mem_univ j)

theorem nones_allNone {c : Cell N n} (h : AllNone c) (i : Fin n) :
    nones c i = Fin.cast (allNone_dim h).symm i := by
  have key : (Fin.castOrderIso (allNone_dim h).symm).toOrderEmbedding = nones c :=
    Finset.orderEmbOfFin_unique' c.prop (fun x => mem_noneSet.mpr (h _))
  exact (congrArg (fun e : Fin n ↪o Fin N => e i) key).symm

theorem nonesIdx_allNone {c : Cell N n} (h : AllNone c) (j : Fin N)
    (hj : j ∈ noneSet c.val) : nonesIdx c j hj = Fin.cast (allNone_dim h) j := by
  apply (nones c).injective
  rw [nones_nonesIdx, nones_allNone h]
  simp

theorem subst_allNone_left {c : Cell N n} (h : AllNone c) (a : Cell n k) (j : Fin N) :
    (subst c a).val j = a.val (Fin.cast (allNone_dim h) j) := by
  rw [subst_val, substFun_of_none c a (h j), nonesIdx_allNone h]

theorem subst_allNone_right (c : Cell N n) {a : Cell n k} (h : AllNone a) (j : Fin N) :
    (subst c a).val j = c.val j := by
  by_cases hc : c.val j = none
  · rw [subst_val, substFun_of_none c a hc, h, hc]
  · rw [subst_val, substFun_of_some c a hc]

end StdCube

/-! ## The monoidal structure on `Box` -/

namespace Box

open StdCube

/-- **A `Box` map that drops no dimension is unique** — its sign frees every coordinate, so
there is nothing left to choose.  Every coherence morphism of the tensor is of this shape. -/
theorem hom_ext_dim {X Y : Box} {f g : X ⟶ Y} (h : Y.dim = X.dim) : f = g :=
  hom_ext (Subtype.ext (funext fun j =>
    (allNone_of_dim (c := sign f) h j).trans (allNone_of_dim (c := sign g) h j).symm))

/-- **A naturality square against coherence morphisms**: `v` and `w` free no coordinate, so the
two sides read as `sign u` and `sign x`, at the same index up to the dimension recast. -/
theorem comp_ext_allNone {A B C D : Box} {u : A ⟶ B} {v : B ⟶ D} {w : A ⟶ C} {x : C ⟶ D}
    (hv : AllNone (sign v)) (hw : AllNone (sign w))
    (h : ∀ j, (sign u).val (Fin.cast (allNone_dim hv) j) = (sign x).val j) : u ≫ v = w ≫ x :=
  hom_ext (Subtype.ext (funext fun j => by
    rw [sign_comp, sign_comp, subst_allNone_left hv, subst_allNone_right _ hw]
    exact h j))

/-! ### The tensor -/

/-- `▫m ⊗ ▫n = ▫(m + n)`. -/
def tensorObj (X Y : Box) : Box := ob (X.dim + Y.dim)

/-- Tensor of morphisms: concatenation of sign vectors. -/
def tensorHom {X Y Z W : Box} (f : X ⟶ Y) (g : Z ⟶ W) :
    tensorObj X Z ⟶ tensorObj Y W :=
  ofSign (appendCell (sign f) (sign g))

theorem tensorObj_assoc (X Y Z : Box) :
    tensorObj (tensorObj X Y) Z = tensorObj X (tensorObj Y Z) := by
  change ob (X.dim + Y.dim + Z.dim) = ob (X.dim + (Y.dim + Z.dim))
  rw [Nat.add_assoc]

theorem zero_tensorObj (X : Box) : tensorObj (ob 0) X = X := by
  change ob (0 + X.dim) = X
  rw [Nat.zero_add]

theorem tensorObj_zero (X : Box) : tensorObj X (ob 0) = X := rfl

instance monoidalStruct : MonoidalCategoryStruct Box where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := ob 0
  associator X Y Z := eqToIso (tensorObj_assoc X Y Z)
  leftUnitor X := eqToIso (zero_tensorObj X)
  rightUnitor X := eqToIso (tensorObj_zero X)

@[simp] theorem tensorObj_dim (X Y : Box) : (X ⊗ Y).dim = X.dim + Y.dim := rfl

@[simp] theorem tensorUnit_dim : (𝟙_ Box).dim = 0 := rfl

@[simp] theorem sign_tensorHom {X Y Z W : Box} (f : X ⟶ Y) (g : Z ⟶ W) :
    sign (f ⊗ₘ g) = appendCell (sign f) (sign g) := sign_ofSign _

/-! The three structural isos are `eqToIso`s of dimension equalities, so each `.hom` frees no
coordinate — `allNone_of_dim` at the corresponding `ℕ`-identity. -/

theorem allNone_sign_associator (X Y Z : Box) : AllNone (sign (α_ X Y Z).hom) :=
  allNone_of_dim (Nat.add_assoc X.dim Y.dim Z.dim).symm

theorem allNone_sign_leftUnitor (X : Box) : AllNone (sign (λ_ X).hom) :=
  allNone_of_dim (Nat.zero_add X.dim).symm

theorem allNone_sign_rightUnitor (X : Box) : AllNone (sign (ρ_ X).hom) :=
  allNone_of_dim rfl

theorem sign_tensorHom_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Box} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    sign ((f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂)) = sign ((f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)) := by
  rw [sign_comp, sign_tensorHom, sign_tensorHom, sign_tensorHom, sign_comp, sign_comp]
  exact subst_appendCell _ _ _ _

instance monoidal : MonoidalCategory Box :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X Y => by
      apply hom_ext
      rw [sign_tensorHom, sign_id, sign_id, appendCell_topCell, sign_id]
      rfl)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => hom_ext (sign_tensorHom_comp f₁ f₂ g₁ g₂))
    (associator_naturality := fun f₁ f₂ f₃ =>
      comp_ext_allNone (allNone_sign_associator _ _ _) (allNone_sign_associator _ _ _) (fun j => by
        rw [sign_tensorHom, sign_tensorHom, sign_tensorHom, sign_tensorHom,
          appendCell_val, appendCell_val, appendCell_val, appendCell_val]
        exact congrFun (Fin.append_assoc _ _ _) _))
    (leftUnitor_naturality := fun f =>
      comp_ext_allNone (allNone_sign_leftUnitor _) (allNone_sign_leftUnitor _) (fun j => by
        rw [sign_tensorHom, sign_id, appendCell_val]
        exact congrFun (Fin.append_left_nil _ _ rfl) _))
    (rightUnitor_naturality := fun f =>
      comp_ext_allNone (allNone_sign_rightUnitor _) (allNone_sign_rightUnitor _) (fun j => by
        rw [sign_tensorHom, sign_id, appendCell_val]
        exact congrFun (Fin.append_right_nil _ _ rfl) _))
    (pentagon := fun W X Y Z => hom_ext_dim (by simp only [tensorObj_dim]; omega))
    (triangle := fun X Y => hom_ext_dim (by simp only [tensorObj_dim, tensorUnit_dim]; omega))

end Box

/-! ## The free-coordinate embedding of a cube face

A `k`-face `f : ▫k ⟶ ▫m` has `k` free (`none`) coordinates; `faceEmb f` enumerates them in
increasing order.  It lives in the root namespace because it is used unqualified throughout. -/

open StdCube in
/-- The order embedding of the free coordinates of a cube face `f : ▫k ⟶ ▫m`. -/
def faceEmb {k m : ℕ} (f : ▫k ⟶ ▫m) : Fin k ↪o Fin m := nones (Box.sign f)

theorem faceEmb_id (k : ℕ) (x : Fin k) : faceEmb (𝟙 ▫k) x = x := StdCube.nones_topCell k x

/-- `faceEmb` is functorial: substitution composes the free-coordinate enumerations. -/
theorem faceEmb_comp {k e m : ℕ} (p : ▫k ⟶ ▫e) (q : ▫e ⟶ ▫m) (x : Fin k) :
    faceEmb (p ≫ q) x = faceEmb q (faceEmb p x) := by
  change StdCube.nones (Box.sign (p ≫ q)) x = _
  rw [Box.sign_comp]
  exact StdCube.nones_subst _ _ x

