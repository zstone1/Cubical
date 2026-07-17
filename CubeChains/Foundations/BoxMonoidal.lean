import CubeChains.Foundations.Representable
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Foundations/BoxMonoidal

The **parallel tensor** on the box category: `▫m ⊗ ▫n = ▫(m + n)`, on morphisms the
*concatenation of sign vectors*.

Via cube Yoneda a morphism `▫m ⟶ ▫n` is a sign vector `Cell n m` (`Fin n → Option Bool`
with exactly `m` `none`s), composition is **substitution** (`subst`: plug the source vector
into the free coordinates of the target vector), and the tensor is `Fin.append`.  The whole
monoidal structure is therefore sign-vector algebra; `sign` (= `ev`) is the bridge.

The associator and both unitors are `eqToIso` of `Nat.add_assoc`/`add_zero`/`zero_add`: the
structure is strict on the nose except for these `ℕ`-transports.  Every coherence morphism has
an **all-`none`** sign vector, and two `Box` maps with all-`none` signs are equal
(`hom_ext_allNone`) — that is what discharges pentagon and triangle.

**`Box` is not braided.**  A `Box` morphism cannot permute coordinates (the symmetry-free
convention), so there is no block swap `▫(m+n) ⟶ ▫(n+m)`; do not look for one.  The braiding
of the geometric product lives one level up, between *cube chains* of `K ⊗ L`, not here.
-/

open CategoryTheory MonoidalCategory

namespace StdCube

/-! ### Substitution of sign vectors

`subst c a` plugs the cell `a` of `□ⁿ` into the free coordinates of `c : Cell N n`; it is
composition in `Box`, computed (`act_eq_subst`). -/

variable {N n k : ℕ}

theorem nones_mem (c : Cell N n) (i : Fin n) : nones c i ∈ noneSet c.val :=
  Finset.orderEmbOfFin_mem _ c.prop i

theorem val_nones (c : Cell N n) (i : Fin n) : c.val (nones c i) = none :=
  mem_noneSet.mp (nones_mem c i)

theorem nonesIdx_nones (c : Cell N n) (i : Fin n) (h : nones c i ∈ noneSet c.val) :
    nonesIdx c (nones c i) h = i :=
  (nones c).injective (nones_nonesIdx c (nones c i) h)

/-- The raw substituted sign vector: keep the fixed coordinates of `c`, and fill its `i`-th
free coordinate with the `i`-th entry of `a`. -/
def substFun (c : Cell N n) (a : Cell n k) : Fin N → Option Bool := fun j =>
  if h : c.val j = none then a.val (nonesIdx c j (mem_noneSet.mpr h)) else c.val j

theorem substFun_of_none (c : Cell N n) (a : Cell n k) {j : Fin N} (h : c.val j = none) :
    substFun c a j = a.val (nonesIdx c j (mem_noneSet.mpr h)) := dif_pos h

theorem substFun_of_some (c : Cell N n) (a : Cell n k) {j : Fin N} (h : c.val j ≠ none) :
    substFun c a j = c.val j := dif_neg h

theorem noneSet_substFun (c : Cell N n) (a : Cell n k) :
    noneSet (substFun c a) = (noneSet a.val).map (nones c).toEmbedding := by
  ext j
  rw [mem_noneSet, Finset.mem_map]
  constructor
  · intro hj
    by_cases hc : c.val j = none
    · refine ⟨nonesIdx c j (mem_noneSet.mpr hc), ?_, nones_nonesIdx c j _⟩
      rw [substFun_of_none c a hc] at hj
      rwa [mem_noneSet]
    · rw [substFun_of_some c a hc] at hj
      exact absurd hj hc
  · rintro ⟨i, hi, rfl⟩
    change substFun c a (nones c i) = none
    rw [substFun_of_none c a (val_nones c i), nonesIdx_nones]
    rwa [mem_noneSet] at hi

/-- Substitution: plug `a` into the free coordinates of `c`. -/
def subst (c : Cell N n) (a : Cell n k) : Cell N k :=
  ⟨substFun c a, by rw [noneSet_substFun, Finset.card_map, a.prop]⟩

@[simp] theorem subst_val (c : Cell N n) (a : Cell n k) : (subst c a).val = substFun c a := rfl

theorem nones_subst (c : Cell N n) (a : Cell n k) (i : Fin k) :
    nones (subst c a) i = nones c (nones a i) := by
  have key : (nones a).trans (nones c) = nones (subst c a) := by
    refine Finset.orderEmbOfFin_unique' (subst c a).prop (fun x => ?_)
    rw [mem_noneSet]
    change substFun c a (nones c (nones a x)) = none
    rw [substFun_of_none c a (val_nones c _), nonesIdx_nones]
    exact val_nones a x
  exact (congrArg (fun e : Fin k ↪o Fin N => e i) key).symm

theorem subst_topCell (c : Cell N n) : subst c (topCell n) = c := by
  apply Subtype.ext
  funext j
  rw [subst_val]
  by_cases h : c.val j = none
  · rw [substFun_of_none c _ h]
    exact h.symm
  · rw [substFun_of_some c _ h]

theorem subst_faceCell (c : Cell N n) {k : ℕ} (ε : Bool) (i : Fin (k + 1))
    (a : Cell n (k + 1)) :
    subst c (faceCell ε i a) = faceCell ε i (subst c a) := by
  apply Subtype.ext
  rw [face_val, subst_val, subst_val, nones_subst]
  funext j
  by_cases hj : j = nones c (nones a i)
  · subst hj
    rw [Function.update_self, substFun_of_none c _ (val_nones c _), nonesIdx_nones, face_val,
      Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hc : c.val j = none
    · have hne : nonesIdx c j (mem_noneSet.mpr hc) ≠ nones a i := by
        intro hcontra
        exact hj (by rw [← nones_nonesIdx c j (mem_noneSet.mpr hc), hcontra])
      rw [substFun_of_none c _ hc, substFun_of_none c a hc, face_val,
        Function.update_of_ne hne]
    · rw [substFun_of_some c _ hc, substFun_of_some c a hc]

/-- Substitution as a precubical map `□ⁿ ⟶ □ᴺ` — the canonical map of `c`, computed. -/
def substMap (c : Cell N n) : PrecubicalConstructions.Hom (stdPre n) (stdPre N) where
  app _k a := subst c a
  app_face ε i a := subst_faceCell c ε i a

/-- The iterated-face description of the canonical map is substitution. -/
theorem act_eq_subst (c : Cell N n) (a : Cell n k) :
    act (K := stdPre N) c a = subst c a :=
  (app_unique (K := stdPre N) (c := c) (substMap c) (subst_topCell c) a).symm

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

/-- Block concatenation of two order embeddings, as a plain function. -/
def addFun (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) : Fin (n₁ + n₂) → Fin (N₁ + N₂) :=
  Fin.addCases (fun i₁ => Fin.castAdd N₂ (e₁ i₁)) (fun i₂ => Fin.natAdd N₁ (e₂ i₂))

@[simp] theorem addFun_castAdd (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) (i : Fin n₁) :
    addFun e₁ e₂ (Fin.castAdd n₂ i) = Fin.castAdd N₂ (e₁ i) := Fin.addCases_left _

@[simp] theorem addFun_natAdd (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) (i : Fin n₂) :
    addFun e₁ e₂ (Fin.natAdd n₁ i) = Fin.natAdd N₁ (e₂ i) := Fin.addCases_right _

theorem addFun_strictMono (e₁ : Fin n₁ ↪o Fin N₁) (e₂ : Fin n₂ ↪o Fin N₂) :
    StrictMono (addFun e₁ e₂) := by
  intro i j hij
  cases i using Fin.addCases with
  | left i₁ =>
    cases j using Fin.addCases with
    | left j₁ =>
      rw [addFun_castAdd, addFun_castAdd]
      have hlt : i₁ < j₁ := by
        rw [Fin.lt_def] at hij ⊢
        rw [Fin.val_castAdd, Fin.val_castAdd] at hij
        exact hij
      have he := e₁.strictMono hlt
      rw [Fin.lt_def] at he ⊢
      rw [Fin.val_castAdd, Fin.val_castAdd]
      exact he
    | right j₂ =>
      rw [addFun_castAdd, addFun_natAdd, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      have := (e₁ i₁).isLt
      omega
  | right i₂ =>
    cases j using Fin.addCases with
    | left j₁ =>
      exfalso
      rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hij
      have := j₁.isLt
      omega
    | right j₂ =>
      rw [addFun_natAdd, addFun_natAdd]
      have hlt : i₂ < j₂ := by
        rw [Fin.lt_def] at hij ⊢
        rw [Fin.val_natAdd, Fin.val_natAdd] at hij
        omega
      have he := e₂.strictMono hlt
      rw [Fin.lt_def] at he ⊢
      rw [Fin.val_natAdd, Fin.val_natAdd]
      omega

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
    appendCell (topCell m) (topCell n) = topCell (m + n) := by
  apply Subtype.ext
  funext j
  rw [appendCell_val]
  cases j using Fin.addCases with
  | left i => rw [Fin.append_left]; rfl
  | right i => rw [Fin.append_right]; rfl

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

theorem allNone_appendCell {c₁ : Cell N₁ n₁} {c₂ : Cell N₂ n₂}
    (h₁ : AllNone c₁) (h₂ : AllNone c₂) : AllNone (appendCell c₁ c₂) := by
  intro j
  rw [appendCell_val]
  cases j using Fin.addCases with
  | left i => rw [Fin.append_left]; exact h₁ i
  | right i => rw [Fin.append_right]; exact h₂ i

theorem allNone_subst {c : Cell N n} {a : Cell n k} (hc : AllNone c) (ha : AllNone a) :
    AllNone (subst c a) := fun j => (subst_allNone_right c ha j).trans (hc j)

/-- Appending on the left of an empty block is a `Fin.cast`. -/
theorem append_zero_left {α : Type*} {M : ℕ} (u : Fin 0 → α) (v : Fin M → α)
    (j : Fin (0 + M)) : Fin.append u v j = v (Fin.cast (Nat.zero_add M) j) := by
  cases j using Fin.addCases with
  | left i => exact i.elim0
  | right i =>
    rw [Fin.append_right]
    congr 1
    apply Fin.ext
    simp

/-- Appending on the right of an empty block is a `Fin.cast`. -/
theorem append_zero_right {α : Type*} {M : ℕ} (u : Fin M → α) (v : Fin 0 → α)
    (j : Fin (M + 0)) : Fin.append u v j = u (Fin.cast (Nat.add_zero M) j) := by
  cases j using Fin.addCases with
  | left i =>
    have hcast : Fin.cast (Nat.add_zero M) (Fin.castAdd 0 i) = i := by apply Fin.ext; simp
    rw [Fin.append_left, hcast]
  | right i => exact i.elim0

end StdCube

/-! ## The monoidal structure on `Box` -/

namespace Box

open StdCube

/-- The sign vector of a `Box` morphism (cube Yoneda: `(X ⟶ Y) ≃ Cell Y.dim X.dim`). -/
def sign {X Y : Box} (f : X ⟶ Y) : Cell Y.dim X.dim :=
  StdCube.ev (K := stdPre Y.dim) (n := X.dim) f

/-- The `Box` morphism classified by a sign vector. -/
def ofSign {X Y : Box} (c : Cell Y.dim X.dim) : X ⟶ Y :=
  StdCube.canonicalMap (K := stdPre Y.dim) (n := X.dim) c

@[simp] theorem sign_ofSign {X Y : Box} (c : Cell Y.dim X.dim) : sign (ofSign c) = c :=
  ev_canonicalMap (K := stdPre Y.dim) (n := X.dim) c

theorem hom_ext {X Y : Box} {f g : X ⟶ Y} (h : sign f = sign g) : f = g :=
  (cubeRepr (stdPre Y.dim) X.dim).injective h

@[simp] theorem sign_id (X : Box) : sign (𝟙 X) = topCell X.dim := rfl

theorem sign_comp {X Y Z : Box} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sign (f ≫ g) = subst (sign g) (sign f) := by
  have h1 : sign (f ≫ g)
      = PrecubicalConstructions.Hom.app (K := stdPre Y.dim) (L := stdPre Z.dim) g X.dim
        (sign f) := rfl
  rw [h1, ← act_eq_subst]
  exact app_unique (K := stdPre Z.dim) (c := sign g) g rfl (sign f)

theorem hom_ext_allNone {X Y : Box} {f g : X ⟶ Y} (hf : AllNone (sign f))
    (hg : AllNone (sign g)) : f = g :=
  hom_ext (Subtype.ext (funext fun j => (hf j).trans (hg j).symm))

theorem allNone_sign_id (X : Box) : AllNone (sign (𝟙 X)) := allNone_topCell _

theorem allNone_sign_comp {X Y Z : Box} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : AllNone (sign f)) (hg : AllNone (sign g)) : AllNone (sign (f ≫ g)) := by
  rw [sign_comp]; exact allNone_subst hg hf

theorem allNone_sign_eqToHom {X Y : Box} (h : X = Y) : AllNone (sign (eqToHom h)) := by
  cases h
  rw [eqToHom_refl]
  exact allNone_sign_id _


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

@[simp] theorem sign_tensorHom {X Y Z W : Box} (f : X ⟶ Y) (g : Z ⟶ W) :
    sign (f ⊗ₘ g) = appendCell (sign f) (sign g) := sign_ofSign _

theorem associator_hom_eq (X Y Z : Box) :
    (α_ X Y Z).hom = eqToHom (tensorObj_assoc X Y Z) := rfl

theorem leftUnitor_hom_eq (X : Box) : (λ_ X).hom = eqToHom (zero_tensorObj X) := rfl

theorem rightUnitor_hom_eq (X : Box) : (ρ_ X).hom = eqToHom (tensorObj_zero X) := rfl

theorem allNone_sign_tensorHom {X Y Z W : Box} {f : X ⟶ Y} {g : Z ⟶ W}
    (hf : AllNone (sign f)) (hg : AllNone (sign g)) : AllNone (sign (f ⊗ₘ g)) := by
  rw [sign_tensorHom]; exact allNone_appendCell hf hg

theorem allNone_sign_associator (X Y Z : Box) : AllNone (sign (α_ X Y Z).hom) := by
  rw [associator_hom_eq]; exact allNone_sign_eqToHom _

theorem allNone_sign_leftUnitor (X : Box) : AllNone (sign (λ_ X).hom) := by
  rw [leftUnitor_hom_eq]; exact allNone_sign_eqToHom _

theorem allNone_sign_rightUnitor (X : Box) : AllNone (sign (ρ_ X).hom) := by
  rw [rightUnitor_hom_eq]; exact allNone_sign_eqToHom _

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
    (associator_naturality := fun f₁ f₂ f₃ => by
      apply hom_ext
      apply Subtype.ext
      funext j
      rw [sign_comp, sign_comp,
        subst_allNone_left (allNone_sign_associator _ _ _),
        subst_allNone_right _ (allNone_sign_associator _ _ _),
        sign_tensorHom, sign_tensorHom, sign_tensorHom, sign_tensorHom,
        appendCell_val, appendCell_val, appendCell_val, appendCell_val]
      exact congrFun (Fin.append_assoc _ _ _) _)
    (leftUnitor_naturality := fun {X Y} f => by
      apply hom_ext
      apply Subtype.ext
      funext j
      rw [sign_comp, sign_comp,
        subst_allNone_left (allNone_sign_leftUnitor _),
        subst_allNone_right _ (allNone_sign_leftUnitor _),
        sign_tensorHom, sign_id, appendCell_val]
      exact append_zero_left _ _ _)
    (rightUnitor_naturality := fun {X Y} f => by
      apply hom_ext
      apply Subtype.ext
      funext j
      rw [sign_comp, sign_comp,
        subst_allNone_left (allNone_sign_rightUnitor _),
        subst_allNone_right _ (allNone_sign_rightUnitor _),
        sign_tensorHom, sign_id, appendCell_val]
      exact append_zero_right _ _ _)
    (pentagon := fun W X Y Z =>
      hom_ext_allNone
        (allNone_sign_comp
          (allNone_sign_tensorHom (allNone_sign_associator W X Y) (allNone_sign_id Z))
          (allNone_sign_comp (allNone_sign_associator W (X ⊗ Y) Z)
            (allNone_sign_tensorHom (allNone_sign_id W) (allNone_sign_associator X Y Z))))
        (allNone_sign_comp (allNone_sign_associator (W ⊗ X) Y Z)
          (allNone_sign_associator W X (Y ⊗ Z))))
    (triangle := fun X Y =>
      hom_ext_allNone
        (allNone_sign_comp (allNone_sign_associator X (𝟙_ Box) Y)
          (allNone_sign_tensorHom (allNone_sign_id X) (allNone_sign_leftUnitor Y)))
        (allNone_sign_tensorHom (allNone_sign_rightUnitor X) (allNone_sign_id Y)))

end Box
