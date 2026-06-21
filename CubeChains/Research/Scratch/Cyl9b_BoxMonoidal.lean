import CubeChains.Foundations.Shift
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Research/Scratch/Cyl9b_BoxMonoidal

Feasibility scratch: a `MonoidalCategory Box` whose object tensor is addition of
dimensions, `⟨a⟩ ⊗ ⟨b⟩ = ⟨a + b⟩`, and whose morphism tensor juxtaposes cells via
`Fin.append`.

This is a SELF-CONTAINED scratch file; it touches nothing else.
-/

open CategoryTheory Opposite

namespace StdCube

variable {N : ℕ}

/-! ### `noneSet` cardinality under `Fin.append` -/

/-- The `none`-count of an append is the sum of the `none`-counts. -/
theorem card_noneSet_append {m n : ℕ} (u : Fin m → Option Bool) (v : Fin n → Option Bool) :
    (noneSet (Fin.append u v)).card = (noneSet u).card + (noneSet v).card := by
  rw [card_noneSet_eq_sum, card_noneSet_eq_sum, card_noneSet_eq_sum, Fin.sum_univ_add]
  congr 1 <;>
  · apply Finset.sum_congr rfl
    intro j _
    simp

/-! ### Prepending a free coordinate (`consFree`)

Mirror of `snocFree`, but at the *front* of the cell.  The combinatorial crux
`app_consFree` is proved exactly like `app_snocFree`. -/

/-- Prepending a coordinate `e` adds one `none` iff `e = none`. -/
theorem card_noneSet_cons {n : ℕ} (v : Fin n → Option Bool) (e : Option Bool) :
    (noneSet (Fin.cons e v)).card = (if e = none then 1 else 0) + (noneSet v).card := by
  rw [card_noneSet_eq_sum (Fin.cons e v), Fin.sum_univ_succ, card_noneSet_eq_sum v]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Prepend a free (`none`) first coordinate to a `k`-cell, giving a `(k+1)`-cell. -/
def consFree {k : ℕ} (a : cells N k) : cells (N + 1) (k + 1) :=
  ⟨Fin.cons none a.val, by rw [card_noneSet_cons, a.prop]; simp [Nat.add_comm]⟩

@[simp] theorem consFree_val {k : ℕ} (a : cells N k) :
    (consFree a).val = Fin.cons none a.val := rfl

/-- The `none`-positions of `consFree a`: the new first coordinate `0`, then the
prefix ones via `succ`. -/
theorem nones_consFree {k : ℕ} (a : cells N k) :
    (nones (consFree a) : Fin (k + 1) → Fin (N + 1))
      = Fin.cases (0 : Fin (N + 1)) (fun x => Fin.succ (nones a x)) := by
  refine (Finset.orderEmbOfFin_unique (consFree a).prop ?_ ?_).symm
  · intro y
    rw [mem_noneSet]
    refine Fin.cases ?_ ?_ y
    · simp only [Fin.cases_zero, consFree_val, Fin.cons_zero]
    · intro x
      simp only [Fin.cases_succ, consFree_val, Fin.cons_succ]
      rw [← mem_noneSet]; exact Finset.orderEmbOfFin_mem _ a.prop x
  · intro p q
    refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q <;> intro hpq
    · exact absurd hpq (lt_irrefl _)
    · simp only [Fin.cases_zero, Fin.cases_succ]
      exact Fin.succ_pos _
    · exact absurd hpq (Fin.not_lt_zero _)
    · simp only [Fin.cases_succ]
      exact Fin.succ_lt_succ_iff.mpr
        ((nones a).strictMono (Fin.succ_lt_succ_iff.mp hpq))

theorem nones_consFree_succ {k : ℕ} (a : cells N k) (x : Fin k) :
    nones (consFree a) (Fin.succ x) = Fin.succ (nones a x) := by
  have h := congrFun (nones_consFree a) (Fin.succ x)
  simpa using h

theorem nones_consFree_zero {k : ℕ} (a : cells N k) :
    nones (consFree a) (0 : Fin (k + 1)) = 0 := by
  have h := congrFun (nones_consFree a) (0 : Fin (k + 1))
  simpa using h

/-- The top cell prepends to the top cell. -/
theorem consFree_topCell (N : ℕ) : consFree (topCell N) = topCell (N + 1) := by
  apply Subtype.ext
  rw [consFree_val]
  funext q
  refine Fin.cases ?_ ?_ q
  · rw [Fin.cons_zero]; rfl
  · intro q'; rw [Fin.cons_succ]; rfl

/-- Facing a non-front coordinate commutes with `consFree`. -/
theorem face_consFree_succ {k : ℕ} (X : cells N (k + 1)) (ε : Bool) (i : Fin (k + 1)) :
    face ε (Fin.succ i) (consFree X) = consFree (face ε i X) := by
  apply Subtype.ext
  simp only [face_val, consFree_val, nones_consFree_succ, Fin.cons_update]

/-- The single combinatorial crux for prepend: `app` commutes with `consFree`. -/
theorem app_consFree {P : ℕ} (c : cells P N) {k : ℕ} (a : cells N k) :
    sapp (consFree c) (consFree a) = consFree (sapp c a) := by
  induction hd : N - k using Nat.strong_induction_on generalizing k a with
  | _ d ih =>
    rcases Nat.lt_or_ge k N with hlt | hge
    · have hstep : sapp (consFree c) (consFree (freeMin a hlt))
          = consFree (sapp c (freeMin a hlt)) := ih (N - (k + 1)) (by omega) (freeMin a hlt) rfl
      calc sapp (consFree c) (consFree a)
          = sapp (consFree c)
              (consFree (face (minFixedVal a hlt) (minFixedIdx a hlt) (freeMin a hlt))) := by
            rw [face_freeMin]
        _ = sapp (consFree c) (face (minFixedVal a hlt) (Fin.succ (minFixedIdx a hlt))
              (consFree (freeMin a hlt))) := by rw [face_consFree_succ]
        _ = face (minFixedVal a hlt) (Fin.succ (minFixedIdx a hlt))
              (sapp (consFree c) (consFree (freeMin a hlt))) := sapp_face _ _ _ _
        _ = face (minFixedVal a hlt) (Fin.succ (minFixedIdx a hlt))
              (consFree (sapp c (freeMin a hlt))) := by rw [hstep]
        _ = consFree (face (minFixedVal a hlt) (minFixedIdx a hlt) (sapp c (freeMin a hlt))) := by
            rw [face_consFree_succ]
        _ = consFree (sapp c a) := by rw [← sapp_unfold c a hlt]
    · have hkn : k = N := le_antisymm (cells_card_le a) hge
      subst hkn
      rw [eq_topCell a, consFree_topCell, sapp_topCell, sapp_topCell]

/-! ### Juxtaposition of cells (`tensorCell` via `Fin.append`) -/

/-- Updating a right-block coordinate of an append. -/
theorem append_update_right {m n : ℕ} {α : Type*} (u : Fin m → α) (v : Fin n → α)
    (j : Fin n) (x : α) :
    Function.update (Fin.append u v) (Fin.natAdd m j) x
      = Fin.append u (Function.update v j x) := by
  funext q
  refine Fin.addCases (fun p => ?_) (fun p => ?_) q
  · rw [Function.update_of_ne, Fin.append_left, Fin.append_left]
    intro h
    rw [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at h
    have := p.isLt; omega
  · rw [Fin.append_right]
    by_cases hpj : p = j
    · subst hpj; rw [Function.update_self, Function.update_self]
    · have hne : (Fin.natAdd m p) ≠ (Fin.natAdd m j) := by
        intro h; apply hpj
        rw [Fin.ext_iff, Fin.val_natAdd, Fin.val_natAdd] at h
        exact Fin.ext (by omega)
      rw [Function.update_of_ne hne, Function.update_of_ne hpj, Fin.append_right]

/-- Updating a left-block coordinate of an append. -/
theorem append_update_left {m n : ℕ} {α : Type*} (u : Fin m → α) (v : Fin n → α)
    (j : Fin m) (x : α) :
    Function.update (Fin.append u v) (Fin.castAdd n j) x
      = Fin.append (Function.update u j x) v := by
  funext q
  refine Fin.addCases (fun p => ?_) (fun p => ?_) q
  · rw [Fin.append_left]
    by_cases hpj : p = j
    · subst hpj; rw [Function.update_self, Function.update_self]
    · have hne : (Fin.castAdd n p) ≠ (Fin.castAdd n j) := by
        intro h; apply hpj
        rw [Fin.ext_iff, Fin.val_castAdd, Fin.val_castAdd] at h
        exact Fin.ext h
      rw [Function.update_of_ne hne, Function.update_of_ne hpj, Fin.append_left]
  · rw [Function.update_of_ne, Fin.append_right, Fin.append_right]
    intro h
    rw [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at h
    have := j.isLt; omega

/-- Juxtapose a `k₁`-cell of `□^{N₁}` and a `k₂`-cell of `□^{N₂}` into a
`(k₁+k₂)`-cell of `□^{N₁+N₂}`. -/
def tensorCell {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ k₂) :
    cells (N₁ + N₂) (k₁ + k₂) :=
  ⟨Fin.append a₁.val a₂.val, by rw [card_noneSet_append, a₁.prop, a₂.prop]⟩

@[simp] theorem tensorCell_val {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ k₂) :
    (tensorCell a₁ a₂).val = Fin.append a₁.val a₂.val := rfl

/-- The `none`-positions of `tensorCell a₁ a₂`: the left block's positions (via
`castAdd`) then the right block's (via `natAdd`). -/
theorem nones_tensorCell {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ k₂) :
    (nones (tensorCell a₁ a₂) : Fin (k₁ + k₂) → Fin (N₁ + N₂))
      = Fin.addCases (fun x => Fin.castAdd N₂ (nones a₁ x))
          (fun y => Fin.natAdd N₁ (nones a₂ y)) := by
  refine (Finset.orderEmbOfFin_unique (tensorCell a₁ a₂).prop ?_ ?_).symm
  · intro y
    rw [mem_noneSet]
    refine Fin.addCases (fun x => ?_) (fun x => ?_) y
    · simp only [Fin.addCases_left, tensorCell_val, Fin.append_left]
      rw [← mem_noneSet]; exact Finset.orderEmbOfFin_mem _ a₁.prop x
    · simp only [Fin.addCases_right, tensorCell_val, Fin.append_right]
      rw [← mem_noneSet]; exact Finset.orderEmbOfFin_mem _ a₂.prop x
  · intro p q
    refine Fin.addCases (fun p' => ?_) (fun p' => ?_) p <;>
      refine Fin.addCases (fun q' => ?_) (fun q' => ?_) q <;> intro hpq
    · simp only [Fin.addCases_left]
      refine (Fin.strictMono_castAdd N₂) ((nones a₁).strictMono ?_)
      rw [Fin.lt_def, Fin.val_castAdd, Fin.val_castAdd] at hpq
      exact Fin.lt_def.mpr hpq
    · simp only [Fin.addCases_left, Fin.addCases_right]
      rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      have := (nones a₁ p').isLt
      omega
    · exfalso
      rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hpq
      have := (nones a₁ q').isLt
      omega
    · simp only [Fin.addCases_right]
      refine (Fin.strictMono_natAdd N₁) ((nones a₂).strictMono ?_)
      rw [Fin.lt_def, Fin.val_natAdd, Fin.val_natAdd] at hpq
      exact Fin.lt_def.mpr (by omega)

theorem nones_tensorCell_castAdd {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ k₂)
    (x : Fin k₁) :
    nones (tensorCell a₁ a₂) (Fin.castAdd k₂ x) = Fin.castAdd N₂ (nones a₁ x) := by
  have h := congrFun (nones_tensorCell a₁ a₂) (Fin.castAdd k₂ x)
  simpa using h

theorem nones_tensorCell_natAdd {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ k₂)
    (y : Fin k₂) :
    nones (tensorCell a₁ a₂) (Fin.natAdd k₁ y) = Fin.natAdd N₁ (nones a₂ y) := by
  have h := congrFun (nones_tensorCell a₁ a₂) (Fin.natAdd k₁ y)
  simpa using h

/-- The top cells juxtapose to the top cell. -/
theorem tensorCell_topCell (N₁ N₂ : ℕ) :
    tensorCell (topCell N₁) (topCell N₂) = topCell (N₁ + N₂) := by
  apply Subtype.ext
  rw [tensorCell_val]
  funext q
  refine Fin.addCases (fun x => ?_) (fun x => ?_) q
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- Juxtaposition with the grade written reassociated as `k₁ + k₂ + 1`, so that
the standard `face` (which needs the grade in `_ + 1` form) applies in the *left*
block.  Same underlying value as `tensorCell`. -/
def tensorCellL {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ (k₁ + 1)) (a₂ : cells N₂ k₂) :
    cells (N₁ + N₂) (k₁ + k₂ + 1) :=
  ⟨Fin.append a₁.val a₂.val, by rw [card_noneSet_append, a₁.prop, a₂.prop]; omega⟩

@[simp] theorem tensorCellL_val {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ (k₁ + 1))
    (a₂ : cells N₂ k₂) : (tensorCellL a₁ a₂).val = Fin.append a₁.val a₂.val := rfl

/-- `tensorCellL` and `tensorCell` share their underlying value (only the grade
index differs by associativity). -/
theorem nones_tensorCellL {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ (k₁ + 1)) (a₂ : cells N₂ k₂) :
    (nones (tensorCellL a₁ a₂) : Fin (k₁ + k₂ + 1) → Fin (N₁ + N₂))
      = Fin.addCases (fun x => Fin.castAdd N₂ (nones a₁ x))
          (fun y => Fin.natAdd N₁ (nones a₂ y)) ∘ Fin.cast (by omega) := by
  funext x
  rw [Function.comp_apply, ← congrFun (nones_tensorCell a₁ a₂) (Fin.cast (by omega) x)]
  -- both sides are `orderEmbOfFin` of the *same* finset (the underlying `append`)
  exact (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).mpr (by simp)

/-- Juxtaposition with the right factor one grade up, written at the reassociated
grade `k₁ + k₂ + 1` so the standard `face` applies in the *right* block. -/
def tensorCellR {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ (k₂ + 1)) :
    cells (N₁ + N₂) (k₁ + k₂ + 1) :=
  ⟨Fin.append a₁.val a₂.val, by rw [card_noneSet_append, a₁.prop, a₂.prop]; omega⟩

@[simp] theorem tensorCellR_val {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁)
    (a₂ : cells N₂ (k₂ + 1)) : (tensorCellR a₁ a₂).val = Fin.append a₁.val a₂.val := rfl

theorem nones_tensorCellR {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ (k₂ + 1)) :
    (nones (tensorCellR a₁ a₂) : Fin (k₁ + k₂ + 1) → Fin (N₁ + N₂))
      = Fin.addCases (fun x => Fin.castAdd N₂ (nones a₁ x))
          (fun y => Fin.natAdd N₁ (nones a₂ y)) ∘ Fin.cast (by omega) := by
  funext x
  rw [Function.comp_apply, ← congrFun (nones_tensorCell a₁ a₂) (Fin.cast (by omega) x)]
  exact (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).mpr (by simp)

/-- The right-block face index inside the (reassociated) juxtaposed cell. -/
def rightIdx (k₁ : ℕ) {k₂ : ℕ} (i : Fin (k₂ + 1)) : Fin (k₁ + k₂ + 1) :=
  Fin.cast (by omega) (Fin.natAdd k₁ i)

/-- The left-block face index inside the (reassociated) juxtaposed cell. -/
def leftIdx {k₁ : ℕ} (i : Fin (k₁ + 1)) (k₂ : ℕ) : Fin (k₁ + k₂ + 1) :=
  Fin.cast (by omega) (Fin.castAdd k₂ i)

theorem nones_tensorCellR_rightIdx {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁)
    (a₂ : cells N₂ (k₂ + 1)) (i : Fin (k₂ + 1)) :
    nones (tensorCellR a₁ a₂) (rightIdx k₁ i) = Fin.natAdd N₁ (nones a₂ i) := by
  have h := congrFun (nones_tensorCellR a₁ a₂) (rightIdx k₁ i)
  rw [h, Function.comp_apply, rightIdx]
  rw [show Fin.cast (by omega) (Fin.cast (by omega) (Fin.natAdd k₁ i))
      = (Fin.natAdd k₁ i : Fin (k₁ + (k₂ + 1))) from by apply Fin.ext; simp]
  rw [Fin.addCases_right]

theorem nones_tensorCellL_leftIdx {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ (k₁ + 1))
    (a₂ : cells N₂ k₂) (i : Fin (k₁ + 1)) :
    nones (tensorCellL a₁ a₂) (leftIdx i k₂) = Fin.castAdd N₂ (nones a₁ i) := by
  have h := congrFun (nones_tensorCellL a₁ a₂) (leftIdx i k₂)
  rw [h, Function.comp_apply, leftIdx]
  rw [show Fin.cast (by omega) (Fin.cast (by omega) (Fin.castAdd k₂ i))
      = (Fin.castAdd k₂ i : Fin ((k₁ + 1) + k₂)) from by apply Fin.ext; simp]
  rw [Fin.addCases_left]

/-- Facing in the right block commutes with juxtaposition (reassociated grade). -/
theorem face_tensorCellR_rightIdx {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ k₁)
    (a₂ : cells N₂ (k₂ + 1)) (ε : Bool) (i : Fin (k₂ + 1)) :
    face ε (rightIdx k₁ i) (tensorCellR a₁ a₂) = tensorCell a₁ (face ε i a₂) := by
  apply Subtype.ext
  rw [face_val, nones_tensorCellR_rightIdx, tensorCellR_val, tensorCell_val, face_val,
    append_update_right]

/-- Facing in the left block commutes with juxtaposition (reassociated grade). -/
theorem face_tensorCellL_leftIdx {N₁ N₂ k₁ k₂ : ℕ} (a₁ : cells N₁ (k₁ + 1))
    (a₂ : cells N₂ k₂) (ε : Bool) (i : Fin (k₁ + 1)) :
    face ε (leftIdx i k₂) (tensorCellL a₁ a₂) = tensorCell (face ε i a₁) a₂ := by
  apply Subtype.ext
  rw [face_val, nones_tensorCellL_leftIdx, tensorCellL_val, tensorCell_val, face_val,
    append_update_left]

/-! ### The master lemma: `app` commutes with juxtaposition

The two `tensorCellR`/`tensorCellL` cells share their underlying value with
`tensorCell` and differ only by associativity of the grade.  For the *right*
block (`k₁ + (k₂+1)` vs `(k₁+k₂)+1`) the grades are even definitionally equal; for
the *left* block (`(k₁+1)+k₂` vs `k₁+k₂+1`) they are only propositionally equal, so
we transport `sapp` along the grade equality with `sapp_grade_congr`. -/

/-- `sapp` depends on its cell argument only through the underlying value: cells
with equal `.val` (hence equal — possibly only propositionally — grade) have equal
`sapp`-values. -/
theorem sapp_grade_congr {P N k k' : ℕ} (c : cells P N) (a : cells N k) (a' : cells N k')
    (hv : a.val = a'.val) : (sapp c a).val = (sapp c a').val := by
  have hk : k = k' := by rw [← a.prop, ← a'.prop, hv]
  subst hk
  have : a = a' := Subtype.ext hv
  rw [this]

/-- **Base case** of the master lemma: the right factor is the top cell.  Proved by
induction on the left block (using left-block faces). -/
theorem app_tensorCell_topRight {P₁ P₂ N₁ N₂ : ℕ} (c₁ : cells P₁ N₁) (c₂ : cells P₂ N₂)
    {k₁ : ℕ} (a₁ : cells N₁ k₁) :
    sapp (tensorCell c₁ c₂) (tensorCell a₁ (topCell N₂))
      = tensorCell (sapp c₁ a₁) c₂ := by
  induction hd : N₁ - k₁ using Nat.strong_induction_on generalizing k₁ a₁ with
  | _ d ih =>
    rcases Nat.lt_or_ge k₁ N₁ with hlt | hge
    · -- peel the smallest fixed coordinate of `a₁` (left block)
      have hstep : sapp (tensorCell c₁ c₂) (tensorCell (freeMin a₁ hlt) (topCell N₂))
          = tensorCell (sapp c₁ (freeMin a₁ hlt)) c₂ :=
        ih (N₁ - (k₁ + 1)) (by omega) (freeMin a₁ hlt) rfl
      rw [sapp_unfold c₁ a₁ hlt, ← face_tensorCellL_leftIdx]
      conv_lhs =>
        rw [show tensorCell a₁ (topCell N₂)
              = tensorCell (face (minFixedVal a₁ hlt) (minFixedIdx a₁ hlt) (freeMin a₁ hlt))
                  (topCell N₂) from by rw [face_freeMin],
          ← face_tensorCellL_leftIdx, sapp_face]
      congr 1
      -- transport `hstep` (in grade `(k₁+1)+N₂`) to the `tensorCellL` grade `k₁+N₂+1`
      apply Subtype.ext
      rw [sapp_grade_congr (tensorCell c₁ c₂) (tensorCellL (freeMin a₁ hlt) (topCell N₂))
            (tensorCell (freeMin a₁ hlt) (topCell N₂)) rfl,
        congrArg Subtype.val hstep, tensorCellL_val, tensorCell_val]
    · -- `k₁ = N₁`, so `a₁ = topCell N₁`
      have hkn : k₁ = N₁ := le_antisymm (cells_card_le a₁) hge
      subst hkn
      rw [eq_topCell a₁, tensorCell_topCell, sapp_topCell, sapp_topCell]

/-- **The master lemma.**  `app` commutes with juxtaposition of cells. -/
theorem app_tensorCell {P₁ P₂ N₁ N₂ : ℕ} (c₁ : cells P₁ N₁) (c₂ : cells P₂ N₂)
    {k₁ k₂ : ℕ} (a₁ : cells N₁ k₁) (a₂ : cells N₂ k₂) :
    sapp (tensorCell c₁ c₂) (tensorCell a₁ a₂)
      = tensorCell (sapp c₁ a₁) (sapp c₂ a₂) := by
  induction hd : N₂ - k₂ using Nat.strong_induction_on generalizing k₂ a₂ with
  | _ d ih =>
    rcases Nat.lt_or_ge k₂ N₂ with hlt | hge
    · -- peel the smallest fixed coordinate of `a₂` (right block)
      have hstep : sapp (tensorCell c₁ c₂) (tensorCell a₁ (freeMin a₂ hlt))
          = tensorCell (sapp c₁ a₁) (sapp c₂ (freeMin a₂ hlt)) :=
        ih (N₂ - (k₂ + 1)) (by omega) (freeMin a₂ hlt) rfl
      rw [sapp_unfold c₂ a₂ hlt, ← face_tensorCellR_rightIdx]
      conv_lhs =>
        rw [show tensorCell a₁ a₂
              = tensorCell a₁ (face (minFixedVal a₂ hlt) (minFixedIdx a₂ hlt) (freeMin a₂ hlt))
                from by rw [face_freeMin],
          ← face_tensorCellR_rightIdx, sapp_face]
      exact congrArg (face (minFixedVal a₂ hlt) (rightIdx k₁ (minFixedIdx a₂ hlt))) hstep
    · -- `k₂ = N₂`, so `a₂ = topCell N₂`: reduce to the base case
      have hkn : k₂ = N₂ := le_antisymm (cells_card_le a₂) hge
      subst hkn
      rw [eq_topCell a₂, sapp_topCell]
      exact app_tensorCell_topRight c₁ c₂ a₁

/-! ### Empty-block juxtaposition (for the unitors) -/

/-- Right-juxtaposing the empty cell is a `Fin.cast`. -/
theorem tensorCell_topCell_zero {N k : ℕ} (a : cells N k) :
    (tensorCell a (topCell 0)).val = a.val ∘ Fin.cast (Nat.add_zero N) := by
  rw [tensorCell_val]
  funext q
  simp only [Function.comp_apply]
  refine Fin.addCases (fun p => ?_) (fun p => p.elim0) q
  rw [Fin.append_left, show Fin.cast (Nat.add_zero N) (Fin.castAdd 0 p) = p from by
    apply Fin.ext; simp]

/-- Left-juxtaposing the empty cell is a `Fin.cast`. -/
theorem topCell_zero_tensorCell {N k : ℕ} (a : cells N k) :
    (tensorCell (topCell 0) a).val = a.val ∘ Fin.cast (Nat.zero_add N) := by
  rw [tensorCell_val]
  funext q
  simp only [Function.comp_apply]
  refine Fin.addCases (fun p => p.elim0) (fun p => ?_) q
  rw [Fin.append_right, show Fin.cast (Nat.zero_add N) (Fin.natAdd 0 p) = p from by
    apply Fin.ext; simp]

end StdCube

/-! ## The monoidal structure on `Box`

Object tensor is addition of dimensions; the morphism tensor juxtaposes the cells
`ev f`, `ev g` via `StdCube.tensorCell`. -/

namespace Box

open StdCube

/-- The tensor of two box morphisms: juxtapose the representing cells. -/
noncomputable def tensorHomFn {a₁ b₁ a₂ b₂ : Box} (f : a₁ ⟶ b₁) (g : a₂ ⟶ b₂) :
    Box.ob (a₁.dim + a₂.dim) ⟶ Box.ob (b₁.dim + b₂.dim) :=
  canonicalMap (K := stdPre (b₁.dim + b₂.dim)) (tensorCell (ev f) (ev g))

@[simp] theorem ev_tensorHomFn {a₁ b₁ a₂ b₂ : Box} (f : a₁ ⟶ b₁) (g : a₂ ⟶ b₂) :
    ev (tensorHomFn f g) = tensorCell (ev f) (ev g) :=
  ev_canonicalMap _

/-- `ev` of a `Box` composite peels the first factor. -/
theorem ev_comp_box {a b c : Box} (f : a ⟶ b) (g : b ⟶ c) :
    ev (f ≫ g) = sapp (ev g) (ev f) :=
  app_unique g rfl (ev f)

@[simp] theorem ev_id_box (a : Box) : ev (𝟙 a) = topCell a.dim := rfl

/-- `tensorHomFn` of identities is the identity. -/
theorem tensorHomFn_id (a b : Box) :
    tensorHomFn (𝟙 a) (𝟙 b) = 𝟙 (Box.ob (a.dim + b.dim)) := by
  rw [tensorHomFn, ev_id_box, ev_id_box, tensorCell_topCell]
  exact canonicalMap_topCell _

/-- `tensorHomFn` respects composition (functoriality), via the master lemma. -/
theorem tensorHomFn_comp {a₁ b₁ c₁ a₂ b₂ c₂ : Box} (f₁ : a₁ ⟶ b₁) (g₁ : b₁ ⟶ c₁)
    (f₂ : a₂ ⟶ b₂) (g₂ : b₂ ⟶ c₂) :
    tensorHomFn (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHomFn f₁ f₂ ≫ tensorHomFn g₁ g₂ := by
  apply PrecubicalConstructions.hom_ext
  intro k x
  change sapp (tensorCell (ev (f₁ ≫ g₁)) (ev (f₂ ≫ g₂))) x
    = sapp (tensorCell (ev g₁) (ev g₂)) (sapp (tensorCell (ev f₁) (ev f₂)) x)
  rw [ev_comp_box, ev_comp_box, sapp_comp, app_tensorCell]

/-! ### The `MonoidalCategoryStruct` -/

noncomputable instance : MonoidalCategoryStruct Box where
  tensorObj X Y := Box.ob (X.dim + Y.dim)
  whiskerLeft X _ _ g := tensorHomFn (𝟙 X) g
  whiskerRight f Y := tensorHomFn f (𝟙 Y)
  tensorHom f g := tensorHomFn f g
  tensorUnit := Box.ob 0
  associator X Y Z := eqToIso (by rw [Nat.add_assoc])
  leftUnitor X := eqToIso (by obtain ⟨m⟩ := X; rw [Nat.zero_add])
  rightUnitor X := eqToIso (by obtain ⟨m⟩ := X; rfl)

@[simp] theorem tensorObj_def (X Y : Box) :
    MonoidalCategoryStruct.tensorObj X Y = Box.ob (X.dim + Y.dim) := rfl

@[simp] theorem tensorHom_eq {a₁ b₁ a₂ b₂ : Box} (f : a₁ ⟶ b₁) (g : a₂ ⟶ b₂) :
    MonoidalCategoryStruct.tensorHom f g = tensorHomFn f g := rfl

@[simp] theorem whiskerLeft_eq (X : Box) {a b : Box} (g : a ⟶ b) :
    MonoidalCategoryStruct.whiskerLeft X g = tensorHomFn (𝟙 X) g := rfl

@[simp] theorem whiskerRight_eq {a b : Box} (f : a ⟶ b) (Y : Box) :
    MonoidalCategoryStruct.whiskerRight f Y = tensorHomFn f (𝟙 Y) := rfl

/-! ### The `MonoidalCategory` laws

The five "functorial" laws (`tensorHom_def`, `id_tensorHom_id`,
`tensorHom_comp_tensorHom`, `whiskerLeft_id`, `id_whiskerRight`) follow directly
from `tensorHomFn_id`/`tensorHomFn_comp`.  The coherence laws involve the
`eqToHom` associator/unitors. -/

theorem law_tensorHom_def {a₁ b₁ a₂ b₂ : Box} (f : a₁ ⟶ b₁) (g : a₂ ⟶ b₂) :
    tensorHomFn f g = tensorHomFn f (𝟙 a₂) ≫ tensorHomFn (𝟙 b₁) g := by
  rw [← tensorHomFn_comp, Category.comp_id, Category.id_comp]

theorem law_id_tensorHom_id (a b : Box) :
    tensorHomFn (𝟙 a) (𝟙 b) = 𝟙 (Box.ob (a.dim + b.dim)) := tensorHomFn_id a b

theorem law_tensorHom_comp {a₁ b₁ c₁ a₂ b₂ c₂ : Box} (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂)
    (g₁ : b₁ ⟶ c₁) (g₂ : b₂ ⟶ c₂) :
    tensorHomFn f₁ f₂ ≫ tensorHomFn g₁ g₂ = tensorHomFn (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  (tensorHomFn_comp f₁ g₁ f₂ g₂).symm

/-! ### `eqToHom` bookkeeping for the coherence laws -/

/-- `tensorHomFn` of two `eqToHom`s is an `eqToHom` (the object-level associativity
/ unitality transports).  Proved by reducing the dimension equalities and using
functoriality. -/
theorem tensorHomFn_eqToHom {a₁ b₁ a₂ b₂ : Box} (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) :
    tensorHomFn (eqToHom h₁) (eqToHom h₂)
      = eqToHom (show Box.ob (a₁.dim + a₂.dim) = Box.ob (b₁.dim + b₂.dim) by
          rw [h₁, h₂]) := by
  subst h₁; subst h₂
  rw [eqToHom_refl, eqToHom_refl]
  exact tensorHomFn_id a₁ a₂

/-- The monoidal unit's dimension is `0`. -/
@[simp] theorem tensorUnit_dim : (MonoidalCategoryStruct.tensorUnit Box).dim = 0 := rfl

theorem assoc_obj_eq (X Y Z : Box) :
    Box.ob (X.dim + Y.dim + Z.dim) = Box.ob (X.dim + (Y.dim + Z.dim)) := by
  rw [Nat.add_assoc]

theorem leftUnitor_obj_eq (X : Box) : Box.ob (0 + X.dim) = X := by
  obtain ⟨m⟩ := X; rw [Nat.zero_add]

theorem rightUnitor_obj_eq (X : Box) : Box.ob (X.dim + 0) = X := by
  obtain ⟨m⟩ := X; rfl

/-- The associator/unitor `.hom`s are `eqToHom`. -/
@[simp] theorem associator_hom_def (X Y Z : Box) :
    (MonoidalCategoryStruct.associator X Y Z).hom = eqToHom (assoc_obj_eq X Y Z) := rfl

@[simp] theorem leftUnitor_hom_def (X : Box) :
    (MonoidalCategoryStruct.leftUnitor X).hom = eqToHom (leftUnitor_obj_eq X) := rfl

@[simp] theorem rightUnitor_hom_def (X : Box) :
    (MonoidalCategoryStruct.rightUnitor X).hom = eqToHom (rightUnitor_obj_eq X) := rfl

/-- Whiskering an `eqToHom` on the right is an `eqToHom`. -/
theorem whiskerRight_eqToHom {a b : Box} (h : a = b) (Y : Box) :
    tensorHomFn (eqToHom h) (𝟙 Y) = eqToHom (by rw [h]) := by
  rw [show (𝟙 Y) = eqToHom (rfl : Y = Y) from rfl, tensorHomFn_eqToHom]

/-- Whiskering an `eqToHom` on the left is an `eqToHom`. -/
theorem whiskerLeft_eqToHom (X : Box) {a b : Box} (h : a = b) :
    tensorHomFn (𝟙 X) (eqToHom h) = eqToHom (by rw [h]) := by
  rw [show (𝟙 X) = eqToHom (rfl : X = X) from rfl, tensorHomFn_eqToHom]

/-! ### Coherence laws (standalone, to be assembled into the instance) -/

-- pentagon: pure `eqToHom` object-coherence (no morphisms), collapses.
theorem law_pentagon (W X Y Z : Box) :
    tensorHomFn (eqToHom (assoc_obj_eq W X Y)) (𝟙 Z) ≫
        eqToHom (assoc_obj_eq W (Box.ob (X.dim + Y.dim)) Z) ≫
          tensorHomFn (𝟙 W) (eqToHom (assoc_obj_eq X Y Z))
      = eqToHom (assoc_obj_eq (Box.ob (W.dim + X.dim)) Y Z) ≫
          eqToHom (assoc_obj_eq W X (Box.ob (Y.dim + Z.dim))) := by
  rw [whiskerRight_eqToHom, whiskerLeft_eqToHom]
  simp only [eqToHom_trans]

-- triangle: pure `eqToHom` object-coherence.
theorem law_triangle (X Y : Box) :
    eqToHom (assoc_obj_eq X (Box.ob 0) Y) ≫
        tensorHomFn (𝟙 X) (eqToHom (leftUnitor_obj_eq Y))
      = tensorHomFn (eqToHom (rightUnitor_obj_eq X)) (𝟙 Y) := by
  rw [whiskerLeft_eqToHom, whiskerRight_eqToHom]
  simp only [eqToHom_trans]

/-! ### Status: what remains for the full `MonoidalCategory Box` instance

Sorry-free above:
* `MonoidalCategoryStruct Box` (object tensor `= (·+·)`, morphism tensor via
  `tensorCell`/`Fin.append`, associator/unitors as `eqToIso`);
* the **master combinatorial lemma** `StdCube.app_tensorCell`
  (`app` commutes with juxtaposition) and its functoriality consequences
  `tensorHomFn_id`, `tensorHomFn_comp`;
* the five "functorial" `MonoidalCategory` fields: `law_tensorHom_def`,
  `law_id_tensorHom_id`, `law_tensorHom_comp`, and the two `whisker(Left/Right)_id`
  laws (provable inline by `tensorHomFn_id`);
* the two coherence laws with no morphism input, `law_pentagon` and `law_triangle`
  (pure `eqToHom` object-coherence).

OPEN — the three *naturality* fields (`associator_naturality`,
`leftUnitor_naturality`, `rightUnitor_naturality`).  Precise obstruction: each
reduces to an equation `(tensorHomFn … f …) ≫ eqToHom = eqToHom ≫ (tensorHomFn … f …)`
where the `eqToHom` is the associator/unitor.  Discharging it requires transporting
`StdCube.app`/`sapp` (equivalently `ev`/`canonicalMap`) across an *object-level*
`eqToHom`, i.e. across a `Fin.cast` on the source/target dimension coming from a
**non-defeq** `Nat.add` reassociation (`(a+b)+c` vs `a+(b+c)`) or left-unit
(`0+a` vs `a`).  Unlike the right block of `app_tensorCell` (`a+(b+1)` *is* defeq
`(a+b)+1`), these casts are not definitional, so they need a genuine `HEq`/`cast`
transport lemma for `app` (the analogue of `app_tensorCell` but for `Fin.append_assoc`
/ empty-block `Fin.append`).  The same `eqToHom`-rebasing-over-`append` gap is noted
in `Cyl4_Generation.lean` and handled with `HEq` machinery in
`Chains/Correspondence.lean` (`eqToHom_type_apply`); porting that here is the
remaining work (estimate: a `sapp`-transport lemma plus the `Fin.append_assoc`
master lemma, ~150-250 lines).

Everything below the struct is therefore the assembled instance MINUS those three
fields; we expose the proven fields as named `law_*` theorems above. -/

end Box
