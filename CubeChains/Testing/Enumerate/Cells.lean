import CubeChains.Precubical.Basic.StandardCube
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

/-!
# Testing/Enumerate/Cells — cells of `□n` as raw sign vectors, and sub-precubical sets of `□n`

A cell of `□n` is a sign vector `Fin n → Option Bool` (`none = ∗` free, `some ε` fixed), with the
`Cell N k` dimension index dropped so that face-closure is `decide`-able.  The bi-pointing of `□n`
fixes the reading: `(cube n).init = canonicalMap (constVertex n false)`, so `some false` is the
*initial* value — a direction not yet performed — and `some true` the final one.

Not built by `lake build CubeChains`.
-/

open StdCube

variable {n : ℕ}

/-- `c'` is a face of `c`: `c'` may free no coordinate that `c` fixes. -/
def IsFace (c' c : Fin n → Option Bool) : Prop := ∀ d, (c d).isSome → c' d = c d

instance (c' c : Fin n → Option Bool) : Decidable (IsFace c' c) :=
  inferInstanceAs (Decidable (∀ d, (c d).isSome → c' d = c d))

@[refl] theorem IsFace.refl (c : Fin n → Option Bool) : IsFace c c := fun _ _ => rfl

theorem IsFace.trans {c'' c' c : Fin n → Option Bool} (h₁ : IsFace c'' c') (h₂ : IsFace c' c) :
    IsFace c'' c := fun d hd => (h₁ d (by rw [h₂ d hd]; exact hd)).trans (h₂ d hd)

/-- A sub-precubical set of `□n`: a decidable set of cells closed under faces. -/
structure SubCube (n : ℕ) where
  mem : (Fin n → Option Bool) → Bool
  face_closed : ∀ c c', mem c → IsFace c' c → mem c'

/-- `□n` itself. -/
def SubCube.full (n : ℕ) : SubCube n where
  mem _ := true
  face_closed _ _ _ _ := rfl

/-- `∂□n`: the cells of dimension `< n`, i.e. those fixing at least one coordinate. -/
def SubCube.boundary (n : ℕ) : SubCube n where
  mem c := (List.finRange n).any fun d => (c d).isSome
  face_closed c c' hc hf := by
    simp only [List.any_eq_true, List.mem_finRange, true_and] at hc ⊢
    obtain ⟨d, hd⟩ := hc
    exact ⟨d, by rw [hf d hd]; exact hd⟩

/-- The dimension of a cell: its number of free directions. -/
def cellDim (c : Fin n → Option Bool) : ℕ := (List.finRange n).countP fun d => (c d).isNone

/-- The `k`-skeleton of `□n`.  Faces only fix more coordinates, so dimension drops. -/
def SubCube.skeleton (k : ℕ) (n : ℕ) : SubCube n where
  mem c := decide (cellDim c ≤ k)
  face_closed c c' hc hf := by
    simp only [decide_eq_true_eq] at hc ⊢
    refine le_trans (List.countP_mono_left ?_) hc
    intro d _ hd
    cases hcd : c d with
    | none => simp
    | some v =>
        rw [hf d (by simp [hcd]), hcd] at hd
        simp at hd

/-- The face of `□n` spanned by the directions `b`, sitting past the directions `done`. -/
def beadCell (done b : List (Fin n)) : Fin n → Option Bool :=
  fun d => if d ∈ b then none else some (decide (d ∈ done))

@[simp] theorem beadCell_eq_none_iff {done b : List (Fin n)} {d : Fin n} :
    beadCell done b d = none ↔ d ∈ b := by
  by_cases h : d ∈ b <;> simp [beadCell, h]

/-- Growing a block frees more coordinates — the pruning fact: a rejected block rejects all of its
supersets, since `beadCell done b` is a face of `beadCell done b'`. -/
theorem beadCell_isFace {done b b' : List (Fin n)} (h : b ⊆ b') :
    IsFace (beadCell done b) (beadCell done b') := by
  intro d hd
  have hb' : d ∉ b' := fun hmem => by simp [beadCell, hmem] at hd
  have hb : d ∉ b := fun hmem => hb' (h hmem)
  simp [beadCell, hb, hb']
