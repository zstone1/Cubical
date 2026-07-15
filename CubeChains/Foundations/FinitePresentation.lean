import CubeChains.Foundations.Nerve
import Mathlib.Tactic.DeriveFintype

/-!
# Foundations/FinitePresentation

A **finite presentation** of a precubical set and its realization as a *computable*
`BPSet`.  `FinPre V` is a dimension grading plus a total face table on a cell type
`V`; `toConcrete` turns it into a `PrecubicalConstructions` (reusing that model's
proven face/vertex API), and `toBPSet` bipoints its `Nerve`.  Because `coface`,
`faceMap`, `vertex₀/₁` and the cube Yoneda `canonicalMap` are all computable, faces
and extremal vertices of `K = Nerve (toConcrete D)` `#eval`.

The two `Prop` fields of `FinPre` are decidable (bounded quantifiers), so a finite
example discharges them by `decide`.  Finiteness of a model is *not* baked into
`FinPre` — both `PrecubicalConstructions` and `PrecubicalSet` keep `cells : ℕ →
Type`; it enters only by choosing a finite `V`.
-/

open CategoryTheory Opposite StdCube PrecubicalSet

/-- A finite presentation of a precubical set: a dimension grading `dim` and a total
face table `rawFace ε i v` (the `(ε,i)`-face of `v`, meaningful only at `i < dim v`),
obeying dimension-drop and the precubical identity on the in-range indices. -/
structure FinPre (V : Type) where
  /-- The dimension of each cell. -/
  dim : V → ℕ
  /-- The face table.  `rawFace ε i v` is the `(ε,i)`-face of `v`, used only for
  `i < dim v`; its value elsewhere is irrelevant. -/
  rawFace : Bool → ℕ → V → V
  /-- Faces lower dimension by one (on the in-range indices). -/
  dim_rawFace : ∀ (ε : Bool) (v : V) (i : ℕ), i < dim v → dim (rawFace ε i v) + 1 = dim v
  /-- The precubical identity, on the in-range indices.  The redundant `i < dim v`,
  `j < dim v` bounds (implied by `i ≤ j` and `j + 1 < dim v`) make this decidable. -/
  rawFace_id : ∀ (ε η : Bool) (v : V) (i : ℕ), i < dim v → ∀ (j : ℕ), j < dim v →
    i ≤ j → j + 1 < dim v →
    rawFace ε i (rawFace η (j + 1) v) = rawFace η j (rawFace ε i v)

namespace FinPre

variable {V : Type} (D : FinPre V)

/-- The concrete precubical set presented by `D`: `n`-cells are the `v : V` with
`dim v = n`; faces are read off the table (dimension drop and the precubical
identity are supplied by `D`'s fields). -/
def toConcrete : PrecubicalConstructions where
  cells n := { v : V // D.dim v = n }
  face {n} ε i c :=
    ⟨D.rawFace ε i.val c.val, by
      have h := D.dim_rawFace ε c.val i.val (by rw [c.prop]; exact i.isLt)
      rw [c.prop] at h; omega⟩
  face_face {n} ε η i j hij c := by
    apply Subtype.ext
    have hip := i.isLt
    have hjp := j.isLt
    have hi : i.val < D.dim c.val := by rw [c.prop]; omega
    have hj : j.val < D.dim c.val := by rw [c.prop]; omega
    have hj1 : j.val + 1 < D.dim c.val := by rw [c.prop]; omega
    exact D.rawFace_id ε η c.val i.val hi j.val hj hij hj1

@[simp] theorem toConcrete_cells (n : ℕ) : D.toConcrete.cells n = { v : V // D.dim v = n } := rfl

@[simp] theorem toConcrete_face_val {n : ℕ} (ε : Bool) (i : Fin (n + 1))
    (c : D.toConcrete.cells (n + 1)) :
    (D.toConcrete.face ε i c).val = D.rawFace ε i.val c.val := rfl

/-! ### The bipointed nerve — a computable `BPSet` -/

/-- The nerve cell classified by a presenting element `d`: its canonical cube map. -/
def mkCell {n : ℕ} (d : D.toConcrete.cells n) : (Nerve.obj D.toConcrete).cells n :=
  (nerveCellEquiv D.toConcrete n).symm d

/-- Read a nerve `n`-cell back to its presenting element of `V`. -/
def readCell {n : ℕ} (f : (Nerve.obj D.toConcrete).cells n) : V :=
  (nerveCellEquiv D.toConcrete n f).val

@[simp] theorem readCell_mkCell {n : ℕ} (d : D.toConcrete.cells n) :
    D.readCell (D.mkCell d) = d.val := by
  unfold readCell mkCell; rw [Equiv.apply_symm_apply]

/-- Bipoint the nerve of `D.toConcrete` at chosen `0`-cells `u`, `v`. -/
def toBPSet (u v : D.toConcrete.cells 0) : BPSet where
  toPsh := Nerve.obj D.toConcrete
  init := D.mkCell u
  final := D.mkCell v

@[simp] theorem toBPSet_toPsh (u v : D.toConcrete.cells 0) :
    (D.toBPSet u v).toPsh = Nerve.obj D.toConcrete := rfl

/-- **Correctness of the realized face.**  The topos face map of the nerve, read back
to `V`, is exactly the table's face — the whole `coface`/Yoneda machinery collapses
to `rawFace`. -/
theorem readCell_faceMap_mkCell {n : ℕ} (ε : Bool) (i : Fin (n + 1))
    (d : D.toConcrete.cells (n + 1)) :
    D.readCell ((Nerve.obj D.toConcrete).faceMap ε i (D.mkCell d))
      = D.rawFace ε i.val d.val := by
  unfold readCell mkCell
  rw [nerveCellEquiv_faceMap, Equiv.apply_symm_apply]
  rfl

end FinPre

/-! ## Examples: `#eval` a face and an extremal vertex

The interval `□¹` and the square `□²` as finite presentations.  `#eval`-ing a face
and an extremal vertex of `Nerve (toConcrete _)` runs the real (formerly
`noncomputable`) topos face/vertex maps end to end. -/

namespace FinPre.Examples

/-- Cells of the interval `□¹`: two vertices and an edge. -/
inductive Iv | v0 | v1 | e
  deriving DecidableEq, Repr, Fintype

/-- The interval `□¹` as a finite presentation. -/
def interval : FinPre Iv where
  dim v := match v with | .e => 1 | _ => 0
  rawFace ε _ v := match v with | .e => cond ε .v1 .v0 | x => x
  dim_rawFace := by decide
  rawFace_id := by decide

/-- The bipointed interval `K = Nerve (toConcrete interval)`. -/
def intervalK : BPSet := interval.toBPSet ⟨.v0, rfl⟩ ⟨.v1, rfl⟩

-- Target face of the edge `e` (the `d¹`-face at coordinate 0): its target vertex.
#eval interval.readCell (intervalK.toPsh.faceMap true 0 (interval.mkCell ⟨.e, rfl⟩))   -- v1
-- Source extremal vertex of the edge `e`.
#eval interval.readCell (intervalK.toPsh.vertex₀ (interval.mkCell ⟨.e, rfl⟩))           -- v0

/-- Cells of the square `□²`: 4 vertices, 4 edges, 1 square. -/
inductive Sq | c00 | c10 | c01 | c11 | e0_ | e1_ | e_0 | e_1 | sq
  deriving DecidableEq, Repr, Fintype

/-- The square `□²` as a finite presentation.  Edges: `e0_ = {x₀=0}`, `e1_ = {x₀=1}`,
`e_0 = {x₁=0}`, `e_1 = {x₁=1}`. -/
def square : FinPre Sq where
  dim v := match v with
    | .sq => 2 | .e0_ | .e1_ | .e_0 | .e_1 => 1 | _ => 0
  rawFace ε i v := match v, i with
    | .e0_, _ => cond ε .c01 .c00
    | .e1_, _ => cond ε .c11 .c10
    | .e_0, _ => cond ε .c10 .c00
    | .e_1, _ => cond ε .c11 .c01
    | .sq, 0 => cond ε .e1_ .e0_
    | .sq, _ => cond ε .e_1 .e_0
    | x, _ => x
  dim_rawFace := by decide
  rawFace_id := by decide

/-- The bipointed square `K = Nerve (toConcrete square)`. -/
def squareK : BPSet := square.toBPSet ⟨.c00, rfl⟩ ⟨.c11, rfl⟩

-- The `x₁=1` face of the square (target face at coordinate 1).
#eval square.readCell (squareK.toPsh.faceMap true 1 (square.mkCell ⟨.sq, rfl⟩))   -- e_1
-- The two extremal vertices of the square.
#eval square.readCell (squareK.toPsh.vertex₀ (square.mkCell ⟨.sq, rfl⟩))          -- c00
#eval square.readCell (squareK.toPsh.vertex₁ (square.mkCell ⟨.sq, rfl⟩))          -- c11

/-- The `#eval`ed face is machine-checked via `readCell_faceMap_mkCell`. -/
example :
    square.readCell (squareK.toPsh.faceMap true 1 (square.mkCell ⟨.sq, rfl⟩)) = .e_1 := by
  change square.readCell ((Nerve.obj square.toConcrete).faceMap true 1 (square.mkCell ⟨.sq, rfl⟩))
      = .e_1
  rw [readCell_faceMap_mkCell]; rfl

end FinPre.Examples
