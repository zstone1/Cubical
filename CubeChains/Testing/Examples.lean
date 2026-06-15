import CubeChains.Testing.Lowering

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false

/-!
# Example finite precubical sets, and lowering-conjecture tests on them

Each example is a `FinBPSet` over a small named cell type.  We `#eval` a `Report`
and pin the headline boolean with `native_decide`.  See `Model.lean` for why this
combinatorial surrogate is a faithful and fully computable stand-in for the real
(noncomputable) `Ch K`.
-/

namespace CubeTest
namespace Examples

open FinBPSet

/-! ## The interval `□¹` and the square `□²` (rigid baselines) -/

/-- Cells of the interval `□¹`: two vertices and an edge. -/
inductive I | v0 | v1 | e
  deriving DecidableEq, Repr

/-- The interval `□¹` as a bi-pointed precubical set. -/
def interval : FinBPSet I where
  cellList := [.v0, .v1, .e]
  dim := fun c => match c with | .e => 1 | _ => 0
  face := fun ε i c => match c, i with
    | .e, 0 => some (cond ε .v1 .v0)
    | _, _  => none
  init := .v0
  final := .v1

/-- Cells of the square `□²`: 4 vertices, 4 edges, 1 square. -/
inductive Sq | c00 | c10 | c01 | c11 | e0_ | e1_ | e_0 | e_1 | sq
  deriving DecidableEq, Repr

/-- The square `□²`.  Edges: `e0_ = {0}×□` (`x₀=0`), `e1_ = {1}×□`, `e_0 = □×{0}`,
`e_1 = □×{1}`. -/
def square : FinBPSet Sq where
  cellList := [.c00, .c10, .c01, .c11, .e0_, .e1_, .e_0, .e_1, .sq]
  dim := fun c => match c with
    | .sq => 2 | .e0_ | .e1_ | .e_0 | .e_1 => 1 | _ => 0
  face := fun ε i c => match c, i with
    | .e0_, 0 => some (cond ε .c01 .c00)   -- x₀=0, vary x₁
    | .e1_, 0 => some (cond ε .c11 .c10)   -- x₀=1, vary x₁
    | .e_0, 0 => some (cond ε .c10 .c00)   -- x₁=0, vary x₀
    | .e_1, 0 => some (cond ε .c11 .c01)   -- x₁=1, vary x₀
    | .sq, 0  => some (cond ε .e1_ .e0_)   -- face along x₀
    | .sq, 1  => some (cond ε .e_1 .e_0)   -- face along x₁
    | _, _    => none
  init := .c00
  final := .c11

/-! ## The four-square loop (the necessity witness from `Unrealizable.lean`)

Vertices `o, w, wp, z1, z2, t`; edges `a:o→w, ap:o→wp, b1:w→z1, b2:w→z2,
g1:wp→z1, g2:wp→z2, d1:z1→t, d2:z2→t`; four square "forks" `T12, T23, T34, T41`.
The four directed paths `o ⤳ t` form a 4-cycle joined by the squares; the rotation
`ρ` is a (non-orientation-preserving) automorphism of the chain poset not realized
by any map of `K`.  Lowering should still hold *with* orientation-preservation. -/

/-- Cells of the four-square loop. -/
inductive FS
  | o | w | wp | z1 | z2 | t
  | a | ap | b1 | b2 | g1 | g2 | d1 | d2
  | T12 | T23 | T34 | T41
  deriving DecidableEq, Repr

/-- The four-square loop. -/
def fourSquare : FinBPSet FS where
  cellList := [.o, .w, .wp, .z1, .z2, .t,
               .a, .ap, .b1, .b2, .g1, .g2, .d1, .d2,
               .T12, .T23, .T34, .T41]
  dim := fun c => match c with
    | .o | .w | .wp | .z1 | .z2 | .t => 0
    | .a | .ap | .b1 | .b2 | .g1 | .g2 | .d1 | .d2 => 1
    | .T12 | .T23 | .T34 | .T41 => 2
  face := fun ε i c => match c, i with
    -- edges
    | .a,  0 => some (cond ε .w .o)
    | .ap, 0 => some (cond ε .wp .o)
    | .b1, 0 => some (cond ε .z1 .w)
    | .b2, 0 => some (cond ε .z2 .w)
    | .g1, 0 => some (cond ε .z1 .wp)
    | .g2, 0 => some (cond ε .z2 .wp)
    | .d1, 0 => some (cond ε .t .z1)
    | .d2, 0 => some (cond ε .t .z2)
    -- T12 : w ⤳ t, corners (0,0)=w (1,1)=t (0,1)=z1 (1,0)=z2
    | .T12, 0 => some (cond ε .d2 .b1)
    | .T12, 1 => some (cond ε .d1 .b2)
    -- T34 : wp ⤳ t.  Oriented (coord 0 ↔ b/g via z2) so the symmetry
    -- `w↔wp, z1↔z2` maps T12 to T34 index-preservingly.
    | .T34, 0 => some (cond ε .d1 .g2)
    | .T34, 1 => some (cond ε .d2 .g1)
    -- T23 : o ⤳ z2, corners (0,0)=o (1,1)=z2 (0,1)=w (1,0)=wp
    | .T23, 0 => some (cond ε .g2 .a)
    | .T23, 1 => some (cond ε .b2 .ap)
    -- T41 : o ⤳ z1.  Oriented so `w↔wp, z1↔z2` maps T23 to T41.
    | .T41, 0 => some (cond ε .b1 .ap)
    | .T41, 1 => some (cond ε .g1 .a)
    | _, _    => none
  init := .o
  final := .t

/-! ## Two squares glued along an edge (a `2×1` grid) -/

/-- Cells of the `2×1` grid: vertices `vIJ` (column `I∈{0,1,2}`, row `J∈{0,1}`),
horizontal edges `hIJ`, vertical edges `wI`, squares `S0` (left), `S1` (right). -/
inductive G
  | v00 | v10 | v20 | v01 | v11 | v21
  | h00 | h10 | h01 | h11 | w0 | w1 | w2
  | S0 | S1
  deriving DecidableEq, Repr

/-- The `2×1` grid of squares. -/
def grid2 : FinBPSet G where
  cellList := [.v00, .v10, .v20, .v01, .v11, .v21,
               .h00, .h10, .h01, .h11, .w0, .w1, .w2, .S0, .S1]
  dim := fun c => match c with
    | .S0 | .S1 => 2
    | .h00 | .h10 | .h01 | .h11 | .w0 | .w1 | .w2 => 1
    | _ => 0
  face := fun ε i c => match c, i with
    | .h00, 0 => some (cond ε .v10 .v00)
    | .h10, 0 => some (cond ε .v20 .v10)
    | .h01, 0 => some (cond ε .v11 .v01)
    | .h11, 0 => some (cond ε .v21 .v11)
    | .w0,  0 => some (cond ε .v01 .v00)
    | .w1,  0 => some (cond ε .v11 .v10)
    | .w2,  0 => some (cond ε .v21 .v20)
    | .S0, 0 => some (cond ε .w1 .w0)     -- vary x₀ (vertical edges)
    | .S0, 1 => some (cond ε .h01 .h00)   -- vary x₁ (horizontal edges)
    | .S1, 0 => some (cond ε .w2 .w1)
    | .S1, 1 => some (cond ε .h11 .h10)
    | _, _   => none
  init := .v00
  final := .v21

/-! ## Reports and findings

Running `#eval _.report` on each example.  **The conjecture is refuted already at
`□²`:** it is *rigid* in the symmetry-free precubical model (`autK = [id]`), yet
`Ch(□²)` has the orientation-preserving automorphism that swaps the two "staircase"
edge-paths `[e_0,e1_]` and `[e0_,e_1]` — both of dimension sequence `[1,1]` — which
is therefore **not** in the image of `liftToCh` (`existence = false`).  The
four-square loop and the grid fail for the same reason (`Ch K` carries
staircase/reflection symmetries the symmetry-free `K` lacks).  This is a concrete
witness that the *provisional* `OrientationPreserving` (dimension-sequence
preservation; note it preserves altitude bands too) is **too weak** for the
lowering lemma in this setting.

The `2×1` grid, by contrast, **passes** (`existence = true`): gluing the two
squares pins their staircases, so `Ch K` has no extra orientation-preserving
symmetry.  So the failure is about *unpinned local cube symmetry*, not gluing
per se — the conjecture can still hold for suitably rigid `K`. -/

#eval interval.report
#eval square.report
#eval fourSquare.report
#eval grid2.report

-- The square is the minimal witness: rigid `K`, but `Ch K` has an extra symmetry.
#eval square.chains                      -- [[e_0,e1_], [e0_,e_1], [sq]]
#eval square.autK.length                 -- 1  (only the identity: □² is rigid)
#eval square.opAutCh                     -- [[0,1,2], [1,0,2]]  (id and the staircase swap)
#eval square.autK.map square.liftIdx     -- [[0,1,2]]  (image of liftToCh: only id)

/-! ### The findings, pinned by `native_decide`

`checkLowering K` is `validInput ∧ existence ∧ soundness ∧ injective`. -/

-- All four examples are well-formed and satisfy the three side conditions.
example : interval.validInput = true := by native_decide
example : square.validInput = true := by native_decide
example : fourSquare.validInput = true := by native_decide
example : grid2.validInput = true := by native_decide

-- Uniqueness/faithfulness always holds (matches `liftToCh_injective`).
example : interval.report.injective = true := by native_decide
example : square.report.injective = true := by native_decide
example : fourSquare.report.injective = true := by native_decide
example : grid2.report.injective = true := by native_decide

-- The interval `□¹` satisfies the full lowering conjecture.
example : interval.checkLowering = true := by native_decide

-- **The square `□²` refutes it**: rigid `K`, but an unrealized OP auto of `Ch K`.
example : square.autK.length = 1 := by native_decide
example : square.opAutCh.length = 2 := by native_decide
example : square.report.existence = false := by native_decide
example : square.checkLowering = false := by native_decide

-- The four-square loop fails the same way (existence fails).
example : fourSquare.report.existence = false := by native_decide
example : fourSquare.checkLowering = false := by native_decide

-- The grid, by contrast, PASSES: gluing pins the staircases.
example : grid2.report.existence = true := by native_decide
example : grid2.checkLowering = true := by native_decide

end Examples
end CubeTest
