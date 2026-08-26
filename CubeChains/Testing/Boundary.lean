import CubeChains.Testing.Enumerate
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Testing/Boundary — the boundary `∂□ⁿ` as a genuine sub-precubical set

`∂□ⁿ ↪ □ⁿ` — the "`n`-cube minus its top cell" — built *literally*, not as a filter: the subfunctor
of `□ⁿ` on the cells of dimension `< n`.  For the cube this is exactly the boundary, since every
proper face lies on it and the only cell of dimension `n` is the top one.  Hence `Ch⋆(∂□ⁿ)`
is a real
type — `ChStar` of an actual `BPSet` — and the inclusion is a genuine mono of bi-pointed sets.

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChains StdCube

/-- **`∂□ⁿ` as a subfunctor of `□ⁿ`**: the cells of dimension `< n`.  Closed under restriction
because
`Box` morphisms only lower dimension (`boxHom_dim_le`). -/
def bdrySub (n : ℕ) : Subfunctor (cube n).toPsh where
  obj U := {_x | U.unop.dim < n}
  map {U V} i := fun _x hx => lt_of_le_of_lt (boxHom_dim_le i.unop) hx

/-- **The boundary `∂□ⁿ`** as a bi-pointed precubical set — the cube's own endpoints survive
(they are
`0`-cells, and `0 < n`). -/
def boundaryCube (n : ℕ) [NeZero n] : BPSet where
  toPsh := (bdrySub n).toFunctor
  init := ⟨(cube n).init, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  final := ⟨(cube n).final, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- **The inclusion `∂□ⁿ ↪ □ⁿ`** of bi-pointed sets — the subfunctor mono, endpoints preserved
on the
nose. -/
def boundaryIncl (n : ℕ) [NeZero n] : boundaryCube n ⟶ cube n where
  hom := (bdrySub n).ι
  app_init := rfl
  app_final := rfl

/-- **`Ch⋆(∂□ⁿ)`** — the executions of the boundary, literally `ChStar` of the sub-`BPSet` `∂□ⁿ`. -/
abbrev ChStarBoundary (n : ℕ) [NeZero n] : Type := Ch⋆ (boundaryCube n)

-- The type exists and the inclusion is a mono; enumeration follows via `Ch⋆`-pushforward.
#check (ChStarBoundary 3 : Type)
#check (boundaryIncl 3 : boundaryCube 3 ⟶ cube 3)
