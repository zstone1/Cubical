import CubeChains.Foundations.Bipointed
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Foundations/Terminal — the final (terminal) precubical set `Z`

`Z := (Functor.const Boxᵒᵖ).obj PUnit` — a single cell in every dimension, every face map forced.
It is the terminal object of `PrecubicalSet = Boxᵒᵖ ⥤ Type`, the mirror of `emptyPsh` (the initial
one).

Its point: unlike `□n`, `Z`'s events carry no refinement-invariant axis name, so the braid it grades
is the *whole* braid group, not just the pure part.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace CubeChains

/-- The **final precubical set**: a single cell in every dimension. -/
def Z : PrecubicalSet := (Functor.const Boxᵒᵖ).obj PUnit

@[simp] theorem Z_obj (c : Boxᵒᵖ) : Z.obj c = PUnit := rfl

@[simp] theorem Z_cells (n : ℕ) : Z.cells n = PUnit := rfl

/-- **`Z` is terminal.**  A constant functor at a terminal object is terminal. -/
def isTerminalZ : IsTerminal Z :=
  Functor.isTerminalConst Boxᵒᵖ Types.isTerminalPUnit

/-- The unique precubical map into `Z`. -/
def toZ (X : PrecubicalSet) : X ⟶ Z := isTerminalZ.from X

/-- `Z` as a bi-pointed precubical set.  It has a single vertex, so the bi-pointing is forced. -/
def Zbp : BPSet where
  toPsh := Z
  init := PUnit.unit
  final := PUnit.unit

@[simp] theorem Zbp_toPsh : Zbp.toPsh = Z := rfl

end CubeChains
