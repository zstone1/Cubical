import CubeChains.Box

/-!
# Representability of the standard cube (Yoneda for cubes)

The bridge `PrecubicalSet ≌ PrecubicalConstructions` rests on a single lemma:
the standard cube `□ⁿ` is *representable*, i.e. a precubical map `□ⁿ ⟶ K` is the
same data as an `n`-cell of `K`,

  `(□ⁿ ⟶ K) ≃ K.cells n`,

naturally in `n` (along `Box`) and `K`.  The forward map `ev` sends `f` to its
value `f.app n ⊤` on the top cell `⊤` (all coordinates free).  The inverse is the
*canonical map* `c ↦ canonicalMap c`, the unique precubical map sending `⊤` to
`c`, built from iterated faces of `c` at the fixed coordinates.

This file fixes the statement (`cubeRepr`).  The construction of the inverse is
the iterated-face computation flagged in `DESIGN.md`; it is the cube's Yoneda
lemma and is the remaining proof obligation of the topos bridge.
-/

open CategoryTheory

namespace StdCube

/-- The top cell of `□ⁿ`: every coordinate free (`none`), the unique `n`-cell. -/
def topCell (n : ℕ) : cells n n :=
  ⟨fun _ => none, by simp [noneSet]⟩

/-- The cube inclusion `Box ⥤ PrecubicalConstructions`, `[n] ↦ □ⁿ`.  Fully
faithful by construction, since `Box`'s homs *are* precubical maps of cubes. -/
def cubeι : Box ⥤ PrecubicalConstructions where
  obj b := stdPre b.dim
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `cubeι` is fully faithful: this holds definitionally, as `Box (m ⟶ n)` is by
definition `□^m ⟶ □^n`. -/
def cubeιFullyFaithful : cubeι.FullyFaithful where
  preimage f := f

/-- Evaluation of a precubical map out of `□ⁿ` at the top cell: an `n`-cell of `K`. -/
def ev {K : PrecubicalConstructions} {n : ℕ} (f : stdPre n ⟶ K) : K.cells n :=
  PrecubicalConstructions.Hom.app f n (topCell n)

end StdCube
