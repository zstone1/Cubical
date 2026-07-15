import CubeChains.Chains.WedgeMap

/-!
# Testing/WedgeCompute

The wedge pushout is **computable**: `serialWedge` glues cubes along the explicit
`Glue.gluePsh` (a pointwise `Quot`), not the `Classical.choice`-opaque mathlib `pushout`.
So a cell of `wedge[2,2]` and the action of a concrete wedge map on it `#eval`.

`unseal` locally exposes the `Glue` `Quot` during elaboration (the compiler already
ignores `irreducible`), letting a `Quot.lift` read a positive-dimensional cell back to
`(block index, sign vector)` — the relation is empty above dimension `0`, so the lift is
free.  Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite StdCube BPSet CubeChain

-- Read a `2`-cell of `wedge[2,2]` back to `(block index, sign vector of its □² cell)`.
unseal Glue.gluePsh Glue.inl Glue.inr in
def readW22 (c : (⋁([2, 2] : List ℕ+)).cells 2) : ℕ × List (Option Bool) :=
  Quot.lift
    (fun x => match x with
      | Sum.inl a => (0, List.ofFn (ev a).val)
      | Sum.inr b =>
          Quot.lift
            (fun y => match y with
              | Sum.inl a => (1, List.ofFn (ev a).val)
              | Sum.inr z => ((cube0_cells_isEmpty (m := 2) (by omega)).false z).elim)
            (by intro _ _ r; obtain ⟨s⟩ := r
                exact ((cube0_cells_isEmpty (m := 2) (by omega)).false s).elim)
            b)
    (by intro _ _ r; obtain ⟨s⟩ := r
        exact ((cube0_cells_isEmpty (m := 2) (by omega)).false s).elim)
    c

/-- A cell of `wedge[2,2]`: the top `2`-cell of block `0`, via the block inclusion `ιᵂ`. -/
def cellBlock0 : (⋁([2, 2] : List ℕ+)).cells 2 :=
  (ιᵂ ([2, 2] : List ℕ+) 0)⟪2⟫ (canonicalMap (topCell 2))

#eval readW22 cellBlock0                                                    -- (0, [none, none])

-- The action of a concrete wedge map (`ιᵂ 1 : □² ⟶ ⋁[2,2]`) on `□²`'s top cell.
#eval readW22 ((ιᵂ ([2, 2] : List ℕ+) 1)⟪2⟫ (canonicalMap (topCell 2)))     -- (1, [none, none])

/-- Machine-checked: the block-0 cell reads back as the full square in block `0`. -/
example : readW22 cellBlock0 = (0, [none, none]) := by native_decide
