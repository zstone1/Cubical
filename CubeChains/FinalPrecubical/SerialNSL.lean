import CubeChains.FinalPrecubical.CubeChainPoset

/-!
# FinalPrecubical/SerialNSL — serial wedges are non-self-linked

The linchpin of the Segal-route braid rebuild (`BRAID2_PLAN.md` §2.3, §Risk R1):
a plain serial wedge of cubes, `serialWedge B`, is **non-self-linked**.

Unlike the terminal object `Z` (a single `0`-cell, genuinely *not* NSL) and unlike the
pathological `Correspondence` counterexamples (corner-identified `□²`, cross-glued cubes),
a serial wedge glues its cube blocks only at junction *vertices* (distinct `0`-cells), so
each positive cell lives in a unique block that is itself a standard cube.

## Route

For a cell `c : (serialWedge B).cells n`:

* **`n = 0` (vertex).**  The canonical map `(serialWedge B).cubeMap c` is a map out of
  `□⁰`, whose source cells are subsingletons in every dimension, so its components are
  injective for free (`CubeChain.vertexMap_app_injective`).
* **`n ≥ 1` (positive cell).**  `c` factors through a *unique* block inclusion
  (`serialWedge_cell_exists`): `c = (serialWedge.ι B i).app _ x` for a cube cell
  `x : (cube (B.get i)).cells n`.  Yoneda then factors the canonical map as
  `cubeMap c = cubeMap x ≫ serialWedge.ι B i`, so its `m`-component is the composite of
  two injections — `cube_nonSelfLinked (B.get i)` (each block is a cube, `CubeChainPoset`)
  and `serialWedge_ι_app_injective` (block inclusions are monos).

**Layer:** FinalPrecubical.  **Imports:** `FinalPrecubical.CubeChainPoset` (which supplies
`cube_nonSelfLinked` and transitively the `Chains/WedgeMap` block combinatorics).
-/

open CategoryTheory Opposite

namespace FinalPrecubical

open BPSet CubeChain PrecubicalSet

/-- **Serial wedges are non-self-linked.**  Every positive cell lies in a unique cube block
(`serialWedge_cell_exists`), whose inclusion is a mono (`serialWedge_ι_app_injective`) and
which is itself non-self-linked (`cube_nonSelfLinked`); vertices map out of the subsingleton
`□⁰` (`vertexMap_app_injective`).  This is the hypothesis that lets `equivWedgeCat` apply to
the ambient serial wedge (`BRAID2_PLAN.md` §2.3, §Risk R1). -/
theorem serialWedge_nonSelfLinked (B : List ℕ+) : (BPSet.serialWedge B).NonSelfLinked := by
  intro n c m
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- Vertex case: `cubeMap c` maps out of `□⁰`, whose cells are subsingletons.
    subst hn0
    exact vertexMap_app_injective ((BPSet.serialWedge B).toPsh.cubeMap c)
  · -- Positive cell: factor through the unique block, a standard cube.
    obtain ⟨i, x, hx⟩ := serialWedge_cell_exists B hn c
    -- Yoneda factors the canonical map through the block inclusion.
    have hmor : (BPSet.serialWedge B).toPsh.cubeMap c
        = (BPSet.cube (B.get i : ℕ)).toPsh.cubeMap x ≫ BPSet.serialWedge.ι B i := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp]
      simp only [PrecubicalSet.cubeMap, Equiv.apply_symm_apply]
      exact hx.symm
    rw [hmor]
    -- The `m`-component is now a composite of two injections.
    intro a b hab
    apply cube_nonSelfLinked (B.get i : ℕ) n x m
    apply serialWedge_ι_app_injective B i
    exact hab

end FinalPrecubical
