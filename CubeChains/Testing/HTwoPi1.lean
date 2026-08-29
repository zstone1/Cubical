import CubeChains.Testing.HTwo

/-!
# Testing/HTwoPi1 — the groupoid completion, as a cross-check

`FreeGroupoid (C[W⁻¹]) = FreeGroupoid C`, so `π₁` of the execution poset is an invariant of the
localization whatever `W` is: equivalent localizations force isomorphic `π₁`.  It is a coarse one —
it cannot see a `3`-cell — and `present`'s relator deduplication is quadratic, so the `H²` poset at
`n = 4` (`1128` nodes, `47136` arrows) is out of its reach; the graded hom-sets of `Testing/HTwo`
are the sharp instrument.

Not built by `lake build CubeChains`.
-/

namespace CubeChains

/-- `⟨generators, relations, components, H₁⟩` of `π₁` of the nerve. -/
def pi1Data (L : FinLoc) : ℕ × ℕ × ℕ × ℕ × List ℕ :=
  let P := (present (toPoset L)).simplify
  (P.nGens, P.rels.size, P.components, P.homology)

/-! `H` at `n = 4`: removing the `24` one-bead executions removes `3`-cells of the Salvetti
complex, so `π₁` cannot tell them apart — as the graded hom-sets confirm it should not. -/

#eval (pi1Data (chStarLoc (SubCube.full 4)), pi1Data (chStarLoc (SubCube.boundary 4)))

/-! `H²` at `n = 3`, where the localizations really do differ. -/

#eval (pi1Data (hStarLoc (SubCube.full 3)), pi1Data (hStarLoc (SubCube.boundary 3)))

end CubeChains
