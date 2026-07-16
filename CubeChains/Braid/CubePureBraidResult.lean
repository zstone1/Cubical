import CubeChains.Braid.SalvettiBridge
import CubeChains.Braid.CubePureBraid

/-!
# Braid/CubePureBraidResult — Goal 2, axiom-only: `ConcBraid (□n) ≅ Pₙ`

Discharges the `htarget` hypothesis of `CubePureBraid` from the `BRIDGE` lemma
(`cubeFrameDiff_braidSalEquiv`), completing "the cube's concurrency braid group is the pure braid
group" with no dependency beyond `salvettiConstruction_faithful` (Salvetti asphericity).
-/

open CategoryTheory

namespace CubeChains

/-- **The per-edge agreement** (`htarget`), discharged from `BRIDGE`.  The tope-crossing permutation
of a Salvetti edge is the event permutation of the corresponding cube refinement:
`crossPerm a b = cubeFrameDiff Y · (cubeFrameDiff X)⁻¹ = (cubeSh).map F = permCongr (evPerm' F)`. -/
theorem crossPerm_eq_evPerm (n : ℕ) (a b : Sal (braidCOM n)) (hab : a ≤ b) :
    crossPerm a b
      = (finCongr (nEvents_braidSalEquiv_obj n a)).permCongr
          (evPerm' ((braidSalEquiv n).functor.map (homOfLE hab))) := by
  simp only [crossPerm]
  rw [← cubeFrameDiff_braidSalEquiv n b, ← cubeFrameDiff_braidSalEquiv n a,
    ← cubeSh_map_eq ((braidSalEquiv n).functor.map (homOfLE hab)),
    cubeSh_map_eq_permCongr _ (nEvents_braidSalEquiv_obj n a)]

/-- **Goal 2 (`Cubical-xhj.6`), axiom-only.**  The concurrency braid group of the `n`-cube at its run
basepoint is the pure braid group `Pₙ`.  Depends only on `salvettiConstruction_faithful`. -/
noncomputable def cube_concBraid_pureBraid (n : ℕ) (hn : 0 < n) :
    ConcBraid (□n) (seqExec (x₀ hn)) ≃* PureBraid n :=
  cube_concBraid_mulEquiv_pureBraid n (crossPerm_eq_evPerm n) hn

end CubeChains
