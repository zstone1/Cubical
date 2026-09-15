import CubeChains.Precubical.Basic.Altitude
import CubeChains.Precubical.Chains.WedgeMap
import CubeChains.Precubical.Wedge.CubeMerge

/-!
# Precubical/Chains/Altitude — the cube's grading

`□ⁿ` is graded by the number of coordinates fixed at `1` (`cube_admitsAltitude`), and a serial
wedge is graded by pulling the grading back along its merge into a cube
(`serialWedge_admitsAltitude`).
-/

open CategoryTheory Opposite StdCube

namespace BPSet

/-- The altitude on `□ᴺ`: the number of coordinates a cell fixes at `1`. -/
def cubeAlt (N : ℕ) : ∀ m, (□N).cells m → ℤ :=
  fun _ x => (trueCount (Box.sign x) : ℤ)

/-- A face raises `trueCount` by `ε` (`Box.sign_coface_comp`). -/
theorem cube_isAltitude (N : ℕ) : (□N).toPsh.IsAltitude (cubeAlt N) := fun ε i x => by
  change (trueCount (Box.sign ((□N).toPsh.faceMap ε i x)) : ℤ)
    = (trueCount (Box.sign x) : ℤ) + (if ε then 1 else 0)
  rw [show Box.sign ((□N).toPsh.faceMap ε i x) = faceCell ε i (Box.sign x) from
    Box.sign_coface_comp ε i x, trueCount_face]
  push_cast
  ring

theorem cubeAlt_vtx (N : ℕ) (ε : Bool) : cubeAlt N 0 ((□N).vtx ε) = if ε then N else 0 := by
  cases ε
  · exact congrArg Nat.cast (trueCount_constVertex_false N)
  · exact congrArg Nat.cast (trueCount_constVertex_true N)

/-- **The standard cube admits an altitude.** -/
theorem cube_admitsAltitude (N : ℕ) : (□N).AdmitsAltitude :=
  ⟨cubeAlt N, cube_isAltitude N, cubeAlt_vtx N false⟩

/-- **Every serial wedge admits an altitude** — pulled back along its merge into a cube. -/
theorem serialWedge_admitsAltitude (d : List ℕ+) : (⋁d).AdmitsAltitude :=
  (CubeChains.nonempty_toCube d).elim fun χ => (cube_admitsAltitude _).of_hom χ

end BPSet
