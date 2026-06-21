import CubeChains.Testing.Lowering

-- Property-testing file; `native_decide` is the intended engine.
set_option linter.style.nativeDecide false

/-!
# Does the MULTI-BLOCK cylinder sweep connect `ℓ·a` to `r·a` in the RefineObj face-poset?

`Testing/CylinderObstruction.lean` settled the **single-block** case (`dims = [1]`): the flat
ends `b₀`, `b₁` are connected via the direct cospan `b₀ → R ← b₁`.  A build agent then found
that the *naive telescoping* fold (pure prefix/suffix whiskering of per-block direct cospans)
does NOT typecheck for **multi-block** chains, because at an interior junction `w` the two
leg-images `leftLeg w` and `rightLeg w` are distinct vertices (connected only by the cylinder's
vertical prism edge over `w`), so a per-block prism cube `R_j` does not share endpoints with the
flat block ends `ℓc_j`, `r c_j`.  The agent flagged this as a possible fundamental wall.

This file decides the actual question — **connectivity**, not the particular fold — for the
smallest two-block rel-interface cylinder.  If `ℓ·a` and `r·a` are zigzag-connected in `chLe`
(the RefineObj face order, `Model.lean:111`), then the multi-block sweep EXISTS (it is that
zigzag) and the obstruction is *construction complexity* (the junction-bridge staircase), not a
wall.  If they are disconnected, it is a genuine negative result.

## The two-block cylinder `K`

Source `E = □¹ ∨ □¹` (a length-2 path with interior junction `w`).  The cylinder `E ⊗ □¹ ⟶ K`
is two prism squares `R1` (over block 1) and `R2` (over block 2) glued along the vertical edge
`ew` over `w`.  Cells:

* vertices `init, fin` (basepoints) and `mid0 = leftLeg w`, `mid1 = rightLeg w` (interior);
* bottom (left-leg) edges `lc1 : init→mid0`, `lc2 : mid0→fin`;
* top (right-leg) edges `rc1 : init→mid1`, `rc2 : mid1→fin`;
* the vertical junction edge `ew : mid0→mid1` (the cylinder over `w` — NOT a self-loop, the
  reason the naive fold fails);
* basepoint self-loops `sInit : init→init`, `sFin : fin→fin` (the rel-interface);
* prism squares `R1` (coord0 block: `sInit`/`ew`; coord1 cyl: `lc1`/`rc1`; so `init→mid1`) and
  `R2` (coord0 block: `ew`/`sFin`; coord1 cyl: `lc2`/`rc2`; so `mid0→fin`).

`ℓ·a = [lc1, lc2]` (init→mid0→fin), `r·a = [rc1, rc2]` (init→mid1→fin).
-/

namespace CubeTest
namespace Examples

open FinBPSet

inductive TB
  | init | fin | mid0 | mid1
  | lc1 | lc2 | rc1 | rc2 | ew | sInit | sFin
  | R1 | R2
  deriving DecidableEq, Repr

/-- The minimal two-block rel-interface cylinder. -/
def twoBlock : FinBPSet TB where
  cellList := [.init, .fin, .mid0, .mid1, .lc1, .lc2, .rc1, .rc2, .ew, .sInit, .sFin, .R1, .R2]
  dim := fun c => match c with
    | .R1 | .R2 => 2
    | .lc1 | .lc2 | .rc1 | .rc2 | .ew | .sInit | .sFin => 1
    | _ => 0
  face := fun ε i c => match c, i with
    | .lc1, 0 => some (cond ε .mid0 .init)   -- init → mid0
    | .lc2, 0 => some (cond ε .fin .mid0)     -- mid0 → fin
    | .rc1, 0 => some (cond ε .mid1 .init)    -- init → mid1
    | .rc2, 0 => some (cond ε .fin .mid1)     -- mid1 → fin
    | .ew, 0 => some (cond ε .mid1 .mid0)     -- mid0 → mid1  (vertical junction edge)
    | .sInit, 0 => some .init                 -- self-loop at init
    | .sFin, 0 => some .fin                   -- self-loop at fin
    | .R1, 0 => some (cond ε .ew .sInit)      -- block dir: false ↦ sInit, true ↦ ew
    | .R1, 1 => some (cond ε .rc1 .lc1)       -- cyl dir:   false ↦ lc1,   true ↦ rc1
    | .R2, 0 => some (cond ε .sFin .ew)       -- block dir: false ↦ ew,    true ↦ sFin
    | .R2, 1 => some (cond ε .rc2 .lc2)       -- cyl dir:   false ↦ lc2,   true ↦ rc2
    | _, _ => none
  init := .init
  final := .fin

/-! ## Sanity -/

-- Well-formed precubical set (both prism squares satisfy the cubical identity).
#eval twoBlock.wellFormed
-- Prism corners: R1 : init→mid1, R2 : mid0→fin (the level shift across the interval).
#eval (twoBlock.vertex0 TB.R1, twoBlock.vertex1 TB.R1)   -- (init, mid1)
#eval (twoBlock.vertex0 TB.R2, twoBlock.vertex1 TB.R2)   -- (mid0, fin)
-- The junction images are DISTINCT (this is what breaks the naive fold).
#eval (twoBlock.vertex1 TB.lc1, twoBlock.vertex0 TB.rc2)  -- (mid0, mid1): mid0 ≠ mid1

/-! ## The chains -/

/-- `ℓ·a` — the left-leg image of the 2-block source chain. -/
def la : List TB := [.lc1, .lc2]
/-- `r·a` — the right-leg image. -/
def ra : List TB := [.rc1, .rc2]
/-- Mixed chain: block 1 left, block 2 lifted to the prism cube `R2`. -/
def m1 : List TB := [.lc1, .R2]
/-- Mixed chain: block 1 lifted to `R1`, block 2 right. -/
def m2 : List TB := [.R1, .rc2]
/-- The **junction-bridge chain**: left block 1, the vertical edge `ew`, right block 2
(init→mid0→mid1→fin).  This is the common refinement that bridges the interior level mismatch. -/
def bridge : List TB := [.lc1, .ew, .rc2]

/-! ## The decision -/

-- The naive direct cospans FAIL at interior blocks (endpoints don't match):
--   `lc2 → R2`? `R2` is mid0→fin and `lc2` is mid0→fin, but as the WHOLE chain `la` the
--   junction is mid0 while `m2`'s junction is mid1. The connection is NOT a single cospan.
#eval twoBlock.chLe la m1   -- true:  ℓ·a → [lc1, R2]   (lc1↦lc1, lc2↦bottom of R2)
#eval twoBlock.chLe ra m2   -- true:  r·a → [R1, rc2]   (rc1↦top of R1, rc2↦rc2)
#eval twoBlock.chLe bridge m1 -- true: [lc1,ew,rc2] → [lc1,R2]  (ew↦left face, rc2↦top of R2)
#eval twoBlock.chLe bridge m2 -- true: [lc1,ew,rc2] → [R1,rc2]  (lc1↦bottom, ew↦right face)
-- `ℓ·a` and `r·a` are NOT directly comparable — the connection is a genuine zigzag.
#eval (twoBlock.chLe la ra, twoBlock.chLe ra la)  -- (false, false)

-- **THE HEADLINE.**  Flooding comparability over the staircase objects, `ℓ·a` and `r·a` are
-- in ONE zigzag-connected component, via
--    ℓ·a → [lc1,R2] ← [lc1,ew,rc2] → [R1,rc2] ← r·a
#eval twoBlock.chainsConnected [la, m1, bridge, m2, ra]   -- true

/-! ## Findings, pinned by `native_decide` -/

example : twoBlock.wellFormed = true := by native_decide
example : twoBlock.chLe la ra = false := by native_decide
example : twoBlock.chLe ra la = false := by native_decide
example : twoBlock.chLe la m1 = true := by native_decide
example : twoBlock.chLe ra m2 = true := by native_decide
example : twoBlock.chLe bridge m1 = true := by native_decide
example : twoBlock.chLe bridge m2 = true := by native_decide

-- **VERDICT (NOT a wall): the multi-block sweep EXISTS.**  `ℓ·a` and `r·a` are zigzag-connected
-- in the RefineObj face-poset for the two-block cylinder.
example : twoBlock.chainsConnected [la, m1, bridge, m2, ra] = true := by native_decide

/-!
## Verdict: the multi-block obstruction is **construction complexity, not a wall**.

For the smallest two-block rel-interface cylinder, `ℓ·a = [lc1,lc2]` and `r·a = [rc1,rc2]` are
zigzag-connected in `chLe` (the RefineObj face order) by the length-4 staircase

        ℓ·a  →  [lc1, R2]  ←  [lc1, ew, rc2]  →  [R1, rc2]  ←  r·a

The bridge object `[lc1, ew, rc2]` — left block 1, the **vertical junction edge** `ew`, right
block 2 — is the common refinement that absorbs the interior level mismatch the naive fold could
not handle.  So the per-object path `η x` that `pointedOfPaths` needs DOES exist as a real
`FreeGroupoid` morphism; the multi-block `sweepR` must be built as this junction-bridge staircase
(the `P_j`/`R_j` fence with vertical-edge bridges — the same shape as `CylinderCh.lean`'s
staircase, but every refinement here is a genuine `RefineObj` morphism, no boundary-path
workaround and no closing-end obstruction).  The construction is substantial but unblocked.
-/

end Examples
end CubeTest
