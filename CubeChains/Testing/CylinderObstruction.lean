import CubeChains.Testing.Lowering

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false

/-!
# Testing/CylinderObstruction

Is the cylinder ⟹ pointed-functor construction FATALLY obstructed (no-degeneracy)?
This file answers a single decision problem for the cylinder program.  (Verdict: NOT
fatal — the obstruction it probes was subsequently resolved in
`Cylinder/CylinderRefine.lean`, where the deliverable `cylToPointedR` is built green and
sorry-free; this file is the finite `native_decide` witness that motivated it.)

> For a **rel-interface** cylinder, are the two flat chain-ends
> `b₀ = (dims, p ≫ leftLeg)` and `b₁ = (dims, p ≫ rightLeg)` zigzag-connected in
> `FreeGroupoid (Ch K)` (equivalently, in the same connected component / π₀ of
> `Ch K`)?

If YES, the pointed-functor `θ : Lgrpd ⟶ Rgrpd` exists (its components are the
zigzags `b₀ ⇝ b₁`), even though the *naive staircase* closing step cannot be a
single refinement (it would collapse a trailing `□¹` self-loop edge — a degeneracy
that the symmetry-free `PrecubicalSet = Boxᵒᵖ ⥤ Type` lacks).  If NO for some valid
cylinder, the construction genuinely fails (a negative result like the lowering
refutation).

The mathlib bridge `connectedComponentsFreeGroupoidEquiv` gives
`π₀ (Ch K) = π₀ (FreeGroupoid (Ch K))`, so the question is exactly whether `b₀` and
`b₁` lie in the same **zigzag-connected component** of the finite chain poset — a
property the `FinBPSet` harness (`chainsConnected`) decides by `native_decide`.

## The geometry encoded here

A rel-interface cylinder only exists when `K` is **self-linked at its basepoints**:
the interface vertices `E.init`/`E.final` are swept by `cyl` along *self-loop edges*
at `K.init`/`K.final`.  The **smallest** such cylinder takes `dims = [1]`, i.e.
`E = □¹`, so the cylinder map is `cyl : □¹ ⊗ □¹ = □² ⟶ K` — a single square.

Reading off the four faces of that square (coordinate `0` = the block/`E`
direction, coordinate `1` = the cylinder/interval direction):

* bottom (`coord 1 = 0`) `↦ leftLeg`  edge `b0e : init ⟶ final`   (this is `b₀`)
* top    (`coord 1 = 1`) `↦ rightLeg` edge `b1e : init ⟶ final`   (this is `b₁`)
* left   (`coord 0 = 0`, over `E.init`)  `↦` self-loop `sInit : init ⟶ init`
* right  (`coord 0 = 1`, over `E.final`) `↦` self-loop `sFin  : final ⟶ final`
* the square itself `↦` a 2-cell `pSq` (the prism cube `R`).

All four corners of the cylinder square collapse onto `{init, final}` (rel
interface), so `K` has exactly two vertices.  `b₀ = [b0e]`, `b₁ = [b1e]`.
-/

namespace CubeTest
namespace Examples

open FinBPSet

/-- Cells of the smallest `K` that admits a rel-interface cylinder over `E = □¹`:
two vertices `init`,`final`; two parallel "leg" edges `b0e`,`b1e : init ⟶ final`;
a self-loop `sInit` at `init` and `sFin` at `final` (the cylinder over the interface
vertices); and the filling square `pSq` (the prism cube `R`). -/
inductive Cyl
  | init | fin
  | b0e | b1e            -- the two legs (bottom/top of the prism square)
  | sInit | sFin         -- the interface self-loops (left/right of the square)
  | pSq                  -- the filling 2-cell (the prism cube R)
  deriving DecidableEq, Repr

/-- The minimal rel-interface cylinder `K`.  Square orientation:
coordinate `0` = block direction (faces `false0 = sInit`, `true0 = sFin`),
coordinate `1` = cylinder direction (faces `false1 = b0e`, `true1 = b1e`). -/
def cylSquare : FinBPSet Cyl where
  cellList := [.init, .fin, .b0e, .b1e, .sInit, .sFin, .pSq]
  dim := fun c => match c with
    | .pSq => 2
    | .b0e | .b1e | .sInit | .sFin => 1
    | _ => 0
  face := fun ε i c => match c, i with
    | .b0e, 0 => some (cond ε .fin .init)    -- init ⟶ final
    | .b1e, 0 => some (cond ε .fin .init)    -- init ⟶ final
    | .sInit, 0 => some .init                -- self-loop at init
    | .sFin, 0 => some .fin                  -- self-loop at final
    | .pSq, 0 => some (cond ε .sFin .sInit)  -- block direction: false ↦ sInit, true ↦ sFin
    | .pSq, 1 => some (cond ε .b1e .b0e)     -- cyl direction:   false ↦ b0e,   true ↦ b1e
    | _, _ => none
  init := .init
  final := .fin

/-! ## Sanity: the cylinder is geometrically valid, and `b₀`,`b₁` are as intended -/

-- Well-formed (precubical identity holds for the square `pSq`).
#eval cylSquare.wellFormed
-- The vertices: every face's extreme vertices land in {init, final}.
#eval (cylSquare.vertex0 Cyl.b0e, cylSquare.vertex1 Cyl.b0e)   -- (init, fin)
#eval (cylSquare.vertex0 Cyl.pSq, cylSquare.vertex1 Cyl.pSq)   -- (init, fin)
#eval (cylSquare.vertex0 Cyl.sInit, cylSquare.vertex1 Cyl.sInit) -- (init, init): self-loop
#eval (cylSquare.vertex0 Cyl.sFin,  cylSquare.vertex1 Cyl.sFin)  -- (fin, fin):   self-loop

-- `b0e`/`b1e` are faces of the square `pSq` (the bottom/top faces).
#eval (cylSquare.isFace Cyl.b0e Cyl.pSq, cylSquare.isFace Cyl.b1e Cyl.pSq)  -- (true, true)

/-! ## The decision: are `b₀ = [b0e]` and `b₁ = [b1e]` zigzag-connected in `Ch K`?

A self-linked `K` has *self-loop* edges (`sInit`/`sFin`), and the harness's `chains`
enumerator will append a self-loop at `final` arbitrarily often (fuel-bounded), so the
full object list of `Ch K` is cluttered with chains like `[pSq, sFin, sFin, …]`.
Those extra objects are harmless for the connectivity question (more objects in a
component only help), but they make the *full*-`chains` flood expensive and noisy.

We therefore exhibit the connecting zigzag **directly and explicitly**: the three
relevant objects `b₀ = [b0e]`, `R = [pSq]`, `b₁ = [b1e]`, with the two refinements
`b₀ ⟶ R` and `b₁ ⟶ R`.  `chainsConnected [b₀, R, b₁]` floods comparability over
*exactly these three objects*, so `true` means precisely "`b₀` and `b₁` are in one
zigzag-component" — witnessed by `b₀ ⟶ R ⟵ b₁`. -/

/-- The flat bottom end `b₀ = (dims=[1], p ≫ leftLeg)` as a chain object. -/
def b0Chain : List Cyl := [.b0e]
/-- The flat top end `b₁ = (dims=[1], p ≫ rightLeg)` as a chain object. -/
def b1Chain : List Cyl := [.b1e]
/-- The prism cube `R` as a chain object (dimSeq `[2]`). -/
def RChain : List Cyl := [.pSq]

-- The refinements that connect the flat ends to the prism cube `R`:
--   b₀ = [b0e] ⟶ [pSq] = R   (b0e is the bottom face of pSq)
--   b₁ = [b1e] ⟶ [pSq] = R   (b1e is the top face of pSq)
#eval cylSquare.chLe b0Chain RChain   -- true:  b₀ ⟶ R
#eval cylSquare.chLe b1Chain RChain   -- true:  b₁ ⟶ R

-- `b₀` and `b₁` are NOT directly comparable (both are edges, dimSeq [1]) — so the
-- connection genuinely goes THROUGH `R`, it is not a trivial single refinement.
#eval (cylSquare.chLe b0Chain b1Chain, cylSquare.chLe b1Chain b0Chain)  -- (false, false)

-- **The headline computation.**  Flooding comparability over `{b₀, R, b₁}`, the flat
-- ends `b₀` and `b₁` are in the SAME zigzag-connected component of `Ch K`, via the
-- length-2 zigzag `b₀ ⟶ R ⟵ b₁`.
#eval cylSquare.chainsConnected [b0Chain, RChain, b1Chain]  -- true

/-! ## Findings, pinned by `native_decide` -/

-- The example is a well-formed precubical set.
example : cylSquare.wellFormed = true := by native_decide

-- The two closing refinements into the prism cube `R` exist (`b₀ ⟶ R`, `b₁ ⟶ R`).
example : cylSquare.chLe b0Chain RChain = true := by native_decide
example : cylSquare.chLe b1Chain RChain = true := by native_decide

-- The flat ends are mutually INCOMPARABLE: the zigzag must route through `R`.
example : cylSquare.chLe b0Chain b1Chain = false := by native_decide
example : cylSquare.chLe b1Chain b0Chain = false := by native_decide

-- **THE VERDICT (NOT FATAL): `b₀` and `b₁` ARE zigzag-connected in `Ch K`,**
-- via the cospan `b₀ ⟶ R ⟵ b₁` (flood over the three objects `{b₀, R, b₁}`).
example : cylSquare.chainsConnected [b0Chain, RChain, b1Chain] = true := by native_decide

/-!
## Verdict: **NOT FATAL.**

For the smallest valid rel-interface cylinder (`dims = [1]`, the single-square
cylinder), the two flat ends `b₀ = [b0e]` and `b₁ = [b1e]` are zigzag-connected in
`Ch K` by the length-2 zigzag

        b₀ = [b0e]  ⟶  [pSq] = R  ⟵  [b1e] = b₁

where `b0e`/`b1e` are the bottom/top faces of the prism cube `pSq`.  So the
pointed-functor component `θ_{[1]} : of b₀ ⟶ of b₁` exists in `FreeGroupoid (Ch K)`
— it is `of(b₀→R) ≫ inv(of(b₁→R))`.

**Why this does not contradict the no-degeneracy obstruction.**  The local
no-degeneracy obstruction (later resolved in `Cylinder/CylinderRefine.lean`) is real but
*local*: the cospan `b₀ → R` fails to
be a `Ch'` (interface-preserving) morphism for an **interior** block, because there
`R`'s final corner sits one cylinder-level above the flat block's final corner, and
collapsing the trailing `□¹` self-loop would need a degeneracy.  But for the
**whole-chain single block** the block's endpoints ARE the basepoints `init`/`final`,
the self-loops at those basepoints close the gap, and `b₀ → R` IS a genuine refinement
(`chLe b₀ R = true`).  The connecting zigzag is the *direct* cospan into the prism
cube, NOT the naive staircase through boundary paths — so `θ` exists via a
**non-staircase witness**.

**A side observation (self-linked `K` has a non-poset `Ch K`).**  Because the
rel-interface forces self-loop edges at the basepoints, the combinatorial `Ch K`
acquires chains that traverse a basepoint self-loop arbitrarily often (e.g.
`[pSq, sFin]`, `[pSq, sFin, sFin]`, …) — the harness's `chains` enumerator pads with
the `final`-self-loop up to its fuel bound.  Ziemiański's `Ch K` is the *non-looping*
quotient; these extra objects only ADD to a component, so they cannot disconnect
`b₀` from `b₁`.  (This is also why we test the explicit three-object flood rather
than `chConnected` over the cluttered full list.)

**Caveat / scope.** This is decisive for `dims = [1]`.  For longer `dims` the prism
is edge-glued, not a single cube, so the connecting zigzag is the multi-cube fence;
the same self-loop-at-the-basepoint mechanism closes each end, and connectivity is
inherited block-by-block, but that general claim is not the single computation above.
The single-block case is the one the whole program reduces `θ` to (via `θ = (tauto
K).toTransf` whiskered across `Lgrpd_eq_comp`), so the construction is NOT fatally
obstructed: it just needs the cospan-into-`R` witness rather than the staircase one.

**Layer:** Testing.  **Imports:** `Testing/Lowering`.
-/

end Examples
end CubeTest

namespace CubeTest
namespace Examples
open FinBPSet

/-! ## Robustness: same verdict over the self-loop-padded object set

To rule out any artifact of restricting the flood to exactly `{b₀, R, b₁}`, we
re-run the flood over a larger object set that also includes the self-loop-padded
chains `[pSq, sFin]` and `[b0e, sFin]`, `[b1e, sFin]` (genuine objects of the
combinatorial `Ch K` when `K` is self-linked).  The verdict is unchanged: `b₀` and
`b₁` remain in one zigzag-component. -/
#eval cylSquare.chainsConnected
  [[.b0e], [.b1e], [.pSq], [.pSq, .sFin], [.b0e, .sFin], [.b1e, .sFin]]  -- true

example : cylSquare.chainsConnected
    [[.b0e], [.b1e], [.pSq], [.pSq, .sFin], [.b0e, .sFin], [.b1e, .sFin]] = true := by
  native_decide

end Examples
end CubeTest
