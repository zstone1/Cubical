import CubeChains.Testing.Lowering

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false

/-!
# Testing/Examples

Example finite precubical sets, and lowering-conjecture tests on them.
Each example is a `FinBPSet` over a small named cell type.  We `#eval` a `Report`
and pin the headline boolean with `native_decide`.  See `Model.lean` for why this
combinatorial surrogate is a faithful and fully computable stand-in for the real
(noncomputable) `Ch K`.  This is the harness entry point (`lake build
CubeChains.Testing.Examples`).

**Layer:** Testing.  **Imports:** `Testing/Lowering`.
-/

namespace CubeTest
namespace Examples

open FinBPSet

/-! ## The interval `□¹` and the square `□²` (rigid baselines) -/

/-- Cells of the interval `□¹`: two vertices and an edge. -/
inductive I | v0 | v1 | e
  deriving DecidableEq, Repr

/-- The interval `□¹` as a bi-pointed precubical set. -/
def interval : FinBPSet I where
  cellList := [.v0, .v1, .e]
  dim := fun c => match c with | .e => 1 | _ => 0
  face := fun ε i c => match c, i with
    | .e, 0 => some (cond ε .v1 .v0)
    | _, _  => none
  init := .v0
  final := .v1

/-- Cells of the square `□²`: 4 vertices, 4 edges, 1 square. -/
inductive Sq | c00 | c10 | c01 | c11 | e0_ | e1_ | e_0 | e_1 | sq
  deriving DecidableEq, Repr

/-- The square `□²`.  Edges: `e0_ = {0}×□` (`x₀=0`), `e1_ = {1}×□`, `e_0 = □×{0}`,
`e_1 = □×{1}`. -/
def square : FinBPSet Sq where
  cellList := [.c00, .c10, .c01, .c11, .e0_, .e1_, .e_0, .e_1, .sq]
  dim := fun c => match c with
    | .sq => 2 | .e0_ | .e1_ | .e_0 | .e_1 => 1 | _ => 0
  face := fun ε i c => match c, i with
    | .e0_, 0 => some (cond ε .c01 .c00)   -- x₀=0, vary x₁
    | .e1_, 0 => some (cond ε .c11 .c10)   -- x₀=1, vary x₁
    | .e_0, 0 => some (cond ε .c10 .c00)   -- x₁=0, vary x₀
    | .e_1, 0 => some (cond ε .c11 .c01)   -- x₁=1, vary x₀
    | .sq, 0  => some (cond ε .e1_ .e0_)   -- face along x₀
    | .sq, 1  => some (cond ε .e_1 .e_0)   -- face along x₁
    | _, _    => none
  init := .c00
  final := .c11

/-! ## The four-square loop (the necessity witness)

Vertices `o, w, wp, z1, z2, t`; edges `a:o→w, ap:o→wp, b1:w→z1, b2:w→z2,
g1:wp→z1, g2:wp→z2, d1:z1→t, d2:z2→t`; four square "forks" `T12, T23, T34, T41`.
The four directed paths `o ⤳ t` form a 4-cycle joined by the squares; the rotation
`ρ` is a (non-orientation-preserving) automorphism of the chain poset not realized
by any map of `K`.  Lowering should still hold *with* orientation-preservation. -/

/-- Cells of the four-square loop. -/
inductive FS
  | o | w | wp | z1 | z2 | t
  | a | ap | b1 | b2 | g1 | g2 | d1 | d2
  | T12 | T23 | T34 | T41
  deriving DecidableEq, Repr

/-- The four-square loop. -/
def fourSquare : FinBPSet FS where
  cellList := [.o, .w, .wp, .z1, .z2, .t,
               .a, .ap, .b1, .b2, .g1, .g2, .d1, .d2,
               .T12, .T23, .T34, .T41]
  dim := fun c => match c with
    | .o | .w | .wp | .z1 | .z2 | .t => 0
    | .a | .ap | .b1 | .b2 | .g1 | .g2 | .d1 | .d2 => 1
    | .T12 | .T23 | .T34 | .T41 => 2
  face := fun ε i c => match c, i with
    -- edges
    | .a,  0 => some (cond ε .w .o)
    | .ap, 0 => some (cond ε .wp .o)
    | .b1, 0 => some (cond ε .z1 .w)
    | .b2, 0 => some (cond ε .z2 .w)
    | .g1, 0 => some (cond ε .z1 .wp)
    | .g2, 0 => some (cond ε .z2 .wp)
    | .d1, 0 => some (cond ε .t .z1)
    | .d2, 0 => some (cond ε .t .z2)
    -- T12 : w ⤳ t, corners (0,0)=w (1,1)=t (0,1)=z1 (1,0)=z2
    | .T12, 0 => some (cond ε .d2 .b1)
    | .T12, 1 => some (cond ε .d1 .b2)
    -- T34 : wp ⤳ t.  Oriented (coord 0 ↔ b/g via z2) so the symmetry
    -- `w↔wp, z1↔z2` maps T12 to T34 index-preservingly.
    | .T34, 0 => some (cond ε .d1 .g2)
    | .T34, 1 => some (cond ε .d2 .g1)
    -- T23 : o ⤳ z2, corners (0,0)=o (1,1)=z2 (0,1)=w (1,0)=wp
    | .T23, 0 => some (cond ε .g2 .a)
    | .T23, 1 => some (cond ε .b2 .ap)
    -- T41 : o ⤳ z1.  Oriented so `w↔wp, z1↔z2` maps T23 to T41.
    | .T41, 0 => some (cond ε .b1 .ap)
    | .T41, 1 => some (cond ε .g1 .a)
    | _, _    => none
  init := .o
  final := .t

/-- The four-square loop with the square `T41` removed.  Still **globally connected**
(`chConnected`), but the `o ⤳ z1` interval loses its only filling square, so the
`d1`-fiber `{[a,b1,d1], [ap,g1,d1]}` becomes two incomparable chains — `fiberConnected`
fails.  It is nonetheless `coherentAll` (its cubey group is too small to exploit the
gap), so it separates *fiber* connectivity from both *global* connectivity and
*coherence*. -/
def threeSquare : FinBPSet FS where
  cellList := [.o, .w, .wp, .z1, .z2, .t,
               .a, .ap, .b1, .b2, .g1, .g2, .d1, .d2,
               .T12, .T23, .T34]                       -- no T41
  dim := fun c => match c with
    | .o | .w | .wp | .z1 | .z2 | .t => 0
    | .a | .ap | .b1 | .b2 | .g1 | .g2 | .d1 | .d2 => 1
    | .T12 | .T23 | .T34 | .T41 => 2
  face := fun ε i c => match c, i with
    | .a,  0 => some (cond ε .w .o)
    | .ap, 0 => some (cond ε .wp .o)
    | .b1, 0 => some (cond ε .z1 .w)
    | .b2, 0 => some (cond ε .z2 .w)
    | .g1, 0 => some (cond ε .z1 .wp)
    | .g2, 0 => some (cond ε .z2 .wp)
    | .d1, 0 => some (cond ε .t .z1)
    | .d2, 0 => some (cond ε .t .z2)
    | .T12, 0 => some (cond ε .d2 .b1)
    | .T12, 1 => some (cond ε .d1 .b2)
    | .T34, 0 => some (cond ε .d1 .g2)
    | .T34, 1 => some (cond ε .d2 .g1)
    | .T23, 0 => some (cond ε .g2 .a)
    | .T23, 1 => some (cond ε .b2 .ap)
    | _, _    => none
  init := .o
  final := .t

/-! ## Two squares glued along an edge (a `2×1` grid) -/

/-- Cells of the `2×1` grid: vertices `vIJ` (column `I∈{0,1,2}`, row `J∈{0,1}`),
horizontal edges `hIJ`, vertical edges `wI`, squares `S0` (left), `S1` (right). -/
inductive G
  | v00 | v10 | v20 | v01 | v11 | v21
  | h00 | h10 | h01 | h11 | w0 | w1 | w2
  | S0 | S1
  deriving DecidableEq, Repr

/-- The `2×1` grid of squares. -/
def grid2 : FinBPSet G where
  cellList := [.v00, .v10, .v20, .v01, .v11, .v21,
               .h00, .h10, .h01, .h11, .w0, .w1, .w2, .S0, .S1]
  dim := fun c => match c with
    | .S0 | .S1 => 2
    | .h00 | .h10 | .h01 | .h11 | .w0 | .w1 | .w2 => 1
    | _ => 0
  face := fun ε i c => match c, i with
    | .h00, 0 => some (cond ε .v10 .v00)
    | .h10, 0 => some (cond ε .v20 .v10)
    | .h01, 0 => some (cond ε .v11 .v01)
    | .h11, 0 => some (cond ε .v21 .v11)
    | .w0,  0 => some (cond ε .v01 .v00)
    | .w1,  0 => some (cond ε .v11 .v10)
    | .w2,  0 => some (cond ε .v21 .v20)
    | .S0, 0 => some (cond ε .w1 .w0)     -- vary x₀ (vertical edges)
    | .S0, 1 => some (cond ε .h01 .h00)   -- vary x₁ (horizontal edges)
    | .S1, 0 => some (cond ε .w2 .w1)
    | .S1, 1 => some (cond ε .h11 .h10)
    | _, _   => none
  init := .v00
  final := .v21

/-! ## The four-square loop with its 2-cells removed (the 1-skeleton)

The four directed paths `o ⤳ t`, with NO squares.  Now every chain has dimension
sequence `[1,1,1]` and chains are pairwise incomparable (`Ch K` is discrete), so
*every* permutation of the four paths is an orientation-preserving automorphism —
and most disagree on shared edges.  This is where **coherence fails**: removing the
2-cells removes exactly the constraints that pinned the cube map. -/

inductive FG
  | o | w | wp | z1 | z2 | t
  | a | ap | b1 | b2 | g1 | g2 | d1 | d2
  deriving DecidableEq, Repr

/-- The four-square loop's 1-skeleton (vertices and edges only). -/
def fourPaths : FinBPSet FG where
  cellList := [.o, .w, .wp, .z1, .z2, .t, .a, .ap, .b1, .b2, .g1, .g2, .d1, .d2]
  dim := fun c => match c with
    | .o | .w | .wp | .z1 | .z2 | .t => 0
    | _ => 1
  face := fun ε i c => match c, i with
    | .a,  0 => some (cond ε .w .o)
    | .ap, 0 => some (cond ε .wp .o)
    | .b1, 0 => some (cond ε .z1 .w)
    | .b2, 0 => some (cond ε .z2 .w)
    | .g1, 0 => some (cond ε .z1 .wp)
    | .g2, 0 => some (cond ε .z2 .wp)
    | .d1, 0 => some (cond ε .t .z1)
    | .d2, 0 => some (cond ε .t .z2)
    | _, _   => none
  init := .o
  final := .t

/-! ## Standard cubes `□ⁿ` for any `n` (generic, correct by construction)

A `k`-cell of `□ⁿ` is a length-`n` list over `{*, 0, 1}` with exactly `k` stars
(`none = free`).  `face ε i` fixes the `i`-th free coordinate to `ε`.  This builds
`□³` (and beyond) without hand-encoding faces, giving a genuine 3-cell example. -/

/-- Replace the `i`-th free coordinate (`none`) of a cube cell with `some ε`;
`none` if there are not that many free coordinates. -/
def replaceNth (ε : Bool) : ℕ → List (Option Bool) → Option (List (Option Bool))
  | _, []          => none
  | i, none :: t   => if i = 0 then some (some ε :: t) else (replaceNth ε (i - 1) t).map (none :: ·)
  | i, some b :: t => (replaceNth ε i t).map (some b :: ·)

/-- All cells of `□ⁿ`: length-`n` lists over `{*, 0, 1}`. -/
def cubeCells : ℕ → List (List (Option Bool))
  | 0     => [[]]
  | n + 1 => [none, some false, some true].flatMap (fun o => (cubeCells n).map (o :: ·))

/-- The standard cube `□ⁿ` as a `FinBPSet`. -/
def stdCube (n : ℕ) : FinBPSet (List (Option Bool)) where
  cellList := cubeCells n
  dim := fun c => (c.filter Option.isNone).length
  face := fun ε i c => replaceNth ε i c
  init := List.replicate n (some false)
  final := List.replicate n (some true)

/-- The 3-cube `□³` (8 vertices, 12 edges, 6 squares, 1 three-cell). -/
def cube3 : FinBPSet (List (Option Bool)) := stdCube 3

/-! ## Reports and findings

Running `#eval _.report` on each example.  **The conjecture is refuted already at
`□²`:** it is *rigid* in the symmetry-free precubical model (`autK = [id]`), yet
`Ch(□²)` has the orientation-preserving automorphism that swaps the two "staircase"
edge-paths `[e_0,e1_]` and `[e0_,e_1]` — both of dimension sequence `[1,1]` — which
is therefore **not** in the image of `liftToCh` (`existence = false`).  The
four-square loop and the grid fail for the same reason (`Ch K` carries
staircase/reflection symmetries the symmetry-free `K` lacks).  This is a concrete
witness that the *provisional* `OrientationPreserving` (dimension-sequence
preservation; note it preserves altitude bands too) is **too weak** for the
lowering lemma in this setting.

The `2×1` grid, by contrast, **passes** (`existence = true`): gluing the two
squares pins their staircases, so `Ch K` has no extra orientation-preserving
symmetry.  So the failure is about *unpinned local cube symmetry*, not gluing
per se — the conjecture can still hold for suitably rigid `K`. -/

#eval interval.report
#eval square.report
#eval fourSquare.report
#eval grid2.report
#eval cube3.report
#eval (cube3.coherentAll, cube3.firstIncoherence)
-- coherent OP autos vs. realized by `Aut(□³)`:
#eval (cube3.opAutCh.length, (cube3.autK.map cube3.liftIdx).dedup.length)
#eval fourPaths.report
#eval (fourPaths.opAutCh.length, fourPaths.coherentAll)  -- (24, false): coherence FAILS
#eval fourPaths.firstIncoherence                          -- a witness (F, c, d₁, d₂)

-- The square is the minimal witness: rigid `K`, but `Ch K` has an extra symmetry.
#eval square.chains                      -- [[e_0,e1_], [e0_,e_1], [sq]]
#eval square.autK.length                 -- 1  (only the identity: □² is rigid)
#eval square.opAutCh                     -- [[0,1,2], [1,0,2]]  (id and the staircase swap)
#eval square.autK.map square.liftIdx     -- [[0,1,2]]  (image of liftToCh: only id)

/-! ### The findings, pinned by `native_decide`

`checkLowering K` is `validInput ∧ existence ∧ soundness ∧ injective`. -/

-- All four examples are well-formed and satisfy the three side conditions.
example : interval.validInput = true := by native_decide
example : square.validInput = true := by native_decide
example : fourSquare.validInput = true := by native_decide
example : grid2.validInput = true := by native_decide

-- Uniqueness/faithfulness always holds (matches `liftToCh_injective`).
example : interval.report.injective = true := by native_decide
example : square.report.injective = true := by native_decide
example : fourSquare.report.injective = true := by native_decide
example : grid2.report.injective = true := by native_decide

-- The interval `□¹` satisfies the full lowering conjecture.
example : interval.checkLowering = true := by native_decide

-- **The square `□²` refutes it**: rigid `K`, but an unrealized OP auto of `Ch K`.
example : square.autK.length = 1 := by native_decide
example : square.opAutCh.length = 2 := by native_decide
example : square.report.existence = false := by native_decide
example : square.checkLowering = false := by native_decide

-- The four-square loop fails the same way (existence fails).
example : fourSquare.report.existence = false := by native_decide
example : fourSquare.checkLowering = false := by native_decide

-- The grid, by contrast, PASSES: gluing pins the staircases.
example : grid2.report.existence = true := by native_decide
example : grid2.checkLowering = true := by native_decide

/-! ### The refined question: does altitude-preservation force *coherent* cube
choices?

`coherentAll K`: every orientation/altitude-preserving automorphism of `Ch K`
induces a **well-defined** cube map (if a cube `c` lies in chains `p₁, p₂`, then
`F p₁` and `F p₂` agree on the cube at `c`'s altitude band).  `firstIncoherence`:
a witness `(F, c, d₁, d₂)` if some `F` disagrees.

**Answer: it depends on `K` — coherence can FAIL.**  It *holds* when `K` has enough
higher cells to constrain `Ch K`: the non-simply-connected four-square loop (4
automorphisms, shared cubes) and `□³` (27 cells, 13 chains, the 6-element axis-
permutation group `S₃`) are both coherent.  But strip the 2-cells off the four-
square loop (`fourPaths`, its 1-skeleton) and `Ch K` becomes *discrete* — all four
paths are dimension-sequence `[1,1,1]` and pairwise incomparable, so every
permutation (`S₄`, 24 of them) is an orientation-preserving automorphism, and most
disagree on shared edges.  `firstIncoherence` returns a witness: the swap of two
paths sends the shared edge `d1` to both `d1` and `d2`.

So altitude-preservation does **not** force a well-defined cube map in general; the
higher cells are exactly what pin it.  Lowering needs *both* coherence (enough
higher cells) *and* naturality (`σ_F` precubical), and each can fail independently.

But coherence is **not** lowering: `σ_F` need not be a precubical (face-commuting)
map.  For `□²` the staircase swap's `σ_F` is the *axis swap* `e_0↔e0_, e1_↔e_1` —
well-defined, but it does not commute with the face maps, so it is not an
automorphism of `□²`.  The gap shows up numerically as
`#(realized = numImage) < #(coherent) = numOPAutCh`. -/

#eval (interval.coherentAll, square.coherentAll, fourSquare.coherentAll, grid2.coherentAll)
#eval square.firstIncoherence       -- none: coherent
#eval fourSquare.firstIncoherence   -- none: coherent (even the unrealized reflections)

-- Coherence always holds — including the 3-cell stress test `□³`, which has a
-- 6-element symmetry group of `Ch`-automorphisms (the axis permutations `S₃`).
example : interval.coherentAll = true := by native_decide
example : square.coherentAll = true := by native_decide
example : fourSquare.coherentAll = true := by native_decide
example : grid2.coherentAll = true := by native_decide
example : cube3.coherentAll = true := by native_decide

-- …yet `□³` is rigid, so all 6 of those coherent autos but the identity are
-- unrealized: the induced cube maps are the axis permutations, which are honest
-- cell bijections but *not* precubical (face-commuting) maps.
example : cube3.validInput = true := by native_decide
example : cube3.opAutCh.length = 6 := by native_decide
example : cube3.report.existence = false := by native_decide

-- **Coherence FAILS** once the 2-cells are removed: `Ch (fourPaths)` is discrete,
-- so all `4! = 24` permutations are orientation-preserving automorphisms, and most
-- disagree on shared edges.
example : fourPaths.validInput = true := by native_decide
example : fourPaths.opAutCh.length = 24 := by native_decide
example : fourPaths.coherentAll = false := by native_decide
example : fourPaths.firstIncoherence.isSome = true := by native_decide

-- …but for □² and the four-square loop, strictly more autos are coherent than are
-- realized by `Aut K` (so coherence ⇏ lowering; the obstruction is naturality).
#eval (fourSquare.opAutCh.length,                       -- coherent OP autos: 4
       (fourSquare.autK.map fourSquare.liftIdx).dedup.length)  -- realized: 2

/-! ### `fourPaths`: `Aut(Ch K) = S₄`, but `Aut K = V₄` (the fork-flip group)

`Ch(fourPaths)` is the **discrete** category on the 4 maximal directed paths `o ⤳ t`:

    0 = [a,b1,d1]   1 = [a,b2,d2]   2 = [ap,g1,d1]   3 = [ap,g2,d2]

all of dimension sequence `[1,1,1]` and pairwise incomparable.  So "cubey"
(dimension- + inclusion-preserving, the property every `liftToCh σ` enjoys —
`liftToCh_hom_map_φ`) is **vacuous**: with no non-identity morphisms there are no
inclusions to preserve and one dimension class, so *every* one of the `4! = 24`
permutations is an orientation-preserving automorphism — `Aut(Ch K) ≅ S₄`.

But the paths are not abstract points: they are the `2×2` product
`{a,ap} × {d1,d2}` — `path = (prefix out of o, suffix into t)` — and two paths share
their `o→·` prefix iff they agree in the first coordinate, share their `·→t` suffix
iff in the second.  `Aut K` is exactly the symmetries of this product:
(flip prefixes `a↔ap`, the `o`-fork: `w↔wp, bᵢ↔gᵢ`) × (flip suffixes `d1↔d2`, the
`t`-fork: `z1↔z2, b1↔b2, g1↔g2`) = `S₂ × S₂ = V₄`.  Via `liftToCh` these are the
three **double-transpositions** + id:

    id ↦ [0,1,2,3]   t-fork ↦ [1,0,3,2]   o-fork ↦ [2,3,0,1]   both ↦ [3,2,1,0]

i.e. `liftToCh` embeds `Aut K = V₄` as the **normal** Klein-four subgroup of
`Aut(Ch K) = S₄`; the unrealized cubey functors are the quotient `S₄/V₄ ≅ S₃` (20 of
24).  A single transposition like `(0 1)` cannot lower: it fixes paths 2,3 — hence
fixes `d1` — yet must send `d1` (shared by paths 0 *and* 2) also to `d2`, the
incoherence `firstIncoherence` reports.  The cell-**sharing** that cuts `S₄` down to
`V₄` lives in `K` but is invisible to the discrete `Ch K`; the 2-cells of
`fourSquare` are exactly what record it (there `opAutCh` drops to 4). -/

#eval fourPaths.autK.length                          -- 4  (the fork-flip group V₄)
#eval (fourPaths.autK.map fourPaths.liftIdx).dedup   -- id + the 3 double-transpositions
example : fourPaths.autK.length = 4 := by native_decide
example : (fourPaths.autK.map fourPaths.liftIdx).dedup.length = 4 := by native_decide
example : fourPaths.opAutCh.length = 24 := by native_decide

/-! ### The coherence theorem: *fiber*-connectivity ⟹ coherence

**Claim.** If for every cube `c` the *fiber* `Fib(c)` (= the chains containing `c`) is
connected in the refinement poset, then every orientation/altitude-preserving
automorphism `F` of `Ch K` induces a *well-defined* cube map (`coherentAll`).

**Proof (the cover lemma).**  An automorphism `F` of the chain poset preserves the
covering relation, and being orientation-preserving it preserves dimension sequences,
hence the altitude band of every cube.  Let `q ⋖ p` be a cover — `p` refines `q` by
splitting exactly one cube `C` of `q` into a length-2 sub-chain, at `C`'s band.  Then
`F q ⋖ F p` splits one cube of `F q`, necessarily at the *same* band (dimension
sequences are preserved).  So `F p` and `F q` agree at every band except `C`'s.  Now
if a cube `c ≠ C` lies in *both* `p` and `q` (i.e. `c` is not the split cube), its
band is untouched, so `(F p)` and `(F q)` carry `c`'s band to the **same** cube.
Hence the image of `c` is constant along every `c`-preserving cover, so it is constant
on each connected component of `Fib(c)`.  If `Fib(c)` is connected, the image is
unique — coherence at `c`.  ∎

Equivalently `Fib(c) ≅ Ch(init ⤳ vertex₀ c) × Ch(vertex₁ c ⤳ final)`, connected iff
both interval-posets are; so a clean sufficient condition is "**every interval
`Ch(x ⤳ y)` is connected**".

**The hypothesis is *fiber* (local), not *global*, connectivity.**  `threeSquare` is
globally connected (`chConnected`) yet `fiberConnected` fails: deleting `T41` leaves
the `o ⤳ z1` interval with two unlinked routes, so the `d1`-fiber is disconnected.
(It is still `coherentAll` — fiber-connectivity is *sufficient*, not necessary: its
cubey group is too small to exploit the gap.  Whether *global* connectivity alone
forces coherence is not settled here.)  `fourPaths`, by contrast, is fiber- *and*
globally disconnected, and there an `F` does exploit the gap — incoherence. -/

-- fiber-connected ⟹ coherent, on every fiber-connected example:
example : (interval.fiberConnected && interval.coherentAll) = true := by native_decide
example : (square.fiberConnected && square.coherentAll) = true := by native_decide
example : (grid2.fiberConnected && grid2.coherentAll) = true := by native_decide
example : (fourSquare.fiberConnected && fourSquare.coherentAll) = true := by native_decide
example : (cube3.fiberConnected && cube3.coherentAll) = true := by native_decide

-- `threeSquare`: globally connected, fiber-DISCONNECTED, yet still coherent — so the
-- right hypothesis is the fiber one, and it is sufficient but not necessary.
#eval threeSquare.chains.filter (fun ch => memB FS.d1 ch)  -- the disconnected d1-fiber
example : threeSquare.chConnected = true := by native_decide
example : threeSquare.fiberConnected = false := by native_decide
example : threeSquare.coherentAll = true := by native_decide

-- `fourPaths`: fiber- and globally disconnected, and genuinely incoherent.
example : fourPaths.chConnected = false := by native_decide
example : fourPaths.fiberConnected = false := by native_decide
example : fourPaths.coherentAll = false := by native_decide

/-! ### The lowering criterion: `coherent ∧ σ_F precubical ⟺ lowers`

Lowering decomposes into **two independent** conditions on an orientation-preserving
`F`, both about its induced cell map `σ_F`:

* **coherence** — `σ_F` is *well-defined* (`coherentFullF`); supplied by connected
  fibers (the coherence theorem above);
* **naturality** — `σ_F` is *precubical*, i.e. commutes with the face maps
  (`precubicalF`).

**Claim 1.**  `F` lowers (`F = liftToCh σ_F`, `σ_F ∈ Aut K`) iff both hold.
*Proof.* (⇐) coherence makes `σ_F : cells → cells` a function; it is a bijection
(`σ_{F⁻¹} = σ_F⁻¹`) fixing `init`/`final` (the extreme-altitude vertices), and
precubical, so `σ_F ∈ Aut K`; and `F p` relabels `p`'s cubes by `σ_F`, i.e.
`F = liftToCh σ_F`.  (⇒) if `F = liftToCh σ` then `σ_F = σ`, which is well-defined
and precubical.  ∎

So the realized (lifted) automorphisms are *exactly* `{F ∈ opAutCh : lowersBySigma F}`.
This is verified on every example below.  The naive "coherent ⟹ lowers" is **false**:
in `□²` the staircase-swap is coherent but its `σ_F` is the **axis swap**
`e_0↔e0_, e1_↔e_1` — a well-defined cell bijection that is *not* precubical, so it
does not lower.  (Connectivity gives coherence but never naturality: `□²`/`□³` have
connected fibers, yet carry exactly these non-precubical axis symmetries.) -/

-- Claim 1, made precise and checked: the autos that lower are exactly the ones
-- whose induced `σ_F` is well-defined and precubical.
example : interval.opAutCh.all (fun F =>
    interval.lowersBySigma F == memB F (interval.autK.map interval.liftIdx)) = true := by
  native_decide
example : square.opAutCh.all (fun F =>
    square.lowersBySigma F == memB F (square.autK.map square.liftIdx)) = true := by native_decide
example : grid2.opAutCh.all (fun F =>
    grid2.lowersBySigma F == memB F (grid2.autK.map grid2.liftIdx)) = true := by native_decide
example : fourSquare.opAutCh.all (fun F =>
    fourSquare.lowersBySigma F == memB F (fourSquare.autK.map fourSquare.liftIdx)) = true := by
  native_decide
example : cube3.opAutCh.all (fun F =>
    cube3.lowersBySigma F == memB F (cube3.autK.map cube3.liftIdx)) = true := by native_decide
example : fourPaths.opAutCh.all (fun F =>
    fourPaths.lowersBySigma F == memB F (fourPaths.autK.map fourPaths.liftIdx)) = true := by
  native_decide

-- The `□²` staircase swap `[1,0,2]`: coherent, but `σ_F` is NOT precubical — so the
-- naive "coherent ⟹ lowers" fails; the precubical (naturality) condition is essential.
example : square.coherentFullF [1, 0, 2] = true := by native_decide
example : square.precubicalF [1, 0, 2] = false := by native_decide

end Examples
end CubeTest
