import CubeChains.Testing.CubeChainComplex

set_option linter.style.longLine false

/-!
# Testing/MorseReduction — a discrete Morse matching on `Ch K`

`Ch K` is the face poset of a CW structure on `P⃗(K)`: the cell of a chain `c` has dimension
`cellDim c = dimSum c - nbeads c` (a product of permutohedra, one per bead), and merging two
adjacent beads along a staircase of a fusing cube raises `cellDim` by one.  The merge complex
(`ChainComplex.bdAll`) computes `H_*(P⃗ K)`; here we cut it down by an acyclic matching.

## The matching

Both rules are the same left-to-right scan of the beads (`upScan`), differing only in which
staircase of a cube is the *matched* one:

* a bead of dim ≥ 2 is a **stop**: the chain has no up-move — it is the merge-target of the chain
  that splits that bead at its preferred staircase;
* an edge `x` is merged with its successor `y` iff some cube `E` of `K` fuses them along `E`'s
  preferred staircase;
* otherwise, move on.

`fuse0` (rule **a**) prefers the staircase `S = {0}` — purely the cube's internal coordinate order,
no global data at all.  `fusePref` (rule **b**) prefers the staircase whose leading edge is smallest
in the ambient total order on cells (`cellList`).  On `□ⁿ` the two coincide (`cubeCells` is
lexicographic with `none` first, so the `cellList`-smallest leading edge *is* the coordinate-`0`
one), and the unique critical cell is the strictly decreasing permutation.

An altitude/time function `f : V → ℤ` cannot play the role of the tie-break: both staircases of a
cube `E` start at `vertex₀ E`, so their leading edges have the *same* altitude.  Preference between
staircases is exactly the data an altitude does not carry.

Why `upScan` is a matching at all: if `b = up c` then `b`'s scan stops at the fused bead, so `b` has
no up-move, and `c` is recovered by splitting that bead — domain and image are disjoint and `up` is
injective.  (For `fuse0` this is a theorem; for `fusePref` the scan could in principle stop early at
a bead of `b`, so it is `#eval`-checked — `matchingValid`.)  Acyclicity is not automatic for either
rule and is checked separately.

## What the examples say

Rule (a) is acyclic on every example but `fourSquare`, where it produces a *perfect* matching (0
critical cells) with a directed cycle running around the loop of four squares — the local
(permutohedral) matchings do **not** glue.  Rule (b) fixes it.  See the `#eval`s.
-/

namespace CubeTest
namespace Morse

open FinBPSet ChainComplex

/-! ## Linear algebra over ℚ -/

/-- Product of matrices given as row lists. -/
def matMul (A B : List (List ℚ)) : List (List ℚ) :=
  A.map (fun r => (List.range (B.headD []).length).map (fun j =>
    (List.zipWith (fun x row => x * row.getD j 0) r B).sum))

/-- Entrywise difference. -/
def matSub (A B : List (List ℚ)) : List (List ℚ) :=
  List.zipWith (List.zipWith (· - ·)) A B

/-- Inverse of a square matrix by Gauss–Jordan on `[A | I]`; `none` if singular. -/
def invMat (A : List (List ℚ)) : Option (List (List ℚ)) :=
  let n := A.length
  let aug : List (List ℚ) :=
    A.zipIdx.map (fun p => p.1 ++ (List.range n).map (fun j => if p.2 = j then (1 : ℚ) else 0))
  let step : Option (List (List ℚ) × List ℕ) → ℕ → Option (List (List ℚ) × List ℕ) :=
    fun st j => st.bind (fun s =>
      match (List.range n).find? (fun i =>
          !memB i s.2 && decide ((s.1.getD i []).getD j 0 ≠ 0)) with
      | none => none
      | some p =>
        let pr := (s.1.getD p []).map (· / (s.1.getD p []).getD j 0)
        let rows := s.1.zipIdx.map (fun q =>
          if q.2 = p then pr
          else
            let c := q.1.getD j 0
            if c = 0 then q.1 else List.zipWith (fun x y => x - c * y) q.1 pr)
        some (rows, s.2 ++ [p]))
  ((List.range n).foldl step (some (aug, []))).map (fun s =>
    s.2.map (fun p => (s.1.getD p []).drop n))

/-! ## Cycle detection (Kahn: iteratively delete the vertices with no in-edge) -/

/-- One deletion round: a live vertex survives iff it still has an in-edge from a live vertex. -/
def kahn (n : ℕ) (edges : List (ℕ × ℕ)) : ℕ → Array Bool → Array Bool
  | 0, alive => alive
  | fuel + 1, alive =>
    let hasIn : Array Bool := edges.foldl (fun h e =>
        if alive.getD e.1 false && alive.getD e.2 false then h.set! e.2 true else h)
      (List.replicate n false).toArray
    let alive' : Array Bool :=
      ((List.range n).map (fun i => alive.getD i false && hasIn.getD i false)).toArray
    if alive'.toList = alive.toList then alive else kahn n edges fuel alive'

/-- Does the digraph on `{0,…,n-1}` have a directed cycle? -/
def hasCycle (n : ℕ) (edges : List (ℕ × ℕ)) : Bool :=
  ((kahn n (edges.filter (fun e => decide (e.1 < n) && decide (e.2 < n))) n
    (List.replicate n true).toArray).toList).any id

/-! ## The matching -/

section
variable {V : Type*} [DecidableEq V] (K : FinBPSet V)

/-- Number of beads. -/
def nbeads (c : List V) : ℕ := c.length

/-- Total dimension (constant on `K.chains` when `K` has an altitude). -/
def dimSum (c : List V) : ℕ := (K.dimSeq c).sum

/-- Dimension of the cell of `c` in `P⃗(K)`. -/
def cellDim (c : List V) : ℕ := dimSum K c - nbeads c

/-- Position of a cell in the ambient total order `cellList`. -/
def cellIdx (x : V) : ℕ := K.cells.findIdx (fun y => decide (y = x))

/-- **Rule (a)**: `E` fuses the edge `x` with the bead `y` along the staircase `S = {0}` — `x` is
`E`'s coordinate-`0` edge. -/
def fuse0 (x y E : V) : Bool :=
  decide (K.dim x = 1) && decide (K.dim E = 1 + K.dim y) &&
  decide (loPart K [0] E = x) && decide (hiPart K [0] E = y)

/-- The staircase of `E` preferred by rule (b): the coordinate `s` whose leading edge
`loPart {s} E` is smallest in `cellList`. -/
def prefCoord (E : V) : ℕ :=
  (List.range (K.dim E)).foldl
    (fun best s => if cellIdx K (loPart K [s] E) < cellIdx K (loPart K [best] E) then s else best) 0

/-- **Rule (b)**: `E` fuses the edge `x` with the bead `y` along `E`'s preferred staircase. -/
def fusePref (x y E : V) : Bool :=
  decide (K.dim x = 1) && decide (K.dim E = 1 + K.dim y) &&
  decide (loPart K [prefCoord K E] E = x) && decide (hiPart K [prefCoord K E] E = y)

/-- The up-move: leftmost merge of an edge with its successor along a preferred staircase, stopped
by the first bead of dim ≥ 2 (such a chain is matched downwards instead). -/
def upScan (fu : V → V → V → Bool) : List V → Option (List V)
  | [] => none
  | [_] => none
  | x :: y :: t =>
    if 2 ≤ K.dim x then none
    else match K.cells.find? (fun E => fu x y E) with
      | some E => some (E :: t)
      | none => (upScan fu (y :: t)).map (x :: ·)

/-- The one-merge targets of `c` (every staircase of every fusing cube) = the Hasse edges out of
`c` in `Ch K`. -/
def mergeTargets (c : List V) : List (List V) := ((bdAll K c).map Prod.fst).dedup

end

/-! ## The report -/

/-- Per-example Morse data.  `critByDim`, `fullBetti`, `morseBetti` are indexed by `cellDim`. -/
structure MorseReport where
  nChains : ℕ
  nCritical : ℕ
  /-- `100 · #critical / #chains`. -/
  pctKept : ℕ
  /-- `up` is injective, its image is disjoint from its domain, and each pair is a Hasse edge. -/
  matchingValid : Bool
  /-- No directed cycle in the Hasse diagram with the matched edges reversed. -/
  acyclic : Bool
  /-- Every pivot block is invertible (needed for the Morse complex). -/
  pivotsOK : Bool
  critByDim : List ℕ
  fullBetti : List ℤ
  morseBetti : List ℤ
  bettiMatch : Bool
  morseIneq : Bool
  eulerMatch : Bool
deriving Repr

/-- The matching `um`, its acyclicity, and its Morse complex for the merge boundary `bdy`. -/
def morseReport {V : Type*} [DecidableEq V] (K : FinBPSet V)
    (bdy : List V → List (List V × ℚ)) (um : List V → Option (List V)) : MorseReport :=
  let chs := K.chains
  let N := chs.length
  let n := (chs.map (dimSum K)).foldl max 0
  let ix : List V → ℕ := idxOf chs
  let bdT : List (List (ℕ × ℚ)) := chs.map (fun c => (bdy c).map (fun p => (ix p.1, p.2)))
  let up : List (Option ℕ) := chs.map (fun c => (um c).map ix)
  let upIdx : ℕ → Option ℕ := fun i => up.getD i none
  let isUp : ℕ → Bool := fun i => (upIdx i).isSome
  let dnSet : List ℕ := up.filterMap id
  let cells : List ℕ := List.range N
  let deg : ℕ → ℕ := fun i => nbeads (chs.getD i [])
  let crit : List ℕ := cells.filter (fun i => !isUp i && !memB i dnSet)
  let cellsAt : ℕ → List ℕ := fun k => cells.filter (fun i => decide (deg i = k))
  let critAt : ℕ → List ℕ := fun k => crit.filter (fun i => decide (deg i = k))
  let upAt : ℕ → List ℕ := fun k => cells.filter (fun i => isUp i && decide (deg i = k))
  let coeff : ℕ → ℕ → ℚ := fun i j =>
    (bdT.getD i []).foldl (fun acc p => if p.1 = j then acc + p.2 else acc) 0
  let mat : List ℕ → List ℕ → List (List ℚ) := fun rows cols => rows.map (fun i => cols.map (coeff i))
  -- the pivot block in degree `k`: the up-matched cells against their partners
  let piv : ℕ → List (List ℚ) := fun k => mat (upAt k) ((upAt k).filterMap upIdx)
  -- the Morse differential `Crit_k → Crit_{k-1}`: the Schur complement of the pivot block
  -- (= the signed sum over gradient paths)
  let morseMat : ℕ → List (List ℚ) := fun k =>
    let U := upAt k
    let base := mat (critAt k) (critAt (k - 1))
    if U.isEmpty ∨ (critAt k).isEmpty ∨ (critAt (k - 1)).isEmpty then base
    else match invMat (piv k) with
      | none => base
      | some Ai =>
        matSub base
          (matMul (matMul (mat (critAt k) (U.filterMap upIdx)) Ai) (mat U (critAt (k - 1))))
  let fullB : ℕ → ℤ := fun k =>
    ((cellsAt k).length : ℤ) - (rank (mat (cellsAt k) (cellsAt (k - 1))) : ℤ)
      - (rank (mat (cellsAt (k + 1)) (cellsAt k)) : ℤ)
  let morseB : ℕ → ℤ := fun k =>
    ((critAt k).length : ℤ) - (rank (morseMat k) : ℤ) - (rank (morseMat (k + 1)) : ℤ)
  -- reindex by `cellDim = n - nbeads`
  let dims : List ℕ := List.range (n + 1)
  let fullBetti := dims.map (fun d => fullB (n - d))
  let morseBetti := dims.map (fun d => morseB (n - d))
  let critByDim := dims.map (fun d => (critAt (n - d)).length)
  let eul : List ℕ → ℤ := fun l => l.foldl (fun acc i => acc + (-1 : ℤ) ^ (deg i)) 0
  { nChains := N
    nCritical := crit.length
    pctKept := if N = 0 then 0 else 100 * crit.length / N
    matchingValid :=
      dnSet.all (fun i => decide (i < N) && !isUp i) &&
        decide (dnSet.dedup.length = dnSet.length) &&
        cells.all (fun i => match upIdx i with
          | none => true
          | some j =>
            memB (chs.getD j []) (mergeTargets K (chs.getD i [])) && decide (deg j + 1 = deg i))
    acyclic := !hasCycle N (chs.flatMap (fun c =>
      (mergeTargets K c).map (fun b =>
        if upIdx (ix c) = some (ix b) then (ix b, ix c) else (ix c, ix b))))
    pivotsOK := (List.range (n + 2)).all (fun k => decide (rank (piv k) = (upAt k).length))
    critByDim := critByDim
    fullBetti := fullBetti
    morseBetti := morseBetti
    bettiMatch := fullBetti = morseBetti
    morseIneq := (List.zipWith (fun (c : ℕ) (b : ℤ) => decide ((c : ℤ) ≥ b)) critByDim fullBetti).all id
    eulerMatch := eul cells = eul crit }

/-- Rule (a) against the geometric merge boundary (all staircases, sign `(-1)ʲ`). -/
def coord0All {V : Type*} [DecidableEq V] (K : FinBPSet V) : MorseReport :=
  morseReport K (bdAll K) (upScan K (fuse0 K))

/-- Rule (b) against the geometric merge boundary. -/
def prefAll {V : Type*} [DecidableEq V] (K : FinBPSet V) : MorseReport :=
  morseReport K (bdAll K) (upScan K (fusePref K))

/-- Rule (b) against the shuffle-twisted merge boundary. -/
def prefSym {V : Type*} [DecidableEq V] (K : FinBPSet V) : MorseReport :=
  morseReport K (bdSym K) (upScan K (fusePref K))

/-! ## The sharp test: `□ⁿ` must collapse to exactly one critical cell

`n = 2, 3, 4`: `3 → 1`, `13 → 1`, `75 → 1`, in `cellDim` 0.  (The critical cell is the strictly
decreasing permutation of the directions.) -/

/-- The 4-cube. -/
def cube4 : FinBPSet (List (Option Bool)) := Examples.stdCube 4

#eval coord0All Examples.square
#eval coord0All Examples.cube3
#eval coord0All cube4

/-! ## Rule (a) on the other examples

Acyclic everywhere except **`fourSquare`**, where it is a *perfect* matching (`nCritical = 0`) whose
gradient flow cycles around the loop of four squares: the four fine chains and the four
square-chains form an 8-cycle in the Hasse diagram, and every perfect matching of a cycle is cyclic.
`Ch(fourSquare)` needs ≥ 2 critical cells (`H_* = H_*(S¹)`), so a *local* rule that always merges
must fail here — the per-cell (permutohedral) matchings do not glue. -/

#eval coord0All TwoSquares.S
#eval coord0All ChainComplex.diamond
#eval coord0All Examples.grid2
#eval coord0All Examples.fourSquare     -- acyclic := false
#eval coord0All Examples.threeSquare
#eval coord0All Examples.fourPaths
#eval coord0All EventNamingCounterexample.T

/-! ## Rule (b): the global cell order chooses the staircase

Identical to (a) on `□ⁿ` (so the sharp test still passes), and it breaks the `fourSquare` cycle:
the four squares no longer all present their "first" staircase, one merge is declined, and the
matching leaves the 2 critical cells that `H_*(S¹)` demands. -/

#eval prefAll Examples.square
#eval prefAll Examples.cube3
#eval prefAll cube4
#eval prefAll TwoSquares.S
#eval prefAll ChainComplex.diamond
#eval prefAll Examples.grid2
#eval prefAll Examples.fourSquare
#eval prefAll Examples.threeSquare
#eval prefAll Examples.fourPaths
#eval prefAll EventNamingCounterexample.T

/-! ## Size only

The matching alone (no Hasse diagram, no ranks), for `□⁵`: `541 → 1`.  `#chains (□ⁿ)` is the Fubini
number `1, 3, 13, 75, 541, 4683, …`; the matching leaves one cell. -/

/-- `(#chains, #critical)` under rule (b), skipping acyclicity and homology. -/
def sizeOnly {V : Type*} [DecidableEq V] (K : FinBPSet V) : ℕ × ℕ :=
  let chs := K.chains
  let ix := idxOf chs
  let up : List (Option ℕ) := chs.map (fun c => (upScan K (fusePref K) c).map ix)
  let dn := up.filterMap id
  (chs.length,
    ((List.range chs.length).filter (fun i => !(up.getD i none).isSome && !memB i dn)).length)

#eval sizeOnly (Examples.stdCube 5)   -- (541, 1)

/-! ## Rule (b) against the twisted boundary

The trinity `T` is the one example where `bdAll` (untwisted) and `bdSym` (`or`-twisted) differ; the
same matching computes both. -/

#eval prefSym Examples.square
#eval prefSym Examples.cube3
#eval prefSym TwoSquares.S
#eval prefSym ChainComplex.diamond
#eval prefSym Examples.grid2
#eval prefSym Examples.fourSquare
#eval prefSym Examples.threeSquare
#eval prefSym Examples.fourPaths
#eval prefSym EventNamingCounterexample.T

end Morse
end CubeTest
