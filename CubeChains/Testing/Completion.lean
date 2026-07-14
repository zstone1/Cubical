import CubeChains.Testing.Examples
import CubeChains.Testing.TwoSquares

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false
set_option linter.style.longLine false

/-!
# Testing/Completion — the missing strata of `Sched K`, by ambient codimension

`Sched K = Σ_{c ∈ Ch K} Δ°(c)`; the chart of a chain `a` is the open convex cone
`C(a) = {t : E a → ℝ | bead e < bead e' ⟹ t_e < t_e'} ⊆ ℝ^(E a)`, `|E a| = dimSum a`.  In the
ambient `ℝ^(dimSum a)` the stratum of `a` has **codimension `dimSum a − nbeads a`** (a run is a
chamber, codim 0).  The walls of `C(a)` are its adjacent bead pairs `(j, j+1)`: the merge is *legal*
iff some cube of `K` fuses the two beads (all bipartitions), and an illegal merge **removes** the
stratum of the merged chain, of ambient codim `dimSum a − nbeads a + 1`.

The missing strata split by codimension:

* **codim 1** — the illegal merge sits in a *run* (`nbeads = dimSum`), so both beads are single
  events: a **causal 2-path**.  A wall is removed; the metric completion glues it back and the
  homotopy type is unchanged.
* **codim ≥ 2** — the illegal merge sits in an already-concurrent chain: a **missing higher cube**
  (pairwise concurrency without joint concurrency).  A *hole* is removed; the completion fills it and
  the homotopy type changes.  `delCube3 = ∂□³` is the witness: no causal 2-path at all, yet
  `Sched(delCube3) = ℝ³ ∖ {t₁ = t₂ = t₃} ≃ S¹` while `Sched(□³) = ℝ³ ≃ pt`.

**Layer:** Testing (decoupled).  Nothing here imports the main library; the rank routine, the
staircase test, the 2-path partition and the extra examples are copied from `CubeChainComplex.lean` /
`Dichotomy.lean` rather than imported.
-/

namespace CubeTest
namespace Completion

open FinBPSet

/-! ## Sparse rank over ℚ, and the order complex of a finite poset -/

/-- A sparse row: `(column, value)` pairs, strictly ascending, no zero values. -/
abbrev SVec := List (ℕ × ℚ)

/-- `r - c • p`, both sorted (`fuel` = `r.length + p.length`). -/
def svSub : ℕ → SVec → SVec → ℚ → SVec
  | 0, r, _, _ => r
  | _ + 1, r, [], _ => r
  | _ + 1, [], p, c => p.map (fun q => (q.1, -c * q.2))
  | f + 1, (i, a) :: r, (j, b) :: p, c =>
      if i < j then (i, a) :: svSub f r ((j, b) :: p) c
      else if j < i then (j, -c * b) :: svSub f ((i, a) :: r) p c
      else
        let s := a - c * b
        if s = 0 then svSub f r p c else (i, s) :: svSub f r p c

/-- Add `v` at column `j`. -/
def svInsert (j : ℕ) (v : ℚ) : SVec → SVec
  | [] => if v = 0 then [] else [(j, v)]
  | (k, w) :: t =>
      if j < k then (if v = 0 then (k, w) :: t else (j, v) :: (k, w) :: t)
      else if j = k then (if w + v = 0 then t else (k, w + v) :: t)
      else (k, w) :: svInsert j v t

/-- Reduce `r` against the registered pivots until its leading column is pivot-free. -/
def reduceRow (piv : Array (Option SVec)) : ℕ → SVec → SVec
  | 0, r => r
  | _ + 1, [] => []
  | f + 1, (j, a) :: r =>
      match piv.getD j none with
      | some ((_, b) :: q) =>
          reduceRow piv f (svSub (r.length + q.length + 2) ((j, a) :: r) ((j, b) :: q) (a / b))
      | _ => (j, a) :: r

/-- Rank of a sparse matrix over `ℚ`. -/
def rankSparse (ncols : ℕ) (rows : List SVec) : ℕ :=
  (rows.foldl (fun (st : Array (Option SVec) × ℕ) r =>
      match reduceRow st.1 (ncols + 1) r with
      | [] => st
      | (j, a) :: t => (st.1.set! j (some ((j, a) :: t)), st.2 + 1))
    ((List.replicate ncols (none : Option SVec)).toArray, 0)).2

/-- Extend every strictly increasing chain by a new smallest element. -/
def simpStep (N : ℕ) (lt : ℕ → ℕ → Bool) (cur : List (List ℕ)) : List (List ℕ) :=
  cur.flatMap (fun s =>
    match s with
    | [] => []
    | x :: _ => ((List.range N).filter (fun y => lt y x)).map (fun y => y :: s))

/-- The simplices of the order complex, by degree, until empty. -/
def simpLevels (N : ℕ) (lt : ℕ → ℕ → Bool) : ℕ → List (List ℕ) → List (List (List ℕ))
  | 0, _ => []
  | f + 1, cur => if cur.isEmpty then [] else cur :: simpLevels N lt f (simpStep N lt cur)

/-- The simplicial boundary of `s` as a sparse row over the previous degree's basis. -/
def bdRow (col : Std.HashMap (List ℕ) ℕ) (s : List ℕ) : SVec :=
  (List.range s.length).foldl (fun v i =>
    match col[s.eraseIdx i]? with
    | some j => svInsert j ((-1 : ℚ) ^ i) v
    | none => v) []

/-- Betti numbers over `ℚ` from the graded simplex lists. -/
def bettiOf (levels : List (List (List ℕ))) : List ℤ :=
  let L := levels.toArray
  let n := L.size
  let ranks : Array ℕ := (Array.range n).map (fun k =>
    if k = 0 then 0 else
      let prev := L[k - 1]!
      let col : Std.HashMap (List ℕ) ℕ :=
        (List.zip prev (List.range prev.length)).foldl (fun c p => c.insert p.1 p.2) ∅
      rankSparse prev.length ((L[k]!).map (bdRow col)))
  (List.range n).map (fun k =>
    let f : ℕ := (L[k]!).length
    let r0 : ℕ := ranks[k]!
    let r1 : ℕ := ranks.getD (k + 1) 0
    (f : ℤ) - (r0 : ℤ) - (r1 : ℤ))

/-- The walls of the cone of `a`: the adjacent bead pairs `(j, j+1)`. -/
def walls {V : Type} (a : List V) : List ℕ := List.range (a.length - 1)

/-- The name of a missing stratum.  The merged block is a *hypothetical* cube — not a cell of `K`, so
it has no name of its own — and it must be named by data invariant under re-splitting: the set of
edge-paths running through it, saturated under square-swaps (`bpaths`, as a membership vector in the
fixed enumeration of all `v0 ⤳ v1` paths of that length).  Naming it by `(v0, v1, dim)` alone is too
coarse (it would identify `diamond`'s two missing squares); naming it by the two beads `x, y` is too
fine (it would not identify `[sq,e]` with `[e,sq]` in `∂□³`, which are the same stratum). -/
structure MissKey (V : Type) where
  /-- The beads before / after the merged block. -/
  pre : List V
  post : List V
  /-- The merged block: its endpoints, its dimension, and its saturated path set. -/
  v0 : V
  v1 : V
  bdim : ℕ
  bpaths : List Bool
deriving DecidableEq, Repr

section
variable {V : Type} [DecidableEq V] (K : FinBPSet V)

/-! ## Fusion: does a cube of `K` split as `x × y`? -/

/-- Ascending sublists. -/
def sublistsAsc : List ℕ → List (List ℕ)
  | [] => [[]]
  | i :: t => (sublistsAsc t).flatMap (fun s => [s, i :: s])

/-- The face of `D` free on the coordinates `S`, with `Sᶜ` set to `0`. -/
def loPart (S : List ℕ) (D : V) : V :=
  (((List.range (K.dim D)).filter (fun i => !memB i S)).reverse).foldl
    (fun x i => (K.face false i x).getD x) D

/-- The face of `D` free on `Sᶜ`, with `S` set to `1`. -/
def hiPart (S : List ℕ) (D : V) : V :=
  S.reverse.foldl (fun x i => (K.face true i x).getD x) D

/-- `D` fuses the adjacent beads `x, y`: `D = x × y` along **some** staircase (all bipartitions of
the coordinates of `D`, not only the canonical one). -/
def fuses (x y D : V) : Bool :=
  decide (K.dim D = K.dim x + K.dim y) &&
  ((sublistsAsc (List.range (K.dim D))).filter (fun S => decide (S.length = K.dim x))).any
    (fun S => decide (loPart K S D = x) && decide (hiPart K S D = y))

/-! ## Walls, legal merges, missing strata -/

/-- `dimSum a` = the number of events of `a`; `a.length` = the number of beads. -/
def dsum (a : List V) : ℕ := (K.dimSeq a).sum

/-- The merge of the beads `j, j+1` of `a` is **legal**: some cube of `K` fuses them, so the wall
`t_j = t_{j+1}` is the stratum of the merged chain and stays inside `Sched K`. -/
def legalMerge (a : List V) (j : ℕ) : Bool :=
  match a[j]?, a[j + 1]? with
  | some x, some y => K.cells.any (fuses K x y)
  | _, _ => false

/-- `(#walls, #legal, #illegal)` over a list of chains. -/
def wallStats (cs : List (List V)) : ℕ × ℕ × ℕ :=
  let ws : List Bool := cs.flatMap (fun a => (walls a).map (legalMerge K a))
  (ws.length, (ws.filter id).length, (ws.filter (fun b => !b)).length)

/-! ## Coarsest chains (the charts that cover) -/

/-- No adjacent bead pair fuses: `a` admits no coarsening. -/
def isCoarsest (a : List V) : Bool := (walls a).all (fun j => !legalMerge K a j)

/-- The chains with no coarsening; their stars should cover `Sched K`. -/
def coarsest : List (List V) := K.chains.filter (isCoarsest K)

/-! ## The 2-path dichotomy (copied from `Dichotomy.lean`) -/

/-- The edges. -/
def edgesL : List V := K.cells.filter (fun c => decide (K.dim c = 1))

/-- The 2-cubes. -/
def sqs : List V := K.cells.filter (fun c => decide (K.dim c = 2))

/-- Source of an edge. -/
def src (e : V) : V := (K.face false 0 e).getD e

/-- Target of an edge. -/
def tgt (e : V) : V := (K.face true 0 e).getD e

/-- Every directed 2-path, as the ordered pair of its edges. -/
def twoPaths : List (V × V) :=
  (edgesL K).flatMap (fun e₁ =>
    ((edgesL K).filter (fun e₂ => decide (tgt K e₁ = src K e₂))).map (fun e₂ => (e₁, e₂)))

/-- The two staircases of a 2-cube. -/
def stairs (Q : V) : List (V × V) :=
  if K.dim Q = 2 then
    [((K.face false 1 Q).getD Q, (K.face true 0 Q).getD Q),
     ((K.face false 0 Q).getD Q, (K.face true 1 Q).getD Q)]
  else []

/-- The 2-path `e₁, e₂` is filled by some 2-cube. -/
def fills (e₁ e₂ : V) : Bool := (sqs K).any (fun Q => memB (e₁, e₂) (stairs K Q))

/-- The concurrent 2-paths. -/
def P2conc : List (V × V) := (twoPaths K).filter (fun p => fills K p.1 p.2)

/-- The causal 2-paths. -/
def P2caus : List (V × V) := (twoPaths K).filter (fun p => !fills K p.1 p.2)

/-- On a wall between two 1-dimensional beads, "legal merge" and "the 2-path is concurrent" agree. -/
def dichotomyAgrees : Bool :=
  K.chains.all (fun a => (walls a).all (fun j =>
    match a[j]?, a[j + 1]? with
    | some x, some y =>
      if K.dim x = 1 ∧ K.dim y = 1 then
        (legalMerge K a j == fills K x y) && (legalMerge K a j == memB (x, y) (P2conc K))
      else true
    | _, _ => true))

/-! ## Missing strata

The merged block of an illegal merge is a cube that `K` does not have, so it must be named by
re-splitting-invariant data: the edge-paths through it, saturated under square-swaps. -/

/-- Edge-paths of length `d` out of `u`, using only the edges `E`. -/
def pathsIn (E : List V) : V → ℕ → List (List V)
  | _, 0 => [[]]
  | u, d + 1 =>
      (E.filter (fun e => decide (src K e = u))).flatMap (fun e =>
        (pathsIn E (tgt K e) d).map (e :: ·))

/-- The edge-paths through a cube `x` of `K` (the staircases of `x`). -/
def cubePaths (x : V) : List (List V) :=
  pathsIn K ((K.faceClosure x).filter (fun c => decide (K.dim c = 1))) (K.vertex0 x) (K.dim x)

/-- Swap one adjacent pair of a path across a filling square. -/
def swapStep (ps : List (List V)) : List (List V) :=
  (ps ++ ps.flatMap (fun p => (walls p).flatMap (fun i =>
    match p[i]?, p[i + 1]? with
    | some e₁, some e₂ =>
      (sqs K).flatMap (fun Q =>
        match stairs K Q with
        | [s, s'] =>
          if s = (e₁, e₂) then [p.take i ++ [s'.1, s'.2] ++ p.drop (i + 2)]
          else if s' = (e₁, e₂) then [p.take i ++ [s.1, s.2] ++ p.drop (i + 2)]
          else []
        | _ => [])
    | _, _ => []))).dedup

/-- The saturated path set of the hypothetical block `x · y`, as a membership vector in the fixed
enumeration of *all* `vertex₀ x ⤳` paths of length `dim x + dim y`. -/
def blockPaths (x y : V) : List Bool :=
  let d := K.dim x + K.dim y
  let init := (cubePaths K x).flatMap (fun p => (cubePaths K y).map (fun q => p ++ q))
  let cl := (swapStep K)^[d * d + 1] init
  (pathsIn K (edgesL K) (K.vertex0 x) d).map (fun p => memB p cl)

/-- Every illegal merge, as `(name of the removed stratum, its ambient codimension)`.  The codim is
`dimSum a − nbeads a + 1` — one more than the codim of `a`'s own stratum. -/
def missingRaw : List (MissKey V × ℕ) :=
  K.chains.flatMap (fun a => (walls a).filterMap (fun j =>
    if legalMerge K a j then none
    else match a[j]?, a[j + 1]? with
      | some x, some y =>
        some ({ pre := a.take j, post := a.drop (j + 2), v0 := K.vertex0 x, v1 := K.vertex1 y,
                bdim := K.dim x + K.dim y, bpaths := blockPaths K x y },
              dsum K a - a.length + 1)
      | _, _ => none))

/-- The missing strata: the same forbidden chain is reached from several `a`, so dedup. -/
def missingStrata : List (MissKey V × ℕ) := (missingRaw K).dedup

/-! ## The nerve `N(Ch K) ≃ P⃗(K)`

`K.isFace` recomputes the whole face closure on every call, which is far too slow for `□⁴`; memoize
it as a matrix on cell indices first. -/

/-- The iterated-face matrix: `faceMat[p][q]` iff cell `p` is an iterated face of cell `q`. -/
def faceMat : Array (Array Bool) :=
  let m := K.cells.length
  let immL : List (List V) := K.cells.map K.immFaces
  -- `imm[p][q]` : `p` is an *immediate* face of `q`
  let imm : Array (Array Bool) :=
    (K.cells.map (fun p => (immL.map (fun fs => memB p fs)).toArray)).toArray
  (fun R : Array (Array Bool) => (Array.range m).map (fun p => (Array.range m).map (fun q =>
      decide (p = q) || (List.range m).any (fun k => (imm[p]!)[k]! && (R[k]!)[q]!))))^[K.maxDim + 1]
    ((Array.range m).map (fun p => (Array.range m).map (fun q => decide (p = q))))

/-- The chains, as lists of cell indices. -/
def chainIdx : List (List ℕ) :=
  K.chains.map (fun c => c.map (fun x => K.cells.findIdx (fun y => decide (y = x))))

/-- The refinement order on index-chains. -/
def chLeI (R : Array (Array Bool)) (a b : List ℕ) : Bool :=
  a.all (fun p => b.any (fun q => (R[p]!)[q]!))

/-- Every chain refines some coarsest chain (the stars of `coarsest` cover `Sched K`). -/
def coverOK : Bool :=
  let R := faceMat K
  let idx : List V → List ℕ := fun c =>
    c.map (fun x => K.cells.findIdx (fun y => decide (y = x)))
  K.chains.all (fun c => (coarsest K).any (fun a => chLeI R (idx c) (idx a)))

/-- Betti numbers of the order complex of `Ch K`. -/
def nerveBetti : List ℤ :=
  let R := faceMat K
  let chs := (chainIdx K).toArray
  let N := chs.size
  let M : Array (Array Bool) :=
    (Array.range N).map (fun i => (Array.range N).map (fun j => chLeI R (chs[i]!) (chs[j]!)))
  let lt : ℕ → ℕ → Bool := fun i j => (M[i]!)[j]! && !((M[j]!)[i]!)
  bettiOf (simpLevels N lt (N + 2) ((List.range N).map (fun i => [i])))

end

/-! ## The report -/

/-- One example.  `nWalls/nLegal/nIllegal` count *walls* (chain, bead pair); `nMiss*` count the
removed *strata*, deduped. -/
structure Row where
  nChains : ℕ
  nCoarsest : ℕ
  coverOK : Bool
  /-- All chains: `#walls`, and the legal/illegal split. -/
  nWalls : ℕ
  nLegal : ℕ
  nIllegal : ℕ
  dichotomyAgrees : Bool
  /-- The deduped missing strata: total, by codimension (`codimHist[k]` = codim `k`), and the
  codim-1 / codim-≥2 split. -/
  nMissing : ℕ
  codimHist : List ℕ
  nMiss1 : ℕ
  nMissHigh : ℕ
  nCaus : ℕ
  /-- `#codim-1 missing strata = #causal 2-paths`. -/
  claimCount : Bool
  /-- `∃ codim-1 missing stratum ⟺ ∃ causal 2-path`. -/
  claimQual : Bool
  nerveBetti : List ℤ
deriving Repr

/-- Everything about one `K`. -/
def analyze {V : Type} [DecidableEq V] (K : FinBPSet V) : Row :=
  let sA : ℕ × ℕ × ℕ := wallStats K K.chains
  let n : ℕ := ((K.chains.map (dsum K)).foldl max 0)
  let cds : List ℕ := (missingStrata K).map Prod.snd
  let h : List ℕ := (List.range (n + 1)).map (fun k => (cds.filter (fun c => decide (c = k))).length)
  let m1 : ℕ := h.getD 1 0
  let tot : ℕ := cds.length
  let nc : ℕ := (P2caus K).length
  { nChains := K.chains.length
    nCoarsest := (coarsest K).length
    coverOK := coverOK K
    nWalls := sA.1
    nLegal := sA.2.1
    nIllegal := sA.2.2
    dichotomyAgrees := dichotomyAgrees K
    nMissing := tot
    codimHist := h
    nMiss1 := m1
    nMissHigh := tot - m1
    nCaus := nc
    claimCount := decide (m1 = nc)
    claimQual := decide (0 < m1) == decide (0 < nc)
    nerveBetti := nerveBetti K }

/-! ## Examples -/

/-- The diamond: `a → mᵢ → b` (`i = 1,2`), no squares. -/
inductive Dm | a | m1 | m2 | b | e1 | e2 | f1 | f2
  deriving DecidableEq, Repr

/-- Two parallel edge-paths with no filling. -/
def diamond : FinBPSet Dm where
  cellList := [.a, .m1, .m2, .b, .e1, .e2, .f1, .f2]
  dim := fun c => match c with
    | .e1 | .e2 | .f1 | .f2 => 1
    | _ => 0
  face := fun ε i c => match c, i with
    | .e1, 0 => some (cond ε .m1 .a)
    | .f1, 0 => some (cond ε .b .m1)
    | .e2, 0 => some (cond ε .m2 .a)
    | .f2, 0 => some (cond ε .b .m2)
    | _, _ => none
  init := .a
  final := .b

/-- Cells of `a → b → c`. -/
inductive S2 | a | b | c | e | f
  deriving DecidableEq, Repr

/-- Two composable edges, no square: pure causality. -/
def seq2 : FinBPSet S2 where
  cellList := [.a, .b, .c, .e, .f]
  dim := fun x => match x with | .e | .f => 1 | _ => 0
  face := fun ε i x => match x, i with
    | .e, 0 => some (cond ε .b .a)
    | .f, 0 => some (cond ε .c .b)
    | _, _ => none
  init := .a
  final := .c

/-- Cells of the square-then-edge. -/
inductive SE | c00 | c10 | c01 | c11 | z | e0_ | e1_ | e_0 | e_1 | ez | sq
  deriving DecidableEq, Repr

/-- A square `c00 ⤳ c11` followed by an edge `c11 → z`: concurrency *then* causality. -/
def sqThenEdge : FinBPSet SE where
  cellList := [.c00, .c10, .c01, .c11, .z, .e0_, .e1_, .e_0, .e_1, .ez, .sq]
  dim := fun x => match x with
    | .sq => 2 | .e0_ | .e1_ | .e_0 | .e_1 | .ez => 1 | _ => 0
  face := fun ε i x => match x, i with
    | .e0_, 0 => some (cond ε .c01 .c00)
    | .e1_, 0 => some (cond ε .c11 .c10)
    | .e_0, 0 => some (cond ε .c10 .c00)
    | .e_1, 0 => some (cond ε .c11 .c01)
    | .ez,  0 => some (cond ε .z .c11)
    | .sq, 0 => some (cond ε .e1_ .e0_)
    | .sq, 1 => some (cond ε .e_1 .e_0)
    | _, _ => none
  init := .c00
  final := .z

/-- Cells of the two-edges-then-square. -/
inductive ES | a | b | c00 | c10 | c01 | c11 | e | f | e0_ | e1_ | e_0 | e_1 | sq
  deriving DecidableEq, Repr

/-- `a →e→ b →f→ c00`, then a square `c00 ⤳ c11`: **causality then concurrency**.  The single causal
2-path `(e, f)` sits in *two* runs (the square branches after it), so it removes **two** codim-1
strata — this is the counterexample to the *count* form of claim 3(a). -/
def seqThenSq : FinBPSet ES where
  cellList := [.a, .b, .c00, .c10, .c01, .c11, .e, .f, .e0_, .e1_, .e_0, .e_1, .sq]
  dim := fun x => match x with
    | .sq => 2 | .e | .f | .e0_ | .e1_ | .e_0 | .e_1 => 1 | _ => 0
  face := fun ε i x => match x, i with
    | .e,   0 => some (cond ε .b .a)
    | .f,   0 => some (cond ε .c00 .b)
    | .e0_, 0 => some (cond ε .c01 .c00)
    | .e1_, 0 => some (cond ε .c11 .c10)
    | .e_0, 0 => some (cond ε .c10 .c00)
    | .e_1, 0 => some (cond ε .c11 .c01)
    | .sq, 0 => some (cond ε .e1_ .e0_)
    | .sq, 1 => some (cond ε .e_1 .e_0)
    | _, _ => none
  init := .a
  final := .c11

/-- `□⁴`. -/
def cube4 : FinBPSet (List (Option Bool)) := Examples.stdCube 4

/-- `□ⁿ` with its top `n`-cell deleted (everything of dim `< n` kept). -/
def delCube (n : ℕ) : FinBPSet (List (Option Bool)) :=
  { Examples.stdCube n with
    cellList := (Examples.stdCube n).cellList.filter
      (fun c => decide (c ≠ List.replicate n none)) }

/-- `∂□³`: all 8 vertices, 12 edges and 6 squares, no 3-cell.  Every 2-path is filled
(`P2caus = ∅`), yet the chain `[square, edge]` cannot merge — one missing stratum, of codim 2.
`Sched = ℝ³ ∖ (the diagonal line) ≃ S¹`. -/
def delCube3 : FinBPSet (List (Option Bool)) := delCube 3

/-- `∂□⁴` in the same sense (the 4-cell deleted, all 24 squares and 32 cubes kept). -/
def delCube4 : FinBPSet (List (Option Bool)) := delCube 4

-- Sanity: the new examples are well-formed, valid inputs.
#eval [diamond.wellFormed, seq2.wellFormed, sqThenEdge.wellFormed, seqThenSq.validInput,
       delCube3.validInput, delCube4.validInput]

/-! ### The table -/

#eval analyze Examples.interval          -- □¹
#eval analyze Examples.square            -- □²
#eval analyze Examples.cube3             -- □³ : no missing strata, nerve [1,0,0,0]
#eval analyze delCube3                   -- ∂□³: nCaus = 0, one missing stratum of codim 2, nerve [1,1]
#eval analyze cube4                      -- □⁴
#eval analyze delCube4                   -- ∂□⁴: nCaus = 0, one missing stratum of codim 3, nerve [1,0,1]
#eval analyze TwoSquares.S
#eval analyze diamond
#eval analyze Examples.grid2
#eval analyze Examples.fourSquare
#eval analyze Examples.threeSquare
#eval analyze Examples.fourPaths
#eval analyze EventNamingCounterexample.T
#eval analyze seq2
#eval analyze sqThenEdge
#eval analyze seqThenSq                  -- claimCount := false

/-! ## Findings

| K            | chains | coarsest | walls | illegal | missing | codim hist | caus | nerve b   |
|--------------|--------|----------|-------|---------|---------|------------|------|-----------|
| `□¹`         |      1 |        1 |     0 |       0 |       0 | —          |    0 | `[1]`     |
| `□²`         |      3 |        1 |     2 |       0 |       0 | —          |    0 | `[1,0]`   |
| `□³`         |     13 |        1 |    18 |       0 |       0 | —          |    0 | `[1,0,0]` |
| `delCube3`   |     12 |        6 |    18 |       6 |       1 | `1×codim2` |    0 | `[1,1]`   |
| `□⁴`         |     75 |        1 |   158 |       0 |       0 | —          |    0 | `[1,0,0,0]` |
| `delCube4`   |     74 |       14 |   158 |      14 |       1 | `1×codim3` |    0 | `[1,0,1]` |
| `TwoSquares` |      4 |        2 |     2 |       0 |       0 | —          |    0 | `[1,1]`   |
| `diamond`    |      2 |        2 |     2 |       2 |       2 | `2×codim1` |    2 | `[2]`     |
| `grid2`      |      5 |        2 |     8 |       4 |       3 | `2×1, 1×2` |    2 | `[1,0]`   |
| `fourSquare` |      8 |        4 |    12 |       4 |       1 | `1×codim2` |    0 | `[1,1]`   |
| `threeSquare`|      7 |        3 |    11 |       5 |       3 | `2×1, 1×2` |    2 | `[1,0]`   |
| `fourPaths`  |      4 |        4 |     8 |       8 |       8 | `8×codim1` |    8 | `[4]`     |
| trinity `T`  |      6 |        3 |     3 |       0 |       0 | —          |    0 | `[1,1]`   |
| `seq2`       |      1 |        1 |     1 |       1 |       1 | `1×codim1` |    1 | `[1]`     |
| `sqThenEdge` |      3 |        1 |     5 |       3 |       3 | `2×1, 1×2` |    2 | `[1,0]`   |
| `seqThenSq`  |      3 |        1 |     8 |       6 |       6 | `4×1, 2×2` |    3 | `[1,0]`   |

**3(a) — existence form HOLDS, count form FAILS.**  `claimQual` (`∃ codim-1 missing stratum ⟺
P2caus ≠ ∅`) holds on every example, and is a theorem: a causal 2-path extends to a run
(accessibility), and a codim-1 illegal merge is by definition an illegal merge of two adjacent
*events* of a run.  But `claimCount` (`#codim-1 strata = #causal 2-paths`) **FAILS on `seqThenSq`**
(`a →e→ b →f→ c00`, then a square): `nCaus = 3` but `nMiss1 = 4`.  A removed stratum is a *chain*,
not a 2-path, so it remembers the context: the single causal 2-path `(e, f)` lies in the two runs
`[e, f, e0_, e_1]` and `[e, f, e_0, e1_]`, and merging it there gives the two *distinct* missing
chains `[ef, e0_, e_1]` and `[ef, e_0, e1_]`.  So {codim-1 missing strata} ↠ {causal 2-paths} is
onto, with fibres = the run contexts, and is a bijection exactly when each causal 2-path lies in a
unique run — which is the case on all the other examples, hence the counts agree there.

**3(b), 3(c) — HOLD.**  `□¹ … □⁴`, `TwoSquares.S` and the trinity `T` have **no** missing strata
(`Sched` complete).  `delCube3` has **zero** causal 2-paths and exactly **one** missing stratum, of
codim 2 — pairwise concurrency without joint concurrency, as predicted; `delCube4` likewise, one
stratum of codim 3.  `seq2` has exactly one, of codim 1.  **`fourSquare` is a second, pre-existing
witness of the codim-≥2 phenomenon**: `nCaus = 0`, one missing stratum of codim 2, nerve `S¹`.
`grid2`, `threeSquare`, `sqThenEdge`, `seqThenSq` show the two kinds coexisting.

**4 — HOLDS.**  `nerveBetti □³ = [1,0,0]` (contractible: `Ch(□³)` is the face poset of the hexagonal
permutohedron *with* its top, hence a cone) while `nerveBetti delCube3 = [1,1]` — the *proper* face
poset, i.e. the barycentric subdivision of `∂(hexagon) ≃ S¹`.  Likewise `□⁴ ↦ [1,0,0,0]` and
`delCube4 ↦ [1,0,1] ≃ S²`.  So a codim-2 missing stratum is **homotopically essential** (`P⃗ K` goes
from a point to `S¹`) yet **metrically invisible** (the completion of `ℝ³ ∖ line` is `ℝ³`).  That is
why "`Sched‾ K` is a manifold with corners `≃ P⃗ K`" is false, and why only the codim-1 (causal)
missing strata may be glued back. -/

/-! ### The findings, pinned -/

-- Structural guards: the coarsest cones cover, and "legal merge = concurrent 2-path" on runs.
def guards {V : Type} [DecidableEq V] (K : FinBPSet V) : Bool :=
  let r := analyze K
  r.coverOK && r.dichotomyAgrees && r.claimQual

example : [guards Examples.interval, guards Examples.square, guards Examples.cube3,
    guards delCube3, guards cube4, guards delCube4, guards TwoSquares.S, guards diamond,
    guards Examples.grid2, guards Examples.fourSquare, guards Examples.threeSquare,
    guards Examples.fourPaths, guards EventNamingCounterexample.T, guards seq2,
    guards sqThenEdge, guards seqThenSq].all id = true := by native_decide

-- 3(b), 3(c): the cube is complete; deleting its top cell removes exactly one stratum, of codim 2.
example : ((analyze Examples.cube3).nMissing = 0 ∧ (analyze cube4).nMissing = 0) := by native_decide
example : ((analyze delCube3).nCaus = 0 ∧ (analyze delCube3).codimHist = [0, 0, 1, 0]) := by
  native_decide
example : ((analyze delCube4).nCaus = 0 ∧ (analyze delCube4).codimHist = [0, 0, 0, 1, 0]) := by
  native_decide
example : (analyze seq2).codimHist = [0, 1, 0] := by native_decide

-- `fourSquare` is a second witness of 3(b): fully concurrent, one codim-2 hole.
example : ((analyze Examples.fourSquare).nCaus = 0 ∧
    (analyze Examples.fourSquare).codimHist = [0, 0, 1, 0]) := by native_decide

-- 4: the codim-2 hole is homotopically essential (`pt ↝ S¹`) but metrically invisible.
example : (analyze Examples.cube3).nerveBetti = [1, 0, 0] := by native_decide
example : (analyze delCube3).nerveBetti = [1, 1] := by native_decide
example : (analyze cube4).nerveBetti = [1, 0, 0, 0] := by native_decide
example : (analyze delCube4).nerveBetti = [1, 0, 1] := by native_decide

-- 3(a) — count form: **FAILS** on `seqThenSq` (3 causal 2-paths, 4 codim-1 strata) …
example : ((analyze seqThenSq).nCaus = 3 ∧ (analyze seqThenSq).nMiss1 = 4) := by native_decide
example : (analyze seqThenSq).claimCount = false := by native_decide

-- … and holds on every other example.
example : [(analyze Examples.interval).claimCount, (analyze Examples.square).claimCount,
    (analyze Examples.cube3).claimCount, (analyze delCube3).claimCount,
    (analyze cube4).claimCount, (analyze delCube4).claimCount, (analyze TwoSquares.S).claimCount,
    (analyze diamond).claimCount, (analyze Examples.grid2).claimCount,
    (analyze Examples.fourSquare).claimCount, (analyze Examples.threeSquare).claimCount,
    (analyze Examples.fourPaths).claimCount, (analyze EventNamingCounterexample.T).claimCount,
    (analyze seq2).claimCount, (analyze sqThenEdge).claimCount].all id = true := by native_decide

end Completion
end CubeTest
