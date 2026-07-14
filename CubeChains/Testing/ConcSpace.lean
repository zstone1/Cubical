import CubeChains.Testing.Examples
import CubeChains.Testing.TwoSquares

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false
set_option linter.style.longLine false

/-!
# Testing/ConcSpace — the concurrency space `Int(Lines K)`

The **global Salvetti complex** of a finite bi-pointed precubical set `K`: the nerve of the
category of elements of the chamber presheaf on `Ch K`.

* a *chamber* of a `d`-cube `D` is a total order on its `d` directions (the order in which they
  flip), i.e. a permutation of `Fin d`;
* `Lines c = ∏ᵢ chambers(cᵢ)` for a cube chain `c`;
* an object of `Int(Lines K)` is a pair `(c, L)`, `c` a chain, `L ∈ Lines c`;
* `(c, L) ≤ (c', L')` iff `c'` refines `c` and `L'` is `L` restricted along the refinement:
  each fine bead `e` is a face of a unique coarse bead `D`, occupying the free-coordinate set
  `S ⊆ Fin (dim D)` of the unique sign vector cutting it out, and `L' e` must be the order `L D`
  induces on `S`.

Output = simplicial homology (over ℚ, Gaussian elimination) of the order complex of that poset.
For `□ⁿ` this is the Salvetti complex of the braid arrangement `A_{n-1}`, i.e. the ordered
configuration space `F(ℂ, n)` — so `b₁ = n(n-1)/2`.

The face relation and the free-coordinate sets are both read off the **sign vectors** of a cube
(`e` is an iterated face of `D` iff `e = D[a]` for some `a : Fin (dim D) → {*,0,1}`), which is the
same relation as `Model.isFace` but avoids its quadratic `faceClosure` (checked by `modelAgrees`).
-/

namespace CubeTest
namespace Conc

open FinBPSet

/-! ## Sparse rank over ℚ -/

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
      | some ((_, b) :: q) => reduceRow piv f (svSub (r.length + q.length + 2) ((j, a) :: r) ((j, b) :: q) (a / b))
      | _ => (j, a) :: r

/-- Rank of a sparse matrix over ℚ (rows given as `SVec`s, `ncols` columns). -/
def rankSparse (ncols : ℕ) (rows : List SVec) : ℕ :=
  (rows.foldl (fun (st : Array (Option SVec) × ℕ) r =>
      match reduceRow st.1 (ncols + 1) r with
      | [] => st
      | (j, a) :: t => (st.1.set! j (some ((j, a) :: t)), st.2 + 1))
    ((List.replicate ncols (none : Option SVec)).toArray, 0)).2

/-! ## Chambers, lines, sign vectors -/

/-- All insertions of `x` into a list. -/
def inserts (x : ℕ) : List ℕ → List (List ℕ)
  | [] => [[x]]
  | y :: t => (x :: y :: t) :: (inserts x t).map (y :: ·)

/-- All permutations. -/
def perms : List ℕ → List (List ℕ)
  | [] => [[]]
  | x :: t => (perms t).flatMap (inserts x)

/-- The chambers of a `d`-cube: the orders in which its `d` directions flip. -/
def chambersD (d : ℕ) : List (List ℕ) := perms (List.range d)

/-- Sign vectors of a `d`-cube (`none` = free coordinate). -/
def signVecs : ℕ → List (List (Option Bool))
  | 0 => [[]]
  | n + 1 => [none, some false, some true].flatMap (fun o => (signVecs n).map (o :: ·))

variable {V : Type*} [DecidableEq V]

/-- The iterated face of `D` cut out by `a`.  Coordinates are fixed top-down, so the index of the
coordinate being fixed is still its index in `D` (all lower ones are still free). -/
def signFace (K : FinBPSet V) (a : List (Option Bool)) (D : V) : V :=
  (List.range a.length).reverse.foldl (fun x i =>
    match a[i]? with
    | some (some ε) => (K.face ε i x).getD x
    | _ => x) D

/-! ## Precomputed tables -/

/-- Tables for one `K`, all indexed by position in `K.cells`. -/
structure Ctx where
  /-- Dimension of each cell. -/
  dims : Array ℕ
  /-- `free[q][p]` = every free-coordinate set of `p` inside `q` (a singleton iff `p` occurs as a
  face of `q` in exactly one way — the non-self-linked case). -/
  free : Array (Array (List (List ℕ)))
  /-- `faceT[p][q]` = `p` is an iterated face of `q`. -/
  faceT : Array (Array Bool)
  /-- The cube chains, as lists of cell indices. -/
  chains : Array (List ℕ)

/-- Build the tables. -/
def mkCtx (K : FinBPSet V) : Ctx :=
  let m := K.cells.length
  let idxOf : V → ℕ := fun x => K.cells.findIdx (fun y => decide (y = x))
  let free : Array (Array (List (List ℕ))) :=
    (List.zip (List.range m) K.cells).foldl (fun acc qD =>
      (signVecs (K.dim qD.2)).foldl (fun acc a =>
        let S := (List.range a.length).filter (fun i => decide (a[i]? = some none))
        acc.modify qD.1 (fun row => row.modify (idxOf (signFace K a qD.2)) (S :: ·))) acc)
      ((List.replicate m ((List.replicate m ([] : List (List ℕ))).toArray)).toArray)
  { dims := (K.cells.map K.dim).toArray
    free := free
    faceT := (Array.range m).map (fun p => (Array.range m).map (fun q => !(free[q]!)[p]!.isEmpty))
    chains := (K.chains.map (fun c => c.map idxOf)).toArray }

/-- The refinement order on chains: every bead of `a` is a face of a bead of `b`. -/
def chLeI (X : Ctx) (a b : List ℕ) : Bool :=
  a.all (fun p => b.any (fun q => (X.faceT[p]!)[q]!))

/-- `Lines c` — one chamber per bead. -/
def linesOf (X : Ctx) : List ℕ → List (List (List ℕ))
  | [] => [[]]
  | p :: t => (linesOf X t).flatMap (fun L => (chambersD (X.dims[p]!)).map (fun ch => ch :: L))

/-- Restriction data of a refinement `cb ⊑ ca`: for each bead of `cb`, the index of the coarse bead
of `ca` containing it and its free-coordinate set there.  `none` if either is non-unique (a
self-linking failure). -/
def restrData (X : Ctx) (ca cb : List ℕ) : Option (List (ℕ × List ℕ)) :=
  cb.mapM (fun e =>
    match (List.range ca.length).filter (fun i => (X.faceT[e]!)[ca.getD i 0]!) with
    | [i] =>
        match (X.free[ca.getD i 0]!)[e]! with
        | [S] => some (i, S)
        | _ => none
    | _ => none)

/-- Restrict a line along a refinement: `L D` induces an order on the free set `S` of each fine
bead, relabelled by the rank inside `S`. -/
def restrLine (rd : List (ℕ × List ℕ)) (L : List (List ℕ)) : List (List ℕ) :=
  rd.map (fun q =>
    ((L.getD q.1 []).filter (fun j => memB j q.2)).map
      (fun j => (q.2.filter (fun k => decide (k < j))).length))

/-! ## The order complex of `Int(Lines K)` -/

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

/-- Betti numbers over ℚ from the graded simplex lists. -/
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

/-! ## Report -/

/-- Per-example output. -/
structure Report where
  /-- Number of cube chains (objects of `Ch K`). -/
  nChains : ℕ
  /-- Number of objects of `Int(Lines K)`. -/
  nObjs : ℕ
  /-- Strictly comparable pairs (the 1-simplices). -/
  nEdges : ℕ
  /-- Covering pairs. -/
  nCovers : ℕ
  /-- Simplex counts by degree. -/
  fVec : List ℕ
  /-- Euler characteristic. -/
  euler : ℤ
  /-- Betti numbers over ℚ. -/
  betti : List ℤ
  /-- Every refinement has a unique coarse bead and a unique sign vector for each fine bead. -/
  sane : Bool
  /-- The relation really is a partial order (reflexive, transitive, antisymmetric). -/
  poset : Bool
deriving Repr

/-- The concurrency space of `K`. -/
def analyze (K : FinBPSet V) : Report :=
  let X := mkCtx K
  let chs := X.chains
  let nc := chs.size
  let rdt : Array (Array (Option (List (ℕ × List ℕ)))) :=
    (Array.range nc).map (fun i => (Array.range nc).map (fun j =>
      if chLeI X (chs[j]!) (chs[i]!) then restrData X (chs[i]!) (chs[j]!) else none))
  let sane : Bool := (List.range nc).all (fun i => (List.range nc).all (fun j =>
    !(chLeI X (chs[j]!) (chs[i]!)) || ((rdt[i]!)[j]!).isSome))
  let objs : Array (ℕ × List (List ℕ)) :=
    ((List.range nc).flatMap (fun i => (linesOf X (chs[i]!)).map (fun L => (i, L)))).toArray
  let N := objs.size
  let le : Array (Array Bool) := (Array.range N).map (fun p => (Array.range N).map (fun q =>
    match (rdt[(objs[p]!).1]!)[(objs[q]!).1]! with
    | some rd => decide (restrLine rd (objs[p]!).2 = (objs[q]!).2)
    | none => false))
  let lt : ℕ → ℕ → Bool := fun p q => (le[p]!)[q]! && !((le[q]!)[p]!)
  let poset : Bool :=
    (List.range N).all (fun p => (le[p]!)[p]!) &&
    (List.range N).all (fun p => (List.range N).all (fun q => (List.range N).all (fun r =>
      !((le[p]!)[q]! && (le[q]!)[r]!) || (le[p]!)[r]!))) &&
    (List.range N).all (fun p => (List.range N).all (fun q =>
      !((le[p]!)[q]! && (le[q]!)[p]!) || decide (p = q)))
  let covers : ℕ := ((List.range N).flatMap (fun p => (List.range N).filter (fun q =>
    lt p q && (List.range N).all (fun r => !(lt p r && lt r q))))).length
  let levels := simpLevels N lt (N + 2) ((List.range N).map (fun i => [i]))
  let fVec := levels.map List.length
  { nChains := nc
    nObjs := N
    nEdges := fVec.getD 1 0
    nCovers := covers
    fVec := fVec
    euler := (List.range fVec.length).foldl
      (fun a k => a + (-1 : ℤ) ^ k * (fVec.getD k 0 : ℤ)) 0
    betti := bettiOf levels
    sane := sane
    poset := poset }

/-- Cross-check of the sign-vector face relation against `Model.isFace` (quadratic — small `K` only). -/
def modelAgrees (K : FinBPSet V) : Bool :=
  let X := mkCtx K
  let ics := List.zip (List.range K.cells.length) K.cells
  ics.all (fun px => ics.all (fun qy => (X.faceT[px.1]!)[qy.1]! == K.isFace px.2 qy.2))

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

/-- `□⁴`. -/
def cube4 : FinBPSet (List (Option Bool)) := Examples.stdCube 4

/-! ### The sign-vector face relation agrees with the model's `isFace` -/

#eval (modelAgrees Examples.square, modelAgrees Examples.cube3, modelAgrees TwoSquares.S,
       modelAgrees diamond, modelAgrees Examples.grid2, modelAgrees Examples.fourSquare,
       modelAgrees Examples.threeSquare, modelAgrees Examples.fourPaths)

/-! ### The concurrency spaces -/

#eval analyze Examples.interval
#eval analyze Examples.square      -- □²
#eval analyze Examples.cube3       -- □³
#eval analyze TwoSquares.S
#eval analyze diamond
#eval analyze Examples.grid2
#eval analyze Examples.threeSquare
#eval analyze Examples.fourSquare
#eval analyze Examples.fourPaths
#eval analyze cube4                -- □⁴

/-! ### Findings

`sane` and `poset` hold on every example: each fine bead has a unique coarse bead and a unique
sign vector, so no example here is self-linked, and the restriction rule really does define a
partial order.

| K            | #obj | #edge | χ  | Betti        |
|--------------|------|-------|----|--------------|
| `□²`         |    4 |     4 |  0 | `[1,1]`      |
| `□³`         |   24 |    96 |  0 | `[1,3,2]`    |
| `□⁴`         |  192 |  2688 |  0 | `[1,6,11,6]` |
| `TwoSquares` |    6 |     8 | -2 | `[1,3]`      |
| `diamond`    |    2 |     0 |  2 | `[2]`        |
| `grid2`      |    7 |     8 | -1 | `[1,2]`      |
| `threeSquare`|   10 |    12 | -2 | `[1,3]`      |
| `fourSquare` |   12 |    16 | -4 | `[1,5]`      |
| `fourPaths`  |    4 |     0 |  4 | `[4]`        |

`Int(Lines(□ⁿ))` reproduces `F(ℂ, n)` exactly: the Betti numbers are the coefficients of
`∏_{k<n} (1 + k t)` (`n = 2,3,4`), so `b₁ = n(n-1)/2` and `χ = 0`.  `□⁵` (1920 objects, 99840
edges) is out of reach: enumerating the order complex alone runs for >10 min. -/

-- `b₁(Int(Lines(□ⁿ))) = n(n-1)/2` for `n ≤ 4`:  [0, 0, 1, 3, 6]
#eval (List.range 5).map (fun n => (analyze (Examples.stdCube n)).betti.getD 1 0)

example : (analyze Examples.square).betti = [1, 1] := by native_decide
example : (analyze Examples.cube3).betti = [1, 3, 2] := by native_decide
example : (analyze cube4).betti = [1, 6, 11, 6] := by native_decide
example : (analyze TwoSquares.S).betti = [1, 3] := by native_decide
example : (analyze diamond).betti = [2] := by native_decide

-- The order really is a poset, and no example is self-linked.
example : [analyze Examples.square, analyze Examples.cube3, analyze cube4, analyze TwoSquares.S,
    analyze diamond, analyze Examples.grid2, analyze Examples.threeSquare,
    analyze Examples.fourSquare, analyze Examples.fourPaths].all (fun r => r.sane && r.poset)
    = true := by native_decide

end Conc
end CubeTest
