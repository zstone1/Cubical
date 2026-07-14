import CubeChains.Testing.Examples
import CubeChains.Testing.TwoSquares

-- Property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false
set_option linter.style.longLine false

/-!
# Testing/Skeleton — does `Int(Lines K)`'s `π₁` only see the 3-skeleton?

A `d`-cube of `K` contributes Salvetti cells of dimension `d - 1` (a chain `c` gives a cell of
dimension `dimSum c - nbeads c`).  `π₁` sees only the 2-skeleton, so cubes of dimension `≥ 4`
should be invisible to it:

  **`b₁(Int(Lines K))` should depend only on `K`'s 3-skeleton.**

`skel n K` deletes every cell of dimension `> n`.  The test: `b₁(Int(Lines (skel n K)))` as a
function of `n` should stabilise at `n = 3`, and (for a `K` with a 3-cell) move at `n = 2`.

The `Int(Lines K)` machinery is copied verbatim from `Testing/ConcSpace.lean` so that this file
is an independent re-derivation of its table (cross-checked below on `□²`, `□³`, `□⁴`).
-/

namespace CubeTest
namespace Skel

open FinBPSet

/-! ## Skeleta -/

variable {V : Type*} [DecidableEq V]

/-- `skel n K` = `K` with every cell of dimension `> n` deleted.  Faces of a kept cell have
smaller dimension, so they are kept too; `face` needs no adjustment. -/
def skel (n : ℕ) (K : FinBPSet V) : FinBPSet V :=
  { K with cellList := K.cellList.filter (fun c => decide (K.dim c ≤ n)) }

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

/-- Rank of a sparse matrix over ℚ. -/
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

/-- The iterated face of `D` cut out by `a`.  Coordinates are fixed top-down, so the index of the
coordinate being fixed is still its index in `D`. -/
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
  /-- `free[q][p]` = every free-coordinate set of `p` inside `q`. -/
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

/-- Restriction data of a refinement `cb ⊑ ca`: coarse bead index + free-coordinate set, per fine
bead.  `none` if either is non-unique (a self-linking failure). -/
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

/-- Betti numbers over ℚ from the graded simplex lists.  If the list is truncated at degree `k`,
only `b₀ … b_{k-1}` are meaningful (`b_k` is missing `∂_{k+1}`). -/
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
  /-- Simplex counts by degree. -/
  fVec : List ℕ
  /-- Euler characteristic. -/
  euler : ℤ
  /-- Betti numbers over ℚ. -/
  betti : List ℤ
  /-- Every refinement has a unique coarse bead and a unique sign vector for each fine bead. -/
  sane : Bool
  /-- The relation really is a partial order. -/
  poset : Bool
deriving Repr

/-- The order relation of `Int(Lines K)`: `(#objects, ≤, #chains, sane)`. -/
def ordOf (K : FinBPSet V) : ℕ × Array (Array Bool) × ℕ × Bool :=
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
  (N, le, nc, sane)

/-- Strict order from the `≤` table. -/
def strict (le : Array (Array Bool)) : ℕ → ℕ → Bool :=
  fun p q => (le[p]!)[q]! && !((le[q]!)[p]!)

/-- The concurrency space of `K`: full order complex. -/
def analyze (K : FinBPSet V) : Report :=
  let (N, le, nc, sane) := ordOf K
  let lt := strict le
  let poset : Bool :=
    (List.range N).all (fun p => (le[p]!)[p]!) &&
    (List.range N).all (fun p => (List.range N).all (fun q => (List.range N).all (fun r =>
      !((le[p]!)[q]! && (le[q]!)[r]!) || (le[p]!)[r]!))) &&
    (List.range N).all (fun p => (List.range N).all (fun q =>
      !((le[p]!)[q]! && (le[q]!)[p]!) || decide (p = q)))
  let levels := simpLevels N lt (N + 2) ((List.range N).map (fun i => [i]))
  let fVec := levels.map List.length
  { nChains := nc, nObjs := N, fVec := fVec
    euler := (List.range fVec.length).foldl
      (fun a k => a + (-1 : ℤ) ^ k * (fVec.getD k 0 : ℤ)) 0
    betti := bettiOf levels, sane := sane, poset := poset }

/-- `(f₀,f₁,f₂ ; b₀,b₁)` only: enumerates the order complex to degree 2 (`b₁` needs `∂₁` and `∂₂`,
not `∂₃`), so it survives examples whose full order complex does not fit. -/
def betti01 (K : FinBPSet V) : List ℕ × List ℤ :=
  let (N, le, _, _) := ordOf K
  let levels := simpLevels N (strict le) 3 ((List.range N).map (fun i => [i]))
  (levels.map List.length, (bettiOf levels).take 2)

/-- `b₁` alone. -/
def b1 (K : FinBPSet V) : ℤ := (betti01 K).2.getD 1 0

/-! ## Cross-check: the copied machinery reproduces `ConcSpace`'s published table -/

/-- `□ⁿ`. -/
abbrev cube (n : ℕ) : FinBPSet (List (Option Bool)) := Examples.stdCube n

#eval analyze (cube 2)   -- 4 obj, betti [1,1]
#eval analyze (cube 3)   -- 24 obj, betti [1,3,2]
#eval analyze (cube 4)   -- 192 obj, betti [1,6,11,6]
#eval analyze TwoSquares.S
#eval analyze Examples.fourSquare

example : (analyze (cube 2)).betti = [1, 1] := by native_decide
example : (analyze (cube 3)).betti = [1, 3, 2] := by native_decide
example : (analyze (cube 4)).betti = [1, 6, 11, 6] := by native_decide
example : (analyze TwoSquares.S).betti = [1, 3] := by native_decide
example : (analyze Examples.fourSquare).betti = [1, 5] := by native_decide

/-! ## Skeleta are well-formed -/

#eval ((List.range 5).map (fun n => (skel n (cube 4)).wellFormed),
       (List.range 6).map (fun n => (skel n (cube 5)).wellFormed),
       (List.range 4).map (fun n => (skel n Examples.fourSquare).wellFormed),
       (List.range 4).map (fun n => (skel n TwoSquares.S).wellFormed))

example : ((List.range 5).map (fun n => (skel n (cube 4)).wellFormed)).all id = true := by
  native_decide
example : ((List.range 4).map (fun n => (skel n Examples.fourSquare).wellFormed)).all id = true := by
  native_decide

/-! ## (a) `delCube3` = `□³` minus its 3-cell -/

/-- The hollow 3-cube: all six squares, no 3-cell. -/
abbrev delCube3 : FinBPSet (List (Option Bool)) := skel 2 (cube 3)

#eval analyze delCube3     -- vs. `analyze (cube 3)` = betti [1,3,2]

/-! ## (b) `delCube4` = `□⁴` minus its 4-cell -/

/-- The hollow 4-cube: everything of dimension `≤ 3`. -/
abbrev delCube4 : FinBPSet (List (Option Bool)) := skel 3 (cube 4)

#eval analyze delCube4     -- vs. `analyze (cube 4)` = betti [1,6,11,6]

/-! ## (d) The skeleton ladder for `□⁴` -/

#eval (List.range 5).map (fun n => ((skel n (cube 4)).chains.length, analyze (skel n (cube 4))))

-- `b₁` ladder for `□⁴`, `n = 0..4`:
#eval (List.range 5).map (fun n => b1 (skel n (cube 4)))

/-! ## (4) The ladder on branching examples

`fourSquare`, `TwoSquares.S`, `grid2` top out at dimension 2, so their ladders only witness that
`skel n` is the identity once `n ≥ maxDim`.  For a *non-vacuous* branching test we need a
branching `K` that actually has a 4-cell: `serial` glues `K.final` to `L.init`. -/

#eval (List.range 3).map (fun n => analyze (skel n Examples.fourSquare))
#eval (List.range 3).map (fun n => analyze (skel n TwoSquares.S))
#eval (List.range 3).map (fun n => analyze (skel n Examples.grid2))

variable {W : Type*} [DecidableEq W]

/-- `serial K L`: `K` then `L`, gluing `K.final` to `L.init` (which is dropped from `L`'s cells).
Requires `L.init ≠ L.final`. -/
def serial (K : FinBPSet V) (L : FinBPSet W) : FinBPSet (V ⊕ W) where
  cellList := K.cells.map Sum.inl ++ (L.cells.filter (fun c => decide (c ≠ L.init))).map Sum.inr
  dim := Sum.elim K.dim L.dim
  face := fun ε i c => match c with
    | .inl x => (K.face ε i x).map Sum.inl
    | .inr y => (L.face ε i y).map (fun d => if d = L.init then Sum.inl K.final else Sum.inr d)
  init := Sum.inl K.init
  final := Sum.inr L.final

/-- The diamond `a → mᵢ → b` (`i = 1,2`): two parallel edge-paths, no filling. -/
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

/-- Branching, has a 4-cell: `diamond ∘ □⁴`. -/
abbrev dmCube4 : FinBPSet (Dm ⊕ List (Option Bool)) := serial diamond (cube 4)

/-- Branching + connected, has a 3-cell: `grid2 ∘ □³`. -/
abbrev gridCube3 : FinBPSet (Examples.G ⊕ List (Option Bool)) := serial Examples.grid2 (cube 3)

#eval ((List.range 6).map (fun n => (skel n dmCube4).wellFormed),
       (List.range 5).map (fun n => (skel n gridCube3).wellFormed))

example : ((List.range 6).map (fun n => (skel n dmCube4).wellFormed)).all id = true := by
  native_decide
example : ((List.range 5).map (fun n => (skel n gridCube3).wellFormed)).all id = true := by
  native_decide

-- Ladders on the branching examples, `n = 1 .. maxDim`.
#eval (List.range 4).map (fun n => analyze (skel (n + 1) dmCube4))
#eval (List.range 3).map (fun n => analyze (skel (n + 1) gridCube3))

/-! ## (c) `□⁵`

Out of reach: `Int(Lines(□⁵))` has 1920 objects and 99840 edges, and the degree-2 part of its
order complex (needed for `∂₂`, hence for `b₁`) is far larger still.  Only the chain counts are
recorded. -/

#eval ((skel 3 (cube 5)).chains.length, (skel 4 (cube 5)).chains.length,
       (cube 5).chains.length)   -- (530, 540, 541)

/-! ## Verdict

`b₁` **stabilises at the 3-skeleton**, on cubes and on branching `K` alike.

`b₁(Int(Lines (skel n K)))`:

| K                     | n=1 | n=2 | n=3 | n=4 |
|-----------------------|-----|-----|-----|-----|
| `□³`                  |   0 |   7 |   3 |   3 |
| `□⁴`                  |   0 |  31 |   6 |   6 |
| `diamond ∘ □⁴`        |   0 |  62 |  12 |  12 |
| `grid2 ∘ □³`          |   0 |   9 |   5 |   5 |

Full Betti numbers at the decisive step:

| K            | betti                | K minus its top cell | betti          |
|--------------|----------------------|----------------------|----------------|
| `□³`         | `[1,3,2]`            | `skel 2 □³`          | `[1,7]`        |
| `□⁴`         | `[1,6,11,6]`         | `skel 3 □⁴`          | `[1,6,29]`     |

Deleting the 3-cell of `□³` removes 2-dimensional Salvetti cells and moves `b₁` (3 → 7).
Deleting the 4-cell of `□⁴` removes only 3-dimensional Salvetti cells: `b₀` and `b₁` are
untouched (`1, 6`), while the top Betti number moves (`11, 6` → `29`). -/

-- Deleting a 3-cell MOVES `b₁`; deleting a 4-cell does NOT.
example : (analyze delCube3).betti = [1, 7] := by native_decide
example : (analyze delCube4).betti = [1, 6, 29] := by native_decide

-- The `□³`/`□⁴` ladders stabilise at `n = 3`.
example : (List.range 5).map (fun n => b1 (skel n (cube 3))) = [0, 0, 7, 3, 3] := by native_decide
example : (List.range 5).map (fun n => b1 (skel n (cube 4))) = [0, 0, 31, 6, 6] := by native_decide

-- Same on branching `K`.
example : (List.range 5).map (fun n => b1 (skel n dmCube4)) = [0, 0, 62, 12, 12] := by
  native_decide
example : (List.range 4).map (fun n => b1 (skel n gridCube3)) = [0, 0, 9, 5] := by native_decide

-- The degree-≤2 truncation `betti01` agrees with the full computation on `b₁`.
example : [cube 2, cube 3, cube 4, delCube3, delCube4].map
    (fun K => decide (b1 K = (analyze K).betti.getD 1 0)) = [true, true, true, true, true] := by
  native_decide

end Skel
end CubeTest
