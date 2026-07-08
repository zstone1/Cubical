import Mathlib

/-!
# Probe: counting `|Hom(serialWedge A, serialWedge B)|` vs `|{valid σ}|`

Fully self-contained (mathlib only). Three independent computations:

* `bruteValid A B` — brute force over all permutations σ of `Fin n`
  (n = A.sum = B.sum), counting those satisfying `IsEvValid` (encoded combinatorially).
* `chainCountRec A B` and `formula2 A B` — two closed forms of the derived count.
* `homGeom A B` — a **geometric** count of cube-chains of shape A in a concrete
  model of `serialWedge B` (sign vectors + junction canonicalization),
  i.e. an INDEPENDENT computation of `|Hom(serialWedge A, serialWedge B)|`.

If all four agree across the sample, the counting formula is empirically confirmed.
Not imported by root; disposable.
-/

namespace EvCount

/-! ## Basic arithmetic -/

def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- multinomial `b! / ∏ parts!`. -/
def multinom (b : ℕ) (parts : List ℕ) : ℕ := fact b / (parts.map fact).prod

/-- block index of position `x` under contiguous blocks of sizes `L`. -/
def blockId : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: L, x => if x < a then 0 else blockId L (x - a) + 1

/-! ## (1) Brute force over permutations: `IsEvValid` -/

def sigmaAt (p : List ℕ) (x : ℕ) : ℕ := p.getD x 0

/-- Faithful encoding of `IsEvValid σ` for a permutation `p` (p x = σ x):
    (i) within each A-block σ is strictly monotone;
    (ii-placement) same A-block ⟹ same B-block;
    (ii-monotone) the induced block map is monotone. -/
def validPerm (A B : List ℕ) (p : List ℕ) : Bool :=
  let n := A.sum
  (List.range n).all (fun x =>
    (List.range n).all (fun x' =>
      if x < x' then
        (if blockId A x = blockId A x'
           then decide (sigmaAt p x < sigmaAt p x') else true)
        &&
        (if blockId A x = blockId A x'
           then decide (blockId B (sigmaAt p x) = blockId B (sigmaAt p x')) else true)
        &&
        decide (blockId B (sigmaAt p x) ≤ blockId B (sigmaAt p x'))
      else true))

def bruteValid (A B : List ℕ) : ℕ :=
  if A.sum ≠ B.sum then 0 else
  let n := A.sum
  ((List.permutations (List.range n)).filter (validPerm A B)).length

/-! ## (2) Two derived closed forms -/

/-- Segal-split recursion: `Σ_{A = pre ++ suf, pre.sum = b} multinom b pre * rec suf B'`. -/
def chainCountRec : List ℕ → List ℕ → ℕ
  | A, [] => if A.sum = 0 then 1 else 0
  | A, b :: B' =>
      (List.range (A.length + 1)).foldl (fun acc k =>
        let pre := A.take k
        let suf := A.drop k
        if pre.sum = b then acc + multinom b pre * chainCountRec suf B' else acc) 0

/-- number of ways to split A into `|B|` consecutive segments with segment j summing B[j]. -/
def splitCount : List ℕ → List ℕ → ℕ
  | A, [] => if A.sum = 0 then 1 else 0
  | A, b :: B' =>
      (List.range (A.length + 1)).foldl (fun acc k =>
        if (A.take k).sum = b then acc + splitCount (A.drop k) B' else acc) 0

/-- `formula2 = #{valid bm} * (∏ B[j]!) / (∏ A[i]!)`. -/
def formula2 (A B : List ℕ) : ℕ :=
  splitCount A B * (B.map fact).prod / (A.map fact).prod

/-! ## (3) Independent geometric count of `|Hom(serialWedge A, serialWedge B)|` -/

/-- all sign vectors (faces) of `□^N`: length-N lists over `Option Bool`. -/
def allFaces : ℕ → List (List (Option Bool))
  | 0 => [[]]
  | N + 1 => (allFaces N).flatMap (fun f => [none :: f, some false :: f, some true :: f])

def faceDim (f : List (Option Bool)) : ℕ := (f.filter Option.isNone).length

/-- faces of `□^N` of dimension `d`. -/
def facesOfDim (N d : ℕ) : List (List (Option Bool)) :=
  (allFaces N).filter (fun f => faceDim f = d)

/-- source corner (none ↦ false). -/
def v0 (f : List (Option Bool)) : List Bool := f.map (fun o => o.getD false)
/-- target corner (none ↦ true). -/
def v1 (f : List (Option Bool)) : List Bool := f.map (fun o => o.getD true)

/-- canonical global vertex of `serialWedge B`.
    A cube-vertex `w` of block `j`: all-false ↦ junction `j`; all-true ↦ junction `j+1`;
    else an interior vertex `(j,w)`. Junctions are `Sum.inl k`, interiors `Sum.inr (j,w)`. -/
def canon (j : ℕ) (w : List Bool) : Sum ℕ (ℕ × List Bool) :=
  if w.all (· = false) then Sum.inl j
  else if w.all (· = true) then Sum.inl (j + 1)
  else Sum.inr (j, w)

instance : DecidableEq (Sum ℕ (ℕ × List Bool)) := by infer_instance

/-- choices for one source cube of dim `d`: a block `j` and a face of `□^{B[j]}` of dim `d`. -/
def cubeChoices (B : List ℕ) (d : ℕ) : List (ℕ × List (Option Bool)) :=
  (List.range B.length).flatMap (fun j =>
    (facesOfDim (B.getD j 0) d).map (fun f => (j, f)))

/-- cartesian product of the per-cube choice lists. -/
def assignments (A B : List ℕ) : List (List (ℕ × List (Option Bool))) :=
  A.foldr (fun d acc =>
    (cubeChoices B d).flatMap (fun c => acc.map (fun rest => c :: rest))) [[]]

/-- check one assignment is a valid init→final chain in serialWedge B. -/
def chainOK (B : List ℕ) (asg : List (ℕ × List (Option Bool))) : Bool :=
  match asg with
  | [] => B.length = 0  -- empty chain: only valid when B is empty (n=0)
  | (j0, f0) :: _ =>
      let lastPair := asg.getLast?.getD (0, [])
      -- init: source corner of first cube is global init (junction 0)
      (canon j0 (v0 f0) == Sum.inl 0) &&
      -- final: target corner of last cube is global final (junction |B|)
      (canon lastPair.1 (v1 lastPair.2) == Sum.inl B.length) &&
      -- consecutive junctions match
      ((List.range (asg.length - 1)).all (fun i =>
        let a := asg.getD i (0, [])
        let b := asg.getD (i + 1) (0, [])
        canon a.1 (v1 a.2) == canon b.1 (v0 b.2)))

def homGeom (A B : List ℕ) : ℕ :=
  if A.sum ≠ B.sum then 0 else
  ((assignments A B).filter (chainOK B)).length

/-! ## Sample table -/

/-- one row: (bruteValid, chainCountRec, formula2, homGeom). -/
def row (A B : List ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (bruteValid A B, chainCountRec A B, formula2 A B, homGeom A B)

-- sanity: all four columns should agree in every row.
#eval row [1,1] [2]        -- expect 2
#eval row [2] [1,1]        -- expect 0
#eval row [1,1] [1,1]      -- id chain shape
#eval row [2] [2]          -- single 2-cube: 1
#eval row [1,1,1] [3]      -- multinomial 3!/1 = 6
#eval row [2,1] [3]        -- 3!/2! = 3
#eval row [1,2] [3]        -- 3!/2! = 3
#eval row [3] [3]          -- 1
#eval row [1,1,1] [2,1]    -- split-sum
#eval row [1,1,1] [1,2]
#eval row [1,1,1] [1,1,1]
#eval row [2,1] [1,2]
#eval row [2,1] [2,1]
#eval row [1,2] [2,1]
#eval row [2,2] [2,2]
#eval row [1,1,2] [2,2]
#eval row [1,3] [4]        -- 4!/3! = 4
#eval row [2,2] [4]        -- 4!/(2!2!) = 6
#eval row [1,1,1,1] [2,2]  -- split-sum of multinomials

-- an aggregate boolean: do all four agree on every sampled row?
def samples : List (List ℕ × List ℕ) :=
  [([1,1],[2]), ([2],[1,1]), ([1,1],[1,1]), ([2],[2]), ([1,1,1],[3]),
   ([2,1],[3]), ([1,2],[3]), ([3],[3]), ([1,1,1],[2,1]), ([1,1,1],[1,2]),
   ([1,1,1],[1,1,1]), ([2,1],[1,2]), ([2,1],[2,1]), ([1,2],[2,1]),
   ([2,2],[2,2]), ([1,1,2],[2,2]), ([1,3],[4]), ([2,2],[4]), ([1,1,1,1],[2,2])]

#eval samples.all (fun (AB : List ℕ × List ℕ) =>
  let (a,b,c,d) := row AB.1 AB.2
  (a == b) && (b == c) && (c == d))

-- splitCount is always ≤ 1 (A entries positive ⟹ prefix sums strictly increasing ⟹
-- each B-boundary has a unique cut). So the closed form collapses to
-- `∏ B! / ∏ A!` when A refines B, else 0.
#eval samples.all (fun AB => splitCount AB.1 AB.2 ≤ 1)  -- expect true

/-- The OLD (buggy) validity, WITHOUT the `Monotone bm` clause. -/
def validPermNoMono (A B : List ℕ) (p : List ℕ) : Bool :=
  let n := A.sum
  (List.range n).all (fun x =>
    (List.range n).all (fun x' =>
      if x < x' then
        (if blockId A x = blockId A x'
           then decide (sigmaAt p x < sigmaAt p x') else true)
        &&
        (if blockId A x = blockId A x'
           then decide (blockId B (sigmaAt p x) = blockId B (sigmaAt p x')) else true)
      else true))

def bruteNoMono (A B : List ℕ) : ℕ :=
  if A.sum ≠ B.sum then 0 else
  ((List.permutations (List.range A.sum)).filter (validPermNoMono A B)).length

-- The bug the `Monotone bm` clause fixes: without it, [1,1]→[1,1] over-counts (2 vs |Hom|=1).
#eval (bruteNoMono [1,1] [1,1], bruteValid [1,1] [1,1], homGeom [1,1] [1,1])  -- (2,1,1)

end EvCount
