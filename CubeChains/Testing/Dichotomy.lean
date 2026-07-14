import CubeChains.Testing.Examples
import CubeChains.Testing.TwoSquares

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false
set_option linter.style.longLine false

/-!
# Testing/Dichotomy — concurrency vs. causality

Two features of a finite bi-pointed precubical set, and two invariants, one per feature.

* **causality** = a directed 2-path `w →e₁→ x →e₂→ v` that is *not* filled by a 2-cube: `e₂` must
  wait for `e₁`.  Detected (allegedly) by the **curvature** `∂²` of the vertex/altitude complex
  `C_k = ℚ[alt⁻¹ k]`, `∂[v] = Σ_{e : u → v} ε e · [u]`.
* **concurrency** = a 2-path that *is* filled: `e₁, e₂` commute.  Detected by the **braid**
  invariant: `Int(Lines K)` (the global Salvetti complex, `ConcSpace.lean`) is non-discrete.

The 2-paths are represented by their **pair of edges** `(e₁, e₂)` (not by the vertex triple: `K` may
have parallel edges), and are partitioned by `fills` into `P2conc` (some 2-cube fuses them) and
`P2caus`.

**Verdict (all machine-checked below).**  Independence (four quadrants) HOLDS.  Braid triviality
HOLDS.  Exactness on cubes HOLDS.  The curvature claim `∂² = 0 ⟺ P2caus = ∅` **FAILS in both
directions** (`EventNamingCounterexample.T` and `Examples.threeSquare`) — see the findings at the
bottom.

**Layer:** Testing (decoupled).  Nothing here imports the main library; the linear algebra, the
`fuses`-style staircase test and `Int(Lines K)` are copied from `CubeChainComplex.lean` /
`ConcSpace.lean` rather than imported.
-/

namespace CubeTest
namespace Dichotomy

open FinBPSet

/-! ## Linear algebra -/

/-- Matrix rank by Gaussian elimination over `ℚ` (`fuel` = number of rows). -/
def rankAux : ℕ → List (List ℚ) → ℕ
  | 0, _ => 0
  | fuel + 1, rows =>
    match rows.filter (fun r => r.any (fun x => decide (x ≠ 0))) with
    | [] => 0
    | r :: rest =>
      match r.findIdx? (fun x => decide (x ≠ 0)) with
      | none => 0
      | some j =>
        let a := r.getD j 0
        let rest' := rest.map (fun s =>
          let c := s.getD j 0 / a
          List.zipWith (fun x y => x - c * y) s r)
        1 + rankAux fuel rest'

/-- Rank over `ℚ` of a matrix presented as its list of rows. -/
def rank (rows : List (List ℚ)) : ℕ := rankAux rows.length rows

/-- `a ⊕ b` over `F₂`. -/
def xorRow (a b : List Bool) : List Bool := List.zipWith xor a b

/-- Solve `A x = b` over `F₂`; a row is `A_i ++ [b_i]`, `n` unknowns.  Free variables are set to `0`;
`none` iff the system is inconsistent. -/
def solveF2 (n : ℕ) (rows : List (List Bool)) : Option (List Bool) :=
  let st := (List.range n).foldl (fun (st : List (ℕ × List Bool) × List (List Bool)) j =>
    match st.2.findIdx? (fun r => r.getD j false) with
    | none => st
    | some i =>
      let p := st.2.getD i []
      ((j, p) :: st.1,
        (st.2.eraseIdx i).map (fun r => if r.getD j false then xorRow r p else r))) ([], rows)
  if st.2.any (fun r => r.getD n false) then none
  else
    -- pivots are stored largest-column-first, which is the back-substitution order
    some (st.1.foldl (fun x jp =>
      x.set jp.1 ((List.range n).foldl (fun acc k =>
        if decide (k ≠ jp.1) && jp.2.getD k false then xor acc (x.getD k false) else acc)
        (jp.2.getD n false))) (List.replicate n false))

/-- All `±1` vectors of length `n`, as bit vectors (`true = -1`). -/
def boolVecs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolVecs n).flatMap (fun v => [false :: v, true :: v])

section
variable {V : Type} [DecidableEq V] (K : FinBPSet V)

/-! ## Vertices, edges, altitude -/

/-- The vertices. -/
def verts : List V := K.cells.filter (fun c => decide (K.dim c = 0))

/-- The edges. -/
def edgesL : List V := K.cells.filter (fun c => decide (K.dim c = 1))

/-- The 2-cubes. -/
def sqs : List V := K.cells.filter (fun c => decide (K.dim c = 2))

/-- Source of an edge. -/
def src (e : V) : V := (K.face false 0 e).getD e

/-- Target of an edge. -/
def tgt (e : V) : V := (K.face true 0 e).getD e

/-- The altitude table: the Bellman–Ford fixpoint of `Model.altStep` (`alt (vertex₁ c) =
alt (vertex₀ c) + dim c`), seeded at `init`.  Meaningful exactly when `K.admitsAltitude`. -/
def altTable : List (V × ℤ) :=
  ((fun s => Option.bind s K.altStep)^[K.cells.length] (some [(K.init, (0 : ℤ))])).getD []

/-- The altitude of a vertex. -/
def altAt (A : List (V × ℤ)) (v : V) : ℤ := (alook A v).getD 0

/-- Vertices of altitude `k`. -/
def vertsAt (A : List (V × ℤ)) (k : ℤ) : List V :=
  (verts K).filter (fun v => decide (altAt A v = k))

/-- The top altitude. -/
def maxAlt (A : List (V × ℤ)) : ℤ := (verts K).foldl (fun a v => max a (altAt A v)) 0

/-! ## 2-paths, staircases, the concurrency/causality partition -/

/-- Every directed 2-path, as the **ordered pair of its edges** `(e₁, e₂)` with
`tgt e₁ = src e₂` (parallel edges therefore give distinct 2-paths). -/
def twoPaths : List (V × V) :=
  (edgesL K).flatMap (fun e₁ =>
    ((edgesL K).filter (fun e₂ => decide (tgt K e₁ = src K e₂))).map (fun e₂ => (e₁, e₂)))

/-- The two staircases of a 2-cube `Q`, i.e. the 2-paths it fuses: `(loPart S Q, hiPart S Q)` for the
two bipartitions `S = {0}` and `S = {1}` of its coordinates.  `S = {0}` is exactly
`CubeChainComplex.fuses`' canonical decomposition (`loFace 1 × hiFace 1`); `S = {1}` is the other,
which the canonical rule misses. -/
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

/-! ## The edge signs -/

/-- Position of an edge in `edgesL`. -/
def eIdx (E : List V) (e : V) : ℕ := E.findIdx (fun y => decide (y = e))

/-- The sign system over `F₂`: one equation per 2-cube `Q`, namely `∏_{e ∈ ∂Q} ε e = -1` (parity of
the four staircase edges), which is what makes the two 2-paths across `Q` cancel in `∂²`. -/
def signRows : List (List Bool) :=
  let E := edgesL K
  (sqs K).map (fun Q =>
    let es := (stairs K Q).flatMap (fun p => [p.1, p.2])
    (E.map (fun e => decide ((es.filter (fun x => decide (x = e))).length % 2 = 1))) ++ [true])

/-- A solution of the sign system, if one exists. -/
def signSol : Option (List Bool) := solveF2 (edgesL K).length (signRows K)

/-- Sign rule (ii): `ε e = -1` iff the bit vector says so.  `ε ≡ +1` (rule (i)) when there is no
solution. -/
def epsOf (E : List V) (x : Option (List Bool)) (e : V) : ℤ :=
  match x with
  | some bs => if bs.getD (eIdx E e) false then -1 else 1
  | none => 1

/-! ## The curvature `∂²` -/

/-- The `(w,v)` entry of `∂ ∘ ∂`: `Σ_{2-paths w →e₁→ x →e₂→ v} ε e₁ * ε e₂`.  (`∂` is graded of
degree `-1` for free: every edge raises the altitude by exactly `1`.) -/
def d2entry (TP : List (V × V)) (ε : V → ℤ) (w v : V) : ℤ :=
  (TP.filter (fun p => decide (src K p.1 = w) && decide (tgt K p.2 = v))).foldl
    (fun acc p => acc + ε p.1 * ε p.2) 0

/-- The pairs `(w,v)` joined by a 2-path — the possible support of `∂²`. -/
def d2pairs (TP : List (V × V)) : List (V × V) := (TP.map (fun p => (src K p.1, tgt K p.2))).dedup

/-- The support of `∂²`. -/
def d2support (TP : List (V × V)) (ε : V → ℤ) : List (V × V) :=
  (d2pairs K TP).filter (fun q => decide (d2entry K TP ε q.1 q.2 ≠ 0))

/-- `∂² = 0`. -/
def d2zero (TP : List (V × V)) (ε : V → ℤ) : Bool := (d2support K TP ε).isEmpty

/-- Is there **any** `ε : edges → {±1}` with `∂² = 0`?  Brute force, so `none` when `#edges > 10`
(for `□³`, `□⁴` the sign rule (ii) already witnesses existence). -/
def someSignZero : Option Bool :=
  let E := edgesL K
  let TP := twoPaths K
  if E.length > 10 then none
  else some ((boolVecs E.length).any (fun x =>
    d2zero K TP (fun e => if x.getD (eIdx E e) false then -1 else 1)))

/-- `∂_k`: rows = altitude-`k` vertices, columns = altitude-`(k-1)` vertices, entry
`Σ_{e : u → v} ε e` (parallel edges add). -/
def dMat (A : List (V × ℤ)) (ε : V → ℤ) (k : ℤ) : List (List ℚ) :=
  (vertsAt K A k).map (fun v => (vertsAt K A (k - 1)).map (fun u =>
    ((edgesL K).filter (fun e => decide (src K e = u) && decide (tgt K e = v))).foldl
      (fun a e => a + (ε e : ℚ)) 0))

/-- Betti numbers of the vertex/altitude complex over `ℚ`. -/
def bettiVert (A : List (V × ℤ)) (ε : V → ℤ) : List ℤ :=
  (List.range ((maxAlt K A).toNat + 1)).map (fun k =>
    ((vertsAt K A k).length : ℤ) - (rank (dMat K A ε (k : ℤ)) : ℤ)
      - (rank (dMat K A ε ((k : ℤ) + 1)) : ℤ))

end

/-! ## `Int(Lines K)` — the braid invariant (copied from `ConcSpace.lean`) -/

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

section
variable {V : Type} [DecidableEq V]

/-- The iterated face of `D` cut out by `a`. -/
def signFace (K : FinBPSet V) (a : List (Option Bool)) (D : V) : V :=
  (List.range a.length).reverse.foldl (fun x i =>
    match a[i]? with
    | some (some ε) => (K.face ε i x).getD x
    | _ => x) D

/-- Tables for one `K`, indexed by position in `K.cells`. -/
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

/-- The refinement order on chains. -/
def chLeI (X : Ctx) (a b : List ℕ) : Bool := a.all (fun p => b.any (fun q => (X.faceT[p]!)[q]!))

/-- `Lines c` — one chamber per bead. -/
def linesOf (X : Ctx) : List ℕ → List (List (List ℕ))
  | [] => [[]]
  | p :: t => (linesOf X t).flatMap (fun L => (chambersD (X.dims[p]!)).map (fun ch => ch :: L))

/-- Restriction data of a refinement `cb ⊑ ca`. -/
def restrData (X : Ctx) (ca cb : List ℕ) : Option (List (ℕ × List ℕ)) :=
  cb.mapM (fun e =>
    match (List.range ca.length).filter (fun i => (X.faceT[e]!)[ca.getD i 0]!) with
    | [i] =>
        match (X.free[ca.getD i 0]!)[e]! with
        | [S] => some (i, S)
        | _ => none
    | _ => none)

/-- Restrict a line along a refinement. -/
def restrLine (rd : List (ℕ × List ℕ)) (L : List (List ℕ)) : List (List ℕ) :=
  rd.map (fun q =>
    ((L.getD q.1 []).filter (fun j => memB j q.2)).map
      (fun j => (q.2.filter (fun k => decide (k < j))).length))

end

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

/-! ## Reports -/

/-- Checks 1, 2, 3, 6 for one `K`. -/
structure DRow (V : Type) where
  /-- `#vertices`, `#edges`, `#2-cubes`. -/
  nV : ℕ
  nE : ℕ
  nSq : ℕ
  /-- The altitude fixpoint is consistent, and covers every vertex. -/
  admitsAlt : Bool
  altTotal : Bool
  /-- **Check 1.** `|P2| = |P2conc| + |P2caus|`, and the two are disjoint. -/
  nP2 : ℕ
  nConc : ℕ
  nCaus : ℕ
  partitionOK : Bool
  /-- **Check 6.** `#(2-cube, staircase)` pairs; every staircase really is a 2-path. -/
  nStairs : ℕ
  stairsOK : Bool
  concEqStairs : Bool
  /-- **Check 2.** The sign system is solvable; `∂² = 0` under rule (i) `ε ≡ +1` and under
  rule (ii); and whether *some* `±1` edge-sign kills `∂²` (brute force). -/
  signsExist : Bool
  d2zeroPlus : Bool
  d2zeroSgn : Bool
  someSignWorks : Option Bool
  /-- Support of `∂²` (rule (ii)): `(w, v, the 2-paths w ⤳ v, are they all causal?)`. -/
  supp : List (V × V × List (V × V) × Bool)
  /-- `∂² = 0 ⟺ P2caus = ∅`, and every nonzero entry is joined only by causal 2-paths. -/
  claimCurvature : Bool
  /-- **Check 3.** Betti numbers of the vertex/altitude complex; exact = all zero. -/
  bettiVertex : List ℤ
  exactB : Bool
deriving Repr

/-- Everything about `K` except the braid invariant. -/
def analyzeD {V : Type} [DecidableEq V] (K : FinBPSet V) : DRow V :=
  let A := altTable K
  let E := edgesL K
  let TP := twoPaths K
  let sol := signSol K
  let ε := epsOf E sol
  let ε1 : V → ℤ := fun _ => 1
  let conc := P2conc K
  let caus := P2caus K
  let st := (sqs K).flatMap (stairs K)
  let supp := (d2support K TP ε).map (fun q =>
    let ps := TP.filter (fun p => decide (src K p.1 = q.1) && decide (tgt K p.2 = q.2))
    (q.1, q.2, ps, ps.all (fun p => !fills K p.1 p.2)))
  let bv := bettiVert K A ε
  { nV := (verts K).length
    nE := E.length
    nSq := (sqs K).length
    admitsAlt := K.admitsAltitude
    altTotal := (verts K).all (fun v => (alook A v).isSome)
    nP2 := TP.length
    nConc := conc.length
    nCaus := caus.length
    partitionOK := decide (TP.length = conc.length + caus.length) &&
      conc.all (fun p => !memB p caus)
    nStairs := st.length
    stairsOK := st.all (fun p => memB p TP)
    concEqStairs := decide (conc.length = st.length)
    signsExist := sol.isSome
    d2zeroPlus := d2zero K TP ε1
    d2zeroSgn := d2zero K TP ε
    someSignWorks := someSignZero K
    supp := supp
    claimCurvature := (d2zero K TP ε == decide (caus.length = 0)) && supp.all (fun q => q.2.2.2)
    bettiVertex := bv
    exactB := bv.all (fun b => decide (b = 0)) }

/-- Check 4 for one `K`. -/
structure BRow where
  /-- `#2-cubes`, and `#cells of dim ≥ 2`. -/
  nSq : ℕ
  nHigh : ℕ
  /-- `Int(Lines K)`: objects, strictly comparable pairs, Betti numbers. -/
  nChains : ℕ
  nObjs : ℕ
  nIntEdges : ℕ
  betti : List ℤ
  b1 : ℤ
  /-- `Int(Lines K)` has no nonidentity morphism. -/
  discrete : Bool
  objsGtChains : Bool
  /-- `K` has a square ⟺ `Int(Lines K)` is not discrete. -/
  claimBraid : Bool
deriving Repr

/-- The braid invariant of `K`. -/
def braidRow {V : Type} [DecidableEq V] (K : FinBPSet V) : BRow :=
  let X := mkCtx K
  let chs := X.chains
  let nc := chs.size
  let rdt : Array (Array (Option (List (ℕ × List ℕ)))) :=
    (Array.range nc).map (fun i => (Array.range nc).map (fun j =>
      if chLeI X (chs[j]!) (chs[i]!) then restrData X (chs[i]!) (chs[j]!) else none))
  let objs : Array (ℕ × List (List ℕ)) :=
    ((List.range nc).flatMap (fun i => (linesOf X (chs[i]!)).map (fun L => (i, L)))).toArray
  let N := objs.size
  let le : Array (Array Bool) := (Array.range N).map (fun p => (Array.range N).map (fun q =>
    match (rdt[(objs[p]!).1]!)[(objs[q]!).1]! with
    | some rd => decide (restrLine rd (objs[p]!).2 = (objs[q]!).2)
    | none => false))
  let lt : ℕ → ℕ → Bool := fun p q => (le[p]!)[q]! && !((le[q]!)[p]!)
  let levels := simpLevels N lt (N + 2) ((List.range N).map (fun i => [i]))
  let fv := levels.map List.length
  let b := bettiOf levels
  let nsq := (sqs K).length
  { nSq := nsq
    nHigh := (K.cells.filter (fun c => decide (2 ≤ K.dim c))).length
    nChains := nc
    nObjs := N
    nIntEdges := fv.getD 1 0
    betti := b
    b1 := b.getD 1 0
    discrete := decide (fv.getD 1 0 = 0)
    objsGtChains := decide (N > nc)
    claimBraid := decide (0 < nsq) == decide (0 < fv.getD 1 0) }

/-- The four-quadrant cell of `K`: `(braid nontrivial?, curvature ≠ 0?)`. -/
def quadrant {V : Type} [DecidableEq V] (K : FinBPSet V) : Bool × Bool :=
  (!(braidRow K).discrete, !(analyzeD K).d2zeroSgn)

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

/-- A square `c00 ⤳ c11` followed by an edge `c11 → z`: concurrency *and* causality. -/
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

/-- `□⁴`. -/
def cube4 : FinBPSet (List (Option Bool)) := Examples.stdCube 4

-- Every example is well-formed.
#eval [Examples.interval.wellFormed, Examples.square.wellFormed, Examples.cube3.wellFormed,
       cube4.wellFormed, TwoSquares.S.wellFormed, diamond.wellFormed, Examples.grid2.wellFormed,
       Examples.fourSquare.wellFormed, Examples.threeSquare.wellFormed, Examples.fourPaths.wellFormed,
       EventNamingCounterexample.T.wellFormed, seq2.wellFormed, sqThenEdge.wellFormed]

/-! ### Checks 1, 2, 3, 6 -/

#eval analyzeD Examples.square              -- □²
#eval analyzeD Examples.cube3               -- □³
#eval analyzeD cube4                        -- □⁴
#eval analyzeD TwoSquares.S
#eval analyzeD diamond
#eval analyzeD Examples.grid2
#eval analyzeD Examples.fourSquare
#eval analyzeD Examples.threeSquare         -- claimCurvature := false
#eval analyzeD Examples.fourPaths
#eval analyzeD EventNamingCounterexample.T  -- claimCurvature := false
#eval analyzeD Examples.interval
#eval analyzeD seq2
#eval analyzeD sqThenEdge

/-! ### Check 4 — braid triviality -/

#eval braidRow Examples.interval
#eval braidRow seq2
#eval braidRow Examples.square
#eval braidRow sqThenEdge
#eval braidRow Examples.cube3
#eval braidRow TwoSquares.S
#eval braidRow diamond
#eval braidRow Examples.grid2
#eval braidRow Examples.fourSquare
#eval braidRow Examples.threeSquare
#eval braidRow Examples.fourPaths
#eval braidRow EventNamingCounterexample.T

/-! ### Check 5 — the four quadrants `(braid nontrivial?, curvature ≠ 0?)` -/

#eval (quadrant Examples.interval,          -- (false, false)
       quadrant seq2,                       -- (false, true)
       quadrant Examples.square,            -- (true,  false)
       quadrant sqThenEdge)                 -- (true,  true)

/-! ## Findings

| K            | ‖E‖ | ‖P2‖ | conc | caus | #sq | stairs | signs? | ∂²=0 (ε≡1) | ∂²=0 (ε) | ∃ε: ∂²=0 | claim 2 |
|--------------|-----|------|------|------|-----|--------|--------|------------|----------|----------|---------|
| `□¹`         |   1 |    0 |    0 |    0 |   0 |      0 | yes    | yes        | yes      | yes      | ✔       |
| `seq2`       |   2 |    1 |    0 |    1 |   0 |      0 | yes    | no         | no       | no       | ✔       |
| `□²`         |   4 |    2 |    2 |    0 |   1 |      2 | yes    | no         | yes      | yes      | ✔       |
| `sqThenEdge` |   5 |    4 |    2 |    2 |   1 |      2 | yes    | no         | no       | no       | ✔       |
| `□³`         |  12 |   12 |   12 |    0 |   6 |     12 | yes    | no         | yes      | —        | ✔       |
| `□⁴`         |  32 |   48 |   48 |    0 |  24 |     48 | yes    | no         | yes      | —        | ✔       |
| `TwoSquares` |   4 |    2 |    2 |    0 |   2 |      4 | yes    | no         | yes      | yes      | ✔       |
| `diamond`    |   4 |    2 |    0 |    2 |   0 |      0 | yes    | no         | no       | **yes**  | ✔       |
| `grid2`      |   7 |    6 |    4 |    2 |   2 |      4 | yes    | no         | no       | no       | ✔       |
| `fourSquare` |   8 |    8 |    8 |    0 |   4 |      8 | yes    | no         | yes      | yes      | ✔       |
| `threeSquare`|   8 |    8 |    6 |    2 |   3 |      6 | yes    | no         | **yes**  | yes      | **✘**   |
| `fourPaths`  |   8 |    8 |    0 |    8 |   0 |      0 | yes    | no         | no       | yes      | ✔       |
| trinity `T`  |   6 |    3 |    3 |    0 |   3 |      6 | **no** | no         | **no**   | **no**   | **✘**   |

**Claim 1 (partition) — HOLDS** everywhere (`partitionOK`), by construction.

**Claim 2 (curvature) — FAILS, in both directions.**  Sign rule (i) `ε ≡ +1` is useless: `∂² = 0`
only when there is no 2-path at all.  Sign rule (ii) is: choose `ε : edges → {±1}` so that for every
2-cube the product of `ε` over its four boundary edges is `-1` (an affine `F₂` system, one equation
per 2-cube — this is exactly what makes the two staircases of a square cancel in `∂²`).  Under (ii):

* it works on `□ⁿ`, `grid2`, `fourSquare`, `TwoSquares.S`, `diamond`, `seq2`, `sqThenEdge`,
  `fourPaths` — `∂² = 0` iff there is no causal 2-path, and the support of `∂²` is exactly the pairs
  `(w,v)` joined by causal 2-paths;
* a 2-path lying in **two** squares is harmless (`TwoSquares.S`): 2-paths are counted once, not once
  per filling square, so the two staircases still cancel and `∂² = 0`;
* **`threeSquare` refutes `caus ≠ ∅ ⟹ ∂² ≠ 0`.**  Its two causal 2-paths `(a,b1)` and `(ap,g1)` are
  *parallel* (both `o ⤳ z1`), and the three squares force `ε(a)ε(b1)ε(ap)ε(g1) = -1` (the equation of
  the *deleted* square `T41` is the sum of the other three), so the two causal terms cancel and
  `∂² = 0` for **every** admissible sign.  Causality is present and invisible.
* **the trinity `T` refutes `caus = ∅ ⟹ ∂² = 0`.**  All 3 of its 2-paths are concurrent, but they
  are pairwise parallel (`a ⤳ d`) and there are an **odd** number of them, so `∂²(a,d) = ±1 ±1 ±1 ≠ 0`
  for every `ε` (`someSignWorks = false`, brute-forced over all `2⁶` signs).  Equivalently: the `F₂`
  sign system is **inconsistent** (the three square-equations sum to `0 = 1`) — the same obstruction
  as the non-orientability of `Sched T` in `CubeChainComplex.orientReport`.
* `diamond` shows the "∃ a sign" reading is also wrong: its 2 causal 2-paths are parallel, so a
  *bespoke* sign kills `∂²`, even though no square exists (`someSignWorks = true`).

  **What `∂²` actually computes:** the *signed* count of 2-paths between each pair of vertices.  It
  detects causality only up to cancellation between parallel 2-paths.  So `∂²` is a lower bound:
  `∂² ≠ 0 ⟹ P2caus ≠ ∅` FAILS (trinity), and `P2caus ≠ ∅ ⟹ ∂² ≠ 0` FAILS (`threeSquare`).

**Claim 3 (exactness on cubes) — HOLDS.**  `□², □³, □⁴` all have `bettiVertex = [0,…,0]` (including
`b₀`): the vertex/altitude complex of `□ⁿ` with sign rule (ii) is the Koszul complex of `Λ*(ℚⁿ)`,
which is exact.  So where the "Morse complex" is defined it carries no information.  (`bettiVertex`
is *only* meaningful when `d2zeroSgn` — otherwise there is no complex, and the alternating count goes
negative: `grid2` prints `[0,-1,-1,0]`.  It is exact on `□ⁿ`, `fourSquare`, `threeSquare`,
`TwoSquares.S` — i.e. on every example where `∂² = 0`.)

**Claim 4 (braid triviality) — HOLDS** on all 12 examples, under all three readings, which agree:
`K` has a cell of dimension `≥ 2` ⟺ `Int(Lines K)` has a nonidentity morphism (`nIntEdges > 0`) ⟺
`#objects > #chains` ⟺ `b₁(Int(Lines K)) ≠ 0`.

**Claim 5 (independence) — HOLDS.**  All four quadrants are occupied:

| K            | braid nontrivial | curvature ≠ 0 |
|--------------|------------------|---------------|
| `□¹`         | no               | no            |
| `seq2`       | no               | **yes**       |
| `□²`         | **yes**          | no            |
| `sqThenEdge` | **yes**          | **yes**       |

So concurrency and causality are logically independent, and each invariant is blind to the other
feature.  (`curvature ≠ 0` is read off sign rule (ii); by Claim 2 it is only a *sufficient* witness
of causality, not a characterisation.)

**Claim 6 (conservation) — FAILS as an identity, holds as an inequality.**  What is counted:
`nConc` = distinct edge-pairs `(e₁,e₂)` that some 2-cube fuses; `nStairs` = `(2-cube, staircase)`
pairs = `2 · #squares` (every staircase is a 2-path — `stairsOK` holds everywhere).  These agree on
every example **except** `TwoSquares.S` (`2 ≠ 4`) and the trinity `T` (`3 ≠ 6`) — exactly the two
examples where a 2-path is filled by more than one square.  So the honest statement is
`nConc ≤ 2 · #squares`, with equality iff no 2-path is doubly filled.  (The literal reading
"#braid generators = 2-paths that fill" is `nConc` by definition, i.e. vacuous.) -/

/-! ### The findings, pinned -/

/-- The four structural guards of `analyzeD` (Claim 1 + sanity). -/
def guards {V : Type} [DecidableEq V] (K : FinBPSet V) : Bool :=
  let r := analyzeD K
  r.partitionOK && r.stairsOK && r.admitsAlt && r.altTotal

-- Claim 1 and the staircase sanity check, everywhere.
example : [guards Examples.square, guards Examples.cube3, guards TwoSquares.S,
    guards Examples.grid2, guards Examples.fourSquare, guards Examples.threeSquare,
    guards Examples.fourPaths, guards diamond, guards EventNamingCounterexample.T,
    guards Examples.interval, guards seq2, guards sqThenEdge].all id = true := by native_decide

-- Claim 3: the vertex/altitude complex of a cube is exact.
example : (analyzeD Examples.square).bettiVertex = [0, 0, 0] := by native_decide
example : (analyzeD Examples.cube3).bettiVertex = [0, 0, 0, 0] := by native_decide
example : (analyzeD cube4).bettiVertex = [0, 0, 0, 0, 0] := by native_decide

-- Claim 5: the four quadrants.
example : (quadrant Examples.interval, quadrant seq2, quadrant Examples.square, quadrant sqThenEdge)
    = ((false, false), (false, true), (true, false), (true, true)) := by native_decide

-- Claim 4, on every example.
example : [braidRow Examples.interval, braidRow seq2, braidRow Examples.square,
    braidRow sqThenEdge, braidRow Examples.cube3, braidRow TwoSquares.S, braidRow diamond,
    braidRow Examples.grid2, braidRow Examples.fourSquare, braidRow Examples.threeSquare,
    braidRow Examples.fourPaths, braidRow EventNamingCounterexample.T].all
    (fun r => r.claimBraid && (r.discrete == !r.objsGtChains) && (r.discrete == decide (r.b1 = 0)))
    = true := by native_decide

-- **Claim 2 FAILS.**  `threeSquare`: two causal 2-paths, yet `∂² = 0` for every admissible sign.
example : (analyzeD Examples.threeSquare).nCaus = 2 := by native_decide
example : (analyzeD Examples.threeSquare).d2zeroSgn = true := by native_decide
example : (analyzeD Examples.threeSquare).claimCurvature = false := by native_decide

-- **Claim 2 FAILS.**  The trinity: no causal 2-path, yet `∂² ≠ 0` for *every* `±1` edge sign.
example : (analyzeD EventNamingCounterexample.T).nCaus = 0 := by native_decide
example : (analyzeD EventNamingCounterexample.T).signsExist = false := by native_decide
example : (analyzeD EventNamingCounterexample.T).someSignWorks = some false := by native_decide
example : (analyzeD EventNamingCounterexample.T).claimCurvature = false := by native_decide

-- The `diamond`: no square at all, yet a bespoke sign kills `∂²` — "∃ε" is not the right reading.
example : ((analyzeD diamond).nSq = 0 ∧ (analyzeD diamond).nCaus = 2) := by native_decide
example : (analyzeD diamond).someSignWorks = some true := by native_decide
example : (analyzeD diamond).d2zeroSgn = false := by native_decide

-- **Claim 6 FAILS as an identity**: `TwoSquares.S` and the trinity doubly-fill a 2-path.
example : ((analyzeD TwoSquares.S).nConc = 2 ∧ (analyzeD TwoSquares.S).nStairs = 4) := by
  native_decide
example : ((analyzeD EventNamingCounterexample.T).nConc = 3 ∧
    (analyzeD EventNamingCounterexample.T).nStairs = 6) := by native_decide
example : [(analyzeD Examples.square).concEqStairs, (analyzeD Examples.cube3).concEqStairs,
    (analyzeD Examples.grid2).concEqStairs, (analyzeD Examples.fourSquare).concEqStairs,
    (analyzeD Examples.threeSquare).concEqStairs, (analyzeD sqThenEdge).concEqStairs].all id
    = true := by native_decide

end Dichotomy
end CubeTest
