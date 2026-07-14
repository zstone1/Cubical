import CubeChains.Testing.Examples
import CubeChains.Testing.TwoSquares

set_option linter.style.longLine false

/-!
# Testing/CubeChainComplex — the merge complex vs. the nerve of `Ch K`

Two ℚ-chain complexes attached to a finite bi-pointed precubical set `K`:

* the **merge complex**, graded by `nbeads`: the cell of a chain `c` is its stratum
  `{τ : Fin (nbeads c) → ℝ | StrictMono}`, and `∂` merges adjacent beads `c_j, c_{j+1}` into a cube
  `D` of `K`.  This is the Borel–Moore (cellular) complex of the schedule space, locally `ℝⁿ`;
* the **order complex** of the poset `Ch K` (simplicial homology of `N(Ch K) ≃ P⃗(K)`).

Poincaré duality predicts `bₖ(merge) = bₙ₋ₖ(nerve)`, `n = dimSum`.  Three boundary rules are run:
`bd` (only the canonical staircase `D = loFace × hiFace` — **misses cells**), `bdAll` (every
staircase, sign `(-1)ʲ`) and `bdSym` (every staircase, `(-1)ʲ ·` shuffle sign).  The shuffle sign is
the cocycle of the orientation local system of `Sched K` (`orientReport`); `bdAll` and `bdSym`
therefore compute the untwisted and the `or`-twisted BM homology, and agree iff `Sched K` is
orientable.  Everything is `#eval`-able; ranks are Gaussian elimination over ℚ.
-/

namespace CubeTest
namespace ChainComplex

open FinBPSet

/-! ## Linear algebra over ℚ -/

/-- Matrix rank by Gaussian elimination (`fuel` = number of rows). -/
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

/-- Rank of a matrix presented as its list of rows. -/
def rank (rows : List (List ℚ)) : ℕ := rankAux rows.length rows

/-- Coordinates of a formal ℚ-combination in the given basis. -/
def coeffVec {α : Type*} [DecidableEq α] (basis : List α) (s : List (α × ℚ)) : List ℚ :=
  basis.map (fun b => s.foldl (fun acc p => if p.1 = b then acc + p.2 else acc) 0)

section
variable {V : Type*} [DecidableEq V] (K : FinBPSet V)

/-! ## The merge complex -/

/-- Set the last `q` coordinates of `D` to `0` (lands in `dim D - q`). -/
def loFace (q : ℕ) (D : V) : V := (fun x => (K.face false (K.dim x - 1) x).getD x)^[q] D

/-- Set the first `p` coordinates of `D` to `1` (lands in `dim D - p`). -/
def hiFace (p : ℕ) (D : V) : V := (fun x => (K.face true 0 x).getD x)^[p] D

/-- `D` *fuses* the adjacent beads `x, y`: `D = x × y` as a cube of `K`. -/
def fuses (x y D : V) : Bool :=
  decide (K.dim D = K.dim x + K.dim y) &&
  decide (loFace K (K.dim y) D = x) && decide (hiFace K (K.dim x) D = y)

/-- The `j`-th term of `∂[c]`: merge beads `j, j+1` along every fusing cube. -/
def mergeAt (c : List V) (j : ℕ) : List (List V × ℚ) :=
  match c[j]?, c[j + 1]? with
  | some x, some y =>
    (K.cells.filter (fuses K x y)).map (fun D => (c.take j ++ D :: c.drop (j + 2), (-1 : ℚ) ^ j))
  | _, _ => []

/-- The merge boundary `∂[c] = Σ_j (-1)^j Σ_{D fuses beads j,j+1} [c ▸ D]`. -/
def bd (c : List V) : List (List V × ℚ) :=
  (List.range (c.length - 1)).flatMap (mergeAt K c)

/-! ### The shuffle variant of `∂`

`fuses` only recognizes the *canonical* decomposition `D = (lo face) × (hi face)`, i.e. the lower
staircase of `D`.  Geometrically the merged cell of `D` lies in the closure of the cone of **every**
staircase of `D` — one for each shuffle `S ⊔ Sᶜ` of its coordinates — with the shuffle sign.  This
variant puts all of them in. -/

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

/-- Sign of the shuffle `(S, Sᶜ)` of `{0,…,n-1}`. -/
def shuffleSign (n : ℕ) (S : List ℕ) : ℚ :=
  (-1 : ℚ) ^ (S.flatMap (fun i =>
    (List.range n).filter (fun j => !memB j S && decide (j < i)))).length

/-- Signed contributions of `D` to the merge of the beads `x, y`, one per staircase of `D`. -/
def fuseSigns (x y D : V) : List ℚ :=
  if K.dim D = K.dim x + K.dim y then
    ((sublistsAsc (List.range (K.dim D))).filter (fun S => decide (S.length = K.dim x))).filterMap
      (fun S => if loPart K S D = x ∧ hiPart K S D = y then some (shuffleSign (K.dim D) S) else none)
  else []

/-- The shuffle-corrected merge boundary. -/
def bdSym (c : List V) : List (List V × ℚ) :=
  (List.range (c.length - 1)).flatMap (fun j =>
    match c[j]?, c[j + 1]? with
    | some x, some y => K.cells.flatMap (fun D =>
        (fuseSigns K x y D).map (fun s => (c.take j ++ D :: c.drop (j + 2), (-1 : ℚ) ^ j * s)))
    | _, _ => [])

/-- All staircases, sign `(-1)ʲ` only: the induced-boundary sign of `ι_ν(dτ₀∧⋯∧dτ_{k-1})` at the
wall `τⱼ = τⱼ₊₁`, which does not see the block contents. -/
def bdAll (c : List V) : List (List V × ℚ) :=
  (List.range (c.length - 1)).flatMap (fun j =>
    match c[j]?, c[j + 1]? with
    | some x, some y => K.cells.flatMap (fun D =>
        (fuseSigns K x y D).map (fun _ => (c.take j ++ D :: c.drop (j + 2), (-1 : ℚ) ^ j)))
    | _, _ => [])

/-! ### The orientation character

`bdSym` and `bdAll` differ, edge by edge on the Hasse diagram of `Ch K`, by the shuffle sign of the
merge.  That `±1` edge-labelling is a coboundary (`sign(c ⟶ b) = ε c · ε b`) exactly when the two
complexes are isomorphic — i.e. when the orientation local system of `Sched K` is trivial. -/

/-- Index of a chain in `K.chains`. -/
def idxOf (l : List (List V)) (x : List V) : ℕ := l.findIdx (fun y => decide (y = x))

/-- One-step merges as sign-labelled edges `(source, target, ±1)` on chain indices. -/
def mergeEdges : List (ℕ × ℕ × ℤ) :=
  let chs := K.chains
  chs.flatMap (fun c =>
    (List.range (c.length - 1)).flatMap (fun j =>
      match c[j]?, c[j + 1]? with
      | some x, some y => K.cells.flatMap (fun D =>
          (fuseSigns K x y D).map (fun s =>
            (idxOf chs c, idxOf chs (c.take j ++ D :: c.drop (j + 2)),
             if s < 0 then (-1 : ℤ) else 1)))
      | _, _ => []))

/-- One pass of sign propagation along the edges. -/
def relax (edges : List (ℕ × ℕ × ℤ)) (lab : List (Option ℤ)) : List (Option ℤ) :=
  edges.foldl (fun l e =>
    match l.getD e.1 none, l.getD e.2.1 none with
    | some a, none => l.set e.2.1 (some (a * e.2.2))
    | none, some b => l.set e.1 (some (b * e.2.2))
    | _, _ => l) lab

/-- A candidate `ε : chains → {±1}`: seed one vertex per component, propagate to a fixpoint. -/
def orientLabels (N : ℕ) (edges : List (ℕ × ℕ × ℤ)) : List (Option ℤ) :=
  (fun l =>
    let l := match l.findIdx? Option.isNone with
      | none => l
      | some i => l.set i (some 1)
    (relax edges)^[N + 1] l)^[N + 1] (List.replicate N none)

/-- The sign labelling is a coboundary: every edge agrees with the propagated `ε`. -/
def orientableB (N : ℕ) (edges : List (ℕ × ℕ × ℤ)) : Bool :=
  let l := orientLabels N edges
  edges.all (fun e =>
    match l.getD e.1 none, l.getD e.2.1 none with
    | some a, some b => decide (b = a * e.2.2)
    | _, _ => false)

/-- One BFS pass; each vertex records its parent and the sign of the edge to it (edges undirected,
signs are involutive). -/
def bfsStep (edges : List (ℕ × ℕ × ℤ)) (par : List (Option (ℕ × ℤ))) : List (Option (ℕ × ℤ)) :=
  edges.foldl (fun p e =>
    match p.getD e.1 none, p.getD e.2.1 none with
    | some _, none => p.set e.2.1 (some (e.1, e.2.2))
    | none, some _ => p.set e.1 (some (e.2.1, e.2.2))
    | _, _ => p) par

/-- Tree path from `v` up to (but excluding) `src`, as `(vertex, sign of the edge to its parent)`. -/
def pathBack (par : List (Option (ℕ × ℤ))) (src : ℕ) : ℕ → ℕ → List (ℕ × ℤ)
  | 0, _ => []
  | fuel + 1, v =>
    if v = src then [] else
      match par.getD v none with
      | some (u, s) => (v, s) :: pathBack par src fuel u
      | none => []

/-- A cycle whose sign product is `-1`, when one exists: a label-violating edge, closed by a tree
path in the graph *without* that edge.  Returns the vertex sequence and the sign of each successive
edge (the last sign is the closing edge). -/
def oddCycleIdx (N : ℕ) (edges : List (ℕ × ℕ × ℤ)) : Option (List ℕ × List ℤ) :=
  let l := orientLabels N edges
  match edges.findIdx? (fun e =>
      match l.getD e.1 none, l.getD e.2.1 none with
      | some a, some b => decide (b ≠ a * e.2.2)
      | _, _ => true) with
  | none => none
  | some k =>
    match edges[k]? with
    | none => none
    | some e =>
      let par := (bfsStep (edges.eraseIdx k))^[N + 1]
        ((List.replicate N none).set e.1 (some (e.1, 1)))
      let p := pathBack par e.1 (N + 1) e.2.1
      if p.isEmpty then none
      else some (e.1 :: (p.map Prod.fst).reverse, (p.map Prod.snd).reverse ++ [e.2.2])

/-! ## The order complex of `Ch K`

Objects are indices into `K.chains`; a `k`-simplex is a strictly increasing index list. -/

/-- The refinement order as a Boolean matrix on `K.chains`. -/
def leMat : List (List Bool) := K.chains.map (fun a => K.chains.map (fun b => K.chLe a b))

/-- Strict order from the order matrix. -/
def ltIdx (M : List (List Bool)) (i j : ℕ) : Bool :=
  (M.getD i []).getD j false && !(M.getD j []).getD i false

/-- The `k`-simplices of `N(Ch K)`: strictly increasing lists `x₀ < ⋯ < x_k` of indices. -/
def simp (M : List (List Bool)) (N : ℕ) : ℕ → List (List ℕ)
  | 0 => (List.range N).map (fun i => [i])
  | k + 1 => (simp M N k).flatMap (fun s =>
      match s with
      | [] => []
      | x :: _ => ((List.range N).filter (fun y => ltIdx M y x)).map (fun y => y :: s))

/-- The alternating-face simplicial boundary. -/
def simpBd (s : List ℕ) : List (List ℕ × ℚ) :=
  (List.range s.length).map (fun i => (s.eraseIdx i, (-1 : ℚ) ^ i))

end

/-! ## The comparison -/

/-- Per-example output.  `mergeBetti`/`nerveBetti` are `b₀ … bₙ` (`n = dimSum`); `duality` is the
prediction `bₖ(merge) = bₙ₋ₖ(nerve)`. -/
structure Report where
  nChains : ℕ
  /-- The distinct values of `dimSum` (expected: a singleton `[n]`). -/
  dimSums : List ℕ
  /-- Every merged chain is again an object of `Ch K`. -/
  mergeClosed : Bool
  dSquaredZero : Bool
  mergeBetti : List ℤ
  nerveBetti : List ℤ
  /-- No simplices were dropped past degree `n`. -/
  nerveTruncOK : Bool
  duality : Bool
deriving Repr

/-- Both complexes of `K`, their Betti numbers, and the duality check; `∂` is the merge boundary
under test (`bd K` = the canonical rule, `bdSym K` = the shuffle variant). -/
def report {V : Type*} [DecidableEq V] (K : FinBPSet V)
    (bdy : List V → List (List V × ℚ)) : Report :=
  let chs := K.chains
  let dsums := (chs.map (fun c => (K.dimSeq c).sum)).dedup
  let n := dsums.headD 0
  let ofLen : ℕ → List (List V) := fun k => chs.filter (fun c => decide (c.length = k))
  let mMat : ℕ → List (List ℚ) := fun k =>
    (ofLen k).map (fun c => coeffVec (ofLen (k - 1)) (bdy c))
  let mergeB : List ℤ := (List.range (n + 1)).map (fun k =>
    ((ofLen k).length : ℤ) - (rank (mMat k) : ℤ) - (rank (mMat (k + 1)) : ℤ))
  let M := leMat K
  let N := chs.length
  let S : ℕ → List (List ℕ) := simp M N
  let nMat : ℕ → List (List ℚ) := fun k =>
    if k = 0 then [] else (S k).map (fun s => coeffVec (S (k - 1)) (simpBd s))
  let nerveB : List ℤ := (List.range (n + 1)).map (fun k =>
    ((S k).length : ℤ) - (rank (nMat k) : ℤ) - (rank (nMat (k + 1)) : ℤ))
  { nChains := N
    dimSums := dsums
    mergeClosed := chs.all (fun c => (bdy c).all (fun p => memB p.1 chs))
    dSquaredZero := chs.all (fun c =>
      (coeffVec chs ((bdy c).flatMap (fun p => (bdy p.1).map (fun q => (q.1, p.2 * q.2))))).all
        (fun x => decide (x = 0)))
    mergeBetti := mergeB
    nerveBetti := nerveB
    nerveTruncOK := (S (n + 1)).isEmpty
    duality := mergeB = nerveB.reverse }

/-- The spec'd merge complex (canonical decomposition only). -/
def reportCanon {V : Type*} [DecidableEq V] (K : FinBPSet V) : Report := report K (bd K)

/-- The shuffle-corrected merge complex. -/
def reportSym {V : Type*} [DecidableEq V] (K : FinBPSet V) : Report := report K (bdSym K)

/-- All staircases, sign `(-1)ʲ` only. -/
def reportAll {V : Type*} [DecidableEq V] (K : FinBPSet V) : Report := report K (bdAll K)

/-- Orientability of `Sched K`: is the shuffle-sign 1-cochain on the Hasse diagram a coboundary? -/
structure OrientReport where
  nEdges : ℕ
  /-- Merges that carry the sign `-1`. -/
  nOdd : ℕ
  orientable : Bool
deriving Repr

/-- The orientation character of `Ch K`, computed with no reference to any chain complex. -/
def orientReport {V : Type*} [DecidableEq V] (K : FinBPSet V) : OrientReport :=
  let E := mergeEdges K
  { nEdges := E.length
    nOdd := (E.filter (fun e => decide (e.2.2 < 0))).length
    orientable := orientableB K.chains.length E }

/-- A cycle of `Ch K` along which the orientation character is `-1` (`prod` re-verifies it). -/
structure OddCycle (α : Type*) where
  cycle : List α
  signs : List ℤ
  prod : ℤ
deriving Repr

/-- The non-orientability witness: chains `c₀ … c_m`, closed by an edge `c_m — c₀`. -/
def oddCycle {V : Type*} [DecidableEq V] (K : FinBPSet V) : Option (OddCycle (List V)) :=
  (oddCycleIdx K.chains.length (mergeEdges K)).map (fun p =>
    { cycle := p.1.map (fun i => K.chains.getD i [])
      signs := p.2
      prod := p.2.foldl (· * ·) 1 })

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

/-! ### The spec'd merge complex (canonical decomposition only)

Duality `bₖ(merge) = bₙ₋ₖ(nerve)` holds for every example **except `fourSquare`**, where the merge
complex is acyclic (`∂₃` is an isomorphism) while the nerve is `S¹`.  Cause: each square is fused to
only *one* of the two paths across it, so the four-cycle's incidences are half missing. -/

#eval reportCanon Examples.square
#eval reportCanon Examples.cube3
#eval reportCanon TwoSquares.S
#eval reportCanon diamond
#eval reportCanon Examples.grid2
#eval reportCanon Examples.fourSquare   -- duality := false
#eval reportCanon Examples.threeSquare
#eval reportCanon Examples.fourPaths

/-! ### The shuffle variant

Restores the missing incidences; duality then holds on all eight examples, and on the trinity. -/

#eval reportSym Examples.square
#eval reportSym Examples.cube3
#eval reportSym TwoSquares.S
#eval reportSym diamond
#eval reportSym Examples.grid2
#eval reportSym Examples.fourSquare
#eval reportSym Examples.threeSquare
#eval reportSym Examples.fourPaths

/-! ### All staircases, sign `(-1)ʲ` only (the geometric induced-boundary sign)

Agrees with `reportSym` on all eight (they differ by the coboundary `ε`, since all eight are
orientable).  The trinity below separates them. -/

#eval reportAll Examples.square
#eval reportAll Examples.cube3
#eval reportAll TwoSquares.S
#eval reportAll diamond
#eval reportAll Examples.grid2
#eval reportAll Examples.fourSquare
#eval reportAll Examples.threeSquare
#eval reportAll Examples.fourPaths

/-! ### The orientation character (no chain complex involved) -/

#eval orientReport Examples.square
#eval orientReport Examples.cube3
#eval orientReport TwoSquares.S
#eval orientReport diamond
#eval orientReport Examples.grid2
#eval orientReport Examples.fourSquare
#eval orientReport Examples.threeSquare
#eval orientReport Examples.fourPaths

#eval oddCycle Examples.fourSquare

/-! ### The trinity

`EventNamingCounterexample.T` has **no global event naming**, and it is the one example whose
orientation character is nontrivial: `N(Ch T) ≃ S¹`, `Sched T` is a non-orientable surface, `bdAll`
is acyclic (= `H^{2-k}(S¹; or) = 0`) while `bdSym` is dual to the nerve. -/

#eval reportCanon EventNamingCounterexample.T
#eval reportSym EventNamingCounterexample.T
#eval reportAll EventNamingCounterexample.T
#eval orientReport EventNamingCounterexample.T
#eval oddCycle EventNamingCounterexample.T

end ChainComplex
end CubeTest
