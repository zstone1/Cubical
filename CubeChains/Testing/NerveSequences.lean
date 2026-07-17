import CubeChains.Testing.TerminalPi1
import Std.Data.HashMap

/-!
# Testing/NerveSequences — full f-vector, Euler, and Betti sequences of `ConcGrpd(Zbp)`

Extends `TerminalPi1`'s finite combinatorial model of the `n`-event stratum of `ConcCat Zbp`
to the *entire* nerve: not just `V, E, F₂` but all higher nondegenerate simplices `F_k` (chains
of `k` composable non-identity refinements), the full-complex Euler characteristic, and Betti
numbers `b_k` via modular Gaussian elimination on every boundary map `∂_k`.

Key structural fact making this a genuine finite complex: a non-identity refinement strictly
increases the bead count, and bead count ranges in `[1, n]`; so composites of non-identities are
non-identities (no degeneracy), and the top nondegenerate dimension is `n-1` (`F_k = 0` for `k ≥ n`).

Ranks are computed over a large prime field `𝔽_p` (two primes, cross-checked) to avoid the rational
bignum explosion of `TerminalPi1.rankRows`; the Euler = alternating-Betti identity cross-checks all.

Overnight computational run.  Not built by `lake build CubeChains`.
-/

set_option linter.style.nativeDecide false
set_option maxRecDepth 10000

open TerminalPi1

namespace NerveSeq

/-! ## Nerve data: objects, edges, composition, out-adjacency -/

/-- Precomputed model of the `n`-event stratum: indexed objects/edges plus the maps needed for
composition (`edgeMap`) and chain extension (`outEdges`). -/
structure NerveData where
  V : Nat
  objs : Array Obj
  edges : Array (Nat × Part × Nat)   -- (srcObjIdx, block data, tgtObjIdx)
  E : Nat
  edgeMap : Std.HashMap (Nat × Part) Nat  -- (srcObjIdx, Part) ↦ edge index
  outEdges : Array (Array Nat)            -- per object index: edge indices sourced there

/-- Build the indexed model from `objectsOf`/`edgesOf`. -/
def buildNerve (n : Nat) : NerveData := Id.run do
  let objs := (objectsOf n).toArray
  let V := objs.size
  let mut objIdx : Std.HashMap Obj Nat := {}
  for i in [0:V] do
    objIdx := objIdx.insert objs[i]! i
  let mut edges : Array (Nat × Part × Nat) := #[]
  let mut edgeMap : Std.HashMap (Nat × Part) Nat := {}
  let mut outEdges : Array (Array Nat) := Array.replicate V #[]
  for e in edgesOf n do
    let s := objIdx.getD e.1 0
    let t := objIdx.getD e.2.2 0
    let idx := edges.size
    edges := edges.push (s, e.2.1, t)
    edgeMap := edgeMap.insert (s, e.2.1) idx
    outEdges := outEdges.modify s (fun arr => arr.push idx)
  return { V, objs, edges, E := edges.size, edgeMap, outEdges }

/-! ## Chain enumeration (nondegenerate simplices of the nerve) -/

/-- `chainLevels nd maxK`: `result[i]` = all `(i+1)`-chains (arrays of `i+1` composable edge
indices), for `i = 0 .. maxK-1`.  A `(k)`-chain is a nondegenerate `k`-simplex of the nerve. -/
def chainLevels (nd : NerveData) (maxK : Nat) : Array (Array (Array Nat)) := Id.run do
  if maxK == 0 then return #[]
  let mut levels : Array (Array (Array Nat)) := #[]
  let one := (Array.range nd.E).map (fun e => #[e])
  levels := levels.push one
  let mut cur := one
  for _ in [1:maxK] do
    let mut nxt : Array (Array Nat) := #[]
    for ch in cur do
      let last := ch[ch.size - 1]!
      let (_, _, t) := nd.edges[last]!
      for e in nd.outEdges[t]! do
        nxt := nxt.push (ch.push e)
    cur := nxt
    levels := levels.push nxt
  return levels

/-- f-vector `[V, F₁, F₂, …, F_{n-1}]` where `F_k` = # nondegenerate `k`-simplices. -/
def fVector (n : Nat) : Array Nat := Id.run do
  let nd := buildNerve n
  let maxK := n - 1   -- top nondegenerate dimension
  let levels := chainLevels nd maxK
  let mut fv : Array Nat := #[nd.V]
  for lvl in levels do
    fv := fv.push lvl.size
  return fv

/-- f-vector by a walk-count recurrence (no chain materialization).  `v L e` = # of `L`-chains
starting with edge `e`; `v (L+1) e = Σ_{src e' = tgt e} v L e'`; `F_L = Σ_e v L e`.  Cheap enough
for `n = 5`, where materializing all chains would blow memory. -/
def fVectorCount (n : Nat) : Array Nat := Id.run do
  let nd := buildNerve n
  let maxK := n - 1
  let mut fv : Array Nat := #[nd.V]
  if maxK == 0 then return fv
  let mut v : Array Nat := Array.replicate nd.E 1
  fv := fv.push (v.foldl (· + ·) 0)
  for _ in [1:maxK] do
    let mut w : Array Nat := Array.replicate nd.E 0
    for e in [0:nd.E] do
      let (_, _, t) := nd.edges[e]!
      let mut s := 0
      for e' in nd.outEdges[t]! do
        s := s + v[e']!
      w := w.set! e s
    v := w
    fv := fv.push (v.foldl (· + ·) 0)
  return fv

/-! ## Boundary maps and sparse modular rank

Columns of `∂_k` are the boundaries of the `k`-simplices, each with ≤ `k+1` nonzeros.  Rank is
computed over `𝔽_p` (large prime) by sparse Gaussian elimination in echelon form keyed by leading
(minimal) row index — avoids the rational bignum blowup of dense elimination. -/

/-- A sparse column: row index ↦ coefficient (kept nonzero; reduced mod `p` during elimination). -/
abbrev SVec := Std.HashMap Nat Int

def nrm (p x : Int) : Int := ((x % p) + p) % p

/-- `base ^ exp mod p`. -/
partial def modPow (p base exp : Int) : Int :=
  if exp ≤ 0 then 1
  else
    let h := modPow p base (exp / 2)
    let h2 := (h * h) % p
    if exp % 2 == 1 then (h2 * (nrm p base)) % p else h2

/-- Modular inverse mod prime `p` (Fermat). -/
def modInv (p a : Int) : Int := modPow p (nrm p a) (p - 2)

/-- `v + factor · pv` (mod `p`), dropping resulting zeros. -/
def addScaled (p : Int) (v : SVec) (factor : Int) (pv : SVec) : SVec := Id.run do
  let mut r := v
  for (k, c) in pv.toList do
    let nc := nrm p ((r.getD k 0) + factor * c)
    if nc == 0 then r := r.erase k else r := r.insert k nc
  return r

/-- Minimal (leading) row index present in the sparse vector. -/
def leadIdx (v : SVec) : Option Nat := Id.run do
  let mut best : Option Nat := none
  for (k, _) in v.toList do
    match best with
    | none => best := some k
    | some b => if k < b then best := some k
  return best

/-- Reduce `v` against the echelon `pivots` (keyed by leading index); return a new pivot
`(leadingRow, reducedVec)` if `v` is independent, else `none`. -/
partial def reduceVec (p : Int) (pivots : Std.HashMap Nat SVec) (v : SVec) : Option (Nat × SVec) :=
  match leadIdx v with
  | none => none
  | some r =>
    match pivots.get? r with
    | none => some (r, v)
    | some pv =>
      let piv := pv.getD r 0
      let cr := v.getD r 0
      let factor := nrm p (- cr * modInv p piv)
      reduceVec p pivots (addScaled p v factor pv)

/-- Rank over `𝔽_p` of the matrix whose columns are `cols`. -/
def rankSparse (p : Int) (cols : Array SVec) : Nat := Id.run do
  let mut pivots : Std.HashMap Nat SVec := {}
  let mut rank := 0
  for c in cols do
    match reduceVec p pivots c with
    | none => pure ()
    | some (r, v) => pivots := pivots.insert r v; rank := rank + 1
  return rank

/-! ### Building boundary columns -/

/-- Edge index of the composite `a ; b` (source of `a`, block data `compParts (part a) (part b)`). -/
def compEdgeIdx (nd : NerveData) (a b : Nat) : Nat :=
  let (sa, pa, _) := nd.edges[a]!
  let (_, pb, _) := nd.edges[b]!
  nd.edgeMap.getD (sa, compParts pa pb) 0

/-- Faces of a `k`-chain `c` as `(faceKey, sign)`: `d₀` (drop first), `dᵢ` (compose `c[i-1];c[i]`,
`1≤i≤k-1`), `d_k` (drop last); sign of `dᵢ` is `(-1)^i`. -/
def faces (nd : NerveData) (c : Array Nat) : List (List Nat × Int) := Id.run do
  let k := c.size
  let cl := c.toList
  let mut fs : List (List Nat × Int) := [(cl.drop 1, (1 : Int))]     -- d₀, sign +1
  for i in [1:k] do
    let comp := compEdgeIdx nd (c[i-1]!) (c[i]!)
    let key := (cl.take (i-1)) ++ [comp] ++ (cl.drop (i+1))
    fs := (key, if i % 2 == 0 then 1 else -1) :: fs
  fs := (cl.take (k-1), if k % 2 == 0 then 1 else -1) :: fs           -- d_k, sign (-1)^k
  return fs

/-- `∂₁` columns (over objects): edge `(s,_,t)` ↦ `[t] − [s]`. -/
def d1cols (nd : NerveData) : Array SVec :=
  nd.edges.map fun (s, _, t) =>
    let m : SVec := {}
    (m.insert t (1 : Int)).insert s (-1)

/-- `∂_k` columns (`k≥2`), over `(k-1)`-simplices indexed by `idxMap`. -/
def dkCols (nd : NerveData) (kchains : Array (Array Nat))
    (idxMap : Std.HashMap (List Nat) Nat) : Array SVec :=
  kchains.map fun c => Id.run do
    let mut col : SVec := {}
    for (key, sign) in faces nd c do
      match idxMap.get? key with
      | none => pure ()
      | some fi =>
        let nc := (col.getD fi 0) + sign
        if nc == 0 then col := col.erase fi else col := col.insert fi nc
    return col

/-- Index maps `(k-1)-chain ↦ index` for every level. -/
def buildChainIdx (levels : Array (Array (Array Nat))) :
    Array (Std.HashMap (List Nat) Nat) := Id.run do
  let mut res := #[]
  for lvl in levels do
    let mut m : Std.HashMap (List Nat) Nat := {}
    for i in [0:lvl.size] do
      m := m.insert (lvl[i]!.toList) i
    res := res.push m
  return res

/-! ### Full analysis: f-vector, boundary ranks, Betti numbers, Euler -/

/-- All boundary ranks `[r₁, …, r_{maxDim}]` under prime `p`, plus the f-vector. -/
def rankVector (n : Nat) (p : Int) : Array Nat × Array Nat := Id.run do
  let nd := buildNerve n
  let maxDim := n - 1
  let levels := chainLevels nd maxDim
  let idx := buildChainIdx levels
  let mut fv : Array Nat := #[nd.V]
  for lvl in levels do fv := fv.push lvl.size
  let mut ranks : Array Nat := #[]
  if maxDim ≥ 1 then
    ranks := ranks.push (rankSparse p (d1cols nd))
  for k in [2:maxDim+1] do
    ranks := ranks.push (rankSparse p (dkCols nd levels[k-1]! idx[k-2]!))
  return (fv, ranks)

/-- Betti numbers from f-vector and boundary ranks: `b₀ = F₀−r₁`, `b_k = F_k − r_k − r_{k+1}`. -/
def bettiOf (fv ranks : Array Nat) : Array Nat := Id.run do
  let maxDim := fv.size - 1
  let r : Nat → Nat := fun k => if 1 ≤ k ∧ k ≤ ranks.size then ranks[k-1]! else 0
  let mut b : Array Nat := #[]
  for k in [0:maxDim+1] do
    b := b.push (fv[k]! - r k - r (k+1))
  return b

/-- Signed Euler characteristic `Σ (-1)^k F_k`. -/
def eulerFull (fv : Array Nat) : Int := Id.run do
  let mut s : Int := 0
  for k in [0:fv.size] do
    s := s + (if k % 2 == 0 then 1 else -1) * (fv[k]! : Int)
  return s

/-- Signed alternating Betti sum `Σ (-1)^k b_k` (must equal `eulerFull`). -/
def eulerBetti (b : Array Nat) : Int := Id.run do
  let mut s : Int := 0
  for k in [0:b.size] do
    s := s + (if k % 2 == 0 then 1 else -1) * (b[k]! : Int)
  return s

/-- One-line report for `n` under prime `p`. -/
def report (n : Nat) (p : Int) : String := Id.run do
  let (fv, ranks) := rankVector n p
  let b := bettiOf fv ranks
  let fvStr := String.intercalate " " ((List.range fv.size).map fun k => s!"F{k}={fv[k]!}")
  let bStr := String.intercalate " " ((List.range b.size).map fun k => s!"b{k}={b[k]!}")
  let rStr := String.intercalate " " ((List.range ranks.size).map fun k => s!"r{k+1}={ranks[k]!}")
  let chiGraph : Int := (fv[0]! : Int) - (if fv.size ≥ 2 then (fv[1]! : Int) else 0)
  s!"n={n}: {fvStr} | {rStr} | χ_graph(V-E)={chiGraph} χ={eulerFull fv} χ_betti={eulerBetti b} | {bStr}"

end NerveSeq

open NerveSeq
-- cross-check: array enumeration vs recurrence agree
#eval fVector 4        -- #[47, 1964, 5360, 3456]
#eval fVectorCount 4   -- must match
#eval fVectorCount 5

def p1 : Int := 2147483647    -- 2^31 - 1 (prime)
def p2 : Int := 1000000007    -- prime

-- n=3 cross-check against TerminalPi1 (rank ∂₁=10, rank ∂₂=68, b₁=2, b₂=4)
#eval report 1 p1
#eval report 2 p1
#eval report 3 p1
#eval report 3 p2
#eval report 4 p1
#eval report 4 p2
