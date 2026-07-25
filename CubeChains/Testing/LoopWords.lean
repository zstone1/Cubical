import CubeChains.Testing.Pi1

/-!
# Testing/LoopWords — the Artin braid word of each generating loop of `Ch⋆(∂□³)`

The graph has `E − V + 1 = 7` independent loops.  Each edge carries a permutation (`permShadow`,
proven `= ConcPos`'s crossing map); its positive Artin lift is the bubble-sort word.  A spanning tree
gives one fundamental cycle per non-tree edge, whose braid word is the product of the edge words
around it (inverse on backward tree edges).  The seven words are the generators of the concurrency
braid group, ready for GAP / manual inspection.

Everything is computed with `ℕ`-encoded nodes/edges + `Multiset.sort` (no noncomputable `toList`).

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain StdCube

/-! ## Permutation shadow → positive Artin word (bubble sort) -/

def firstInv : List ℕ → Option ℕ
  | a :: b :: rest => if b < a then some 0 else (firstInv (b :: rest)).map (· + 1)
  | _ => none

def swapAt : ℕ → List ℕ → List ℕ
  | 0, a :: b :: rest => b :: a :: rest
  | j + 1, a :: rest => a :: swapAt j rest
  | _, l => l

/-- The positive Artin word of a permutation given by its image list (`σ i = l[i]`): bubble-sort it to
the identity, recording each adjacent swap `(j, j+1)` as the generator `σ_{j+1}`. -/
def bubbleArtin : ℕ → List ℕ → List ℤ
  | 0, _ => []
  | fuel + 1, l =>
    match firstInv l with
    | none => []
    | some j => ((j : ℤ) + 1) :: bubbleArtin fuel (swapAt j l)

/-- Inverse of a braid word: reverse and negate. -/
def invWord (w : List ℤ) : List ℤ := (w.map fun x => -x).reverse

/-! ## `ℕ` encodings (so `Multiset.sort` yields computable lists) -/

def zToNat (x : ℤ) : ℕ := if 0 ≤ x then 2 * x.toNat else 2 * (-x).toNat - 1
def natToZ (m : ℕ) : ℤ := if m % 2 = 0 then (m / 2 : ℤ) else -(((m + 1) / 2 : ℕ) : ℤ)

def encNats : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.pair x (encNats xs) + 1

def decNats : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _, 0 => []
  | fuel + 1, m + 1 => (Nat.unpair m).1 :: decNats fuel (Nat.unpair m).2

def encWord (w : List ℤ) : ℕ := encNats (w.map zToNat)
def decWord (fuel c : ℕ) : List ℤ := (decNats fuel c).map natToZ

def encLL (ll : List (List ℕ)) : ℕ := encNats (ll.map encNats)
def encLLL (lll : List (List (List ℕ))) : ℕ := encNats (lll.map encLL)

/-- An injective `ℕ`-code for an execution's node key. -/
def encNkey (k : NKey) : ℕ := Nat.pair (encLL k.1) (encLLL k.2)

def encEdge (s t : ℕ) (w : List ℤ) : ℕ := Nat.pair (Nat.pair s t) (encWord w)
def decEdge (fuel c : ℕ) : ℕ × ℕ × List ℤ :=
  ((Nat.unpair (Nat.unpair c).1).1, (Nat.unpair (Nat.unpair c).1).2, decWord fuel (Nat.unpair c).2)

/-! ## The keyed graph, as computable lists (parameterized over the node/edge multisets) -/

/-- Sorted node codes. -/
def nodeCodesOf (n : ℕ) (nodes : Multiset (Exec n)) : List ℕ :=
  ((nodes.map fun e => encNkey (nkey n e)).dedup).sort (· ≤ ·)

/-- Sorted, non-identity directed edge codes (source ≠ target), carrying the bubble-sort word. -/
def edgeCodesOf (n : ℕ) (edges : Multiset (Exec n × Exec n × List ℕ)) : List ℕ :=
  ((edges.map fun t =>
      encEdge (encNkey (nkey n t.1)) (encNkey (nkey n t.2.1))
        (bubbleArtin (t.2.2.length * t.2.2.length + 1) t.2.2)).filter
    fun c => (Nat.unpair (Nat.unpair c).1).1 ≠ (Nat.unpair (Nat.unpair c).1).2).dedup.sort (· ≤ ·)

/-- All executions of `□n` (unfiltered), and all their refinement edges — the full graph. -/
def allExecNodes (n : ℕ) : Multiset (Exec n) := (Finset.univ : Finset (Exec n)).val
def allExecEdges (n : ℕ) : Multiset (Exec n × Exec n × List ℕ) :=
  (allExecNodes n).bind fun e => (outEdges e).map fun t => (e, t.1, t.2)

/-! ## Spanning tree (BFS) and the loop words -/

def symEdges (edges : List (ℕ × ℕ × List ℤ)) : List (ℕ × ℕ × List ℤ) :=
  edges ++ edges.map fun e => (e.2.1, e.1, invWord e.2.2)

/-- Expand the BFS frontier at `v`, recording parent pointers `(child, parent, word)`. -/
def bfsExpand (E : List (ℕ × ℕ × List ℤ)) (v : ℕ)
    (st : List ℕ × List (ℕ × ℕ × List ℤ) × List ℕ) : List ℕ × List (ℕ × ℕ × List ℤ) × List ℕ :=
  (E.filter fun e => e.1 = v).foldl
    (fun a e =>
      if a.1.elem e.2.1 then a
      else (e.2.1 :: a.1, (e.2.1, v, e.2.2) :: a.2.1, e.2.1 :: a.2.2)) st

def bfsLoop (E : List (ℕ × ℕ × List ℤ)) :
    ℕ → List ℕ × List (ℕ × ℕ × List ℤ) × List ℕ → List ℕ × List (ℕ × ℕ × List ℤ)
  | 0, st => (st.1, st.2.1)
  | fuel + 1, st =>
    match st.2.2 with
    | [] => (st.1, st.2.1)
    | frontier =>
      let next := frontier.foldl (fun a v => bfsExpand E v a) (st.1, st.2.1, [])
      bfsLoop E fuel next

/-- The braid word along the tree from the root to `v`. -/
def rootPath (par : List (ℕ × ℕ × List ℤ)) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | fuel + 1, v =>
    match par.find? fun e => e.1 = v with
    | none => []
    | some e => rootPath par fuel e.2.1 ++ e.2.2

/-- `{a,b}` is an edge of the spanning tree. -/
def isTreeEdge (par : List (ℕ × ℕ × List ℤ)) (a b : ℕ) : Bool :=
  (par.any fun e => e.1 = b && e.2.1 = a) || (par.any fun e => e.1 = a && e.2.1 = b)

/-- The loop braid words of a graph given by its node/edge code lists. -/
def loopWordsFrom (nc ec : List ℕ) : List (List ℤ) :=
  let V := nc.length
  let edges : List (ℕ × ℕ × List ℤ) := ec.map (decEdge 64)
  let root : ℕ := nc.headD 0
  let par := (bfsLoop (symEdges edges) (V + 1) ([root], [], [root])).2
  (edges.filter fun e => !(isTreeEdge par e.1 e.2.1)).map fun e =>
    rootPath par (V + 1) e.1 ++ e.2.2 ++ invWord (rootPath par (V + 1) e.2.1)

/-- The loop braid words of the boundary graph `Ch⋆(∂□n)`. -/
def loopWords (n : ℕ) : List (List ℤ) :=
  loopWordsFrom (nodeCodesOf n (bdryNodes n)) (edgeCodesOf n (bdryEdges n))

/-- The loop braid words of the full graph `Ch⋆(□n)` (with the top cell) — the theorem's `Pₙ`. -/
def loopWordsFull (n : ℕ) : List (List ℤ) :=
  loopWordsFrom (nodeCodesOf n (allExecNodes n)) (edgeCodesOf n (allExecEdges n))
