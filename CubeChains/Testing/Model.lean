import Mathlib.Tactic

/-!
# A computable finite model of bi-pointed precubical sets, for property testing

This is a **standalone, fully computable** combinatorial surrogate for the
bi-pointed precubical sets `BPSet` of the main development, built so that
properties of the cube-chain category `Ch K` can be `#eval`/`native_decide`-tested
on small finite examples *before* anyone attempts to prove them.

Why a surrogate (and not the real `BPSet`/`Ch`)?  The main development lives in the
topos `PrecubicalSet = Boxᵒᵖ ⥤ Type`, where wedges are *generic pushouts*
(`Classical.choice`), so `serialWedge`, `Ch`, `Aut.liftToCh` are all
`noncomputable` and cannot be run.  We avoid them entirely: we model `Ch K`
**combinatorially**, exactly as Paliga–Ziemiański's Lemma 2.11 describes it under
the side conditions — objects are cube chains (lists of positive-dimensional cubes
from `init` to `final`), and `𝐚 ⟶ 𝐛` exists iff every cube of `𝐚` is a face of a
cube of `𝐛`.  (Internally this matches `equivWedgeCat : RefineObj ≌ ChainCat.Obj`.)

So testing needs **no** removal of the spurious `noncomputable`s: the surrogate
never touches a pushout.  Nothing here imports the main library.

A cell type `V` is any type with `DecidableEq`; the `FinBPSet` carries the explicit
list `cellList` of all cells (so enumeration stays computable — `Finset.toList` is
noncomputable).  Examples use named inductive types `deriving DecidableEq, Repr`.
-/

namespace CubeTest

universe u

/-- Membership of a list as a `Bool`. -/
def memB {V : Type u} [DecidableEq V] (a : V) (l : List V) : Bool :=
  l.any (fun b => decide (a = b))

/-- Association lookup keyed by a `DecidableEq` type (avoids `List.lookup`'s `BEq`). -/
def alook {V : Type u} {β : Type*} [DecidableEq V] (l : List (V × β)) (a : V) : Option β :=
  (l.find? (fun p => decide (p.1 = a))).map Prod.snd

/-- A finite bi-pointed precubical set on a cell type `V`.  `face ε i c` is the
`i`-th `ε`-face of `c` (`ε = false` source, `true` target), `none` when `i` is out
of range (`i ≥ dim c`).  `cellList` lists every cell once.  Well-formedness (the
precubical identities, dimension bookkeeping) is checked separately by
`wellFormed`. -/
structure FinBPSet (V : Type u) [DecidableEq V] where
  /-- Every cell, listed once. -/
  cellList : List V
  /-- The dimension of each cell. -/
  dim : V → ℕ
  /-- Face maps: `face ε i c` is the `(ε,i)`-face, `none` if `i ≥ dim c`. -/
  face : Bool → ℕ → V → Option V
  /-- The initial vertex (`dim = 0`). -/
  init : V
  /-- The final vertex (`dim = 0`). -/
  final : V

namespace FinBPSet

variable {V : Type u} [DecidableEq V] (K : FinBPSet V)

/-- All cells. -/
def cells : List V := K.cellList

/-- The positive-dimensional cells. -/
def posCells : List V := K.cells.filter (fun c => 0 < K.dim c)

/-- The maximum dimension present. -/
def maxDim : ℕ := (K.cells.map K.dim).foldl max 0

/-! ### Extreme vertices and faces -/

/-- The source extreme vertex `vertex₀ c`: fix every coordinate to `0` by iterating
the smallest source face `dim c` times. -/
def vertex0 (c : V) : V := (fun x => (K.face false 0 x).getD x)^[K.dim c] c

/-- The target extreme vertex `vertex₁ c`: fix every coordinate to `1`. -/
def vertex1 (c : V) : V := (fun x => (K.face true 0 x).getD x)^[K.dim c] c

/-- The immediate (codimension-1) faces of a cell. -/
def immFaces (c : V) : List V :=
  (List.range (K.dim c)).flatMap (fun i => [K.face false i c, K.face true i c].filterMap id)

/-- One round of closing a cell list under immediate faces. -/
def faceStep (acc : List V) : List V := (acc ++ acc.flatMap K.immFaces).dedup

/-- All iterated faces of a cell (closure under `face`), with fuel `#cells`. -/
def faceClosure (c : V) : List V := (K.faceStep)^[K.cells.length] [c]

/-- `x` is an iterated face of `y`. -/
def isFace (x y : V) : Bool := memB x (K.faceClosure y)

/-! ### Cube chains (objects of `Ch K`) -/

/-- Auxiliary enumeration: all cube chains from `v` to `final`, with `fuel`
bounding the length (chain length `≤ #cells`, since altitude is strictly
increasing). -/
def chainsAux (K : FinBPSet V) : ℕ → V → List (List V)
  | 0,        v => if v = K.final then [[]] else []
  | fuel + 1, v =>
      (if v = K.final then [([] : List V)] else []) ++
      (K.posCells.filter (fun c => decide (K.vertex0 c = v))).flatMap (fun c =>
        (chainsAux K fuel (K.vertex1 c)).map (fun tl => c :: tl))

/-- The objects of (the combinatorial model of) `Ch K`: all cube chains from
`init` to `final`, each presented as its list of cubes. -/
def chains : List (List V) := K.chainsAux (K.cells.length + 1) K.init

/-- The dimension sequence of a chain. -/
def dimSeq (cs : List V) : List ℕ := cs.map K.dim

/-- The refinement order (Lemma 2.11(c)): a morphism `a ⟶ b` exists iff every cube
of `a` is a face of a cube of `b`. -/
def chLe (a b : List V) : Bool := a.all (fun c => b.any (fun d => K.isFace c d))

/-! ### Side conditions (decidable checkers) -/

/-- **Well-formed**: `init`/`final` are vertices; `face ε i` is defined exactly for
`i < dim`, lowering dimension by one; and the precubical identity holds. -/
def wellFormed : Bool :=
  (decide (K.dim K.init = 0) && decide (K.dim K.final = 0)) &&
  K.cells.all (fun c =>
    (List.range (K.dim c)).all (fun i =>
      [false, true].all (fun ε =>
        match K.face ε i c with
        | some d => decide (K.dim d + 1 = K.dim c)
        | none   => false)) &&
    ((List.range (K.maxDim + 2)).filter (fun i => decide (K.dim c ≤ i))).all (fun i =>
      [false, true].all (fun ε => (K.face ε i c).isNone))) &&
  -- precubical identity: for i ≤ j, face ε i ∘ face η (j+1) = face η j ∘ face ε i
  K.cells.all (fun c =>
    (List.range (K.maxDim + 1)).all (fun i =>
      (List.range (K.maxDim + 1)).all (fun j =>
        if i ≤ j then
          [false, true].all (fun ε => [false, true].all (fun η =>
            decide (((K.face η (j + 1) c).bind (K.face ε i))
                  = ((K.face ε i c).bind (K.face η j)))))
        else true)))

/-- **Non-self-linked**: each cube's canonical map `□ⁿ ⟶ K` is injective, i.e. the
number of distinct `k`-faces of an `n`-cube `c` equals `C(n,k)·2^(n-k)`. -/
def nonSelfLinked : Bool :=
  K.cells.all (fun c =>
    (List.range (K.dim c + 1)).all (fun k =>
      decide (((K.faceClosure c).filter (fun x => decide (K.dim x = k))).dedup.length
        = Nat.choose (K.dim c) k * 2 ^ (K.dim c - k))))

/-- One Bellman–Ford-style relaxation of the altitude difference constraints
`alt (vertex₁ c) = alt (vertex₀ c) + dim c`. -/
def altStep (alt : List (V × ℤ)) : Option (List (V × ℤ)) :=
  K.posCells.foldl (fun acc? c =>
    acc?.bind (fun acc =>
      match alook acc (K.vertex0 c) with
      | none => some acc
      | some a =>
        let b := a + (K.dim c : ℤ)
        match alook acc (K.vertex1 c) with
        | none    => some ((K.vertex1 c, b) :: acc)
        | some b' => if b = b' then some acc else none)) (some alt)

/-- **Admits an altitude function**: the vertex difference constraints are
consistent (no contradictory directed cycle). -/
def admitsAltitude : Bool :=
  match (fun s => Option.bind s K.altStep)^[K.cells.length] (some [(K.init, (0 : ℤ))]) with
  | none     => false
  | some alt =>
    K.posCells.all (fun c =>
      match alook alt (K.vertex0 c), alook alt (K.vertex1 c) with
      | some a, some b => decide (b = a + (K.dim c : ℤ))
      | _, _ => false)

/-- The one-step `Reach` edges on cells (`face false i c ⤳ c`, `c ⤳ face true i c`). -/
def reachEdges : List (V × V) :=
  K.posCells.flatMap (fun c =>
    (List.range (K.dim c)).flatMap (fun i =>
      (match K.face false i c with | some d => [(d, c)] | none => []) ++
      (match K.face true i c with | some d => [(c, d)] | none => [])))

/-- Forward reachability closure of a start set along an edge list. -/
def reachClosure (edges : List (V × V)) (start : List V) : List V :=
  (fun acc => (acc ++ (edges.filter (fun e => memB e.1 acc)).map Prod.snd).dedup)^[K.cells.length]
    start

/-- **Accessible**: every cell is reachable from `init` and reaches `final`. -/
def accessible : Bool :=
  let fromInit := K.reachClosure K.reachEdges [K.init]
  let toFinal := K.reachClosure (K.reachEdges.map Prod.swap) [K.final]
  K.cells.all (fun c => memB c fromInit && memB c toFinal)

/-- All three side conditions assumed by the lowering conjecture, plus
well-formedness. -/
def validInput : Bool :=
  K.wellFormed && K.nonSelfLinked && K.admitsAltitude && K.accessible

end FinBPSet
end CubeTest
