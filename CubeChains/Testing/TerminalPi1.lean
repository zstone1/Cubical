import CubeChains.Testing.TerminalBraids
import Mathlib.Data.Rat.Defs

/-!
# Testing/TerminalPi1 — is the vertex group of `ConcGrpd Zbp` at `RZ` equal to `Bₙ`?

`concBraidHomGen (RZ n)` is known **surjective** onto `Braid n` (`TerminalSurj`).  This file tests
**injectivity** computationally: it computes the fundamental group / `H₁` rank of the `n`-event
stratum of `ConcCat Zbp` at the run basepoint `RZ`.

Two independent computations:

* **Part 1** — from the *real* `braidGrading`: `allBraids` of the single `[k]`-bead terminal
  execution has `k!` distinct entries, so there are exactly `k!` distinct `ConcCat Zbp` morphisms
  `[k]-bead ⟶ RZ` (the multiplicity crux).

* **Part 2** — a faithful finite combinatorial model of the stratum (objects = compositions of `n`
  with a chamber per bead; morphisms = per-bead ordered-set-partition refinements, target line
  forced by restriction), and its `H₁` rank via rational matrix rank of the nerve boundary maps.
  `Bₙ^ab = ℤ` (rank 1), so `rank H₁ > 1 ⟹` the vertex group is strictly bigger than `Bₙ`.

Not built by `lake build CubeChains`.
-/

set_option linter.style.nativeDecide false

open CubeChains CubeChains.BraidTest CategoryTheory Opposite BPSet

namespace TerminalPi1

/-! ## Part 1 — the morphism multiplicity `[k]-bead ⟶ RZ`, from real `braidGrading`

`execZk` is the single-`[k]`-bead terminal execution (`= bZ k` up to defeq); `allBraids execZk`
is `braidGrading`'s value on every one of its lines, i.e. on every morphism `execZk ⟶ RZ`.  The
entries being `Nodup` means those `k!` morphisms are pairwise distinct in `ConcGrpd Zbp`. -/

def cZ2 : Ch Zbp := ⟨[2], ⟨toZ _, rfl, rfl⟩⟩
def execZ2 : ConcCat Zbp := ⟨op cZ2, stdLine _⟩
def cZ3 : Ch Zbp := ⟨[3], ⟨toZ _, rfl, rfl⟩⟩
def execZ3 : ConcCat Zbp := ⟨op cZ3, stdLine _⟩

#eval (allBraids execZ2).length   -- 2   : two morphisms [2]-bead ⟶ RZ
#eval allBraids execZ2            -- [[], [1]]  = {id, σ₁}
#eval (allBraids execZ3).length   -- 6   : six morphisms [3]-bead ⟶ RZ
#eval allBraids execZ3            -- the 6 permutation braids of B₃

/-- **Two distinct morphisms `[2]-bead ⟶ RZ`.** -/
example : (allBraids execZ2).Nodup := by native_decide
/-- **Six distinct morphisms `[3]-bead ⟶ RZ`.** -/
example : (allBraids execZ3).Nodup := by native_decide

/-! ## Part 2 — a finite combinatorial model of the `n`-event stratum

An object of the `n`-event stratum of `ConcCat Zbp` is a chain of `Zbp` with `n` events (a
composition `c` of `n`, since `Zbp` is terminal so the chain is pinned by its dims) together with a
**line**: a chamber (strict total order = flip order) of each bead's directions.  A morphism
`x ⟶ y` is a refinement (coarse→fine): for each coarse bead `i` an ordered set partition of its
`c_i` directions into the consecutive fine beads, with the fine line forced by restricting the
coarse chamber (`Chamber.restrict` along the block's increasing enumeration, `linesRestrict`). -/

/-- An object: `(dims, chambers)` — the composition and one flip-order (a permutation of
`[0,…,d-1]`) per bead. -/
abbrev Obj := List ℕ × List (List ℕ)

/-- A morphism's block data: per coarse bead, an ordered list of blocks (each an increasing
direction-subset). -/
abbrev Part := List (List (List ℕ))

/-- Cartesian product of a list of choice-lists. -/
def cartProd {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (cartProd rest).map (x :: ·)

/-- All compositions of `n` (ordered lists of positive ints summing to `n`). -/
def comps : ℕ → List (List ℕ)
  | 0 => [[]]
  | (m + 1) => (List.range (m + 1)).flatMap fun i =>
      (comps (m - i)).map fun rest => (i + 1) :: rest
  termination_by n => n
  decreasing_by simp_wf

/-- All ordered set partitions of a (sorted) element list, fuel-driven (`fuel = length`). -/
def ospFuel : ℕ → List ℕ → List (List (List ℕ))
  | _, [] => [[]]
  | 0, _ => [[]]
  | (f + 1), s =>
      (s.sublists.filter fun b => !b.isEmpty).flatMap fun b =>
        (ospFuel f (s.filter fun x => !b.contains x)).map (b :: ·)

/-- All ordered set partitions of `[0,…,d-1]`. -/
def osp (d : ℕ) : List (List (List ℕ)) := ospFuel d (List.range d)

/-- All `n`-event objects: compositions × a chamber (flip-order permutation) per bead. -/
def objectsOf (n : ℕ) : List Obj :=
  (comps n).flatMap fun c =>
    (cartProd (c.map fun d => (List.range d).permutations)).map fun chs => (c, chs)

/-- Restrict a coarse flip-order to a block: keep the block's directions in coarse order, relabel to
local indices (`linesRestrict` via `faceEmb`, the block's increasing enumeration). -/
def restrictChamber (coarseOrd block : List ℕ) : List ℕ :=
  (coarseOrd.filter fun x => block.contains x).map fun x => block.findIdx (· == x)

/-- Apply a refinement's block data to an object, computing the fine (target) object. -/
def applyMor (x : Obj) (P : Part) : Obj :=
  let per := (x.2.zip P).map fun cp =>
    (cp.2.map List.length, cp.2.map fun b => restrictChamber cp.1 b)
  ((per.map Prod.fst).flatten, (per.map Prod.snd).flatten)

/-- Every refinement out of `x`: a choice of ordered set partition per coarse bead. -/
def allMorParts (x : Obj) : List Part :=
  cartProd (x.1.map fun d => osp d)

/-- Non-identity morphisms out of `x`, as `(block data, target)`. -/
def morsOf (x : Obj) : List (Part × Obj) :=
  (allMorParts x).filterMap fun P =>
    let y := applyMor x P
    if y = x then none else some (P, y)

/-- All edges of the stratum quiver: `(source, block data, target)`. -/
def edgesOf (n : ℕ) : List (Obj × Part × Obj) :=
  (objectsOf n).flatMap fun x => (morsOf x).map fun py => (x, py.1, py.2)

/-- Regroup a flat list into chunks of the given sizes. -/
def regroup {α : Type} : List ℕ → List α → List (List α)
  | [], _ => []
  | (k :: ks), xs => xs.take k :: regroup ks (xs.drop k)

/-- Compose block data: `P` refines `x`'s coarse beads, `Q` refines the fine beads `P` produced;
the result refines `x`'s coarse beads directly (`blockFace`/`faceEmb` composition). -/
def compParts (P Q : Part) : Part :=
  let Qg := regroup (P.map List.length) Q
  (P.zip Qg).map fun pr =>
    (pr.1.zip pr.2).flatMap fun br =>
      br.2.map fun sub => sub.map fun j => br.1.getD j 0

/-- Index of the edge `(x, P, ·)` in the edge list. -/
def edgeIdx (edges : List (Obj × Part × Obj)) (x : Obj) (P : Part) : Option ℕ :=
  edges.findIdx? fun e => decide (e.1 = x ∧ e.2.1 = P)

/-- The 2-cells (composable pairs of non-identity morphisms) as `(idx f, idx g, idx (g∘f))`. -/
def twoCells (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  let edges := edgesOf n
  let earr := edges.toArray
  let E := earr.size
  (List.range E).flatMap fun i =>
    let f := earr[i]!
    (List.range E).filterMap fun j =>
      let g := earr[j]!
      if g.1 = f.2.2 then
        match edgeIdx edges f.1 (compParts f.2.1 g.2.1) with
        | some k => some (i, j, k)
        | none => none
      else none

/-! ### Rational matrix rank (Gaussian elimination) -/

/-- Rank over `ℚ` of a matrix given as its list of rows. -/
partial def rankRows : List (List ℚ) → ℕ
  | [] => 0
  | r :: rs =>
    match r.findIdx? (· ≠ 0) with
    | none => rankRows rs
    | some p =>
      let piv := r.getD p 0
      let rs' := rs.map fun row =>
        let c := row.getD p 0
        if c = 0 then row else (row.zip r).map fun ab => ab.1 - (c / piv) * ab.2
      1 + rankRows rs'

-- sanity checks on `rankRows`
#eval rankRows [[1, 0], [0, 1], [1, 1]]   -- 2
#eval rankRows [[1, 2], [2, 4]]           -- 1
#eval rankRows [[0, 0], [0, 0]]           -- 0

/-- `∂₁ : C₁ → C₀`, rows = vertices, cols = edges; column of edge `x⟶y` is `[y] - [x]`. -/
def d1rows (n : ℕ) : List (List ℚ) :=
  let objs := objectsOf n
  let edges := edgesOf n
  objs.map fun v => edges.map fun e =>
    (if e.2.2 = v then (1 : ℚ) else 0) - (if e.1 = v then 1 else 0)

/-- `∂₂ : C₂ → C₁`, rows = 2-cells, cols = edges; row of `(f,g)` is `[f] + [g] - [g∘f]`. -/
def d2rows (n : ℕ) : List (List ℚ) :=
  let E := (edgesOf n).length
  (twoCells n).map fun t => (List.range E).map fun e =>
    (if e = t.1 then (1 : ℚ) else 0) + (if e = t.2.1 then 1 else 0) - (if e = t.2.2 then 1 else 0)

/-- `rank H₁ = E − rank ∂₁ − rank ∂₂` (`im ∂₂ ⊆ ker ∂₁`). -/
def h1rank (n : ℕ) : ℕ :=
  (edgesOf n).length - rankRows (d1rows n) - rankRows (d2rows n)

/-- Number of connected components `= V − rank ∂₁` (should be 1: the stratum is connected). -/
def components (n : ℕ) : ℕ := (objectsOf n).length - rankRows (d1rows n)

/-- Composable pairs of non-identity morphisms, ignoring the composite lookup — a guard that every
`g∘f` was actually found among the edges (`= (twoCells n).length` iff no composite was dropped). -/
def composablePairs (n : ℕ) : ℕ :=
  let edges := edgesOf n
  (edges.map fun f => (edges.filter fun g => decide (g.1 = f.2.2)).length).sum

/-- Transpose of `∂₂` (rows = edges).  `rankRows` of it must match `rankRows (d2rows n)`. -/
def d2cols (n : ℕ) : List (List ℚ) :=
  let tcs := twoCells n
  (List.range (edgesOf n).length).map fun e => tcs.map fun t =>
    (if e = t.1 then (1 : ℚ) else 0) + (if e = t.2.1 then 1 else 0) - (if e = t.2.2 then 1 else 0)

/-! ### The single-`[n]`-bead object and the run, in the model -/

/-- The coarse `[n]`-bead object with the natural chamber. -/
def beadObj (n : ℕ) : Obj := ([n], [List.range n])
/-- The run object `RZ`: `n` unit beads, trivial chambers. -/
def runObj (n : ℕ) : Obj := (List.replicate n 1, List.replicate n [0])

/-- Model multiplicity of `[n]-bead ⟶ RZ` — matches the real `k!` from Part 1. -/
def beadToRun (n : ℕ) : ℕ := ((morsOf (beadObj n)).filter fun py => py.2 = runObj n).length

/-! ### Emitting the graph `ConcGrpd(Zbp) | n-event stratum`

Each node is a real `ConcCat Zbp` execution — a chain (pinned by its dims, `chZbp_ext`) with a
chamber (flip order `<a b c>`) per bead.  Each arrow is a real refinement.  The repo proves
(`bZ_mem_pathAutGenM`) the vertex group at the basepoint is generated by exactly one loop per arrow
of this graph, so this graph *is* `ConcGrpd Zbp` on the stratum. -/

/-- A chamber (flip order) as `<a b c>`. -/
def showCh (ord : List ℕ) : String := "<" ++ String.join (ord.map toString) ++ ">"

/-- An execution `[d₁|d₂|…]<line₁><line₂>…`. -/
def showObj (o : Obj) : String :=
  "[" ++ String.intercalate "|" (o.1.map toString) ++ "]" ++ String.join (o.2.map showCh)

/-- The object list, one line each, flagging `RZ` and the coarse `[n]`-beads. -/
def objectLines (n : ℕ) : String :=
  let objs := objectsOf n
  String.intercalate "\n" ((List.range objs.length).map fun i =>
    let o := objs[i]!
    let tag := if o = runObj n then "   <- RZ (run basepoint, the sink)"
      else if o.1.length = 1 then "   (coarse [" ++ toString n ++ "]-bead)" else ""
    s!"  {i}: {showObj o}{tag}")

/-- The arrows, grouped by (source,target) with multiplicity. -/
def adjLines (n : ℕ) : String :=
  let objs := objectsOf n
  let edges := edgesOf n
  let V := objs.length
  String.intercalate "\n" ((List.range V).flatMap fun i =>
    (List.range V).filterMap fun j =>
      let si := objs[i]!
      let sj := objs[j]!
      let m := (edges.filter fun e => e.1 == si && e.2.2 == sj).length
      if m = 0 then none
      else some s!"  {showObj si}  --({m})-->  {showObj sj}")

/-- The whole graph as a string. -/
def graphString (n : ℕ) : String :=
  let objs := objectsOf n
  let edges := edgesOf n
  s!"=== ConcGrpd(Zbp) : {n}-event stratum (the finite graph) ===\n\n"
    ++ s!"Objects  (V = {objs.length}):\n" ++ objectLines n ++ "\n\n"
    ++ s!"Arrows  (E = {edges.length}), by (source --(mult)--> target):\n" ++ adjLines n ++ "\n\n"
    ++ s!"triangles (2-cells) = {(twoCells n).length},  components = {components n},  "
    ++ s!"rank ∂₁ = {rankRows (d1rows n)},  rank ∂₂ = {rankRows (d2rows n)}\n"
    ++ s!"==> vertex group at RZ:  H₁ rank = {h1rank n}   (B{n}^ab = ℤ has rank 1)\n"

/-! ### Every arrow to RZ is a real `seqMor`: grounding the graph in `Zbp` for *every* shape

`allBraids (execShape d)` is the real `braidGrading` of every sequentialization of the standard-line
execution of shape `d` — i.e. of every real `ConcCat Zbp` arrow `(shape d) ⟶ RZ`.  Its length must
equal the model's arrow-count `shape d → RZ` (`= ∏ dᵢ!`). -/

/-- The standard-line execution of a given shape, as a real `ConcCat Zbp` object. -/
def execShape (dims : List ℕ+) : ConcCat Zbp := ⟨op ⟨dims, ⟨toZ _, rfl, rfl⟩⟩, stdLine _⟩

/-! ## The computation

`n = 2`: -/

#eval (objectsOf 2).length     -- 3   objects
#eval (edgesOf 2).length       -- 4   edges
#eval beadToRun 2              -- 2   morphisms [2]-bead ⟶ RZ  (= 2! ; matches Part 1)
#eval (twoCells 2).length      -- 0   two-cells
#eval components 2             -- 1   (connected)
#eval rankRows (d1rows 2)      -- 2   = V - 1
#eval h1rank 2                 -- 2   rank H₁  →  > 1  ⟹ vertex group ⊋ B₂

/-! `n = 3`: -/

#eval (objectsOf 3).length     -- 11  objects
#eval (edgesOf 3).length       -- 80  edges
#eval beadToRun 3              -- 6   morphisms [3]-bead ⟶ RZ  (= 3! ; matches Part 1)
#eval (twoCells 3).length      -- 72  two-cells
#eval components 3             -- 1   (connected)
#eval rankRows (d1rows 3)      -- 10  = V - 1
#eval rankRows (d2rows 3)      -- rank ∂₂
#eval h1rank 3                 -- rank H₁ at RZ

-- guards: every `g∘f` was found among the edges, and `rankRows` is transpose-consistent
#eval composablePairs 3        -- 72  = (twoCells 3).length  ⟹ no composite dropped
#eval decide (composablePairs 3 = (twoCells 3).length)   -- true
#eval rankRows (d2cols 3)      -- 68  = rankRows (d2rows 3)  ⟹ rank routine is consistent

/-! The objects `([n], nat)` and `([n], rev)` are genuinely distinct executions — the crux of the
hand-count.  For `n = 2`: -/

#eval (([2], [[0, 1]]) : Obj) = (([2], [[1, 0]]) : Obj)   -- false  : nat ≠ rev
#eval ((objectsOf 2).filter fun o => o.1 = [2]).length     -- 2  : two [2]-bead objects
#eval ((objectsOf 3).filter fun o => o.1 = [3]).length     -- 6  : six [3]-bead objects

/-! ## Grounding in `Zbp`: every arrow to RZ is a real `seqMor`, for every shape

The model's arrow-count `shape → RZ` equals the number of real `seqMor` sequentializations
(`= |allBraids (execShape shape)|`) for each of the shapes present in the 3-event graph. -/

#eval (allBraids (execShape [3])).length      -- 6  : real arrows [3]<…>   ⟶ RZ
#eval ((morsOf (([3], [[0, 1, 2]]) : Obj)).filter fun p => p.2 = runObj 3).length     -- 6
#eval (allBraids (execShape [2, 1])).length   -- 2  : real arrows [2|1]<…> ⟶ RZ
#eval ((morsOf (([2, 1], [[0, 1], [0]]) : Obj)).filter fun p => p.2 = runObj 3).length -- 2
#eval (allBraids (execShape [1, 2])).length   -- 2  : real arrows [1|2]<…> ⟶ RZ
#eval ((morsOf (([1, 2], [[0], [0, 1]]) : Obj)).filter fun p => p.2 = runObj 3).length -- 2

/-! ## Emit the graph -/

#eval IO.println (graphString 2)
#eval IO.println (graphString 3)

end TerminalPi1
