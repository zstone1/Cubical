import CubeChains.Testing.Model

/-!
# Testing/Lowering

Computable enumeration of automorphisms, and the lowering-conjecture test.
For a finite `K : FinBPSet V` we enumerate, all combinatorially:

* `autK K` — the automorphisms of `K` (dimension-preserving, face-commuting
  bijections fixing `init`/`final`), via constraint-propagation backtracking;
* `opAutCh K` — the **orientation-preserving** automorphisms of `Ch K`, i.e. the
  order-automorphisms of the chain poset that preserve every dimension sequence;
* `liftIdx K σ` — the action of `Aut.liftToCh σ` on chains (post-compose `σ`).

`checkLowering K` then tests the conjecture
`lower_orientationPreserving`: every orientation-preserving automorphism of `Ch K`
is `liftToCh σ` for a **unique** `σ : Aut K`.  Concretely:

* **existence**  — every `Φ ∈ opAutCh K` lies in the image of `liftIdx`;
* **injective**  — distinct `σ` give distinct lifts (uniqueness);
* **soundness**  — every lift is itself an orientation-preserving auto (sanity).

**Layer:** Testing.  **Imports:** `Testing/Model`.
-/

namespace CubeTest
namespace FinBPSet

variable {V : Type} [DecidableEq V] (K : FinBPSet V)

/-! ### Automorphisms of `K` (constraint-propagation backtracking) -/

/-- Apply a partial/total assignment as a function (identity off its domain). -/
def applyAssign (assign : List (V × V)) (v : V) : V := (alook assign v).getD v

/-- Add one forced constraint `d ↦ t'` to `(assign, worklist)`, failing on a clash
with an existing assignment or a violation of injectivity. -/
def addCon (assign wl : List (V × V)) (dt : V × V) : Option (List (V × V) × List (V × V)) :=
  match alook assign dt.1 with
  | some v => if v = dt.2 then some (assign, wl) else none
  | none   => if memB dt.2 (assign.map Prod.snd) then none else some (dt :: assign, dt :: wl)

/-- Propagate face-commutation constraints from a worklist of decided pairs. -/
def propagate (K : FinBPSet V) : ℕ → List (V × V) → List (V × V) → Option (List (V × V))
  | 0,        assign, _        => some assign
  | _,        assign, []       => some assign
  | fuel + 1, assign, (x, y) :: wl =>
      let newcons := (List.range (K.dim x)).flatMap (fun i =>
        [false, true].filterMap (fun ε =>
          match K.face ε i x, K.face ε i y with
          | some d, some t' => some ((d, t') : V × V)
          | _, _ => none))
      match newcons.foldl (fun s dt => s.bind (fun p => addCon p.1 p.2 dt)) (some (assign, wl)) with
      | none => none
      | some (assign', wl') => propagate K fuel assign' wl'

/-- Cells sorted by dimension, descending (top cells first). -/
def cellsDimDesc : List V :=
  (List.range (K.maxDim + 1)).reverse.flatMap
    (fun d => K.cells.filter (fun c => decide (K.dim c = d)))

/-- Backtracking search: extend a partial automorphism over the remaining cells. -/
def extendAux (K : FinBPSet V) : ℕ → List (V × V) → List V → List (List (V × V))
  | _,        assign, []        => [assign]
  | 0,        _,      _         => []
  | fuel + 1, assign, c :: rest =>
      match alook assign c with
      | some _ => extendAux K fuel assign rest
      | none   =>
        let used := assign.map Prod.snd
        let cands := K.cells.filter (fun t => decide (K.dim t = K.dim c) && !memB t used)
        cands.flatMap (fun t =>
          match propagate K (K.cells.length + 1) ((c, t) :: assign) [(c, t)] with
          | none => []
          | some assign' => extendAux K fuel assign' rest)

/-- Canonical total table of an assignment (one entry per cell, in `cells` order). -/
def canonTable (assign : List (V × V)) : List (V × V) :=
  K.cells.map (fun v => (v, applyAssign assign v))

/-- All automorphisms of `K`, as canonical tables. -/
def autK : List (List (V × V)) :=
  ((extendAux K (K.cells.length + 1) [] K.cellsDimDesc).map K.canonTable).filter (fun t =>
    decide (alook t K.init = some K.init) && decide (alook t K.final = some K.final)) |>.dedup

/-! ### The lift, and automorphisms of `Ch K` -/

/-- The action of `Aut.liftToCh σ` on chains, as an index permutation:
`liftIdx σ` sends chain `i` to the index of `(chain i).map σ`. -/
def liftIdx (σ : List (V × V)) : List ℕ :=
  let chs := K.chains
  chs.map (fun cs => chs.findIdx (fun cs' => decide (cs' = cs.map (applyAssign σ))))

/-- Cartesian product: from a per-slot list of choices, all combinations. -/
def cart {α : Type} : List (List α) → List (List α)
  | []        => [[]]
  | xs :: rest => xs.flatMap (fun x => (cart rest).map (fun ys => x :: ys))

/-- The orientation-preserving automorphisms of `Ch K`, as index permutations:
order-automorphisms of the chain poset that permute each dimension-sequence class
among itself.

For efficiency the face-closures and the `M×M` order matrix are precomputed once
(otherwise `isFace`, a face-closure over all cells, is recomputed for every
candidate permutation — unusable already at `□³`). -/
def opAutCh : List (List ℕ) :=
  let chs := K.chains
  let M := chs.length
  let idxs := List.range M
  let chAt := fun i => chs.getD i []
  -- precompute: face-closure of every cell, and the order matrix `mat i j = chLe`.
  let clos := K.cells.map (fun c => (c, K.faceClosure c))
  let isF := fun x y => memB x ((alook clos y).getD [])
  let le := fun (a b : List V) => a.all (fun c => b.any (fun d => isF c d))
  let mat := (chs.map (fun a => chs.map (le a)))
  let leI := fun i j => (mat.getD i []).getD j false
  let dseqs := (idxs.map (fun i => K.dimSeq (chAt i))).dedup
  let groups := dseqs.map (fun ds => idxs.filter (fun i => decide (K.dimSeq (chAt i) = ds)))
  let combos := cart (groups.map (fun g => g.permutations))
  let perms := combos.map (fun combo =>
    let pairs := (groups.zip combo).flatMap (fun gp => gp.1.zip gp.2)
    idxs.map (fun i => (alook pairs i).getD i))
  perms.filter (fun perm =>
    idxs.all (fun i => idxs.all (fun j =>
      leI i j = leI (perm.getD i 0) (perm.getD j 0))))

/-! ### Connectivity of the chain poset, and of cube-fibers

The **coherence theorem** (`Examples.lean`): if every cube's *fiber* — the chains
containing it — is connected in the refinement poset, then every orientation-
preserving automorphism of `Ch K` induces a well-defined cube map (`coherentAll`).
The proof is the *cover lemma*: a single refinement that does not split a cube `c`
leaves `c`'s image under `F` unchanged, so the image is constant on each connected
component of the fiber.  The hypothesis is *fiber* (local) connectivity — strictly
stronger than `Ch K` being globally connected (`chConnected`); see `threeSquare`. -/

/-- Whether a list of chains is connected under comparability (`chLe` either way),
by flood-fill from the first. -/
def chainsConnected (objs : List (List V)) : Bool :=
  let n := objs.length
  let comp := fun a b => K.chLe a b || K.chLe b a
  if n ≤ 1 then true else
    let step := fun (reached : List ℕ) =>
      ((List.range n).filter (fun j =>
        memB j reached || reached.any (fun i => comp (objs.getD i []) (objs.getD j [])))).dedup
    decide (((List.range n).foldl (fun r _ => step r) [0]).dedup.length = n)

/-- `Ch K` is connected as a poset (one component). -/
def chConnected : Bool := K.chainsConnected K.chains

/-- Every cube's fiber (the chains through it) is connected — the hypothesis of the
coherence theorem `fiberConnected ⟹ coherentAll`. -/
def fiberConnected : Bool :=
  K.cells.all (fun c => K.chainsConnected (K.chains.filter (fun ch => memB c ch)))

/-! ### The test -/

/-- A diagnostic summary of the lowering test on `K`. -/
structure Report where
  /-- number of cells -/
  numCells : ℕ
  /-- number of chains (objects of `Ch K`) -/
  numChains : ℕ
  /-- number of automorphisms of `K` -/
  numAutK : ℕ
  /-- number of orientation-preserving automorphisms of `Ch K` -/
  numOPAutCh : ℕ
  /-- number of distinct lifts (image of `liftToCh`) -/
  numImage : ℕ
  /-- whether `K` satisfies well-formedness + the three side conditions -/
  validInput : Bool
  /-- every orientation-preserving auto of `Ch K` is realized by some `σ` -/
  existence : Bool
  /-- every lift is an orientation-preserving auto of `Ch K` (sanity) -/
  soundness : Bool
  /-- distinct `σ` give distinct lifts (uniqueness) -/
  injective : Bool
  deriving Repr

/-- Run the lowering test on `K`, producing a `Report`. -/
def report : Report :=
  let lifts := K.autK.map K.liftIdx
  let imgs := lifts.dedup
  let tgt := K.opAutCh
  { numCells := K.cells.length
    numChains := K.chains.length
    numAutK := K.autK.length
    numOPAutCh := tgt.length
    numImage := imgs.length
    validInput := K.validInput
    existence := tgt.all (fun Φ => memB Φ imgs)
    soundness := imgs.all (fun Φ => memB Φ tgt)
    injective := decide (lifts.length = imgs.length) }

/-- The headline boolean: the lowering conjecture holds for `K` (on valid input). -/
def checkLowering : Bool :=
  let r := K.report
  r.validInput && r.existence && r.soundness && r.injective

/-! ### Coherence of the induced cell map (the well-definedness crux)

For an orientation/altitude-preserving `F` of `Ch K` and a chain `p`, `F p` has the
same dimension sequence, so its cube at each altitude band corresponds to `p`'s.
This induces a candidate cube map `σ_F`.  The question: is `σ_F` **well-defined** —
if a cube `c` appears in two chains `p₁, p₂`, do `F p₁` and `F p₂` agree on the cube
at `c`'s altitude band? -/

/-- The altitude-aligned cube correspondence induced by an automorphism `F` of
`Ch K` (an index permutation): pairs `(c, d)` where `c` is a cube of a chain `p`
and `d` is the cube of `F p` at the same position (= altitude band). -/
def inducedPairs (F : List ℕ) : List (V × V) :=
  let chs := K.chains
  (List.range chs.length).flatMap (fun i =>
    (chs.getD i []).zip (chs.getD (F.getD i 0) []))

/-- The distinct images a cube `c` receives under `F` across all chains. -/
def imagesOf (F : List ℕ) (c : V) : List V :=
  ((K.inducedPairs F).filter (fun p => decide (p.1 = c))).map Prod.snd |>.dedup

/-- `F` induces a **coherent** cube map: every cube gets the same image across all
chains containing it (well-definedness of the reconstructed `σ`). -/
def coherentF (F : List ℕ) : Bool := K.cells.all (fun c => (K.imagesOf F c).length ≤ 1)

/-- A witness that `F` is incoherent: a cube with two different images
`(c, d₁, d₂)`. -/
def incoherenceWitness (F : List ℕ) : Option (V × V × V) :=
  (K.cells.filterMap (fun c =>
    match K.imagesOf F c with
    | d1 :: d2 :: _ => some (c, d1, d2)
    | _ => none)).head?

/-- **The refined question.** Do *all* orientation/altitude-preserving automorphisms
of `Ch K` induce coherent cube maps? -/
def coherentAll : Bool := K.opAutCh.all K.coherentF

/-- The first incoherent automorphism of `Ch K` together with a witness cube, if
any exists. -/
def firstIncoherence : Option (List ℕ × V × V × V) :=
  (K.opAutCh.filterMap (fun F =>
    (K.incoherenceWitness F).map (fun w => (F, w.1, w.2.1, w.2.2)))).head?

/-! ### The induced cell map `σ_F`, and the lowering criterion

`coherence` (above) is only *half* of lowering.  An orientation-preserving `F`
induces a candidate cell map `σ_F` on the cubes — and, extending across junction
vertices, on *all* cells.  `F = liftToCh σ` for some `σ ∈ Aut K` (i.e. `F` **lowers**)
iff that `σ_F` is (i) well-defined (`coherentFullF`) **and** (ii) **precubical** —
commuting with the face maps (`precubicalF`).  Coherence gives (i); (ii) is the
independent *naturality* obstruction — for `□²`/`□³` the induced `σ_F` is an
**axis permutation**, well-defined but not precubical, so those `F` do not lower
(`lowersBySigma` is `false`).  Compare `Examples.lean`, `liftToCh_map_eq`. -/

/-- The induced cell correspondence **including junction vertices**: at matching
positions, the cubes of `p` and `F p`, together with the source vertex of each cube
(and the final vertex).  This is `inducedPairs` extended so `σ_F` is defined on
vertices too, which is needed to test precubicality. -/
def inducedPairsV (F : List ℕ) : List (V × V) :=
  let chs := K.chains
  (K.final, K.final) ::
  (List.range chs.length).flatMap (fun i =>
    let p := chs.getD i []
    let q := chs.getD (F.getD i 0) []
    (p.zip q).flatMap (fun cd => [cd, (K.vertex0 cd.1, K.vertex0 cd.2)]))

/-- The distinct images a cell `c` receives under `F` across all chains (cubes and
vertices). -/
def imagesOfV (F : List ℕ) (c : V) : List V :=
  ((K.inducedPairsV F).filter (fun p => decide (p.1 = c))).map Prod.snd |>.dedup

/-- `F` induces a **well-defined** cell map on *all* cells (cubes and vertices). -/
def coherentFullF (F : List ℕ) : Bool := K.cells.all (fun c => (K.imagesOfV F c).length ≤ 1)

/-- The induced cell map `σ_F` (identity off its domain). -/
def inducedMap (F : List ℕ) (c : V) : V := ((K.imagesOfV F c).head?).getD c

/-- `σ_F` is **precubical**: it commutes with every face map. -/
def precubicalF (F : List ℕ) : Bool :=
  K.cells.all (fun c =>
    (List.range (K.dim c)).all (fun i =>
      [false, true].all (fun ε =>
        match K.face ε i c with
        | some d => decide (some (K.inducedMap F d) = K.face ε i (K.inducedMap F c))
        | none   => true)))

/-- **The lowering criterion of Claim 1.**  `F` lowers (`= liftToCh σ_F`) iff its
induced cell map is well-defined *and* precubical. -/
def lowersBySigma (F : List ℕ) : Bool := K.coherentFullF F && K.precubicalF F

end FinBPSet
end CubeTest
