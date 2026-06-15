import CubeChains.Testing.Model

/-!
# Computable enumeration of automorphisms, and the lowering test

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
among itself. -/
def opAutCh : List (List ℕ) :=
  let chs := K.chains
  let M := chs.length
  let idxs := List.range M
  let chAt := fun i => chs.getD i []
  let dseqs := (idxs.map (fun i => K.dimSeq (chAt i))).dedup
  let groups := dseqs.map (fun ds => idxs.filter (fun i => decide (K.dimSeq (chAt i) = ds)))
  let combos := cart (groups.map (fun g => g.permutations))
  let perms := combos.map (fun combo =>
    let pairs := (groups.zip combo).flatMap (fun gp => gp.1.zip gp.2)
    idxs.map (fun i => (alook pairs i).getD i))
  perms.filter (fun perm =>
    idxs.all (fun i => idxs.all (fun j =>
      K.chLe (chAt i) (chAt j) = K.chLe (chAt (perm.getD i 0)) (chAt (perm.getD j 0)))))

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

end FinBPSet
end CubeTest
