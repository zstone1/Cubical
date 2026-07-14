import CubeChains.Testing.Model

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false
-- Prose in docstrings occasionally runs long; not code.
set_option linter.style.longLine false

/-!
# Testing/EventNamingCounterexample — the "trinity" refutes the event-naming lemma

This file **machine-refutes**, via the computable `FinBPSet` harness of `Model.lean`, the claim

> `NonSelfLinked K ∧ AdmitsAltitude K ⟹ HasGlobalEventNaming K`

(the `EventNamingGoal` of `CubeChains/Events/EventNaming.lean`).  The witness is a small
bi-pointed precubical set `T`, the **trinity**: three directed lines from `a` to `d`

    ℓ_b : a →ab→ b →bd→ d      ℓ_c : a →ac→ c →cd→ d      ℓ_m : a →am→ m →md→ d

with a filling square between *each* pair of lines — `Q` between `ℓ_b,ℓ_c`, `t1` between
`ℓ_b,ℓ_m`, `t2` between `ℓ_c,ℓ_m`.  `T` is non-self-linked and altitude-graded, yet the event
naming folds: the two distinct events (`ab`, `bd`) of the single line `ℓ_b` receive the *same*
canonical name, so `EventFiberInjective` (hence `HasGlobalEventNaming`) fails.

## Why parallelism = the real `eventMap` fold (the thing this file computes)

The `EventNaming.lean` machinery (`EventObj`, `eventMap`, `EventRel`, `EventFiberInjective`) works
like this.  A cube chain `a`'s **events** (`EventObj a`) are the pairs `(bead i, direction δ)`.  A
refinement `f : a ⟶ b` (`a` finer) carries each fine event to the coarse event it sits inside via
`eventMap` — the same `blockIdx`/`blockFace`/`faceEmb` data as `linesRestrict`.  `EventRel`
identifies an event with its `eventMap`-image; the canonical naming is the quotient by `EventRel`,
and the whole lemma reduces (`hasGlobalEventNaming_iff`) to: *this quotient is injective on each
chain's events* (`EventFiberInjective`).

Here is the one-step correspondence this file exploits.  Let `s` be a **square** whose corners run
`a → d = init → final`; then the single-bead chain `⟨s⟩` is a genuine `init → final` chain, and `s`
has exactly two maximal staircase refinements, one down each pair of opposite edges.  A bead `e`
that is a face of `s` refines into `⟨s⟩` occupying the *direction of `s` that `e` runs along*.  Two
edges run along the **same** direction of `s` — hence get the **same** name through `⟨s⟩` — exactly
when they are *opposite* faces `{face false i s, face true i s}` of `s` (both fixing coordinate `i`,
so both free in the other coordinate).  So:

* **one parallelism step** `e ∥ e'` (`{e,e'} = {face false i s, face true i s}` for some square `s`)
  **= one `EventRel` identification** of the `e`-event with the `e'`-event, routed through `⟨s⟩`.

Therefore the transitive closure `parClosure` of `∥` on the edges is a *sound shadow* of the
`EventRel`-fold on events (every `parClosure` step is a genuine `EventRel` step).  In the trinity
the closure collapses **all six edges into one class** — in particular

    ab  ∥  cd   (opposite in Q)      cd  ∥  am   (opposite in t2)      am  ∥  bd   (opposite in t1)

so `ab ~ bd`, and the two events of the honest chain `[ab, bd]` (`a → b → d`) are folded together:
`EventFiberInjective T` fails, and with it `HasGlobalEventNaming T`.  This is a genuine *monodromy*:
transporting a "direction" around the three squares turns the `ab`-direction into the `bd`-direction,
which are *perpendicular* inside `Q`.

## Control

The standard square `□²` (here `ctrl`) is the sanity guard: its two directions stay in **separate**
`parClosure` classes (`{e_0,e_1}` and `{e0_,e1_}`), so a single line of `□²` keeps its two events
distinct — no fold.  The check is discriminating: the trinity folds, the square does not.

**Layer:** Testing (decoupled — not built by `lake build CubeChains`).
**Imports:** `Testing.Model` only.  **Build:** `lake build CubeChains.Testing.EventNamingCounterexample`.
-/

namespace CubeTest
namespace EventNamingCounterexample

open FinBPSet

/-! ## The trinity `T` -/

/-- The 14 cells of the trinity: vertices `a b c m d`, edges `ab ac am bd cd md`, squares `Q t1 t2`. -/
inductive Cell
  | a | b | c | m | d
  | ab | ac | am | bd | cd | md
  | Q | t1 | t2
  deriving DecidableEq, Repr

open Cell

/-- The trinity `T`: three lines `a ⤳ d` (`ℓ_b, ℓ_c, ℓ_m`), each pair filled by a square. -/
def T : FinBPSet Cell where
  cellList := [a, b, c, m, d, ab, ac, am, bd, cd, md, Q, t1, t2]
  dim := fun x => match x with
    | a | b | c | m | d => 0
    | ab | ac | am | bd | cd | md => 1
    | Q | t1 | t2 => 2
  face := fun ε i x => match x, i with
    -- edges (dim 1): face false 0 = source, face true 0 = target
    | ab, 0 => some (cond ε b a)
    | ac, 0 => some (cond ε c a)
    | am, 0 => some (cond ε m a)
    | bd, 0 => some (cond ε d b)
    | cd, 0 => some (cond ε d c)
    | md, 0 => some (cond ε d m)
    -- Q  : F0 = ac, T0 = bd, F1 = ab, T1 = cd   (corners a,c,b,d)
    | Q, 0 => some (cond ε bd ac)
    | Q, 1 => some (cond ε cd ab)
    -- t1 : F0 = am, T0 = bd, F1 = ab, T1 = md   (corners a,m,b,d)
    | t1, 0 => some (cond ε bd am)
    | t1, 1 => some (cond ε md ab)
    -- t2 : F0 = am, T0 = cd, F1 = ac, T1 = md   (corners a,m,c,d)
    | t2, 0 => some (cond ε cd am)
    | t2, 1 => some (cond ε md ac)
    | _, _ => none
  init := a
  final := d

/-! ## 1. Sanity: `T` is a valid precubical set

If `wellFormed` fails, the face maps above are wrong — this is the primary check. -/

/-- **THE sanity check.**  `T` satisfies the precubical identities and dimension bookkeeping. -/
theorem T_wellFormed : T.wellFormed = true := by native_decide

/-! ## 2. Non-self-linked: every cube embeds (distinct faces and corners) -/

/-- Bespoke NSL shadow: each square has 4 distinct edge-faces and 4 distinct corners. -/
def squareNSL {V : Type} [DecidableEq V] (K : FinBPSet V) : Bool :=
  K.posCells.all (fun s =>
    if K.dim s = 2 then
      let edges := ([K.face false 0 s, K.face true 0 s,
                     K.face false 1 s, K.face true 1 s].filterMap id)
      let corners := ([(K.face false 1 s).bind (K.face false 0),
                       (K.face false 1 s).bind (K.face true 0),
                       (K.face true 1 s).bind (K.face false 0),
                       (K.face true 1 s).bind (K.face true 0)].filterMap id)
      (edges.length == 4 && edges.dedup.length == 4) &&
      (corners.length == 4 && corners.dedup.length == 4)
    else true)

/-- Every square of `T` has 4 distinct edge-faces and 4 distinct corners (the computable shadow of
`NonSelfLinked`: each cube embeds). -/
theorem T_squareNSL : squareNSL T = true := by native_decide

/-- The harness's own non-self-linked checker also passes (binomial face-count identity). -/
theorem T_nonSelfLinked : T.nonSelfLinked = true := by native_decide

/-! ## 3. Altitude: `T` is graded -/

/-- The explicit altitude: `a↦0`, `b,c,m↦1`, `d↦2`; each edge ↦ alt of its source; each square ↦
alt of its `vertex0` (all three run from `a`, so `↦ 0`). -/
def altT : Cell → ℕ
  | a => 0
  | b | c | m => 1
  | d => 2
  | ab | ac | am => 0
  | bd | cd | md => 1
  | Q | t1 | t2 => 0

/-- `alt` grades `K`: every cube's source faces sit at `alt = alt(cube)` and its target faces at
`alt + 1`.  For edges this is exactly "each edge raises altitude by 1"; for squares it is "the
square's faces shift altitude correctly".  This witnesses `AdmitsAltitude`. -/
def altGraded {V : Type} [DecidableEq V] (K : FinBPSet V) (alt : V → ℕ) : Bool :=
  K.posCells.all (fun c =>
    (List.range (K.dim c)).all (fun i =>
      match K.face false i c, K.face true i c with
      | some x, some y => decide (alt x = alt c) && decide (alt y = alt c + 1)
      | _, _ => false))

/-- `altT` grades `T`: each edge raises altitude by exactly 1 and each square's faces shift
altitude correctly. -/
theorem T_altGraded : altGraded T altT = true := by native_decide

/-- The harness's own altitude solver also finds `T` admissible. -/
theorem T_admitsAltitude : T.admitsAltitude = true := by native_decide

/-! ## 4. The fold — parallelism of edges (the `eventMap`/`EventRel` shadow) -/

/-- One **parallelism** step: `e` and `e'` are opposite faces `{face false i s, face true i s}` of
some cube `s`.  (Only squares contribute: for an edge `s`, `face _ 0 s` are vertices.)  This is one
`EventRel` identification of the `e`-event with the `e'`-event, routed through the one-bead chain
`⟨s⟩`. -/
def parStep {V : Type} [DecidableEq V] (K : FinBPSet V) (e e' : V) : Bool :=
  K.posCells.any (fun s =>
    (List.range (K.dim s)).any (fun i =>
      match K.face false i s, K.face true i s with
      | some x, some y =>
          (decide (e = x) && decide (e' = y)) || (decide (e = y) && decide (e' = x))
      | _, _ => false))

/-- Forward closure of `start` under `parStep`, iterated `#edges` times (enough to saturate a
component whose size is `≤ #edges`). -/
def parReach {V : Type} [DecidableEq V] (K : FinBPSet V) (edges start : List V) : List V :=
  (fun acc => (acc ++ edges.filter (fun e' => acc.any (fun e => parStep K e e'))).dedup)^[edges.length]
    start

/-- The parallelism class of `e` among `edges`. -/
def parClass {V : Type} [DecidableEq V] (K : FinBPSet V) (edges : List V) (e : V) : List V :=
  parReach K edges [e]

/-- Transitive closure of parallelism: `e` and `e'` are in the same class. -/
def parClosureB {V : Type} [DecidableEq V] (K : FinBPSet V) (edges : List V) (e e' : V) : Bool :=
  memB e' (parClass K edges e)

/-- The 6 edges of `T`. -/
def Tedges : List Cell := [ab, ac, am, bd, cd, md]

/-- **THE FOLD.**  The two events `ab, bd` of the line `ℓ_b = a → b → d` are parallelism-identified
(`ab ∥ cd ∥ am ∥ bd`, one step per square), so the event naming folds them together. -/
theorem T_fold_ab_bd : parClosureB T Tedges ab bd = true := by native_decide

/-- In fact the closure is **total**: all six edges of `T` collapse into `ab`'s single class — the
event naming has no room for distinct names at all. -/
theorem T_fold_total : Tedges.all (fun e => parClosureB T Tedges ab e) = true := by native_decide

/-- The line `ℓ_b = [ab, bd]` is a genuine `init → final` cube chain of `T`, with `ab ≠ bd`. -/
theorem T_line_is_chain : (memB [ab, bd] T.chains && decide (ab ≠ bd)) = true := by native_decide

/-- **The refutation, assembled.**  `[ab, bd]` is an honest chain with two *distinct* beads, yet
those two events are folded by `parClosure` — so `EventFiberInjective T` fails and, by
`hasGlobalEventNaming_iff`, `HasGlobalEventNaming T` is false, even though `T` is non-self-linked and
altitude-graded (`T_nonSelfLinked`, `T_admitsAltitude`).  This refutes
`NonSelfLinked K ∧ AdmitsAltitude K ⟹ HasGlobalEventNaming K`. -/
theorem T_refutes_event_naming :
    (T.wellFormed && T.nonSelfLinked && T.admitsAltitude &&      -- NSL + altitude hypotheses hold
     memB [ab, bd] T.chains && decide (ab ≠ bd) &&               -- an honest 2-event chain
     parClosureB T Tedges ab bd) = true := by native_decide      -- …whose two events fold

/-! ## Control: the standard square `□²` does **not** fold -/

/-- Cells of the control square `□²`.  (`sqC` avoids the clash with mathlib's `sq = ·²`.) -/
inductive CSq | c00 | c10 | c01 | c11 | e0_ | e1_ | e_0 | e_1 | sqC
  deriving DecidableEq, Repr

open CSq

/-- The standard square `□²` (as in `Testing/Examples.square`).  Edges: `e0_ = {0}×□` (x₀=0),
`e1_ = {1}×□`, `e_0 = □×{0}`, `e_1 = □×{1}`. -/
def ctrl : FinBPSet CSq where
  cellList := [c00, c10, c01, c11, e0_, e1_, e_0, e_1, sqC]
  dim := fun x => match x with
    | sqC => 2 | e0_ | e1_ | e_0 | e_1 => 1 | _ => 0
  face := fun ε i x => match x, i with
    | e0_, 0 => some (cond ε c01 c00)
    | e1_, 0 => some (cond ε c11 c10)
    | e_0, 0 => some (cond ε c10 c00)
    | e_1, 0 => some (cond ε c11 c01)
    | sqC, 0  => some (cond ε e1_ e0_)
    | sqC, 1  => some (cond ε e_1 e_0)
    | _, _   => none
  init := c00
  final := c11

/-- The control is a valid precubical set (guards against a bug in the harness itself). -/
theorem ctrl_wellFormed : ctrl.wellFormed = true := by native_decide

/-- The 4 edges of `□²`. -/
def Cedges : List CSq := [e0_, e1_, e_0, e_1]

/-- **Control fails to fold.**  The two directions of `□²` stay in separate parallelism classes:
the line `[e_0, e1_]` (an x₀ edge then an x₁ edge) keeps its two events distinct. -/
theorem ctrl_no_fold : parClosureB ctrl Cedges e_0 e1_ = false := by native_decide

/-- …but the classes are genuinely non-trivial: the two *opposite* edges of each direction *do*
identify (`e_0 ∥ e_1`), so `parClosure` is not vacuously discrete — the discrimination is real. -/
theorem ctrl_pair_folds : parClosureB ctrl Cedges e_0 e_1 = true := by native_decide

/-- `[e_0, e1_]` is a genuine chain of `□²` with `e_0 ≠ e1_` — the exact analogue of the trinity's
`[ab, bd]`, but here the two events are *not* folded. -/
theorem ctrl_line_is_chain :
    (memB [e_0, e1_] ctrl.chains && decide (e_0 ≠ e1_)) = true := by native_decide

/-- **The discriminating comparison.**  Same shape of check on both: an honest 2-event line.  In the
trinity the two events fold (`true`); in the control square they do not (`false`).  So the fold check
is discriminating, and the counterexample is real. -/
theorem fold_is_discriminating :
    (parClosureB T Tedges ab bd,               -- trinity: folds
     parClosureB ctrl Cedges e_0 e1_)          -- square:  does not fold
      = (true, false) := by native_decide

end EventNamingCounterexample
end CubeTest
