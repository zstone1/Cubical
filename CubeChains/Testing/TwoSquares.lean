import CubeChains.Testing.Model
import CubeChains.Testing.EventNamingCounterexample

-- This is a property-testing file; `native_decide` is the intended engine here.
set_option linter.style.nativeDecide false
set_option linter.style.longLine false

/-!
# Testing/TwoSquares — no global chart can model the schedule space

`S` is the **directed sphere**: two 2-cubes `sqA`, `sqB` with the *same* boundary (the same four
edges).  It passes every side condition the label picture was ever given — non-self-linked,
altitude-graded, and its two parallelism classes stay separate (so any edge-labelling is
run-injective) — and yet:

* `Ch S` has **four** chains: `[sqA]`, `[sqB]`, and the two edge paths, each of which refines *both*
  squares.  So `N(Ch S)` is the 4-cycle `K_{2,2} ≃ S¹`.
* `sqA` and `sqB` have **identical** immediate faces, hence identical events and identical labels
  under *any* labelling.  So `labelCone ℓ [sqA] = labelCone ℓ [sqB]` — the label chart cannot separate
  them, and `labelSpace ℓ` collapses `S¹` to something contractible.

That is why the schedule space is built as an atlas (`Schedule/Space.lean`) and not inside a global
coordinate ambient: the fold survives every hypothesis, so no side condition repairs it.  See
`Schedule/DESIGN.md` §1b.
-/

namespace CubeTest
namespace TwoSquares

open FinBPSet

/-- Two squares glued along their whole boundary. -/
inductive Cell | c00 | c10 | c01 | c11 | e0_ | e1_ | e_0 | e_1 | sqA | sqB
  deriving DecidableEq, Repr

open Cell

/-- The directed sphere: `sqA` and `sqB` share all four edges (`face` is the same for both). -/
def S : FinBPSet Cell where
  cellList := [c00, c10, c01, c11, e0_, e1_, e_0, e_1, sqA, sqB]
  dim := fun x => match x with
    | sqA | sqB => 2 | e0_ | e1_ | e_0 | e_1 => 1 | _ => 0
  face := fun ε i x => match x, i with
    | e0_, 0 => some (cond ε c01 c00)
    | e1_, 0 => some (cond ε c11 c10)
    | e_0, 0 => some (cond ε c10 c00)
    | e_1, 0 => some (cond ε c11 c01)
    | sqA,  0 => some (cond ε e1_ e0_)
    | sqA,  1 => some (cond ε e_1 e_0)
    | sqB, 0 => some (cond ε e1_ e0_)
    | sqB, 1 => some (cond ε e_1 e_0)
    | _, _   => none
  init := c00
  final := c11

theorem S_wellFormed : S.wellFormed = true := by native_decide

/-! ## `S` satisfies every side condition -/

theorem S_nonSelfLinked : S.nonSelfLinked = true := by native_decide

theorem S_admitsAltitude : S.admitsAltitude = true := by native_decide

/-- The 4 edges. -/
def edges : List Cell := [e0_, e1_, e_0, e_1]

/-- The two directions stay in **separate** parallelism classes, exactly as in `□²`: so the natural
labelling has two letters and every chain uses each once (run-injective).  `parClosureB` is the
event-fold shadow from `EventNamingCounterexample`. -/
theorem S_no_fold : EventNamingCounterexample.parClosureB S edges e_0 e1_ = false := by
  native_decide

/-! ## …and still the label chart folds -/

/-- The two squares are distinct cells with **identical** boundaries.  Any labelling therefore gives
them the same events with the same labels — the label cone cannot tell them apart. -/
theorem S_same_boundary :
    (decide (sqA ≠ sqB) && decide (S.immFaces sqA = S.immFaces sqB)) = true := by native_decide

/-- `Ch S` has exactly four chains. -/
theorem S_chains_card : S.chains.length = 4 := by native_decide

/-- Both squares and both edge paths are chains `c00 ⟶ c11`. -/
theorem S_chains :
    (memB [sqA] S.chains && memB [sqB] S.chains &&
     memB [e_0, e1_] S.chains && memB [e0_, e_1] S.chains) = true := by native_decide

/-- The two single-bead chains are distinct objects of `Ch S` with the same dimension sequence — the
fold, in one line: distinct chains, identical label data. -/
theorem S_fold :
    (decide ([sqA] ≠ [sqB]) && decide (S.dimSeq [sqA] = S.dimSeq [sqB])) = true := by native_decide

/-- **`Ch S` is the 4-cycle.**  Each edge path refines *both* squares, and neither pair is
comparable, so the refinement order is `K_{2,2}`:

        [sqA]        [sqB]        (maximal: the two fillings)
         ▲  ▲        ▲  ▲
         │   ╲      ╱   │
         │    ╲    ╱    │
      [e_0,e1_]  [e0_,e_1]        (minimal: the two edge paths)

Hence `|N(Ch S)| ≃ S¹` — while the label picture, which cannot separate `[sqA]` from `[sqB]`, sees a
contractible space. -/
theorem S_nerve_K22 :
    (S.chLe [e_0, e1_] [sqA] && S.chLe [e_0, e1_] [sqB] &&
     S.chLe [e0_, e_1] [sqA] && S.chLe [e0_, e_1] [sqB] &&
     !S.chLe [sqA] [sqB] && !S.chLe [sqB] [sqA] &&
     !S.chLe [e_0, e1_] [e0_, e_1] && !S.chLe [e0_, e_1] [e_0, e1_]) = true := by native_decide

end TwoSquares
end CubeTest
