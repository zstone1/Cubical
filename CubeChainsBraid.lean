-- the braid group by its Garside germ, the graded functor, the standard-line section,
-- and the Artin comparison
import CubeChains.Braid.Grading
import CubeChains.Braid.ChGrading
import CubeChains.Braid.Artin

/-!
# `CubeChainsBraid` — the braid thread, and nothing else

The isolation target: `lake build CubeChainsBraid` builds exactly the import cone of the braid
grading `braidGrpd` and its neighbours (the Garside germ, the standard-line section `chBraid`,
the Artin comparison).  A break here is a break in the braid thread, not elsewhere.

The `#print axioms` below is the target's acceptance gate: it must report exactly
`[propext, Classical.choice, Quot.sound]`.  Anything else — in particular `sorryAx` — means the
thread rests on something it should not.
-/

open CubeChains

#print axioms braidGrpd
