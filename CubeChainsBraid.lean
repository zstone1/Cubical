-- HDA ⟺ pure braid — the headline
import CubeChains.Salvetti.PurityHDA

-- the braid group by its Garside germ, the graded functor, and what forgetting the line loses
import CubeChains.Braid.Grading
import CubeChains.Braid.ChGrading
import CubeChains.Braid.Purity

-- the enrichment: CFund, Fund, and the projection
import CubeChains.Flow.CFund
import CubeChains.Flow.Project

-- w₁ = the event-naming monodromy
import CubeChains.Schedule.Orientation

/-!
# `CubeChainsBraid` — the braid thread, and nothing else

The isolation target: `lake build CubeChainsBraid` builds exactly the import cone of the braid
result.  Everything outside that cone — the schedule space and its atlas, `Cylinder/`,
`Cobordisms/`, `Testing/` — is excluded, so a break in this target is a break in the braid thread,
while a break only in `CubeChains` is not.

The imports above are the result's endpoints; transitivity does the rest.

The `#print axioms` below are the target's own acceptance gate: each must report exactly
`[propext, Classical.choice, Quot.sound]`.  Anything else — in particular `sorryAx` — means the
thread rests on something it should not.
-/

open CubeChains

-- HDA ⟺ pure braid
#print axioms hasGlobalEventNaming_iff_braidPure

-- forgetting the line loses only pure braids
#print axioms permHom_braidPhi_eq_one_of_concProjN'

-- the graded braid functor, and the enrichment
#print axioms braidGrpd
#print axioms cfundToFund
