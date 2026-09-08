import CubeChains.Machinery.Braid.PosGerm

/-!
# Machinery/Braid/WeakAction — a downward-closed set of permutations

`WeakDown X` is closure of `X` under the right weak Bruhat order, stated on `permLen` alone so that
it is available below `WeakOrder`.  It is the one hypothesis a germ chart asks of its carrier:
every permutation below one it names is one it names.
-/

namespace CubeChains

open Equiv

variable {N : ℕ}

/-- The permutations `X` names. -/
abbrev WeakSet (X : Perm (Fin N) → Prop) : Type := {σ : Perm (Fin N) // X σ}

/-- **`X` is closed downwards** in the right weak order. -/
def WeakDown (X : Perm (Fin N) → Prop) : Prop :=
  ∀ {u v : Perm (Fin N)}, X v → permLen u + permLen (u⁻¹ * v) = permLen v → X u

end CubeChains
