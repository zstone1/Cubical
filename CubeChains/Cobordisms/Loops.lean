import CubeChains.Cobordisms.DirectedBoundary

/-!
# Cobordisms/Loops

The **loop theory** of a precubical set, milestone **M3** (reachability-only part)
of the directed-cobordism build: loop-freeness and its inheritance through a
confined gluing.

Building on the strong-connectivity relation `StronglyConnected W`
(`Cobordisms/DirectedBoundary.lean`), we define:

* `IsLoopFree W` — `W` has no nontrivial directed loops (every strongly-connected
  pair is equal);
* `LoopFreeOn W P` — the sub-cell-set `P` is loop-free (no nontrivial loop lies
  inside `P`);
* `LoopConfined W P Q` — every nontrivial strongly-connected component lies wholly
  inside `P` or wholly inside `Q`.

The headline result is the **inheritance theorem**
`loopFree_of_confined : LoopConfined W P Q → LoopFreeOn W P → LoopFreeOn W Q →
IsLoopFree W` — when a glued cobordism `W` confines every loop to one of its two
pieces `P`, `Q`, loop-freeness of the pieces transfers to `W`.  This is the M3
"`X`, `Y` loop-free ⇒ `W` loop-free" statement, with the necessary `LoopConfined`
hypothesis made explicit (the directed-boundary disjointness that supplies it lives
in M1, `DirectedBoundary.no_straddle`).

**Layer:** Cobordisms.  **Imports:** `Cobordisms/DirectedBoundary`.
-/

namespace Precubical.Cobordism

open PrecubicalSet

variable {W : PrecubicalSet}

/-! ### Loop-freeness -/

/-- `W` is **loop-free** when it has no nontrivial directed loops: every pair of
mutually-reachable cells is equal. -/
def IsLoopFree (W : PrecubicalSet) : Prop :=
  ∀ x y, StronglyConnected W x y → x = y

/-- A sub-cell-set `P` is **loop-free** when no nontrivial directed loop lies inside
it: any two strongly-connected cells *both in `P`* are equal. -/
def LoopFreeOn (W : PrecubicalSet) (P : W.TotalCell → Prop) : Prop :=
  ∀ x y, StronglyConnected W x y → P x → P y → x = y

/-- The two pieces `P`, `Q` **confine the loops** of `W` when every nontrivial
strongly-connected component is contained wholly in `P` or wholly in `Q`. -/
def LoopConfined (W : PrecubicalSet) (P Q : W.TotalCell → Prop) : Prop :=
  ∀ x y, StronglyConnected W x y → x ≠ y → (P x ∧ P y) ∨ (Q x ∧ Q y)

/-! ### Inheritance -/

/-- **Loop-freeness inheritance (M3).**  If the two pieces `P`, `Q` confine every
nontrivial loop of `W`, and each piece is itself loop-free, then `W` is loop-free.
The confinement hypothesis is the reachability shadow of disjoint directed
boundaries (M1 `no_straddle`): every loop that would otherwise straddle the gluing
is forced into a single piece, where loop-freeness of that piece collapses it. -/
theorem loopFree_of_confined {P Q : W.TotalCell → Prop}
    (hconf : LoopConfined W P Q) (hP : LoopFreeOn W P) (hQ : LoopFreeOn W Q) :
    IsLoopFree W := by
  intro x y hxy
  by_cases hne : x = y
  · exact hne
  · rcases hconf x y hxy hne with ⟨hPx, hPy⟩ | ⟨hQx, hQy⟩
    · exact hP x y hxy hPx hPy
    · exact hQ x y hxy hQx hQy

/-! ### Convenience corollaries -/

/-- A loop-free precubical set is loop-free on every sub-cell-set. -/
theorem IsLoopFree.loopFreeOn (h : IsLoopFree W) (P : W.TotalCell → Prop) :
    LoopFreeOn W P :=
  fun x y hxy _ _ => h x y hxy

/-- Loop-freeness on the whole cell type is exactly loop-freeness. -/
theorem loopFreeOn_univ_iff :
    LoopFreeOn W (fun _ => True) ↔ IsLoopFree W :=
  ⟨fun h x y hxy => h x y hxy trivial trivial,
   fun h => h.loopFreeOn _⟩

/-- Loop-freeness restricts along implication of sub-cell-sets: if `P` is loop-free
and `P'` is contained in `P`, then `P'` is loop-free. -/
theorem LoopFreeOn.mono {P P' : W.TotalCell → Prop} (hP : LoopFreeOn W P)
    (hsub : ∀ z, P' z → P z) : LoopFreeOn W P' :=
  fun x y hxy hP'x hP'y => hP x y hxy (hsub x hP'x) (hsub y hP'y)

/-- A loop-free precubical set has no nontrivial strongly-connected component:
strong connectivity collapses to equality. -/
theorem IsLoopFree.stronglyConnected_iff (h : IsLoopFree W) {x y : W.TotalCell} :
    StronglyConnected W x y ↔ x = y :=
  ⟨h x y, fun hxy => hxy ▸ StronglyConnected.refl x⟩

end Precubical.Cobordism
