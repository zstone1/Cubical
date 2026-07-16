import CubeChains.Braid.PermWord

/-!
# Testing/CubeBoundaryBraids — the braids of the boundary of the 3-cube

The concurrency loops of `∂□³` (the 3-cube with its 3-cell removed) realize the **full pure braid
group `P₃`**.  Each loop is a Schreier generator `ofPerm σ · ofPerm(adjTⱼ) · ofPerm(σ·adjTⱼ)⁻¹` —
a triangle of runs joined by elementary braidings *through the 2-faces*, never the 3-cell — and
`schreierWordZ` emits its signed Artin word (`+k = σₖ`, `-k = σₖ⁻¹`).

Below: the three standard generators of `P₃` and the full twist `Δ² = (σ₁σ₂)³`, the loop around all
six 2-faces.  Not built by `lake build CubeChains`.
-/

open CubeChains

/-- `σ₁ = swap 0 1`: the elementary braiding of the first two of the 3-cube's three events. -/
def s1 : Equiv.Perm (Fin 3) := adjT 0
/-- `σ₂ = swap 1 2`. -/
def s2 : Equiv.Perm (Fin 3) := adjT 1

/-! ## The pure braid generators `P₃ = ⟨A₁₂, A₂₃, A₁₃⟩` -/

#eval schreierWordZ s1 0            -- A₁₂ = σ₁²        = [1, 1]
#eval schreierWordZ s2 1            -- A₂₃ = σ₂²        = [2, 2]
#eval schreierWordZ (s1 * s2) 1     -- A₁₃ = σ₁σ₂²σ₁⁻¹  = [1, 2, 2, -1]

-- The length-additive (ascent) Schreier generators are trivial loops: their words freely reduce.
#eval schreierWordZ s1 1            -- 1 = [1, 2, -2, -1]

/-- **Every boundary loop is a pure braid** — its underlying permutation is the identity (proven). -/
example (σ : Equiv.Perm (Fin 3)) (j : Fin 2) :
    permHom 3 (wordZToBraid (schreierWordZ σ j)) = 1 := schreierWordZ_pure σ j

/-! ## The full twist `Δ² = (σ₁σ₂)³` — the loop around all six 2-faces -/

/-- The underlying permutation of a signed word (each generator is an involution as a permutation,
so the signs are irrelevant here). -/
def wordPerm (w : List ℤ) : Equiv.Perm (Fin 3) :=
  (w.map (fun a => if h : a.natAbs - 1 < 2 then adjT ⟨a.natAbs - 1, h⟩ else 1)).prod

/-- The hexagon of the six orderings of the three events, crossing all six 2-faces. -/
def fullTwist : List ℤ := [1, 2, 1, 2, 1, 2]

#eval fullTwist.length                             -- 6  (the writhe of Δ²)
#eval (List.finRange 3).map (wordPerm fullTwist)   -- [0, 1, 2]  — Δ² returns every strand: pure

/-- Machine-checked: the full-twist loop closes up (trivial underlying permutation). -/
example : (List.finRange 3).map (wordPerm fullTwist) = List.finRange 3 := by native_decide
