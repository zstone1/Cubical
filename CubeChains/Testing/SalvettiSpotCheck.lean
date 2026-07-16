import CubeChains.Testing.CubeRefineBraid
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Fin.VecNotation

/-!
# Testing/SalvettiSpotCheck — an executable spot-check of braid injectivity (n = 3)

A concurrency braid is emitted as a signed Artin word (`List ℤ`, `+k = σ_{k-1}`, `-k = σ_{k-1}⁻¹`)
by `braidGrading`/`braidWordZ`.  List equality is *not* braid equality (`[1,2,1]` and `[2,1,2]` are
the same braid), so to compare braids we normalize through the **Artin representation**
`B₃ ↪ Aut(F₃)` (`F₃ = FreeGroup (Fin 3)`), which is faithful (Artin's theorem).  `braidEqW` decides
braid equality of two words by comparing the two automorphisms they induce on `x₀,x₁,x₂`.

Gotcha: `DecidableEq (FreeGroup (Fin 3))` lives in `FreeGroup.Reduce`, not `.Basic`.

Part 1 validates the normalizer (esp. the braid relation).  Part 2 feeds it the braid words of the
`schreierLoop` concurrency loops that realize the pure-braid generators A₁₂, A₂₃, A₁₃
(`schreierWordZ`, tied to the loops by `wordZToBraid_schreierWordZ` + `readBraid_schreierLoop`) and
checks they are non-trivial and pairwise distinct.  Not built by `lake build CubeChains`.
-/

set_option linter.style.nativeDecide false

open FreeGroup CubeChains CubeChains.BraidTest

namespace SalvettiSpotCheck

/-! ## Part 1 — the Artin-representation braid normalizer

An automorphism of `F₃` is stored as its image tuple `Fin 3 → F₃` (the images of `x₀,x₁,x₂`); it
acts by `FreeGroup.lift`.  `σ_k` conjugates-and-swaps the 0-indexed positions `k-1, k`. -/

local notation "x₀" => FreeGroup.of (0 : Fin 3)
local notation "x₁" => FreeGroup.of (1 : Fin 3)
local notation "x₂" => FreeGroup.of (2 : Fin 3)

/-- The identity automorphism's image tuple (out-of-range letters act trivially). -/
def gid : Fin 3 → FreeGroup (Fin 3) := ![x₀, x₁, x₂]
/-- `σ₁`: `x₀ ↦ x₀x₁x₀⁻¹`, `x₁ ↦ x₀`. -/
def gσ1 : Fin 3 → FreeGroup (Fin 3) := ![x₀ * x₁ * x₀⁻¹, x₀, x₂]
/-- `σ₁⁻¹`: `x₀ ↦ x₁`, `x₁ ↦ x₁⁻¹x₀x₁`. -/
def gσ1inv : Fin 3 → FreeGroup (Fin 3) := ![x₁, x₁⁻¹ * x₀ * x₁, x₂]
/-- `σ₂`: `x₁ ↦ x₁x₂x₁⁻¹`, `x₂ ↦ x₁`. -/
def gσ2 : Fin 3 → FreeGroup (Fin 3) := ![x₀, x₁ * x₂ * x₁⁻¹, x₁]
/-- `σ₂⁻¹`: `x₁ ↦ x₂`, `x₂ ↦ x₂⁻¹x₁x₂`. -/
def gσ2inv : Fin 3 → FreeGroup (Fin 3) := ![x₀, x₂, x₂⁻¹ * x₁ * x₂]

/-- The Artin automorphism of the letter `σ_{|i|-1}^{sign i}`, as an image tuple. -/
def artinGenImages (i : ℤ) : Fin 3 → FreeGroup (Fin 3) :=
  if i = 1 then gσ1 else if i = -1 then gσ1inv
  else if i = 2 then gσ2 else if i = -2 then gσ2inv else gid

/-- Compose two automorphism tuples: apply `t` first, then `s`. -/
def compTuple (s t : Fin 3 → FreeGroup (Fin 3)) : Fin 3 → FreeGroup (Fin 3) :=
  fun p => (FreeGroup.lift s) (t p)

/-- The Artin automorphism induced by a signed braid word, as an image tuple. -/
def artinImage (w : List ℤ) : Fin 3 → FreeGroup (Fin 3) :=
  w.foldl (fun acc i => compTuple acc (artinGenImages i)) gid

/-- Braid equality of two signed words, decided in the faithful Artin representation. -/
def braidEqW (v w : List ℤ) : Bool := decide (∀ p : Fin 3, artinImage v p = artinImage w p)

/-! ### Validation of the normalizer -/

-- The generators are mutually inverse (sanity that the tuples are genuine automorphisms).
example : braidEqW [1, -1] [] = true := by native_decide
example : braidEqW [2, -2] [] = true := by native_decide
example : braidEqW [-1, 1] [] = true := by native_decide

/-- **The braid relation** `σ₁σ₂σ₁ = σ₂σ₁σ₂` holds in the faithful model — independent confirmation
that the word encoding lands in the genuine braid group `B₃` (the repo's `Braid 3` is the *germ*
presentation; this is an outside check). -/
example : braidEqW [1, 2, 1] [2, 1, 2] = true := by native_decide

/-- `(σ₁σ₂σ₁)(σ₂σ₁σ₂)⁻¹ = 1` — the braid relation as a nulhomotopic word that does *not* freely
reduce, so the normalizer is doing real work (not just cancelling `aa⁻¹`). -/
example : braidEqW [1, 2, 1, -2, -1, -2] [] = true := by native_decide

-- Non-relations the normalizer must reject.
example : braidEqW [1, 2] [2, 1] = false := by native_decide
example : braidEqW [1] [] = false := by native_decide
example : braidEqW [2] [] = false := by native_decide
example : braidEqW [1, 1] [2, 2] = false := by native_decide

/-- The two natural `A₁₃` candidates `σ₁σ₂²σ₁⁻¹` and `σ₂σ₁²σ₂⁻¹` are *distinct* pure braids. -/
example : braidEqW [1, 2, 2, -1] [2, 1, 1, -2] = false := by native_decide

/-! ## Part 2 — the spot-check: non-trivial concurrency loops give non-trivial, distinct braids

`schreierWordZ σ j` is the signed braid word of the `schreierLoop` concurrency loop (a genuine
endomorphism of a run in `ConcGrpd (□3)`) whose braid, by `wordZToBraid_schreierWordZ` and
`readBraid_schreierLoop`, is the pure-braid generator
`ofPerm σ · ofPerm(adjT j) · ofPerm(σ·adjT j)⁻¹`.
The surjectivity proof shows these loops realize *all* of the pure braids `P₃`.  Feeding their words
through the normalizer is a spot-check of injectivity on the pure part — the part the permutation
shadow `Bₙ ↠ Sₙ` is *blind* to (every pure braid has trivial permutation). -/

/-- `adjT 0 = swap 0 1` as a permutation of the 3 cube events. -/
def sw01 : Equiv.Perm (Fin 3) := adjT (0 : Fin 2)
/-- `adjT 1 = swap 1 2`. -/
def sw12 : Equiv.Perm (Fin 3) := adjT (1 : Fin 2)

/-- `A₁₂ = σ₁²` — the braid word of the loop realizing the pure generator `A₁₂`. -/
def A12 : List ℤ := schreierWordZ sw01 0
/-- `A₂₃ = σ₂²`. -/
def A23 : List ℤ := schreierWordZ sw12 1
/-- `A₁₃ = σ₁σ₂²σ₁⁻¹`. -/
def A13 : List ℤ := schreierWordZ (sw01 * sw12) 1

#eval A12   -- [1, 1]
#eval A23   -- [2, 2]
#eval A13   -- [1, 2, 2, -1]

/-- **Each pure-braid loop is non-trivial.**  A known pure generator hitting the trivial braid would
refute injectivity on that loop. -/
example : braidEqW A12 [] = false := by native_decide
example : braidEqW A23 [] = false := by native_decide
example : braidEqW A13 [] = false := by native_decide

/-- **The three loops give pairwise-distinct braids** — the braid map separates loops the
permutation shadow cannot (all three are pure: they share the trivial underlying permutation). -/
example : [A12, A23, A13].Pairwise (fun v w => braidEqW v w = false) := by native_decide

/-- **The braid image is non-abelian**: `A₁₂A₂₃ ≠ A₂₃A₁₂`, so the loops see the nonabelian structure
of `P₃` — inconsistent with any collapse of the pure loops to an abelian/trivial image. -/
example : braidEqW (A12 ++ A23) (A23 ++ A12) = false := by native_decide

/-- A Schreier loop whose word `[2,1,2,-1,-2,-1]` does not freely reduce yet is braid-**trivial**
(its underlying pure braid is `1` via the braid relation): a nulhomotopic loop, correctly seen as
trivial.  Consistent with injectivity (trivial loop ↦ trivial braid). -/
example : braidEqW (schreierWordZ (sw12 * sw01) 1) [] = true := by native_decide

/-! ### Bridge to the real cube: the six reordering transports

`allBraids cube3exec` is the braid word `braidGrading` assigns to each of the 6 reorderings of the
3-cube's concurrent events (the run-to-run `elemBraid` transports).  `CubeRefineBraid` checks these
are distinct *as lists*; here they are distinct *as braids* — a strictly stronger statement, decided
by the normalizer on genuine `braidGrading` output. -/

#eval allBraids cube3exec

/-- The six reordering braids of the 3-cube are pairwise distinct **as braids**. -/
example : (allBraids cube3exec).Pairwise (fun v w => braidEqW v w = false) := by native_decide

end SalvettiSpotCheck
