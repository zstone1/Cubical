import CubeChains.Foundations.SortPerm
import CubeChains.Salvetti.RunRestrict
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Salvetti/RunPerm — a run of `□n` *is* a permutation of its axes

`localStep` sends an axis to the step performing it; `runOfPerm` is the inverse, the all-edges
chain whose beads are the singleton blocks of the prescribed order (`blockChain`).  Together they
make `runPermEquiv : Run (□n) ≃ Perm (Fin n)`, with `localStep` as its `toFun` — so downstream
still computes.

Restriction along a face is then *sorting*: `runPermEquiv_restrict` reads `runPresheaf.map g.op`
as the rank map of the tuple `i ↦ localStep r (faceEmb g i)`.
-/

open CategoryTheory Opposite CubeChain BPSet

namespace CubeChains

variable {n : ℕ}

/-! ### The run realising a step order -/

/-- **The run of `□n` performing axis `q` at step `σ q`** — one singleton bead per step. -/
def runOfPerm (σ : Equiv.Perm (Fin n)) : Run (□n) :=
  ⟨blockChain ⇑σ σ.surjective,
    ones_of_dimSum_eq_length
      ((wedgeDimSum_eq (blockChain ⇑σ σ.surjective).map).trans
        (length_blockChain ⇑σ σ.surjective).symm)⟩

@[simp] theorem chain_runOfPerm (σ : Equiv.Perm (Fin n)) :
    (runOfPerm σ).chain = blockChain ⇑σ σ.surjective := rfl

@[simp] theorem localStep_runOfPerm (σ : Equiv.Perm (Fin n)) : localStep (runOfPerm σ) = σ :=
  Equiv.ext fun q =>
    Fin.ext ((localStep_val (runOfPerm σ) q).trans (beadOf_blockChain ⇑σ σ.surjective q))

/-- A run is the run of its own step order — `eq_of_beadOf`, since `localStep` *is* `beadOf`. -/
theorem runOfPerm_localStep (r : Run (□n)) : runOfPerm (localStep r) = r :=
  Run.ext (eq_of_beadOf fun q =>
    (beadOf_blockChain _ (localStep r).surjective q).trans (localStep_val r q))

/-- **A run of `□n` is a linear order on its `n` axes.**  `toFun` is `localStep` on the nose. -/
def runPermEquiv (n : ℕ) : Run (□n) ≃ Equiv.Perm (Fin n) where
  toFun := localStep
  invFun := runOfPerm
  left_inv := runOfPerm_localStep
  right_inv := localStep_runOfPerm

@[simp] theorem runPermEquiv_apply (r : Run (□n)) : runPermEquiv n r = localStep r := rfl

@[simp] theorem runPermEquiv_symm_apply (σ : Equiv.Perm (Fin n)) :
    (runPermEquiv n).symm σ = runOfPerm σ := rfl

/-! ### Restriction along a face is sorting

`localStep_restrict` factors `i ↦ localStep r (faceEmb g i)` as a strictly monotone re-embedding
after the restricted run's own step order.  That factorisation is exactly what characterises
`Tuple.sort`, and the tuple is injective, so the permutation is pinned. -/

/-- **The presheaf-restriction formula.**  The restricted run performs axis `i` at the *rank* of
`localStep r (faceEmb g i)` among the steps `r` gives the face's axes — i.e. its step order is the
inverse of that tuple's sorting permutation. -/
theorem runPermEquiv_restrict {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) :
    runPermEquiv k (runPresheaf.map g.op r)
      = (Tuple.sort fun i => runPermEquiv m r (faceEmb g i))⁻¹ := by
  change localStep (runPresheaf.map g.op r) = (Tuple.sort fun i => localStep r (faceEmb g i))⁻¹
  obtain ⟨s, hs, heq⟩ := localStep_restrict g r
  set σ : Equiv.Perm (Fin k) := localStep (runPresheaf.map g.op r)
  have hcomp : (fun i => localStep r (faceEmb g i)) ∘ ⇑σ⁻¹ = s :=
    funext fun a => (heq (σ.symm a)).trans (congrArg s (σ.apply_symm_apply a))
  have hmono : Monotone ((fun i => localStep r (faceEmb g i)) ∘ ⇑σ⁻¹) := by
    rw [hcomp]; exact hs.monotone
  have hinj : Function.Injective fun i => localStep r (faceEmb g i) :=
    (localStep r).injective.comp (faceEmb g).injective
  exact Tuple.eq_sort_inv hinj hmono

end CubeChains
