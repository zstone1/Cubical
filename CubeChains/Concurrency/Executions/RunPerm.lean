import CubeChains.Concurrency.Executions.RunRestrict
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Concurrency/Executions/RunPerm — a run of `□n` *is* a permutation of its axes

One bijection `Run (□n) ≃ Perm (Fin n)`, in its two readings.  `flatten` is the **firing order**,
axis ↦ step (`runPermEquiv`, with `flatten` as its `toFun`, so downstream still computes); its
inverse is the **word**, step ↦ axis (`runWordEquiv`), which on a chain of the cube is `cross`
(`Concurrency/Merge/CubeCrossing`) — the orientation `Machinery/Braid`'s *right* weak order is
stated in.  `wordRun` is the inverse map, the all-edges chain whose beads are the singleton blocks
of the prescribed order (`blockChain`), and `wordChain` is its chain.

Restriction along a face is then *sorting*: `runPermEquiv_restrict` reads `runPresheaf.map g.op`
as the rank map of the tuple `i ↦ flatten r.chain (faceEmb g i)`.
-/

open CategoryTheory Opposite CubeChain BPSet

namespace CubeChains

variable {n : ℕ}

/-! ### The run realising a word -/

/-- **The run of `□n` performing the axes in the order `w`** — one singleton bead per step. -/
def wordRun (w : Equiv.Perm (Fin n)) : Run (□n) :=
  ⟨blockChain ⇑w.symm w.symm.surjective,
    ones_of_dimSum_eq_length
      ((wedgeDimSum_eq (blockChain ⇑w.symm w.symm.surjective).map).trans
        (length_blockChain ⇑w.symm w.symm.surjective).symm)⟩

@[simp] theorem chain_wordRun (w : Equiv.Perm (Fin n)) :
    (wordRun w).chain = blockChain ⇑w.symm w.symm.surjective := rfl

@[simp] theorem flatten_wordRun (w : Equiv.Perm (Fin n)) : flatten (wordRun w).chain = w⁻¹ :=
  Equiv.ext fun q =>
    Fin.ext ((flatten_eq_beadOf_of_ones (wordRun w).ones q).trans
      (beadOf_blockChain ⇑w.symm w.symm.surjective q))

/-- A run is the run of its own word — `eq_of_beadOf`, since a run's `flatten` *is* `beadOf`. -/
theorem wordRun_flatten (r : Run (□n)) : wordRun (flatten r.chain)⁻¹ = r :=
  Run.ext (eq_of_beadOf fun q =>
    (beadOf_blockChain _ (flatten r.chain).surjective q).trans (flatten_eq_beadOf_of_ones r.ones q))

/-- **A run of `□n` is a linear order on its `n` axes.**  `toFun` is `flatten` on the nose. -/
def runPermEquiv (n : ℕ) : Run (□n) ≃ Equiv.Perm (Fin n) where
  toFun := fun r => flatten r.chain
  invFun := fun σ => wordRun σ⁻¹
  left_inv := wordRun_flatten
  right_inv σ := (flatten_wordRun σ⁻¹).trans (inv_inv σ)

@[simp] theorem runPermEquiv_apply (r : Run (□n)) : runPermEquiv n r = flatten r.chain := rfl

@[simp] theorem runPermEquiv_symm_apply (σ : Equiv.Perm (Fin n)) :
    (runPermEquiv n).symm σ = wordRun σ⁻¹ := rfl

/-- **A run of `□n` is the word it spells** — the same bijection read step-to-axis, i.e.
`runPermEquiv` inverted.  Spelled directly rather than as `.trans (Equiv.inv _)` so that both
`runWordEquiv_apply` and `runWordEquiv_symm_apply` are `rfl` with no double inversion for `whnf`
to chew through.  Every "run word" in the tree (of an execution, of a tope) is this at some run. -/
def runWordEquiv (n : ℕ) : Run (□n) ≃ Equiv.Perm (Fin n) where
  toFun r := (flatten r.chain)⁻¹
  invFun := wordRun
  left_inv := wordRun_flatten
  right_inv w := (congrArg Inv.inv (flatten_wordRun w)).trans (inv_inv w)

@[simp] theorem runWordEquiv_apply (r : Run (□n)) : runWordEquiv n r = (flatten r.chain)⁻¹ := rfl

@[simp] theorem runWordEquiv_symm_apply (w : Equiv.Perm (Fin n)) :
    (runWordEquiv n).symm w = wordRun w := rfl

/-- **The all-edges chain performing the axes in the order `w`.** -/
def wordChain (w : Equiv.Perm (Fin n)) : Ch (□n) := (wordRun w).chain

theorem beadOf_wordChain (w : Equiv.Perm (Fin n)) (q : Fin n) :
    (beadOf (wordChain w) q : ℕ) = (w.symm q : ℕ) := beadOf_blockChain _ _ q

theorem length_wordChain (w : Equiv.Perm (Fin n)) : (wordChain w).dims.length = n :=
  length_blockChain _ _

theorem ones_wordChain (w : Equiv.Perm (Fin n)) : ∀ d ∈ (wordChain w).dims, d = 1 :=
  (wordRun w).ones

/-- **A run's chain is the word chain of its word.** -/
theorem Run.chain_eq_wordChain (r : Run (□n)) : r.chain = wordChain (runWordEquiv n r) :=
  congrArg Run.chain ((runWordEquiv n).symm_apply_apply r).symm

/-- **A run is pinned by the chain it linearizes**, so the word it spells is too. -/
theorem runWordEquiv_eq_of_chain {r : Run (□n)} {w : Equiv.Perm (Fin n)}
    (h : r.chain = wordChain w) : runWordEquiv n r = w :=
  (congrArg (runWordEquiv n) (Run.ext h)).trans ((runWordEquiv n).apply_symm_apply w)

/-! ### Restriction along a face is sorting

`flatten_restrict` factors `i ↦ flatten r.chain (faceEmb g i)` as a strictly monotone re-embedding
after the restricted run's own step order.  That factorisation is exactly what characterises
`Tuple.sort`, and the tuple is injective, so the permutation is pinned. -/

/-- **The presheaf-restriction formula.**  The restricted run performs axis `i` at the *rank* of
`flatten r.chain (faceEmb g i)` among the steps `r` gives the face's axes — i.e. its step order is
the inverse of that tuple's sorting permutation. -/
theorem runPermEquiv_restrict {k m : ℕ} (g : ▫k ⟶ ▫m) (r : Run (□m)) :
    runPermEquiv k (runPresheaf.map g.op r)
      = (Tuple.sort fun i => runPermEquiv m r (faceEmb g i))⁻¹ := by
  change flatten (runPresheaf.map g.op r).chain
    = (Tuple.sort fun i => flatten r.chain (faceEmb g i))⁻¹
  obtain ⟨s, hs, heq⟩ := flatten_restrict g r
  set σ : Equiv.Perm (Fin k) := flatten (runPresheaf.map g.op r).chain
  have hcomp : (fun i => flatten r.chain (faceEmb g i)) ∘ ⇑σ⁻¹ = s :=
    funext fun a => (heq (σ.symm a)).trans (congrArg s (σ.apply_symm_apply a))
  have hmono : Monotone ((fun i => flatten r.chain (faceEmb g i)) ∘ ⇑σ⁻¹) := by
    rw [hcomp]; exact hs.monotone
  have hinj : Function.Injective fun i => flatten r.chain (faceEmb g i) :=
    (flatten r.chain).injective.comp (faceEmb g).injective
  exact Tuple.eq_sort_inv hinj hmono

end CubeChains
