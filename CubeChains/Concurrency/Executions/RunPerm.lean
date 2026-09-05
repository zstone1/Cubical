import CubeChains.Machinery.SortPerm
import CubeChains.Concurrency.Executions.RunRestrict
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Concurrency/Executions/RunPerm — a run of `□n` *is* a permutation of its axes

`flatten` sends an axis to the step performing it; `runOfPerm` is the inverse, the all-edges
chain whose beads are the singleton blocks of the prescribed order (`blockChain`).  Together they
make `runPermEquiv : Run (□n) ≃ Perm (Fin n)`, with `flatten` as its `toFun` — so downstream
still computes.  `runWordEquiv` is the same equivalence read in the *firing* direction, step ↦
axis; every "run word" in the tree (of an execution, of a tope) is it at some run.

Restriction along a face is then *sorting*: `runPermEquiv_restrict` reads `runPresheaf.map g.op`
as the rank map of the tuple `i ↦ flatten r.chain (faceEmb g i)`.
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

@[simp] theorem flatten_runOfPerm (σ : Equiv.Perm (Fin n)) : flatten (runOfPerm σ).chain = σ :=
  Equiv.ext fun q =>
    Fin.ext ((flatten_eq_beadOf_of_ones (runOfPerm σ).ones q).trans
      (beadOf_blockChain ⇑σ σ.surjective q))

/-- A run is the run of its own step order — `eq_of_beadOf`, since a run's `flatten` *is*
`beadOf`. -/
theorem runOfPerm_flatten (r : Run (□n)) : runOfPerm (flatten r.chain) = r :=
  Run.ext (eq_of_beadOf fun q =>
    (beadOf_blockChain _ (flatten r.chain).surjective q).trans (flatten_eq_beadOf_of_ones r.ones q))

/-- **A run of `□n` is a linear order on its `n` axes.**  `toFun` is `flatten` on the nose. -/
def runPermEquiv (n : ℕ) : Run (□n) ≃ Equiv.Perm (Fin n) where
  toFun := fun r => flatten r.chain
  invFun := runOfPerm
  left_inv := runOfPerm_flatten
  right_inv := flatten_runOfPerm

@[simp] theorem runPermEquiv_apply (r : Run (□n)) : runPermEquiv n r = flatten r.chain := rfl

@[simp] theorem runPermEquiv_symm_apply (σ : Equiv.Perm (Fin n)) :
    (runPermEquiv n).symm σ = runOfPerm σ := rfl

/-! ### The word a run spells

`flatten` reads axis ↦ step; the **word** reads it back, step ↦ axis, which is the direction a
caller who is watching the run fire wants.  `wordRun` is the inverse. -/

/-- **The word a run spells**: the axis it performs at each step. -/
def Run.word (r : Run (□n)) : Equiv.Perm (Fin n) := (flatten r.chain).symm

/-- The run performing the axes in the order `w`. -/
def wordRun (w : Equiv.Perm (Fin n)) : Run (□n) := runOfPerm w.symm

/-- **A run of `□n` is the word it spells** — `runPermEquiv` post-composed with inversion, both
sides read step-to-axis. -/
def runWordEquiv (n : ℕ) : Run (□n) ≃ Equiv.Perm (Fin n) :=
  (runPermEquiv n).trans (Equiv.inv (Equiv.Perm (Fin n)))

/-- **The step at which a run fires an axis is that axis' bead** — a run's `flatten` *is*
`beadOf`. -/
theorem Run.word_symm_val (r : Run (□n)) (q : Fin n) :
    (r.word.symm q : ℕ) = (beadOf r.chain q : ℕ) := flatten_eq_beadOf_of_ones r.ones q

/-- **The all-edges chain performing the axes in the order `w`.** -/
def wordChain (w : Equiv.Perm (Fin n)) : Ch (□n) := (wordRun w).chain

theorem beadOf_wordChain (w : Equiv.Perm (Fin n)) (q : Fin n) :
    (beadOf (wordChain w) q : ℕ) = (w.symm q : ℕ) := beadOf_blockChain _ _ q

theorem length_wordChain (w : Equiv.Perm (Fin n)) : (wordChain w).dims.length = n :=
  length_blockChain _ _

theorem ones_wordChain (w : Equiv.Perm (Fin n)) : ∀ d ∈ (wordChain w).dims, d = 1 :=
  (wordRun w).ones

/-- **A run's chain is the word chain of its word.** -/
theorem Run.chain_eq_wordChain (r : Run (□n)) : r.chain = wordChain r.word :=
  congrArg Run.chain ((runWordEquiv n).symm_apply_apply r).symm

/-- **A run is pinned by the chain it linearizes**, so the word it spells is too. -/
theorem Run.word_eq_of_chain {r : Run (□n)} {w : Equiv.Perm (Fin n)}
    (h : r.chain = wordChain w) : r.word = w :=
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
