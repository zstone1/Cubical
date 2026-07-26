import CubeChains.Testing.RunOrder

/-!
# Testing/ArrowRule — a refinement's finer run word is pinned by the coarser one

Two facts determine the run word of the finer end of a refinement `f : x ⟶ y` in `Ch⋆ (□n)`:
**across beads** it follows the bead order of `y`'s own chain (`runWord_group`), and **inside a
bead** it agrees with the coarser end (`runWord_within`).  The second is `within_bead_agree_run`
(`Salvetti/EventBraid`), read on run words.
-/

open CategoryTheory Opposite CubeChain BPSet

namespace CubeChains

open RunWedge hiding runChain
open ChStar

variable {n : ℕ}

/-! ### The run word as a run order -/

/-- The step firing direction `q` is the run order of the event that flips `q`. -/
theorem dir_symm_eq_runOrd (X : RunWedge) (χ : ⋁X.dims ⟶ □n) (q : Fin n) :
    (dir X χ).symm q = runOrd X ((coordFlip χ).symm q) := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [dir_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- …the same for an execution's run word. -/
theorem runWord_symm_runOrd (y : Ch⋆ (□n)) (q : Fin n) :
    ((runWord y).symm q : ℕ) = (runOrd y.runWedge ((coordFlip y.chain.map).symm q) : ℕ) :=
  (runWord_symm_val y q).trans
    ((dir_symm_val y.runWedge y.chain.map q).symm.trans
      (congrArg Fin.val (dir_symm_eq_runOrd y.runWedge y.chain.map q)))

/-! ### The arrow rule -/

/-- **Across beads, an execution runs in its own bead order.**  A property of `y` alone: the
refinement plays no part, so no `f : x ⟶ y` appears. -/
theorem runWord_group (y : Ch⋆ (□n)) {q q' : Fin n}
    (h : (beadOf y.chain q : ℕ) < (beadOf y.chain q' : ℕ)) :
    ((runWord y).symm q : ℕ) < ((runWord y).symm q' : ℕ) := by
  rw [runWord_symm_runOrd, runWord_symm_runOrd]
  exact runOrd_fst_lt h

/-- A refinement carries the event flipping `q` in the finer chain to the one flipping `q` in the
coarser — coend functoriality at the refinement's own factorization `fᵂ ≫ x.map = y.map`. -/
theorem eventEquiv_coordFlip_symm {x y : Ch⋆ (□n)} (f : x ⟶ y) (q : Fin n) :
    eventEquiv ((proj (□n)).map f) ((coordFlip y.chain.map).symm q)
      = (coordFlip x.chain.map).symm q := by
  have hw : wedgeMap ((proj (□n)).map f) ≫ x.chain.map = y.chain.map := f.1.unop.w
  refine (Equiv.eq_symm_apply _).mpr ?_
  rw [eventEquiv_apply]
  refine (coordFlip_comp (wedgeMap ((proj (□n)).map f)) x.chain.map _).symm.trans ?_
  rw [hw]
  exact Equiv.apply_symm_apply _ _

/-- **Inside a bead, the finer execution inherits the coarser one's order.** -/
theorem runWord_within {x y : Ch⋆ (□n)} (f : x ⟶ y) {q q' : Fin n}
    (h : beadOf y.chain q = beadOf y.chain q') :
    ((runWord y).symm q : ℕ) < ((runWord y).symm q' : ℕ)
      ↔ ((runWord x).symm q : ℕ) < ((runWord x).symm q' : ℕ) := by
  have key := within_bead_agree_run ((proj (□n)).map f)
    (a := (coordFlip y.chain.map).symm q) (b := (coordFlip y.chain.map).symm q') h
  rw [eventEquiv_coordFlip_symm f q, eventEquiv_coordFlip_symm f q'] at key
  simp only [runWord_symm_runOrd]
  exact key.symm

end CubeChains
