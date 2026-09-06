import CubeChains.Concurrency.Salvetti.ChainBraidFace
import CubeChains.Concurrency.Salvetti.EventBraid
import CubeChains.Concurrency.Executions.RunPerm

/-!
# Concurrency/Executions/RunWord — the run word of an execution, and how a refinement changes it

An execution of `□n` fires the `n` directions one at a time; its **run word** `runWord` sends a
step to the direction fired there.  Two theorems:

* `stepPerm_eq` — the crossing permutation of a refinement *is* the change of run word: position
  in the source's word ↦ position in the target's.
* the **arrow rule** `runWord_group` / `runWord_within` — the finer end of a refinement runs in its
  own bead order across beads, and inherits the coarser order inside a bead.  This is the Salvetti
  wall-crossing `T' = X' ⊙ T` read on run words.

The engine is coend functoriality (`coordFlip_comp_apply`) applied to the *total* run map
`X.run.map ≫ χ`, which reads the linearization straight against `□n` — no Segal decomposition of
the run, hence no per-bead run geometry.
-/

open CategoryTheory CubeChain BPSet

namespace CubeChains

variable {n : ℕ}

namespace RunWedge

/-! ## The direction fired at a step

A wedge-with-run `X` over `□n` (a map `χ : ⋁X.dims ⟶ □n`) has a **run chain**: the composite
`X.run.map ≫ χ`, an all-edges chain of `□n` with one bead per step.  Its coordinate bijection
`coordFlip` labels each step by the direction it fires. -/

/-- **The run chain**: the run's own linearization of `□n`, one edge per step. -/
def runChain (X : RunWedge) (χ : ⋁X.dims ⟶ □n) : Run (□n) := (Run.pushforward χ).obj X.run

@[simp] theorem runChain_dims (X : RunWedge) (χ : ⋁X.dims ⟶ □n) :
    (runChain X χ).dims = X.run.dims := rfl

@[simp] theorem runChain_map (X : RunWedge) (χ : ⋁X.dims ⟶ □n) :
    (runChain X χ).map = X.run.map ≫ χ := rfl

/-- **The direction fired at each step** — the run chain *is* a run of `□n`, so this is the word
it spells, across the count `dimSum X.dims = n`. -/
def dir (X : RunWedge) (χ : ⋁X.dims ⟶ □n) : Fin (dimSum X.dims) ≃ Fin n :=
  (finCongr (wedgeDimSum_eq χ)).trans (runChain X χ).word

/-- **The unfolding lemma**: `dir` is `coordFlip` of `χ` on the event sitting at step `s` — coend
functoriality splits the total run map, no inverse analysis. -/
theorem dir_apply (X : RunWedge) (χ : ⋁X.dims ⟶ □n) (s : Fin (dimSum X.dims)) :
    dir X χ s = coordFlip χ ((runOrd X).symm s) :=
  coordFlip_comp_apply X.run.map χ ((strand X.run.dims (runDimSum X)).symm s)

/-- **`dir` and `beadOf` are mutually inverse**: the step firing direction `q` is `q`'s bead of the
run chain. -/
theorem dir_symm_val (X : RunWedge) (χ : ⋁X.dims ⟶ □n) (q : Fin n) :
    ((dir X χ).symm q : ℕ) = (beadOf (runChain X χ).chain q : ℕ) :=
  flatten_eq_beadOf_of_ones (runChain X χ).ones q

/-- The step firing direction `q` is the run order of the event that flips `q`. -/
theorem dir_symm_eq_runOrd (X : RunWedge) (χ : ⋁X.dims ⟶ □n) (q : Fin n) :
    (dir X χ).symm q = runOrd X ((coordFlip χ).symm q) := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [dir_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-! ## The label theorem -/

/-- **The label theorem.**  A refinement's crossing permutation carries a step of the source to the
step of the target firing the same direction. -/
theorem dir_permOf {X Y : RunWedge} (f : X ⟶ Y) (χ : ⋁X.dims ⟶ □n) (s : Fin (dimSum X.dims)) :
    dir Y (wedgeMap f ≫ χ) (finCongr (dimSum_eq f) (permOf f s)) = dir X χ s := by
  obtain ⟨e, rfl⟩ := (runOrd X).surjective s
  have hstep : finCongr (dimSum_eq f) (permOf f (runOrd X e)) = runOrd Y ((eventEquiv f).symm e) :=
    Fin.ext (permOf_runOrd_val f e)
  rw [hstep, dir_apply, dir_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    coordFlip_comp_apply]
  exact congrArg (coordFlip χ) (Equiv.apply_symm_apply (eventEquiv f) e)

end RunWedge

/-! ## Executions of `□n`: the run word -/

namespace ChStar

/-- The wedge-with-run underlying an execution. -/
abbrev runWedge (x : Ch⋆ (□n)) : RunWedge := (proj (□n)).obj x

/-- The strand count of an execution of `□n` is `n`, spelled at `runWedge` — where `permOf` lives,
and the spelling `rw` needs. -/
theorem dimSum_runWedge (x : Ch⋆ (□n)) : dimSum x.runWedge.dims = n := wedgeDimSum_eq x.chain.map

/-- The run's linearization of `□n` — an all-edges chain, one bead per step. -/
def runChain (x : Ch⋆ (□n)) : Run (□n) := RunWedge.runChain x.runWedge x.chain.map

/-- **The run word**: the order in which an execution performs the `n` directions of `□n` — the
word its run chain spells. -/
def runWord (x : Ch⋆ (□n)) : Equiv.Perm (Fin n) := (runChain x).word

/-- `runWord` read through `dir` — the spelling the label theorem `dir_permOf` transports. -/
theorem runWord_apply (x : Ch⋆ (□n)) (s : Fin n) :
    runWord x s = RunWedge.dir x.runWedge x.chain.map
      ((finCongr (dimSum_runWedge x)).symm s) := rfl

/-- The crossing permutation of a refinement, at the ambient dimension. -/
def stepPerm {x y : Ch⋆ (□n)} (f : x ⟶ y) : Equiv.Perm (Fin n) :=
  RunWedge.permCast (dimSum_runWedge x)
    (RunWedge.permOf ((proj (□n)).map f))

/-- **The label theorem for executions**: a refinement moves a step to the step firing the same
direction. -/
theorem runWord_stepPerm {x y : Ch⋆ (□n)} (f : x ⟶ y) (s : Fin n) :
    runWord y (stepPerm f s) = runWord x s := by
  have hw : RunWedge.wedgeMap ((proj (□n)).map f) ≫ x.chain.map = y.chain.map := f.1.unop.w
  have key := RunWedge.dir_permOf ((proj (□n)).map f) x.chain.map
    ((finCongr (dimSum_runWedge x)).symm s)
  rw [hw] at key
  rw [runWord_apply, runWord_apply]
  refine Eq.trans (congrArg (RunWedge.dir y.runWedge y.chain.map) (Fin.ext ?_)) key
  rfl

/-- **The crossing permutation is the change of run word** — position in the source's run word ↦
position in the target's. -/
theorem stepPerm_eq {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    stepPerm f = (runWord x).trans (runWord y).symm := by
  refine Equiv.ext fun s => ?_
  rw [Equiv.trans_apply, ← runWord_stepPerm f s, Equiv.symm_apply_apply]

theorem permCast_symm_permCast {m k : ℕ} (h : m = k) (σ : Equiv.Perm (Fin m)) :
    RunWedge.permCast h.symm (RunWedge.permCast h σ) = σ := by subst h; rfl

/-- The same, spelled at the strand count `ConcPos` evaluates `permOf` at. -/
theorem permOf_eq_runWord {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    RunWedge.permOf ((proj (□n)).map f)
      = RunWedge.permCast (dimSum_runWedge x).symm
          ((runWord x).trans (runWord y).symm) :=
  (permCast_symm_permCast _ _).symm.trans
    (congrArg (RunWedge.permCast (dimSum_runWedge x).symm) (stepPerm_eq f))

/-! ## The arrow rule

Two facts determine the run word of the finer end of a refinement `f : x ⟶ y`: **across beads** it
follows the bead order of `y`'s own chain, and **inside a bead** it agrees with the coarser end.
Together they are the wall-crossing `T' = X' ⊙ T` of the Salvetti order. -/

/-- The step firing `q` is the run order of the event flipping `q`, read on an execution. -/
theorem runWord_symm_runOrd (y : Ch⋆ (□n)) (q : Fin n) :
    ((runWord y).symm q : ℕ)
      = (RunWedge.runOrd y.runWedge ((coordFlip y.chain.map).symm q) : ℕ) :=
  ((runChain y).word_symm_val q).trans
    ((RunWedge.dir_symm_val y.runWedge y.chain.map q).symm.trans
      (congrArg Fin.val (RunWedge.dir_symm_eq_runOrd y.runWedge y.chain.map q)))

/-- **Across beads, an execution runs in its own bead order.**  A property of `y` alone: the
refinement plays no part, so no `f : x ⟶ y` appears. -/
theorem runWord_group (y : Ch⋆ (□n)) {q q' : Fin n}
    (h : (beadOf y.chain q : ℕ) < (beadOf y.chain q' : ℕ)) :
    ((runWord y).symm q : ℕ) < ((runWord y).symm q' : ℕ) := by
  rw [runWord_symm_runOrd, runWord_symm_runOrd]
  exact RunWedge.runOrd_fst_lt h

/-- …and across beads the bead order is *all* there is: separated directions are ordered by their
beads, so `runWord_group` is an iff. -/
theorem runWord_lt_iff_beadOf_lt (y : Ch⋆ (□n)) {q q' : Fin n}
    (h : beadOf y.chain q ≠ beadOf y.chain q') :
    ((runWord y).symm q : ℕ) < ((runWord y).symm q' : ℕ)
      ↔ (beadOf y.chain q : ℕ) < (beadOf y.chain q' : ℕ) := by
  refine ⟨fun hlt => ?_, runWord_group y⟩
  rcases lt_trichotomy (beadOf y.chain q : ℕ) (beadOf y.chain q' : ℕ) with hb | hb | hb
  · exact hb
  · exact absurd (Fin.ext hb) h
  · exact absurd hlt (by have := runWord_group y hb; omega)

/-- A refinement carries the event flipping `q` in the finer chain to the one flipping `q` in the
coarser — coend functoriality at the refinement's own factorization `fᵂ ≫ x.map = y.map`. -/
theorem eventEquiv_coordFlip_symm {x y : Ch⋆ (□n)} (f : x ⟶ y) (q : Fin n) :
    RunWedge.eventEquiv ((proj (□n)).map f) ((coordFlip y.chain.map).symm q)
      = (coordFlip x.chain.map).symm q := by
  have hw : RunWedge.wedgeMap ((proj (□n)).map f) ≫ x.chain.map = y.chain.map := f.1.unop.w
  refine (Equiv.eq_symm_apply _).mpr ?_
  rw [RunWedge.eventEquiv_apply]
  refine (coordFlip_comp_apply (RunWedge.wedgeMap ((proj (□n)).map f)) x.chain.map _).symm.trans ?_
  rw [hw]
  exact Equiv.apply_symm_apply _ _

/-- **Inside a bead, the finer execution inherits the coarser one's order.** -/
theorem runWord_within {x y : Ch⋆ (□n)} (f : x ⟶ y) {q q' : Fin n}
    (h : beadOf y.chain q = beadOf y.chain q') :
    ((runWord y).symm q : ℕ) < ((runWord y).symm q' : ℕ)
      ↔ ((runWord x).symm q : ℕ) < ((runWord x).symm q' : ℕ) := by
  have key := RunWedge.within_bead_agree_run ((proj (□n)).map f)
    (a := (coordFlip y.chain.map).symm q) (b := (coordFlip y.chain.map).symm q') h
  rw [eventEquiv_coordFlip_symm f q, eventEquiv_coordFlip_symm f q'] at key
  simp only [runWord_symm_runOrd]
  exact key.symm

end ChStar

end CubeChains
