import CubeChains.Salvetti.ChainBraidFace
import CubeChains.Salvetti.EventBraid

/-!
# Testing/RunOrder — the crossing permutation is the change of run word

An execution of `□n` fires the `n` directions one at a time; its **run word** `runWord` sends a
step to the direction fired there.  `stepPerm_eq` identifies the crossing permutation of a
refinement with the change of run word: position in the source's word ↦ position in the target's.

The engine is coend functoriality (`coordFlip_comp`) applied to the *total* run map
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

/-- The strand count of a wedge over `□n` is `n`. -/
theorem Sev_eq_dim (X : RunWedge) (χ : ⋁X.dims ⟶ □n) : Sev X = n :=
  (Sev_eq_dimSum X).trans (wedgeDimSum_eq χ)

/-- **The run chain**: the run's own linearization of `□n`, one edge per step. -/
def runChain (X : RunWedge) (χ : ⋁X.dims ⟶ □n) : Ch (□n) := ⟨X.run.dims, X.run.map ≫ χ⟩

@[simp] theorem runChain_dims (X : RunWedge) (χ : ⋁X.dims ⟶ □n) :
    (runChain X χ).dims = X.run.dims := rfl

@[simp] theorem runChain_map (X : RunWedge) (χ : ⋁X.dims ⟶ □n) :
    (runChain X χ).map = X.run.map ≫ χ := rfl

/-- The run chain has one bead per direction. -/
theorem runChain_length (X : RunWedge) (χ : ⋁X.dims ⟶ □n) : (runChain X χ).dims.length = n :=
  (dimSum_eq_length_of_ones X.run.ones).symm.trans (wedgeDimSum_eq (X.run.map ≫ χ))

/-- **The direction fired at each step** — the run chain's coordinate bijection, read on the run
order. -/
def dir (X : RunWedge) (χ : ⋁X.dims ⟶ □n) : Fin (Sev X) ≃ Fin n :=
  ((finCongr (runDimSum X)).symm.trans pos.symm).trans (coordFlip (X.run.map ≫ χ))

/-- **The unfolding lemma**: `dir` is `coordFlip` of `χ` on the event sitting at step `s` — coend
functoriality splits the total run map, no inverse analysis. -/
theorem dir_apply (X : RunWedge) (χ : ⋁X.dims ⟶ □n) (s : Fin (Sev X)) :
    dir X χ s = coordFlip χ ((runOrd X).symm s) :=
  coordFlip_comp X.run.map χ (pos.symm ((finCongr (runDimSum X)).symm s))

/-- **`dir` and `beadOf` are mutually inverse**: the step firing direction `q` is `q`'s bead of the
run chain. -/
theorem dir_symm_val (X : RunWedge) (χ : ⋁X.dims ⟶ □n) (q : Fin n) :
    ((dir X χ).symm q : ℕ) = (beadOf (runChain X χ) q : ℕ) :=
  pos_ones X.run.ones ((coordFlip (X.run.map ≫ χ)).symm q)

/-! ## The label theorem -/

/-- **The label theorem.**  A refinement's crossing permutation carries a step of the source to the
step of the target firing the same direction. -/
theorem dir_permOf {X Y : RunWedge} (f : X ⟶ Y) (χ : ⋁X.dims ⟶ □n) (s : Fin (Sev X)) :
    dir Y (wedgeMap f ≫ χ) (finCongr (Sev_eq f) (permOf f s)) = dir X χ s := by
  obtain ⟨e, rfl⟩ := (runOrd X).surjective s
  have hstep : finCongr (Sev_eq f) (permOf f (runOrd X e)) = runOrd Y ((eventEquiv f).symm e) :=
    Fin.ext (permOf_runOrd_val f e)
  rw [hstep, dir_apply, dir_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, coordFlip_comp]
  exact congrArg (coordFlip χ) (Equiv.apply_symm_apply (eventEquiv f) e)

/-- The crossing permutation is *determined* by the two direction labellings. -/
theorem permOf_eq_dir {X Y : RunWedge} (f : X ⟶ Y) (χ : ⋁X.dims ⟶ □n) :
    permOf f
      = ((dir X χ).trans (dir Y (wedgeMap f ≫ χ)).symm).trans (finCongr (Sev_eq f)).symm := by
  refine Equiv.ext fun s => ?_
  rw [Equiv.trans_apply, Equiv.trans_apply, ← dir_permOf f χ s, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

end RunWedge

/-! ## Executions of `□n`: the run word -/

/-- A chain of `□n` is pinned by its ordered partition — `chFace` reads only `beadOf`, and
`chFaceEquiv` is injective. -/
theorem eq_of_beadOf {t t' : Ch (□n)} (h : ∀ q, (beadOf t q : ℕ) = (beadOf t' q : ℕ)) : t = t' :=
  chFaceEquiv.injective
    (Subtype.ext (congrArg braidSign (funext fun q => congrArg Nat.cast (h q))))

namespace ChStar

/-- The wedge-with-run underlying an execution. -/
abbrev runWedge (x : Ch⋆ (□n)) : RunWedge := (proj (□n)).obj x

/-- The run's linearization of `□n` — an all-edges chain, one bead per step. -/
def runChain (x : Ch⋆ (□n)) : Ch (□n) := RunWedge.runChain x.runWedge x.chain.map

theorem runChain_length (x : Ch⋆ (□n)) : (runChain x).dims.length = n :=
  RunWedge.runChain_length _ _

/-- **The run word**: the order in which an execution performs the `n` directions of `□n`. -/
def runWord (x : Ch⋆ (□n)) : Equiv.Perm (Fin n) :=
  (finCongr (RunWedge.Sev_eq_dim x.runWedge x.chain.map)).symm.trans
    (RunWedge.dir x.runWedge x.chain.map)

theorem runWord_apply (x : Ch⋆ (□n)) (s : Fin n) :
    runWord x s = RunWedge.dir x.runWedge x.chain.map
      ((finCongr (RunWedge.Sev_eq_dim x.runWedge x.chain.map)).symm s) := rfl

/-- The step at which a direction fires is its bead in the run chain. -/
theorem runWord_symm_val (x : Ch⋆ (□n)) (q : Fin n) :
    ((runWord x).symm q : ℕ) = (beadOf (runChain x) q : ℕ) :=
  RunWedge.dir_symm_val x.runWedge x.chain.map q

/-- …and conversely: the direction fired at step `s` has bead `s`. -/
theorem beadOf_runWord_val (x : Ch⋆ (□n)) (s : Fin n) :
    (beadOf (runChain x) (runWord x s) : ℕ) = (s : ℕ) :=
  (runWord_symm_val x (runWord x s)).symm.trans
    (congrArg Fin.val ((runWord x).symm_apply_apply s))

/-- **The run word is pinned by the run chain's partition** — the criterion a caller building an
execution from a word uses. -/
theorem runWord_eq_of_beadOf (x : Ch⋆ (□n)) (w : Equiv.Perm (Fin n))
    (h : ∀ q, (beadOf (runChain x) q : ℕ) = (w.symm q : ℕ)) : runWord x = w := by
  have hs : (runWord x).symm = w.symm :=
    Equiv.ext fun q => Fin.ext ((runWord_symm_val x q).trans (h q))
  simpa using congrArg Equiv.symm hs

/-- An execution whose run chain is `ofBlockMap w⁻¹` performs the directions in the order `w`. -/
theorem runWord_of_runChain_ofBlockMap (x : Ch⋆ (□n)) (w : Equiv.Perm (Fin n))
    (h : runChain x = (chEquivCubeChain (□n)).symm (ofBlockMap ⇑w.symm w.symm.surjective)) :
    runWord x = w :=
  runWord_eq_of_beadOf x w fun q => by rw [h, beadOf_ofBlockMap]

/-- The crossing permutation of a refinement, at the ambient dimension. -/
def stepPerm {x y : Ch⋆ (□n)} (f : x ⟶ y) : Equiv.Perm (Fin n) :=
  RunWedge.permCast (RunWedge.Sev_eq_dim x.runWedge x.chain.map)
    (RunWedge.permOf ((proj (□n)).map f))

/-- **The label theorem for executions**: a refinement moves a step to the step firing the same
direction. -/
theorem runWord_stepPerm {x y : Ch⋆ (□n)} (f : x ⟶ y) (s : Fin n) :
    runWord y (stepPerm f s) = runWord x s := by
  have hw : RunWedge.wedgeMap ((proj (□n)).map f) ≫ x.chain.map = y.chain.map := f.1.unop.w
  have key := RunWedge.dir_permOf ((proj (□n)).map f) x.chain.map
    ((finCongr (RunWedge.Sev_eq_dim x.runWedge x.chain.map)).symm s)
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
      = RunWedge.permCast (RunWedge.Sev_eq_dim x.runWedge x.chain.map).symm
          ((runWord x).trans (runWord y).symm) :=
  (permCast_symm_permCast _ _).symm.trans
    (congrArg (RunWedge.permCast (RunWedge.Sev_eq_dim x.runWedge x.chain.map).symm) (stepPerm_eq f))

end ChStar

end CubeChains

