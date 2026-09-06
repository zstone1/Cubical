import CubeChains.Concurrency.Salvetti.EventPerm
import CubeChains.Concurrency.Executions.RunRestrict
import CubeChains.Concurrency.Grading.WedgeBraid
import CubeChains.Machinery.Graded

/-!
# Concurrency/Salvetti/EventBraid — the concurrency braid functor `RunWedge ⥤ FullBraid`

Each execution to its strand count `dimSum X.dims`, each refinement to the positive braid
`ofPerm (permOf f)` of its crossing permutation.  Functoriality is length-additivity
(`permOf_noDoubleCross`) — the no-double-crossing law `eventCross_run` read through the **run
order** `runOrd`: events are ordered by the run linearizing the execution, not by the run-free
flattening `pos`, which would leave the label a function of the chain morphism alone.

`FullBraid` keeps the strand-count transport in one place — its own composition — so the only cast
in sight is the single `permCast` inside `permOf`'s cocycle law, forced by the strand count being
only propositionally constant along a refinement.
-/

open CategoryTheory CubeChain BPSet Equiv Opposite StdCube

namespace CubeChains
namespace RunWedge

/-- Refinement preserves the strand count. -/
theorem dimSum_eq {X Y : RunWedge} (f : X ⟶ Y) : dimSum X.dims = dimSum Y.dims :=
  (serialWedge_dimSum_eq (wedgeMap f)).symm

/-! ## The run order

The braid a refinement performs depends on the order the run performs the events, *not* the run-free
flattening `pos`.  The run *is* a linearization `X.run.map : ⋁X.run.dims ⟶ ⋁X.dims` whose beads are
its edges; its coordinate map `coordMapEquiv X.run.map` says which run-edge each event of `X` sits
on.  On the all-edges `⋁X.run.dims` every bead has one event, so `pos` there is a genuine total
order — the run order.  Pulling `X`'s events back onto it is `runOrd`; `permOf` conjugates by it
rather than by the run-free `pos`. -/

/-- The run's total dimension is the execution's strand count — `X.run.map` preserves `dimSum`. -/
theorem runDimSum (X : RunWedge) : dimSum X.run.dims = dimSum X.dims :=
  serialWedge_dimSum_eq X.run.map

/-- **The run order** of an execution: read which run-edge each event sits on (`coordMapEquiv
X.run.map`), then order by the run's own flattening `strand`. -/
def runOrd (X : RunWedge) : beadEvent X.dims ≃ Fin (dimSum X.dims) :=
  (coordMapEquiv X.run.map).symm.trans (strand X.run.dims (runDimSum X))

/-- The run order compares events by the `pos` of their run-edges — the recount is an order iso,
so it drops out. -/
theorem runOrd_lt_iff {X : RunWedge} (a b : beadEvent X.dims) :
    runOrd X a < runOrd X b ↔
      pos ((coordMapEquiv X.run.map).symm a) < pos ((coordMapEquiv X.run.map).symm b) := by
  simp only [runOrd, Equiv.trans_apply, Fin.lt_def, strand_val]

/-- **The run respects the bead order**: the run is a serial linearization, so an event in an
earlier bead of `⋁X.dims` runs strictly earlier — `coordMapEquiv_symm_fst_lt` on the all-edges
run. -/
theorem runOrd_fst_lt {X : RunWedge} {a b : beadEvent X.dims} (h : (a.1 : ℕ) < b.1) :
    runOrd X a < runOrd X b :=
  (runOrd_lt_iff a b).mpr (pos_lt_of_fst_lt (coordMapEquiv_symm_fst_lt X.run.map h))

/-- Transport a permutation across an equality of strand counts. -/
def permCast {m n : ℕ} (h : m = n) : Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin n) :=
  Equiv.permCongr (finCongr h)

theorem permLen_permCast {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    permLen (permCast h σ) = permLen σ := permLen_permCongr_finCongr h σ

/-- The target's run order, read at the source's strand count. -/
def runOrdTgt {X Y : RunWedge} (f : X ⟶ Y) : beadEvent Y.dims ≃ Fin (dimSum X.dims) :=
  (runOrd Y).trans (finCongr (dimSum_eq f)).symm

/-- The crossing permutation of a refinement, at the source's strand count — the event relabelling
`eventEquiv f` conjugated by the **run order** `runOrd` at each end (`conjPerm`; `crossPerm` is the
same construction ordered by the run-free `pos`). -/
def permOf {X Y : RunWedge} (f : X ⟶ Y) : Equiv.Perm (Fin (dimSum X.dims)) :=
  conjPerm (runOrd X) (runOrdTgt f) (eventEquiv f).symm

theorem permOf_runOrd_val {X Y : RunWedge} (f : X ⟶ Y) (e : beadEvent X.dims) :
    (permOf f (runOrd X e) : ℕ) = (runOrd Y ((eventEquiv f).symm e) : ℕ) := by
  rw [permOf, conjPerm_apply]; rfl

/-- The composite crossing permutation on a based event — its no-double-cross target. -/
theorem rho_sigma_val {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) (e : beadEvent X.dims) :
    ((permCast (dimSum_eq f).symm (permOf g)) (permOf f (runOrd X e)) : ℕ)
      = (runOrd Z ((eventEquiv g).symm ((eventEquiv f).symm e)) : ℕ) := by
  rw [permCast, Equiv.permCongr_apply, finCongr_apply, Fin.val_cast]
  have harg : (finCongr (dimSum_eq f).symm).symm (permOf f (runOrd X e))
      = runOrd Y ((eventEquiv f).symm e) :=
    Fin.ext (by rw [finCongr_symm, finCongr_apply, Fin.val_cast, permOf_runOrd_val])
  rw [harg, permOf_runOrd_val]

theorem permOf_id (X : RunWedge) : permOf (𝟙 X) = 1 := by
  rw [permOf, eventEquiv_id, Equiv.refl_symm]
  exact conjPerm_refl _

/-- **The cocycle law**, `permOf (f ≫ g) = permCast … (permOf g) * permOf f`. -/
theorem permOf_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    permOf (f ≫ g) = permCast (dimSum_eq f).symm (permOf g) * permOf f := by
  refine Equiv.ext fun i => ?_
  obtain ⟨e, rfl⟩ := (runOrd X).surjective i
  apply Fin.ext
  rw [permOf_runOrd_val, eventEquiv_comp, Equiv.symm_trans_apply, Equiv.Perm.mul_apply,
    rho_sigma_val]

/-! ### The step order of a single cube

Within one bead the run order is a *single cube*'s run order — `flatten` of that bead's local run
(`Concurrency/Executions/RunPerm`).  Two facts glue the per-bead orders to the global one: the
**bridge** `runOrd_within_flatten` (a bead of the global order is exactly its local run) and
**face preservation** `flatten_restrict_lt_iff` (`Concurrency/Executions/RunRestrict`). -/

/-- **A bead of the global run order is that bead's own local run** — the linearization is the
concatenation of its per-bead local runs (Segal, `pos_coordMapEquiv_symm_lt_iff`). -/
theorem runOrd_within_flatten {W : RunWedge} (iγ : Fin W.dims.length)
    (k k' : Fin (W.dims.get iγ : ℕ)) :
    runOrd W ⟨iγ, k⟩ < runOrd W ⟨iγ, k'⟩
      ↔ flatten (runProj W.run iγ).chain k < flatten (runProj W.run iγ).chain k' :=
  (runOrd_lt_iff _ _).trans (Fin.lt_def.trans (pos_coordMapEquiv_symm_lt_iff W.run iγ k k'))

/-- **Within a bead a refinement preserves the run order**: `f` embeds a bead of `⋁Y.dims` into one
bead of `⋁X.dims` as a face (`runProj_restrict`), and a face restriction is order-preserving. -/
theorem within_bead_agree_run {X Y : RunWedge} (f : X ⟶ Y) {a b : beadEvent Y.dims}
    (hbead : a.1 = b.1) :
    runOrd X (eventEquiv f a) < runOrd X (eventEquiv f b) ↔ runOrd Y a < runOrd Y b := by
  obtain ⟨iβ, ka⟩ := a
  obtain ⟨jb, kb⟩ := b
  obtain rfl : iβ = jb := hbead
  rw [eventEquiv_mk, eventEquiv_mk, runOrd_within_flatten, runOrd_within_flatten,
    runProj_restrict f iβ, flatten_restrict_lt_iff]

/-- **No double crossing, on the run order.**  If the run of `X` performs `e₁` before `e₂` while the
run of `Y` performs their `f`-preimages in the opposite order (so `f` crosses the pair), then the
further refinement `g` keeps them crossed: a crossing, once made, is never undone.

The crossing pair lands in a common bead (`runOrd_fst_lt`), and `f`/`g` preserve the order inside a
bead (`within_bead_agree_run`) and across beads (`chainBead_refine`). -/
theorem eventCross_run {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) (e₁ e₂ : beadEvent X.dims)
    (h1 : runOrd X e₁ < runOrd X e₂)
    (h2 : runOrd Y ((eventEquiv f).symm e₂) < runOrd Y ((eventEquiv f).symm e₁)) :
    runOrd Z ((eventEquiv g).symm ((eventEquiv f).symm e₂))
      < runOrd Z ((eventEquiv g).symm ((eventEquiv f).symm e₁)) := by
  set a := (eventEquiv f).symm e₁ with ha
  set b := (eventEquiv f).symm e₂ with hb
  have he₁ : eventEquiv f a = e₁ := Equiv.apply_symm_apply _ _
  have he₂ : eventEquiv f b = e₂ := Equiv.apply_symm_apply _ _
  have hstep : (b.1 : ℕ) < a.1 := by
    rcases lt_trichotomy (a.1 : ℕ) (b.1 : ℕ) with hlt | heq | hgt
    · exact absurd (runOrd_fst_lt hlt) (asymm h2)
    · rw [← he₁, ← he₂] at h1
      exact absurd ((within_bead_agree_run f (Fin.ext heq)).mp h1) (asymm h2)
    · exact hgt
  exact runOrd_fst_lt (chainBead_refine g hstep)

/-- **Length-additivity: each pair of events crosses at most once** — the whole content is
`eventCross_run`, that a refinement never un-crosses a pair. -/
theorem permOf_noDoubleCross {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    permLen (permOf (f ≫ g)) = permLen (permOf f) + permLen (permOf g) := by
  have H : ∀ i j : Fin (dimSum X.dims), i < j → permOf f j < permOf f i →
      (permCast (dimSum_eq f).symm (permOf g)) (permOf f j)
        < (permCast (dimSum_eq f).symm (permOf g)) (permOf f i) := by
    intro i j hij hfl
    obtain ⟨e₁, rfl⟩ := (runOrd X).surjective i
    obtain ⟨e₂, rfl⟩ := (runOrd X).surjective j
    have hlt : runOrd Y ((eventEquiv f).symm e₂) < runOrd Y ((eventEquiv f).symm e₁) := by
      rw [Fin.lt_def, ← permOf_runOrd_val, ← permOf_runOrd_val]; exact hfl
    rw [Fin.lt_def, rho_sigma_val, rho_sigma_val]
    exact eventCross_run f g e₁ e₂ hij hlt
  rw [permOf_comp, permLen_mul_of_noDoubleCross H, permLen_permCast]

/-- `ofPerm` transported across a strand-count equality is `ofPerm` of the cast permutation. -/
theorem braidTransport_ofPerm {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    h ▸ ofPerm σ = ofPerm (permCast h σ) := by subst h; rfl

end RunWedge

open RunWedge in
/-- **The concurrency braid functor**, `K`-free: a wedge-with-run to its strand count, a refinement
to the positive braid `ofPerm (permOf f)`.  Length-additivity (`permOf_noDoubleCross`) is what makes
it a functor; `FullBraid`'s composition carries the one strand-count transport. -/
def braidFunctor : RunWedge ⥤ FullBraid where
  obj X := dimSum X.dims
  map f := ⟨dimSum_eq f, ofPerm (permOf f)⟩
  map_id X := GradedHom.ext (by rw [permOf_id, ofPerm_one]; rfl)
  map_comp {X Y Z} f g := by
    refine GradedHom.ext ?_
    change ofPerm (permOf (f ≫ g))
      = ((dimSum_eq f).symm ▸ ofPerm (permOf g)) * ofPerm (permOf f)
    rw [braidTransport_ofPerm]
    exact ofPerm_eq_mul (permOf_comp f g) (by rw [permOf_noDoubleCross, permLen_permCast])

open RunWedge in
/-- **`ConcPos K` — the positive concurrency braid grading**, computable: a refinement of a chain of
`K` to the positive braid of its crossing permutation, *before* inverting refinements. -/
def ConcPos (K : BPSet) : Ch⋆ K ⥤ FullBraid := proj K ⋙ braidFunctor

end CubeChains
