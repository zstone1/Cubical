import CubeChains.Braid.Functor
import CubeChains.Salvetti.Normalize

/-!
# Braid/Grading — the braid of an execution, at every strand count at once

`Braid/Functor` works one stratum at a time, which is not enough: composing executions **adds**
strand counts, so the braid 2-functor cannot be stated per-stratum.

The friction is that `ConcCat K` is not literally a `Σ`-category: `nEvents x = nEvents y` holds only
*propositionally* (`card_eventObj_eq_of_hom`), while `SigmaHom.mk` wants the indices definitionally
equal.  Hence the `eqToHom` recast in `braidGrading.map`, and the transport lemmas below.

Same shape as `Events/OrdSign`'s `orSign`, which carries its count equalities explicitly.
-/

namespace CubeChains

open CategoryTheory Equiv

variable {K : BPSet}

/-! ## Recasting a braid along an equality of strand counts -/

/-- Transport a braid along an equality of strand counts. -/
def braidCast {n m : ℕ} (h : n = m) (b : Braid n) : Braid m := cast (congrArg Braid h) b

@[simp] theorem braidCast_rfl {n : ℕ} (b : Braid n) : braidCast rfl b = b := rfl

theorem braidCast_ofPerm {n m : ℕ} (h : n = m) (σ : Perm (Fin n)) :
    braidCast h (ofPerm σ) = ofPerm ((finCongr h).permCongr σ) := by
  subst h
  simp [braidCast, ← Equiv.Perm.one_def]

theorem permLen_permCongr {n m : ℕ} (h : n = m) (σ : Perm (Fin n)) :
    permLen ((finCongr h).permCongr σ) = permLen σ := by
  subst h
  simp [← Equiv.Perm.one_def]

/-- A recast slides past a braid. -/
theorem braidHom_eqToHom {n m : ℕ} (h : n = m) (b : Braid n) :
    (braidHom b ≫ eqToHom (congrArg strands h) : strands n ⟶ strands m)
      = eqToHom (congrArg strands h) ≫ braidHom (braidCast h b) := by
  subst h
  simp

/-! ## The event count and the event permutation, ungraded -/

/-- The number of events of an execution — the strand count of its braid. -/
noncomputable def nEvents (x : ConcCat K) : ℕ := Fintype.card (EventObj x.chain)

/-- The refinement underlying a morphism of executions (`y`'s chain refines `x`'s). -/
noncomputable def concRefine' {x y : ConcCat K} (f : x ⟶ y) : y.chain ⟶ x.chain := f.1.unop

/-- **The strand count is well defined**: a refinement neither creates nor destroys events. -/
theorem nEvents_eq {x y : ConcCat K} (f : x ⟶ y) : nEvents x = nEvents y :=
  (card_eventObj_eq_of_hom (concRefine' f)).symm

/-- The frame of an execution: its events in `evKey` order (bead first, then the line). -/
noncomputable def evIdx' (x : ConcCat K) : EventObj x.chain ≃ Fin (nEvents x) :=
  keyEquiv (evKey x.line) (evKey_injective _)

/-- The event permutation of a refinement, read in the *source's* frame. -/
noncomputable def evPerm' {x y : ConcCat K} (f : x ⟶ y) : Perm (Fin (nEvents x)) :=
  (((evIdx' x).symm.trans (eventEquiv (concRefine' f)).symm).trans (evIdx' y)).trans
    (finCongr (nEvents_eq f)).symm

end CubeChains
