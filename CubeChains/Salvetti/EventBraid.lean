import CubeChains.Salvetti.EventPerm
import CubeChains.Braid.Full
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Salvetti/EventBraid — the concurrency braid functor `RunWedge ⥤ FullBraid`

Each execution to its strand count `Sev`, each refinement to the positive braid `ofPerm (permOf f)`
of its crossing permutation.  Functoriality is length-additivity (`permOf_noDoubleCross`) — the
no-double-crossing law `eventCross_H` read through the run-free order `pos`.

Mapping into `FullBraid` (not the graded `Braids`) keeps the strand-count transport in one place —
`FullBraid`'s composition — so the only cast in sight is the single `permCast` inside `permOf`'s
cocycle law, forced by `Sev` genuinely varying along a refinement.
-/

open CategoryTheory CubeChain BPSet Equiv

namespace CubeChains
namespace RunWedge

/-- The strand count of an execution: its total bead dimension, as the flattening sees it. -/
abbrev Sev (X : RunWedge) : ℕ := ∑ i : Fin X.dims.length, (X.dims.get i : ℕ)

theorem Sev_eq_dimSum (X : RunWedge) : Sev X = dimSum X.dims :=
  (sum_get_eq_sum_map X.dims (fun d : ℕ+ => (d : ℕ))).trans (dimSum_sum X.dims).symm

/-- Refinement preserves the strand count. -/
theorem Sev_eq {X Y : RunWedge} (f : X ⟶ Y) : Sev X = Sev Y :=
  (Sev_eq_dimSum X).trans
    (((serialWedge_dimSum_eq (wedgeMap f)).symm).trans (Sev_eq_dimSum Y).symm)

/-- The event order of an execution as a `Fin (Sev X)`-labelling. -/
abbrev posOf (X : RunWedge) : beadEvent X.dims ≃ Fin (Sev X) := pos

/-- Transport a permutation across an equality of strand counts. -/
def permCast {m n : ℕ} (h : m = n) : Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin n) :=
  Equiv.permCongr (finCongr h)

theorem permLen_permCast {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    permLen (permCast h σ) = permLen σ := by subst h; rfl

/-- The crossing permutation of a refinement, at the source's strand count. -/
def permOf {X Y : RunWedge} (f : X ⟶ Y) : Equiv.Perm (Fin (Sev X)) :=
  ((posOf X).symm.trans ((eventEquiv f).symm.trans (posOf Y))).trans
    (finCongr (Sev_eq f)).symm

theorem permOf_pos_val {X Y : RunWedge} (f : X ⟶ Y) (e : beadEvent X.dims) :
    (permOf f (posOf X e) : ℕ) = (posOf Y ((eventEquiv f).symm e) : ℕ) := by
  simp only [permOf, Equiv.trans_apply, Equiv.symm_apply_apply, finCongr_symm, finCongr_apply,
    Fin.val_cast]

/-- The value of the composite crossing permutation on a based event — its no-double-cross target. -/
theorem rho_sigma_val {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) (e : beadEvent X.dims) :
    ((permCast (Sev_eq f).symm (permOf g)) (permOf f (posOf X e)) : ℕ)
      = (posOf Z ((eventEquiv g).symm ((eventEquiv f).symm e)) : ℕ) := by
  rw [permCast, Equiv.permCongr_apply, finCongr_apply, Fin.val_cast]
  have harg : (finCongr (Sev_eq f).symm).symm (permOf f (posOf X e))
      = posOf Y ((eventEquiv f).symm e) :=
    Fin.ext (by rw [finCongr_symm, finCongr_apply, Fin.val_cast, permOf_pos_val])
  rw [harg, permOf_pos_val]

theorem permOf_id (X : RunWedge) : permOf (𝟙 X) = 1 := by
  refine Equiv.ext fun i => ?_
  obtain ⟨e, rfl⟩ := (posOf X).surjective i
  apply Fin.ext
  rw [permOf_pos_val, eventEquiv_id, Equiv.refl_symm, Equiv.refl_apply, Equiv.Perm.one_apply]

/-- **The cocycle law**, `permOf (f ≫ g) = permCast … (permOf g) * permOf f`. -/
theorem permOf_comp {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    permOf (f ≫ g) = permCast (Sev_eq f).symm (permOf g) * permOf f := by
  refine Equiv.ext fun i => ?_
  obtain ⟨e, rfl⟩ := (posOf X).surjective i
  apply Fin.ext
  rw [permOf_pos_val, eventEquiv_comp, Equiv.symm_trans_apply, Equiv.Perm.mul_apply, rho_sigma_val]

/-- **Length-additivity: each pair of events crosses at most once** — the whole content is
`eventCross_H`, that a refinement never un-crosses a pair. -/
theorem permOf_noDoubleCross {X Y Z : RunWedge} (f : X ⟶ Y) (g : Y ⟶ Z) :
    permLen (permOf (f ≫ g)) = permLen (permOf f) + permLen (permOf g) := by
  have H : ∀ i j : Fin (Sev X), i < j → permOf f j < permOf f i →
      (permCast (Sev_eq f).symm (permOf g)) (permOf f j)
        < (permCast (Sev_eq f).symm (permOf g)) (permOf f i) := by
    intro i j hij hfl
    obtain ⟨e₁, rfl⟩ := (posOf X).surjective i
    obtain ⟨e₂, rfl⟩ := (posOf X).surjective j
    have hlt : posOf Y ((eventEquiv f).symm e₂) < posOf Y ((eventEquiv f).symm e₁) := by
      rw [Fin.lt_def, ← permOf_pos_val, ← permOf_pos_val]; exact hfl
    rw [Fin.lt_def, rho_sigma_val, rho_sigma_val]
    exact eventCross_H f g e₁ e₂ hij hlt
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
  obj X := Sev X
  map f := ⟨Sev_eq f, ofPerm (permOf f)⟩
  map_id X := FullBraidHom.ext (by rw [permOf_id, ofPerm_one]; rfl)
  map_comp {X Y Z} f g := by
    refine FullBraidHom.ext ?_
    change ofPerm (permOf (f ≫ g))
      = ((Sev_eq f).symm ▸ ofPerm (permOf g)) * ofPerm (permOf f)
    rw [braidTransport_ofPerm, permOf_comp,
      ofPerm_mul (by rw [permLen_permCast, ← permOf_comp, permOf_noDoubleCross]; omega)]

open RunWedge in
/-- **`ConcPos K` — the positive concurrency braid grading**, computable: a refinement of a chain of
`K` to the positive braid of its crossing permutation, *before* inverting refinements.  This is the
functor one actually evaluates; `Conc K` is its free-groupoid completion. -/
def ConcPos (K : BPSet) : Ch⋆ K ⥤ FullBraid := proj K ⋙ braidFunctor

/-- **The concurrency braid grading of `RunWedge`** — refinements inverted. -/
noncomputable def concRunWedge : FreeGroupoid RunWedge ⥤ FullBraid :=
  FreeGroupoid.lift braidFunctor

/-- **`Conc K` — the concurrency braid functor of a precubical set `K`**: chains of `K` with their
refinements inverted, each graded by the positive braid of its crossing permutation.  For the
standard cube the vertex groups are the pure braid groups; for the terminal `Zbp`, the full ones. -/
noncomputable def Conc (K : BPSet) : FreeGroupoid (Ch⋆ K) ⥤ FullBraid :=
  FreeGroupoid.lift (ConcPos K)

end CubeChains
