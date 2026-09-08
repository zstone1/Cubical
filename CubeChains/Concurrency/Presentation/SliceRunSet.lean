import CubeChains.Concurrency.Presentation.SliceExchange
import CubeChains.Machinery.Braid.WeakAction

/-!
# Concurrency/Presentation/SliceRunSet — the runs over a chain, and their down-set

The runs over `d` are the permutations `d`'s blocks allow (`RunOver.perm`), and that set is closed
downwards in the right weak order: the **exchange** `exists_runOver_mul_adjT`, iterated.  That one
fact is the whole of the geometry the braid layer sees.

The fibre is the runs themselves and not their permutations: postcomposition with `f : d' ⟶ d`
leaves a run's source untouched, so the strand count survives on the nose.
-/

open CategoryTheory Opposite BPSet CubeChains CubeChain Equiv

namespace ChainCat

variable {d : Ch Zbp} {N : ℕ}

/-- The runs over `d` on `N` events. -/
abbrev RunAt (d : Ch Zbp) (N : ℕ) : Type := {u : RunOver d // dimSum u.1.left.dims = N}

/-- A run over `d` on `N` events knows `d`'s event count. -/
theorem RunAt.strands (u : RunAt d N) : dimSum d.dims = N :=
  (dimSum_eq_of_hom u.1.1.hom).symm.trans u.2

/-- **The crossing permutation of a run over `d`.** -/
noncomputable def RunAt.perm (u : RunAt d N) : Perm (Fin N) := RunOver.perm u.strands u.1

/-- **A run over `d` is pinned by its crossing permutation.** -/
theorem RunAt.perm_injective : Function.Injective (RunAt.perm (d := d) (N := N)) := fun u _ h =>
  Subtype.ext (RunOver.perm_injective u.strands h)

/-- Off `d`'s own event count there is no run over `d`. -/
theorem isEmpty_runAt (h : N ≠ dimSum d.dims) : IsEmpty (RunAt d N) :=
  ⟨fun u => h u.strands.symm⟩

/-- **The permutations `d`'s blocks allow.** -/
def RunSet (d : Ch Zbp) (N : ℕ) : Perm (Fin N) → Prop := fun σ => ∃ u : RunAt d N, u.perm = σ

/-- A run over `d`, shortened by one descent, is a run over `d` — the exchange, on `RunAt`. -/
theorem exists_runAt_mul_adjT (u : RunAt d N) {k : Fin (N - 1)}
    (hdesc : u.perm (adjHi k) < u.perm (adjLo k)) :
    ∃ v : RunAt d N, v.perm = u.perm * adjT k := by
  obtain ⟨a, ha⟩ := exists_runOver_mul_adjT u.strands u.1 hdesc
  exact ⟨⟨a, RunOver.left_dimSum u.strands a⟩, ha⟩

/-- **Every permutation below one of `d`'s runs is one of `d`'s runs** — the exchange, iterated. -/
theorem runSet_of_le : ∀ (k : ℕ) (u : RunAt d N) (σ : Perm (Fin N)),
    permLen u.perm ≤ k → WeakOrder.of σ ≤ WeakOrder.of u.perm → RunSet d N σ := by
  intro k
  induction k with
  | zero =>
      intro u σ hk hle
      have h0 : permLen u.perm = 0 := Nat.le_zero.mp hk
      have hu : permLen σ = 0 := Nat.le_zero.mp (h0 ▸ WeakOrder.permLen_le_of_le hle)
      exact ⟨u, (eq_one_of_permLen_eq_zero _ h0).trans (eq_one_of_permLen_eq_zero σ hu).symm⟩
  | succ k ih =>
      intro u σ hk hle
      by_cases hne : σ = u.perm
      · exact ⟨u, hne.symm⟩
      · obtain ⟨i, hdesc, hcov⟩ := WeakOrder.exists_cover_of_lt hle hne
        obtain ⟨v, hv⟩ := exists_runAt_mul_adjT u hdesc
        have hlen : permLen u.perm = permLen (u.perm * adjT i) + 1 :=
          permLen_mul_adjT_of_descent hdesc
        exact ih v σ (by rw [hv]; omega) (by rw [hv]; exact hcov)

/-- **`d`'s runs are closed downwards in the right weak order.** -/
theorem weakDown_runSet (d : Ch Zbp) (N : ℕ) : WeakDown (RunSet d N) := by
  rintro σ τ ⟨u, rfl⟩ hle
  exact runSet_of_le (permLen u.perm) u σ le_rfl (WeakOrder.le_def.mpr hle)

/-- **A run over `d` is its permutation.** -/
noncomputable def runAtEquiv (d : Ch Zbp) (N : ℕ) : RunAt d N ≃ WeakSet (RunSet d N) :=
  Equiv.ofBijective (fun u => ⟨u.perm, ⟨u, rfl⟩⟩)
    ⟨fun _ _ h => RunAt.perm_injective (congrArg Subtype.val h),
      by rintro ⟨σ, u, rfl⟩; exact ⟨u, rfl⟩⟩

@[simp] theorem runAtEquiv_val (u : RunAt d N) : (runAtEquiv d N u).1 = u.perm := rfl

/-! ## Pushing a run forward -/

/-- Postcomposition on the runs; it does not touch the source, so the strand count survives on the
nose. -/
def RunAt.push {d' d : Ch Zbp} (f : d' ⟶ d) (u : RunAt d' N) : RunAt d N :=
  ⟨RunOver.push f u.1, u.2⟩

theorem RunAt.push_perm {d' d : Ch Zbp} (f : d' ⟶ d) (hd : dimSum d'.dims = N) (u : RunAt d' N) :
    (RunAt.push f u).perm = crossPerm hd f * u.perm := crossPerm_comp _ u.1.1.hom f

theorem RunAt.push_permLen {d' d : Ch Zbp} (f : d' ⟶ d) (hd : dimSum d'.dims = N)
    (u : RunAt d' N) :
    permLen (RunAt.push f u).perm = permLen u.perm + permLen (crossPerm hd f) :=
  permLen_crossPerm_comp _ u.1.1.hom f

/-- **A germ step survives postcomposition** — the crossings a run makes downstream are new there,
so length-additivity is untouched and the step is left-translated by the merge's own crossing. -/
theorem germStep_push {d' d : Ch Zbp} (f : d' ⟶ d) {β : PosBraid N} {u v : RunAt d' N}
    (h : GermStep β u.perm v.perm) :
    GermStep β (RunAt.push f u).perm (RunAt.push f v).perm := by
  have hd : dimSum d'.dims = N := u.strands
  have key : ∀ w : RunAt d' N, permLen (crossPerm hd f * w.perm)
      = permLen (crossPerm hd f) + permLen w.perm := fun w => by
    rw [← RunAt.push_perm f hd w, RunAt.push_permLen f hd w]
    omega
  rw [RunAt.push_perm f hd u, RunAt.push_perm f hd v]
  exact h.mul_left (key u) (key v)

end ChainCat
