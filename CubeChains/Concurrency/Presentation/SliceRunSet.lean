import CubeChains.Concurrency.Presentation.SliceExchange

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

/-- **The permutations `d`'s blocks allow.** -/
def RunSet (d : Ch Zbp) (N : ℕ) : Perm (Fin N) → Prop := fun σ => ∃ u : RunAt d N, u.perm = σ

/-- A run over `d`, shortened by one descent, is a run over `d` — the exchange, on `RunAt`. -/
theorem exists_runAt_mul_adjT (u : RunAt d N) {k : Fin (N - 1)}
    (hdesc : u.perm (adjHi k) < u.perm (adjLo k)) :
    ∃ v : RunAt d N, v.perm = u.perm * adjT k := by
  obtain ⟨a, ha⟩ := exists_runOver_mul_adjT u.strands u.1 hdesc
  exact ⟨⟨a, RunOver.left_dimSum u.strands a⟩, ha⟩

/-- **Every permutation below one of `d`'s runs is one of `d`'s runs** — the exchange, iterated on
the crossing count, which `permLen_mul_adjT_of_descent` strictly drops at every cover. -/
theorem runSet_of_le (u : RunAt d N) (σ : Perm (Fin N))
    (hle : WeakOrder.of σ ≤ WeakOrder.of u.perm) : RunSet d N σ := by
  generalize hn : permLen u.perm = n
  induction n using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    by_cases hne : σ = u.perm
    · exact ⟨u, hne.symm⟩
    · obtain ⟨i, hdesc, hcov⟩ := WeakOrder.exists_cover_of_lt hle hne
      obtain ⟨v, hv⟩ := exists_runAt_mul_adjT u hdesc
      have hlen : permLen u.perm = permLen (u.perm * adjT i) + 1 :=
        permLen_mul_adjT_of_descent hdesc
      exact ih (permLen v.perm) (by rw [hv]; omega) v (by rw [hv]; exact hcov) rfl

/-- **`d`'s runs are closed downwards in the right weak order.** -/
theorem runSet_down {σ τ : Perm (Fin N)} (h : RunSet d N τ)
    (hle : WeakOrder.of σ ≤ WeakOrder.of τ) : RunSet d N σ := by
  obtain ⟨u, rfl⟩ := h
  exact runSet_of_le u σ hle

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

/-- **A merge's crossings are new above every run**, so translating by it is length-additive.  This
is the one fact that makes postcomposition act on the germ and on the weak order alike. -/
theorem RunAt.permLen_crossPerm_mul {d' d : Ch Zbp} (f : d' ⟶ d) (hd : dimSum d'.dims = N)
    (u : RunAt d' N) :
    permLen (crossPerm hd f * u.perm) = permLen (crossPerm hd f) + permLen u.perm := by
  rw [← RunAt.push_perm f hd u, RunAt.push_permLen f hd u]
  omega

/-- **A germ step survives postcomposition** — the step is left-translated by the merge's own
crossing, and that translation is length-additive. -/
theorem germStep_push {d' d : Ch Zbp} (f : d' ⟶ d) {β : PosBraid N} {u v : RunAt d' N}
    (h : GermStep β u.perm v.perm) :
    GermStep β (RunAt.push f u).perm (RunAt.push f v).perm := by
  rw [RunAt.push_perm f u.strands u, RunAt.push_perm f u.strands v]
  exact h.mul_left (RunAt.permLen_crossPerm_mul f u.strands u)
    (RunAt.permLen_crossPerm_mul f u.strands v)

/-- **…and so does a rise in the weak order** — the translation cancels out of the gap `x⁻¹y` and
adds to both lengths. -/
theorem RunAt.push_le_push {d' d : Ch Zbp} (f : d' ⟶ d) {u v : RunAt d' N}
    (h : WeakOrder.of u.perm ≤ WeakOrder.of v.perm) :
    WeakOrder.of (RunAt.push f u).perm ≤ WeakOrder.of (RunAt.push f v).perm := by
  rw [RunAt.push_perm f u.strands u, RunAt.push_perm f u.strands v]
  exact WeakOrder.of_mul_le_of_mul _ (RunAt.permLen_crossPerm_mul f u.strands u)
    (RunAt.permLen_crossPerm_mul f u.strands v) h

end ChainCat
