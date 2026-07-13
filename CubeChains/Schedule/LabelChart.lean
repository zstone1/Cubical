import CubeChains.Schedule.Space
import CubeChains.Schedule.LabelSpace

/-!
# Schedule/LabelChart — naming schedules by actions

An `EdgeLabelling ℓ : K → A` names the events of every chain by a common alphabet, so a schedule can
be recorded in the **uniform** space `A → ℝ` — one time per action — instead of in its own chart
`ℝ^(EventObj c)`.  `RunInjective` is exactly what makes this well defined (a chain must not use a
label twice).

    Sched K ──labelTime──> A → ℝ         labelTime x ∈ labelCone ℓ x.chain

This is the *chart*, not the space: `labelTime` is **not injective**.  Two cubes with the same
boundary give distinct schedules with equal labellings (they fire the same actions at the same
times), and no side condition repairs it — `RunInjective`, `NonSelfLinked` and thinness all hold in
that example.  So the label picture folds, and `labelCone`/`labelSpace` are its (lossy) image.
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

open HDA

variable {K : BPSet} {A : Type}

open Classical in
/-- The time at which a schedule fires each action; actions it never fires get `0`.
`RunInjective` makes the choice of event well defined. -/
noncomputable def labelTime (ℓ : EdgeLabelling K A) (_hrun : RunInjective ℓ) (x : Sched K) :
    A → ℝ :=
  fun α => if he : ∃ e : EventObj x.chain, evLabel ℓ ⟨x.chain, e⟩ = α
    then x.2.1 he.choose.1 else 0

/-- An event is timed by its own bead. -/
theorem labelTime_event (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) (x : Sched K)
    (e : EventObj x.chain) :
    labelTime ℓ hrun x (evLabel ℓ ⟨x.chain, e⟩) = x.2.1 e.1 := by
  have he : ∃ e' : EventObj x.chain, evLabel ℓ ⟨x.chain, e'⟩ = evLabel ℓ ⟨x.chain, e⟩ := ⟨e, rfl⟩
  rw [labelTime, dif_pos he, (hrun x.chain he.choose_spec : he.choose = e)]

/-- The labelling of a schedule honours its chain's bead order: `StrictMono` on bead times is
exactly the cone condition once events are named by actions. -/
theorem labelTime_mem_labelCone (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) (x : Sched K) :
    labelTime ℓ hrun x ∈ labelCone ℓ x.chain := by
  intro e e' hlt
  rw [labelTime_event ℓ hrun x e, labelTime_event ℓ hrun x e']
  exact x.2.2 hlt

/-- The label picture is the image of the atlas: every schedule lands in the label space. -/
theorem labelTime_mem_labelSpace (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    (x : Sched K) : labelTime ℓ hrun x ∈ labelSpace ℓ :=
  Set.mem_iUnion.mpr ⟨x.chain, labelTime_mem_labelCone ℓ hrun x⟩

/-- **When the label chart is faithful.**  Not automatic: distinct cubes with a common boundary give
distinct schedules with equal labellings. -/
def LabelFaithful (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) : Prop :=
  Function.Injective (labelTime ℓ hrun)

end CubeChains
