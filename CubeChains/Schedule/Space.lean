import CubeChains.Schedule.EventMapBij
import CubeChains.Schedule.Cone

/-!
# Schedule/Space — the schedule space `Sched K`

A **schedule** is a cube chain together with one time per bead, strictly increasing:
`Sched K = Σ c, Stratum c`.  Strictness says no two beads are tied, so the chain component *is* the
tie-block decomposition of the timing — `Sched.chain` is a projection, not a construction.

The topology comes from the **charts**.  For a chain `a`, a refinement `f : c ⟶ a` plus bead times
for `c` spreads to an event-timing of `a` (`spread`), landing in `a`'s cone
`schedCone a ⊆ ℝ^(EventObj a)`:

    Chart a  ──chartCoord──>  ℝ^(EventObj a)        (image = schedCone a, an open convex cone)
       │
       │ chartSched  (forget the refinement)
       v
    Sched K                                          (topology = final topology of all charts)

`Chart a` carries the topology induced from `ℝ^(EventObj a)`; `Sched K` carries the final topology
of `⨆ a, Chart a → Sched K`.  Both are unconditional.  The two facts that make this an *atlas* are
stated as `ChartsCoverCones` (the chart hits exactly the cone — the tie-block bijection) and
`ChartsInjective` (no chart folds — needs `Ch K` thin); neither is proved here.

Gotcha: `Sched K` is locally Euclidean but **not Hausdorff** in general (two cubes with a common
boundary give a doubled stratum), and that is correct — it carries the homotopy type.
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

variable {K : BPSet}

/-! ## Strata and schedules -/

/-- One time per bead of `c`, strictly increasing: the schedules whose finest chain is `c`. -/
def Stratum (c : Ch K) : Type :=
  {τ : ChainCat.Bead c → ℝ // StrictMono τ}

/-- A **schedule**: a cube chain with strictly increasing bead times. -/
def Sched (K : BPSet) : Type :=
  Σ c : Ch K, Stratum c

/-- The chain underlying a schedule — its finest chain, by strictness. -/
def Sched.chain (x : Sched K) : Ch K := x.1

/-! ## The chart of a chain -/

/-- The event bijection along a refinement (`eventMap` is bijective for every `K`). -/
noncomputable def eventEquiv {a b : Ch K} (f : a ⟶ b) : EventObj a ≃ EventObj b :=
  Equiv.ofBijective (eventMap f) (eventMap_bijective f)

/-- Spread bead times of a refinement `f : c ⟶ a` to an event-timing of `a`: an event of `a` is
timed by the bead of `c` it comes from. -/
noncomputable def spread {c a : Ch K} (f : c ⟶ a) (τ : Stratum c) : EventObj a → ℝ :=
  fun e => τ.1 ((eventEquiv f).symm e).1

/-- A spread timing honours `a`'s bead order, i.e. lands in `a`'s cone: `blockIdx` is monotone, so
events in distinct beads of `a` come from distinct beads of `c` *in the same order*, and `τ` is
strictly increasing. -/
theorem spread_mem_cone {c a : Ch K} (f : c ⟶ a) (τ : Stratum c) :
    spread f τ ∈ schedCone a := by
  have hsp : ∀ x : EventObj c, spread f τ (eventMap f x) = τ.1 x.1 := by
    intro x
    have h1 : (eventEquiv f) x = eventMap f x := rfl
    have h2 : (eventEquiv f).symm (eventMap f x) = x := by
      rw [← h1]; exact (eventEquiv f).symm_apply_apply x
    simp only [spread, h2]
  have hmono : Monotone (blockIdx fᵂ) :=
    serialWedge_blockIdx_monotone fᵂ f.φ.app_init
  intro e e' hlt
  obtain ⟨x, rfl⟩ := (eventMap_bijective f).surjective e
  obtain ⟨y, rfl⟩ := (eventMap_bijective f).surjective e'
  rw [hsp x, hsp y]
  refine τ.2 ?_
  by_contra hcon
  exact absurd hlt (not_lt.mpr (Fin.le_def.mp (hmono (not_lt.mp hcon))))

/-- The **chart** of `a`: a refinement of `a` together with bead times for it. -/
def Chart (a : Ch K) : Type :=
  Σ c : Ch K, (c ⟶ a) × Stratum c

/-- The chart's coordinates: an event-timing of `a`. -/
noncomputable def chartCoord (a : Ch K) : Chart a → (EventObj a → ℝ) :=
  fun p => spread p.2.1 p.2.2

theorem chartCoord_mem_cone (a : Ch K) (p : Chart a) :
    chartCoord a p ∈ schedCone a :=
  spread_mem_cone p.2.1 p.2.2

/-- The chart into the schedule space: forget the refinement. -/
def chartSched (a : Ch K) : Chart a → Sched K :=
  fun p => ⟨p.1, p.2.2⟩

/-! ## The topology

`Chart a` is topologized as a subspace of `ℝ^(EventObj a)` (its image is the cone `schedCone a`);
`Sched K` gets the final topology of all the charts at once. -/

noncomputable instance instTopChart (a : Ch K) : TopologicalSpace (Chart a) :=
  TopologicalSpace.induced (chartCoord a) inferInstance

/-- All charts at once. -/
def totalChart (K : BPSet) : (Σ a : Ch K, Chart a) → Sched K :=
  fun p => chartSched p.1 p.2

noncomputable instance instTopSched : TopologicalSpace (Sched K) :=
  TopologicalSpace.coinduced (totalChart K) inferInstance

theorem continuous_totalChart : Continuous (totalChart K) :=
  continuous_coinduced_rng

theorem continuous_chartSched (a : Ch K) : Continuous (chartSched a) :=
  continuous_totalChart.comp continuous_sigmaMk

/-! ## The two atlas properties (stated, not proved)

Together they say the charts are open embeddings onto the cones — i.e. that `Sched K` is glued from
braid cones along refinements. -/

/-- **Tie-blocks.**  Every timing in `a`'s cone is spread from a unique refinement of `a` with
strictly increasing bead times: `chartCoord a` is a bijection onto `schedCone a`.  Surjectivity is
the tie-block decomposition (the cross-bead constraints put each tie-block inside one bead of `a`);
injectivity is `Ch K` thin. -/
def IsAtlas (K : BPSet) : Prop :=
  ∀ a : Ch K,
    Function.Injective (chartCoord a) ∧ Set.range (chartCoord a) = schedCone a

/-- **No folding.**  Distinct points of a chart are distinct schedules — needs `Ch K` thin (a
self-linked cube gives two refinements `c ⟶ a`, hence two chart points naming one schedule). -/
def ChartsFaithful (K : BPSet) : Prop :=
  ∀ a : Ch K, Function.Injective (chartSched a)

end CubeChains
