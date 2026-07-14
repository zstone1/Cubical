import CubeChains.Schedule.ChainCone
import CubeChains.Events.EventMapBij

/-!
# Schedule/Cone — `schedCone`, THE chart cone of the schedule atlas

`schedCone a` is the cone of the chart at a cube chain `a`: it lives in `EventObj a → ℝ` (a real
time per event of `a`), where distinct events never share a coordinate.  This is the cone the
schedule space `Sched K` (`Schedule/Space.lean`) is actually built from.

Contrast the *label* cone `labelCone ℓ a` (`Schedule/ChainCone.lean`), which indexes coordinates by
action-labels via `evLabel`, so a label used twice by one chain folds two events onto one
coordinate.  `labelCone ℓ a` is the `evLabel`-preimage of `schedCone a`
(`labelCone_eq_preimage_schedCone`), so the chart cone isolates where a hypothesis is consumed: the
cone constraints are label-agnostic; only the monotonicity `schedCone_mem_of_pullback` needs
`Surjective (eventMap f)` (discharged for every `K` by `eventMap_surjective`, whence the
side-condition-free `schedCone_mem_of_pullback'`/`labelCone_mono'`).  The reverse inclusion fails
when a coarse bead is subdivided, so monotonicity is one-directional (finer ⊆ coarser).
-/

open CategoryTheory Opposite CubeChain

namespace CubeChains

open HDA

variable {K : BPSet} {A : Type}

/-! ## The occurrence cone -/

/-- The realisable-schedule cone of a chain in the per-chain space `EventObj a → ℝ`: the
schedules honouring the bead order, i.e. `bead e < bead e' → t e < t e'`. -/
def schedCone (a : Ch K) : Set (EventObj a → ℝ) :=
  {t | ∀ e e' : EventObj a, (e.1 : ℕ) < (e'.1 : ℕ) → t e < t e'}

/-- Rewrite the occurrence cone as a finite intersection of per-event-pair constraints. -/
theorem schedCone_eq_iInter (a : Ch K) :
    schedCone a = ⋂ p : EventObj a × EventObj a,
      {t : EventObj a → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) → t p.1 < t p.2} := by
  ext t
  simp only [schedCone, Set.mem_setOf_eq, Set.mem_iInter, Prod.forall]

/-- The strict-comparison set `{t | t e < t e'}` on the occurrence space is convex. -/
theorem convex_occLt (a : Ch K) (e e' : EventObj a) :
    Convex ℝ {t : EventObj a → ℝ | t e < t e'} := by
  have h : {t : EventObj a → ℝ | t e < t e'}
      = {t : EventObj a → ℝ | (fun t : EventObj a → ℝ => t e - t e') t < 0} := by
    ext t; simp only [Set.mem_setOf_eq, sub_neg]
  rw [h]; exact convex_halfSpace_lt (isLinear_diff e e') 0

/-- Open: a finite intersection of open half-spaces `t e < t e'`. -/
theorem isOpen_schedCone (a : Ch K) : IsOpen (schedCone a) := by
  rw [schedCone_eq_iInter]
  refine isOpen_iInter_of_finite (fun p => ?_)
  by_cases h : (p.1.1 : ℕ) < (p.2.1 : ℕ)
  · rw [show {t : EventObj a → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) → t p.1 < t p.2}
        = {t : EventObj a → ℝ | t p.1 < t p.2} from
      Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
    exact isOpen_lt (continuous_apply p.1) (continuous_apply p.2)
  · rw [show {t : EventObj a → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) → t p.1 < t p.2} = Set.univ from
      Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd H h⟩]
    exact isOpen_univ

/-- Convex: a finite intersection of convex sets. -/
theorem convex_schedCone (a : Ch K) : Convex ℝ (schedCone a) := by
  rw [schedCone_eq_iInter]
  refine convex_iInter (fun p => ?_)
  by_cases h : (p.1.1 : ℕ) < (p.2.1 : ℕ)
  · rw [show {t : EventObj a → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) → t p.1 < t p.2}
        = {t : EventObj a → ℝ | t p.1 < t p.2} from
      Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
    exact convex_occLt a p.1 p.2
  · rw [show {t : EventObj a → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) → t p.1 < t p.2} = Set.univ from
      Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd H h⟩]
    exact convex_univ

/-- Nonempty, witnessed by the bead index `e ↦ (e.1 : ℝ)` (distinct beads are strictly ordered).
Contrast `labelCone_nonempty`, whose label witness needs `RunInjective` to keep occurrences
separated. -/
theorem schedCone_nonempty (a : Ch K) : (schedCone a).Nonempty := by
  refine ⟨fun e => ((e.1 : ℕ) : ℝ), fun e e' hlt => ?_⟩
  change ((e.1 : ℕ) : ℝ) < ((e'.1 : ℕ) : ℝ)
  exact_mod_cast hlt

/-! ## Factorization: the label cone is the `evLabel`-preimage of the occurrence cone -/

/-- `labelCone ℓ a` is the preimage of `schedCone a` under `t ↦ t ∘ evLabel`: the same
inequalities, reindexed from occurrences to labels.  Any label-folding enters here, not in the
(label-agnostic) cone constraints. -/
theorem labelCone_eq_preimage_schedCone (ℓ : EdgeLabelling K A) (a : Ch K) :
    labelCone ℓ a = {t : A → ℝ | (fun e : EventObj a => t (evLabel ℓ ⟨a, e⟩)) ∈ schedCone a} :=
  rfl

/-! ## Monotonicity along a refinement

For `f : a ⟶ b`, the occurrence cones relate by a pullback inclusion along
`eventMap f : EventObj a → EventObj b`, needing only `Surjective (eventMap f)`. -/

/-- Pullback monotonicity: for `f : a ⟶ b` (`a` finer) with `eventMap f` surjective, a coarse
schedule `s` that honours `a`'s bead order once pulled back honours `b`'s order.  Order side is
`serialWedge_blockIdx_monotone`.  One-directional: the reverse fails when a coarse bead is
subdivided. -/
theorem schedCone_mem_of_pullback {a b : Ch K} (f : a ⟶ b)
    (hsurj : Function.Surjective (eventMap f)) {s : EventObj b → ℝ}
    (hs : (fun e : EventObj a => s (eventMap f e)) ∈ schedCone a) :
    s ∈ schedCone b := by
  intro eb eb' hlt
  obtain ⟨ea, rfl⟩ := hsurj eb
  obtain ⟨ea', rfl⟩ := hsurj eb'
  have hmono : Monotone (blockIdx fᵂ) :=
    serialWedge_blockIdx_monotone fᵂ f.φ.app_init
  have hlt' : (ea.1 : ℕ) < (ea'.1 : ℕ) := by
    by_contra hcon
    rw [not_lt] at hcon
    have hb := Fin.le_def.mp (hmono (show ea'.1 ≤ ea.1 from hcon))
    have hlt2 : (blockIdx fᵂ ea.1 : ℕ) < (blockIdx fᵂ ea'.1 : ℕ) := hlt
    omega
  exact hs ea ea' hlt'

/-- Occurrence monotonicity from `RunInjective`: it gives `EventFiberInjective` (so `eventMap f`
injective), and equal event counts (`card_eventObj_eq_of_hom`) upgrade to bijective, hence
surjective. -/
theorem schedCone_mem_of_pullback_run (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    {a b : Ch K} (f : a ⟶ b) {s : EventObj b → ℝ}
    (hs : (fun e : EventObj a => s (eventMap f e)) ∈ schedCone a) :
    s ∈ schedCone b := by
  have hfi : EventFiberInjective K :=
    (hasGlobalEventNaming_iff K).mp (hasGlobalEventNaming_of_labelling ℓ hrun)
  have hbij : Function.Bijective (eventMap f) :=
    (Fintype.bijective_iff_injective_and_card (eventMap f)).mpr
      ⟨eventMap_injective hfi f, card_eventObj_eq_of_hom f⟩
  exact schedCone_mem_of_pullback f hbij.surjective hs

/-- Occurrence monotonicity for the cube: `eventMap f` is bijective on chains of `□ⁿ`
(`cube_eventMap_bijective`), so no hypothesis is needed. -/
theorem schedCone_mem_of_pullback_cube {n : ℕ} {a b : Ch (□n)} (f : a ⟶ b)
    {s : EventObj b → ℝ}
    (hs : (fun e : EventObj a => s (eventMap f e)) ∈ schedCone a) :
    s ∈ schedCone b :=
  schedCone_mem_of_pullback f (cube_eventMap_bijective f).surjective hs

/-- The label-cone monotonicity re-derived through the occurrence cone: via the factorization
and `evLabel_coherent`, `labelCone ℓ a ⊆ labelCone ℓ b` reduces to `schedCone_mem_of_pullback`,
turning solely on `Surjective (eventMap f)`. -/
theorem labelCone_mono_via_occ (ℓ : EdgeLabelling K A) {a b : Ch K} (f : a ⟶ b)
    (hsurj : Function.Surjective (eventMap f)) :
    labelCone ℓ a ⊆ labelCone ℓ b := by
  intro t ht
  rw [labelCone_eq_preimage_schedCone]
  refine schedCone_mem_of_pullback f hsurj ?_
  intro e e' he
  change t (evLabel ℓ ⟨b, eventMap f e⟩) < t (evLabel ℓ ⟨b, eventMap f e'⟩)
  rw [evLabel_coherent ℓ f e, evLabel_coherent ℓ f e']
  exact ht e e' he

/-! ## Monotonicity with no side conditions

`eventMap_surjective` holds for every `K`, so the sole input above is free (`'` = the general-`K`
form of the `_cube`/`_run` variants). -/

/-- Occurrence-cone monotonicity for every `K`. -/
theorem schedCone_mem_of_pullback' {a b : Ch K} (f : a ⟶ b) {s : EventObj b → ℝ}
    (hs : (fun e : EventObj a => s (eventMap f e)) ∈ schedCone a) :
    s ∈ schedCone b :=
  schedCone_mem_of_pullback f (eventMap_surjective f) hs

/-- Label-cone monotonicity `labelCone ℓ a ⊆ labelCone ℓ b` for every `K` (contrast
`labelCone_mono_run`, which consumed `RunInjective`). -/
theorem labelCone_mono' (ℓ : EdgeLabelling K A) {a b : Ch K} (f : a ⟶ b) :
    labelCone ℓ a ⊆ labelCone ℓ b :=
  labelCone_mono_via_occ ℓ f (eventMap_surjective f)

end CubeChains
