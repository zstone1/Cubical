import CubeChains.Arrangements.BraidGeometry
import CubeChains.Salvetti.BraidFaceEquiv
import CubeChains.Salvetti.Elements
import CubeChains.Schedule.HDA
import CubeChains.Chains.ChainSkeletal

/-!
# Schedule/ChainCone — the chain → open-convex-cone functor (timing geometry, Phase 2)

Phase 2 of the *timing geometry* program: each cube chain is sent to the **open convex cone** of
timings/schedules that realise it, functorially in refinement (finer chain ⟹ *smaller* cone).

## Part 1 — the cube instance (assumption-free)

For `K = □ⁿ = BPSet.cube n` a chain is a `RefineObj (cube n).init (cube n).final`; its cone is
Phase 1's open star cone of its ordered-set-partition covector,
`chainConeR x = starCone (braidSign (covectorHeight x))` in the schedule space `Fin n → ℝ`.
`isOpen`/`Convex`/`Nonempty` are immediate from `BraidGeometry`, and monotonicity
`chainConeR_mono` is `starCone_antitone ∘ faceLE_of_chainRefine`.  **This uses NO hypotheses on the
cube beyond what `covectorHeight`/`faceLE_of_chainRefine`/`starCone` already bake in — all
assumption-free.**  It is transported to `Ch(□ⁿ) = ChainCat.Obj (cube n)` along the cube
equivalence `cubeChainRefineEquiv` (`chainCone`, `chainCone_mono`).

## Part 2 — the general run-injective HDA cone (the real target)

For any `K : BPSet` with an edge-labelling `ℓ : EdgeLabelling K A` (an HDA), all chains share the
**common schedule space `A → ℝ`** (a real time per action-label).  A chain `a`'s cone is the set of
schedules compatible with its bead order:

> `hdaCone ℓ a = {t | ∀ e e' : EventObj a, bead e < bead e' → t (evLabel e) < t (evLabel e')}`.

`isOpen`/`Convex` are **UNCONDITIONAL** (a finite intersection of open half-spaces `t α < t β`,
finiteness from `Fintype (EventObj a)`, needing nothing on `A`).  Nonemptiness needs `RunInjective`
(labels must be distinguishable to build a realising schedule).  Monotonicity
`hdaCone_mono` (finer `a` ⟹ `hdaCone a ⊆ hdaCone b`) uses `evLabel_coherent` (label preserved along
refinement, *free* from the concurrency axiom) and `serialWedge_blockIdx_monotone` (bead order
refines, *unconditional*) — its **only** extra input is that `eventMap f` is **surjective**, i.e.
that `a` and `b` use the *same* label set.  `hdaCone_mono_of_card` discharges surjectivity from
`RunInjective` (⟹ `eventMap` injective) plus equal event counts.

**Key assumption finding.**  `isOpen`/`Convex` need nothing; mono needs `RunInjective` + the
event-count equality `card (EventObj a) = card (EventObj b)` (equivalently `dimSum a = dimSum b`).
**Both `NonSelfLinked` and `AdmitsAltitude` are never used.**  The count-equality *along a
refinement* is now `dimSum_eq_of_hom` (Deliverable A, below), proved **unconditionally** from the
serial wedge's own altitude (`serialWedge_dimSum_eq`, `ChainSkeletal`); so `hdaCone_mono_run` needs
only `RunInjective`.  (The *global* `ConstEventCount` — all chains equal — is a strictly stronger,
and in general *false*, statement that is not needed; see `ScheduleSpace.lean`.)

-/

open CategoryTheory Opposite CubeChain

namespace FinalBraid

/-! ## Part 1 — the cube instance (assumption-free) -/

section Cube

variable {n : ℕ}

/-- **The realisable-schedule cone of a cube chain** (on the `RefineObj` side): the open star cone
of its ordered-set-partition covector `braidSign (covectorHeight x)`, in the timing space
`Fin n → ℝ`.  Assumption-free. -/
noncomputable def chainConeR (x : RefineObj (BPSet.cube n).init (BPSet.cube n).final) :
    Set (Fin n → ℝ) :=
  starCone (braidSign (covectorHeight x))

/-- The cube-chain cone is open (Phase 1). -/
theorem isOpen_chainConeR (x : RefineObj (BPSet.cube n).init (BPSet.cube n).final) :
    IsOpen (chainConeR x) :=
  isOpen_starCone _

/-- The cube-chain cone is convex (Phase 1). -/
theorem convex_chainConeR (x : RefineObj (BPSet.cube n).init (BPSet.cube n).final) :
    Convex ℝ (chainConeR x) :=
  convex_starCone _

/-- The cube-chain cone is nonempty (realizability, Phase 1): witnessed by the integer timing
`i ↦ (covectorHeight x i : ℝ)`. -/
theorem chainConeR_nonempty (x : RefineObj (BPSet.cube n).init (BPSet.cube n).final) :
    (chainConeR x).Nonempty :=
  starCone_nonempty_of_braidSign _

/-- **Monotonicity (cube, `RefineObj`).**  A refinement `f : x ⟶ y` (`x` finer) gives
`chainConeR x ⊆ chainConeR y`: finer chain ⟹ finer covector (`faceLE_of_chainRefine`) ⟹ smaller
star cone (`starCone_antitone`).  Assumption-free. -/
theorem chainConeR_mono {x y : RefineObj (BPSet.cube n).init (BPSet.cube n).final} (f : x ⟶ y) :
    chainConeR x ⊆ chainConeR y :=
  starCone_antitone (faceLE_of_chainRefine y x f)

/-- **The realisable-schedule cone of a cube chain** (on the `Ch(□ⁿ)` side), transported along the
cube equivalence `cubeChainRefineEquiv`. -/
noncomputable def chainCone (a : ChainCat.Obj (BPSet.cube n)) : Set (Fin n → ℝ) :=
  chainConeR ((cubeChainRefineEquiv n).inverse.obj a)

/-- `chainCone a` is open. -/
theorem isOpen_chainCone (a : ChainCat.Obj (BPSet.cube n)) : IsOpen (chainCone a) :=
  isOpen_chainConeR _

/-- `chainCone a` is convex. -/
theorem convex_chainCone (a : ChainCat.Obj (BPSet.cube n)) : Convex ℝ (chainCone a) :=
  convex_chainConeR _

/-- `chainCone a` is nonempty. -/
theorem chainCone_nonempty (a : ChainCat.Obj (BPSet.cube n)) : (chainCone a).Nonempty :=
  chainConeR_nonempty _

/-- **Monotonicity (cube, `Ch(□ⁿ)`).**  A refinement `f : a ⟶ b` (`a` finer) gives
`chainCone a ⊆ chainCone b`, by transporting `f` through the cube equivalence and applying
`chainConeR_mono`. -/
theorem chainCone_mono {a b : ChainCat.Obj (BPSet.cube n)} (f : a ⟶ b) :
    chainCone a ⊆ chainCone b :=
  chainConeR_mono ((cubeChainRefineEquiv n).inverse.map f)

end Cube

/-! ## Part 2 — the general run-injective HDA cone -/

section HDA

open HDA

variable {K : BPSet} {A : Type}

/-- The coordinate-difference functional `t ↦ t α − t β` on `A → ℝ` is `ℝ`-linear. -/
theorem isLinear_evalSub (α β : A) : IsLinearMap ℝ (fun t : A → ℝ => t α - t β) where
  map_add x y := by simp only [Pi.add_apply]; ring
  map_smul c x := by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- The strict-comparison set `{t | t α < t β}` is open. -/
theorem isOpen_evalLt (α β : A) : IsOpen {t : A → ℝ | t α < t β} :=
  isOpen_lt (continuous_apply α) (continuous_apply β)

/-- The strict-comparison set `{t | t α < t β}` is convex (an open half-space). -/
theorem convex_evalLt (α β : A) : Convex ℝ {t : A → ℝ | t α < t β} := by
  have h : {t : A → ℝ | t α < t β} = {t : A → ℝ | (fun t : A → ℝ => t α - t β) t < 0} := by
    ext t; simp only [Set.mem_setOf_eq, sub_neg]
  rw [h]; exact convex_halfSpace_lt (isLinear_evalSub α β) 0

/-- **The realisable-schedule cone of an HDA chain.**  In the common schedule space `A → ℝ` (a real
time per label), the schedules honouring the bead order of `a`: for events `e, e'` whose beads
satisfy `bead e < bead e'`, the label of `e` must be scheduled strictly before that of `e'`. -/
noncomputable def hdaCone (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) : Set (A → ℝ) :=
  {t | ∀ e e' : EventObj a, (e.1 : ℕ) < (e'.1 : ℕ) →
    t (evLabel ℓ ⟨a, e⟩) < t (evLabel ℓ ⟨a, e'⟩)}

/-- Rewrite the HDA cone as a finite intersection of per-event-pair constraints. -/
theorem hdaCone_eq_iInter (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) :
    hdaCone ℓ a = ⋂ p : EventObj a × EventObj a,
      {t : A → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) →
        t (evLabel ℓ ⟨a, p.1⟩) < t (evLabel ℓ ⟨a, p.2⟩)} := by
  ext t
  simp only [hdaCone, Set.mem_setOf_eq, Set.mem_iInter, Prod.forall]

/-- **The HDA cone is open — UNCONDITIONAL.**  A finite intersection (over the finite event-pair
set) of open half-spaces `t α < t β`; needs nothing on the alphabet `A`. -/
theorem isOpen_hdaCone (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) : IsOpen (hdaCone ℓ a) := by
  rw [hdaCone_eq_iInter]
  refine isOpen_iInter_of_finite (fun p => ?_)
  by_cases h : (p.1.1 : ℕ) < (p.2.1 : ℕ)
  · rw [show {t : A → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) →
          t (evLabel ℓ ⟨a, p.1⟩) < t (evLabel ℓ ⟨a, p.2⟩)}
        = {t : A → ℝ | t (evLabel ℓ ⟨a, p.1⟩) < t (evLabel ℓ ⟨a, p.2⟩)} from
      Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
    exact isOpen_evalLt _ _
  · rw [show {t : A → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) →
          t (evLabel ℓ ⟨a, p.1⟩) < t (evLabel ℓ ⟨a, p.2⟩)} = Set.univ from
      Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd H h⟩]
    exact isOpen_univ

/-- **The HDA cone is convex — UNCONDITIONAL.**  A finite intersection of convex half-spaces. -/
theorem convex_hdaCone (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) : Convex ℝ (hdaCone ℓ a) := by
  rw [hdaCone_eq_iInter]
  refine convex_iInter (fun p => ?_)
  by_cases h : (p.1.1 : ℕ) < (p.2.1 : ℕ)
  · rw [show {t : A → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) →
          t (evLabel ℓ ⟨a, p.1⟩) < t (evLabel ℓ ⟨a, p.2⟩)}
        = {t : A → ℝ | t (evLabel ℓ ⟨a, p.1⟩) < t (evLabel ℓ ⟨a, p.2⟩)} from
      Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
    exact convex_evalLt _ _
  · rw [show {t : A → ℝ | (p.1.1 : ℕ) < (p.2.1 : ℕ) →
          t (evLabel ℓ ⟨a, p.1⟩) < t (evLabel ℓ ⟨a, p.2⟩)} = Set.univ from
      Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd H h⟩]
    exact convex_univ

/-- **The HDA cone is nonempty (realizability) — needs `RunInjective`.**  Schedule each label by the
bead index of its (unique, by `RunInjective`) event; unused labels get `0`.  This honours every
bead-order constraint. -/
theorem hdaCone_nonempty (ℓ : EdgeLabelling K A) (h : RunInjective ℓ) (a : ChainCat.Obj K) :
    (hdaCone ℓ a).Nonempty := by
  classical
  refine ⟨fun α => if he : ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = α
      then ((he.choose.1 : ℕ) : ℝ) else 0, fun e e' hlt => ?_⟩
  have hval : ∀ e₀ : EventObj a,
      (if he : ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = evLabel ℓ ⟨a, e₀⟩
        then ((he.choose.1 : ℕ) : ℝ) else 0) = ((e₀.1 : ℕ) : ℝ) := by
    intro e₀
    have hp : ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = evLabel ℓ ⟨a, e₀⟩ := ⟨e₀, rfl⟩
    rw [dif_pos hp, (h a hp.choose_spec : hp.choose = e₀)]
  simp only []
  rw [hval e, hval e']
  exact_mod_cast hlt

/-- **Monotonicity of the HDA cone, given surjectivity of the event transition.**  For a refinement
`f : a ⟶ b` (`a` finer) whose `eventMap f` is surjective (`a` and `b` use the same labels),
`hdaCone a ⊆ hdaCone b`.  Uses only `evLabel_coherent` (free) and `serialWedge_blockIdx_monotone`
(unconditional). -/
theorem hdaCone_mono (ℓ : EdgeLabelling K A) {a b : ChainCat.Obj K} (f : a ⟶ b)
    (hsurj : Function.Surjective (eventMap f)) :
    hdaCone ℓ a ⊆ hdaCone ℓ b := by
  intro t ht eb eb' hlt
  obtain ⟨ea, rfl⟩ := hsurj eb
  obtain ⟨ea', rfl⟩ := hsurj eb'
  rw [evLabel_coherent ℓ f ea, evLabel_coherent ℓ f ea']
  refine ht ea ea' ?_
  have hmono : Monotone (blockIdx f.φ.hom) :=
    serialWedge_blockIdx_monotone f.φ.hom f.φ.app_init
  have hlt' : (blockIdx f.φ.hom ea.1 : ℕ) < (blockIdx f.φ.hom ea'.1 : ℕ) := hlt
  by_contra hcon
  rw [not_lt] at hcon
  have hle : ea'.1 ≤ ea.1 := hcon
  have hb := Fin.le_def.mp (hmono hle)
  omega

/-- **Monotonicity of the HDA cone from `RunInjective` + equal event counts.**  `RunInjective` gives
a globally coherent naming (`hasGlobalEventNaming_of_labelling`), hence every `eventMap f` is
injective (`eventMap_injective`); with equal (finite) event counts it is bijective, so surjective,
and `hdaCone_mono` applies.  **`NonSelfLinked` is not used.** -/
theorem hdaCone_mono_of_card (ℓ : EdgeLabelling K A) (h : RunInjective ℓ)
    {a b : ChainCat.Obj K} (f : a ⟶ b)
    (hcard : Fintype.card (EventObj a) = Fintype.card (EventObj b)) :
    hdaCone ℓ a ⊆ hdaCone ℓ b := by
  have hfi : EventFiberInjective K :=
    (hasGlobalEventNaming_iff K).mp (hasGlobalEventNaming_of_labelling ℓ h)
  have hbij : Function.Bijective (eventMap f) :=
    (Fintype.bijective_iff_injective_and_card (eventMap f)).mpr
      ⟨eventMap_injective hfi f, hcard⟩
  exact hdaCone_mono ℓ f hbij.surjective

/-! ### Dimension-sum preservation ⟹ constant event count *along a refinement* (unconditional)

Deliverable A.  `dimSum a := Σ (bead dims)` is preserved along **any** refinement `f : a ⟶ b`
(`dimSum_eq_of_hom`, from the serial wedge's own altitude — `serialWedge_dimSum_eq`, no
`AdmitsAltitude`, no `NonSelfLinked`).  Since `card (EventObj a) = dimSum a`, the event counts of a
chain and *any coarsening it maps to* agree, discharging `hdaCone_mono_of_card` without the global
`ConstEventCount` (which is *false* for a disconnected `Ch(K)` — see `ScheduleSpace.lean`). -/

/-- **Deliverable A — `dimSum` is preserved along every refinement, unconditionally.**  A refinement
`f : a ⟶ b` has `f.φ : serialWedge a.dims ⟶ serialWedge b.dims`, so `serialWedge_dimSum_eq` gives
`Σ a.dims = Σ b.dims`.  Uses only the serial wedge's intrinsic altitude — **no `AdmitsAltitude`, no
`NonSelfLinked`.** -/
theorem dimSum_eq_of_hom {a b : ChainCat.Obj K} (f : a ⟶ b) : dimSum a = dimSum b :=
  serialWedge_dimSum_eq f.φ

/-- **Equal event count along a refinement (unconditional).**  `card (EventObj a) = card (EventObj
b)` for a coarsening `f : a ⟶ b`, via `eventObj_card` + `dimSum_eq_of_hom`. -/
theorem card_eventObj_eq_of_hom {a b : ChainCat.Obj K} (f : a ⟶ b) :
    Fintype.card (EventObj a) = Fintype.card (EventObj b) := by
  rw [eventObj_card, eventObj_card, dimSum_eq_of_hom f]

/-- **Cone inclusion along a coarsening — costs only `RunInjective`.**  The unconditional
replacement for `hdaCone_mono_const`: the event-count equality `hdaCone_mono_of_card` needs is from
`card_eventObj_eq_of_hom` (Deliverable A), so no `ConstEventCount`/altitude is consumed. -/
theorem hdaCone_mono_run (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    {a b : ChainCat.Obj K} (f : a ⟶ b) : hdaCone ℓ a ⊆ hdaCone ℓ b :=
  hdaCone_mono_of_card ℓ hrun f (card_eventObj_eq_of_hom f)

end HDA

end FinalBraid
