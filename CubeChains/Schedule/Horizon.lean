import CubeChains.Schedule.ScheduleSpace

/-!
# Schedule/Horizon — occurrence signs: which events a schedule actually fires

`hdaCone ℓ a` leaves the labels *unused* by `a` free, so a point of it does not know which events
fired: cones of chains with disjoint event sets meet, and `{a | t ∈ hdaCone ℓ a}` has no least
element.  Fix the time origin as the **horizon** (the end of the run) and read occurrence off the
*sign* of the coordinate:

    t α < 0   α fires, at time `t α`        t α > 0   α never fires

`hdaConeH` is `hdaCone` cut by those signs.  It stays an intersection of open half-spaces, so it is
still open and convex, but now cones of chains with different label sets are **disjoint** and the
occurring set is recoverable from the point (`occursAt_eq`).

The horizon is a basepoint of the time axis, not a letter of `A`: nothing in `EdgeLabelling` /
`EventObj` / `eventMap` / `RunInjective` sees it.  In arrangement terms it is the extra element `ω`
of the braid arrangement on `A ⊔ {ω}` read in the chart `t ω = 0`, where its walls become the
coordinate hyperplanes `t α = 0` — one per event, hence splitting under `A = A_X ⊔ A_Y` and leaving
the wedge/`directSum` story intact.

`Finite A` is needed for openness (not convexity): the "does not fire" clause ranges over the
complement of `a`'s labels.
-/

open CategoryTheory Opposite CubeChain

namespace FinalBraid

open HDA

variable {K : BPSet} {A : Type}

/-- The coordinate functional `t ↦ t α` is `ℝ`-linear. -/
theorem isLinear_coord (α : A) : IsLinearMap ℝ (fun t : A → ℝ => t α) where
  map_add _ _ := rfl
  map_smul _ _ := rfl

/-! ## Occurrence sets -/

/-- The labels a chain fires. -/
def occursSet (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) : Set A :=
  Set.range fun e : EventObj a => evLabel ℓ ⟨a, e⟩

/-- The labels a *schedule* fires: those scheduled before the horizon. -/
def occursAt (t : A → ℝ) : Set A := {α | t α < 0}

theorem mem_occursSet (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) (α : A) :
    α ∈ occursSet ℓ a ↔ ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = α := Iff.rfl

/-- A refinement preserves the label set: `eventMap` is bijective and `evLabel` is coherent. -/
theorem occursSet_eq_of_hom (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    {a b : ChainCat.Obj K} (f : a ⟶ b) : occursSet ℓ a = occursSet ℓ b := by
  have hfi : EventFiberInjective K :=
    (hasGlobalEventNaming_iff K).mp (hasGlobalEventNaming_of_labelling ℓ hrun)
  have hbij : Function.Bijective (eventMap f) :=
    (Fintype.bijective_iff_injective_and_card (eventMap f)).mpr
      ⟨eventMap_injective hfi f, card_eventObj_eq_of_hom f⟩
  ext α
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨eventMap f e, evLabel_coherent ℓ f e⟩
  · rintro ⟨e', rfl⟩
    obtain ⟨e, rfl⟩ := hbij.surjective e'
    exact ⟨e, (evLabel_coherent ℓ f e).symm⟩

/-! ## The horizon cone -/

/-- `hdaCone ℓ a` cut by the occurrence signs: `a`'s labels fire (negative time), the rest do not
(positive time).  The horizon is `0`. -/
def hdaConeH (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) : Set (A → ℝ) :=
  hdaCone ℓ a ∩ {t | ∀ α ∈ occursSet ℓ a, t α < 0} ∩ {t | ∀ α ∉ occursSet ℓ a, 0 < t α}

/-- A schedule in `a`'s cone fires exactly `a`'s labels — the point knows its own event set. -/
theorem occursAt_eq (ℓ : EdgeLabelling K A) {a : ChainCat.Obj K} {t : A → ℝ}
    (ht : t ∈ hdaConeH ℓ a) : occursAt t = occursSet ℓ a := by
  ext α
  refine ⟨fun hα => ?_, fun hα => ht.1.2 α hα⟩
  by_contra hcon
  exact absurd (ht.2 α hcon) (not_lt.mpr (le_of_lt hα))

section Finite

variable [Finite A]

theorem isOpen_hdaConeH (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) :
    IsOpen (hdaConeH ℓ a) := by
  classical
  have h₁ : IsOpen {t : A → ℝ | ∀ α ∈ occursSet ℓ a, t α < 0} := by
    rw [show {t : A → ℝ | ∀ α ∈ occursSet ℓ a, t α < 0}
        = ⋂ α : A, {t : A → ℝ | α ∈ occursSet ℓ a → t α < 0} from
      Set.ext fun t => by simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    refine isOpen_iInter_of_finite (fun α => ?_)
    by_cases h : α ∈ occursSet ℓ a
    · rw [show {t : A → ℝ | α ∈ occursSet ℓ a → t α < 0} = {t : A → ℝ | t α < 0} from
        Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
      exact isOpen_lt (continuous_apply α) continuous_const
    · rw [show {t : A → ℝ | α ∈ occursSet ℓ a → t α < 0} = Set.univ from
        Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd H h⟩]
      exact isOpen_univ
  have h₂ : IsOpen {t : A → ℝ | ∀ α ∉ occursSet ℓ a, 0 < t α} := by
    rw [show {t : A → ℝ | ∀ α ∉ occursSet ℓ a, 0 < t α}
        = ⋂ α : A, {t : A → ℝ | α ∉ occursSet ℓ a → 0 < t α} from
      Set.ext fun t => by simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    refine isOpen_iInter_of_finite (fun α => ?_)
    by_cases h : α ∈ occursSet ℓ a
    · rw [show {t : A → ℝ | α ∉ occursSet ℓ a → 0 < t α} = Set.univ from
        Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd h H⟩]
      exact isOpen_univ
    · rw [show {t : A → ℝ | α ∉ occursSet ℓ a → 0 < t α} = {t : A → ℝ | 0 < t α} from
        Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
      exact isOpen_lt continuous_const (continuous_apply α)
  exact ((isOpen_hdaCone ℓ a).inter h₁).inter h₂

end Finite

theorem convex_hdaConeH (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) :
    Convex ℝ (hdaConeH ℓ a) := by
  classical
  have h₁ : Convex ℝ {t : A → ℝ | ∀ α ∈ occursSet ℓ a, t α < 0} := by
    rw [show {t : A → ℝ | ∀ α ∈ occursSet ℓ a, t α < 0}
        = ⋂ α : A, {t : A → ℝ | α ∈ occursSet ℓ a → t α < 0} from
      Set.ext fun t => by simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    refine convex_iInter (fun α => ?_)
    by_cases h : α ∈ occursSet ℓ a
    · rw [show {t : A → ℝ | α ∈ occursSet ℓ a → t α < 0} = {t : A → ℝ | t α < 0} from
        Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
      exact convex_halfSpace_lt (isLinear_coord α) 0
    · rw [show {t : A → ℝ | α ∈ occursSet ℓ a → t α < 0} = Set.univ from
        Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd H h⟩]
      exact convex_univ
  have h₂ : Convex ℝ {t : A → ℝ | ∀ α ∉ occursSet ℓ a, 0 < t α} := by
    rw [show {t : A → ℝ | ∀ α ∉ occursSet ℓ a, 0 < t α}
        = ⋂ α : A, {t : A → ℝ | α ∉ occursSet ℓ a → 0 < t α} from
      Set.ext fun t => by simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    refine convex_iInter (fun α => ?_)
    by_cases h : α ∈ occursSet ℓ a
    · rw [show {t : A → ℝ | α ∉ occursSet ℓ a → 0 < t α} = Set.univ from
        Set.ext fun t => ⟨fun _ => trivial, fun _ H => absurd h H⟩]
      exact convex_univ
    · rw [show {t : A → ℝ | α ∉ occursSet ℓ a → 0 < t α} = {t : A → ℝ | 0 < t α} from
        Set.ext fun t => ⟨fun H => H h, fun H _ => H⟩]
      exact convex_halfSpace_gt (isLinear_coord α) 0
  exact ((convex_hdaCone ℓ a).inter h₁).inter h₂

/-- Realizability: fire `a`'s events at their bead index, shifted below the horizon; park the rest
at `1`.  `RunInjective` is what makes the label-indexed time well defined. -/
theorem hdaConeH_nonempty (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) (a : ChainCat.Obj K) :
    (hdaConeH ℓ a).Nonempty := by
  classical
  set N : ℝ := (a.dims.length : ℝ) + 1 with hN
  refine ⟨fun α => if he : ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = α
      then ((he.choose.1 : ℕ) : ℝ) - N else 1,
    ⟨⟨fun e e' hlt => ?_, fun α hα => ?_⟩, fun α hα => ?_⟩⟩
  · have hval : ∀ e₀ : EventObj a,
        (if he : ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = evLabel ℓ ⟨a, e₀⟩
          then ((he.choose.1 : ℕ) : ℝ) - N else 1) = ((e₀.1 : ℕ) : ℝ) - N := by
      intro e₀
      have hp : ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = evLabel ℓ ⟨a, e₀⟩ := ⟨e₀, rfl⟩
      rw [dif_pos hp, (hrun a hp.choose_spec : hp.choose = e₀)]
    simp only []
    rw [hval e, hval e']
    have : ((e.1 : ℕ) : ℝ) < ((e'.1 : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  · obtain ⟨e, rfl⟩ := hα
    have hp : ∃ e' : EventObj a, evLabel ℓ ⟨a, e'⟩ = evLabel ℓ ⟨a, e⟩ := ⟨e, rfl⟩
    simp only []
    rw [dif_pos hp]
    have hlt : (hp.choose.1 : ℕ) < a.dims.length := hp.choose.1.isLt
    have : ((hp.choose.1 : ℕ) : ℝ) < (a.dims.length : ℝ) := by exact_mod_cast hlt
    simp only [hN]; linarith
  · simp only []
    rw [dif_neg (show ¬ ∃ e : EventObj a, evLabel ℓ ⟨a, e⟩ = α from fun h => hα h)]
    exact zero_lt_one

/-- Refinement inclusion survives the extra cuts: refinements preserve the label set, so the sign
clauses on both sides are the same. -/
theorem hdaConeH_mono_run (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    {a b : ChainCat.Obj K} (f : a ⟶ b) : hdaConeH ℓ a ⊆ hdaConeH ℓ b := by
  rintro t ⟨⟨hcone, hneg⟩, hpos⟩
  have h : ∀ α, α ∈ occursSet ℓ b ↔ α ∈ occursSet ℓ a := fun α => by
    rw [occursSet_eq_of_hom ℓ hrun f]
  exact ⟨⟨hdaCone_mono_run ℓ hrun f hcone, fun α hα => hneg α ((h α).mp hα)⟩,
    fun α hα => hpos α (fun hmem => hα ((h α).mpr hmem))⟩

/-- Chains with different label sets have **disjoint** cones — the repair the plain `hdaCone` lacks:
a schedule cannot fire two different event sets at once. -/
theorem hdaConeH_disjoint_of_ne (ℓ : EdgeLabelling K A) {a b : ChainCat.Obj K}
    (hne : occursSet ℓ a ≠ occursSet ℓ b) : Disjoint (hdaConeH ℓ a) (hdaConeH ℓ b) := by
  rw [Set.disjoint_left]
  intro t ha hb
  exact hne (((occursAt_eq ℓ ha).symm).trans (occursAt_eq ℓ hb))

/-! ## The cover

The sign cuts remove intersections between chains with *different* label sets and nothing else:
`hdaConeH_iInter_nonempty` rebuilds any old common schedule as a negative one, by translating the
firing coordinates below the horizon (`hdaCone` only sees their differences) and parking the rest at
`1` (`hdaCone` does not constrain them at all).  So the cover's combinatorics is intact where it was
right, and cut exactly where it was wrong. -/

theorem hdaConeH_subset_hdaCone (ℓ : EdgeLabelling K A) (a : ChainCat.Obj K) :
    hdaConeH ℓ a ⊆ hdaCone ℓ a := fun _ ht => ht.1.1

/-- A common schedule of `hdaCone`s with a common label set survives the sign cuts. -/
theorem hdaConeH_iInter_nonempty [Finite A] (ℓ : EdgeLabelling K A)
    {I : Finset (ChainCat.Obj K)} {S : Set A} (hS : ∀ a ∈ I, occursSet ℓ a = S)
    (h : (⋂ a ∈ I, hdaCone ℓ a).Nonempty) : (⋂ a ∈ I, hdaConeH ℓ a).Nonempty := by
  classical
  obtain ⟨t, ht⟩ := h
  obtain ⟨c, hc⟩ := (Set.finite_range t).bddAbove
  have hle : ∀ α : A, t α ≤ c := fun α => hc (Set.mem_range_self α)
  refine ⟨fun α => if α ∈ S then t α - (c + 1) else 1, Set.mem_iInter₂.mpr (fun a ha => ?_)⟩
  have hcone : t ∈ hdaCone ℓ a := Set.mem_iInter₂.mp ht a ha
  have hlab : ∀ e : EventObj a, evLabel ℓ ⟨a, e⟩ ∈ S := by
    intro e; rw [← hS a ha]; exact ⟨e, rfl⟩
  refine ⟨⟨fun e e' hlt => ?_, fun α hα => ?_⟩, fun α hα => ?_⟩
  · simp only [if_pos (hlab e), if_pos (hlab e')]
    exact sub_lt_sub_right (hcone e e' hlt) _
  · rw [hS a ha] at hα
    simp only [if_pos hα]
    linarith [hle α]
  · rw [hS a ha] at hα
    simp only [if_neg hα]
    exact zero_lt_one

/-- The negative schedules of `K`: those firing some chain, with every other label past the
horizon. -/
def scheduleSpaceH (ℓ : EdgeLabelling K A) : Set (A → ℝ) :=
  ⋃ a : ChainCat.Obj K, hdaConeH ℓ a

theorem scheduleSpaceH_subset (ℓ : EdgeLabelling K A) : scheduleSpaceH ℓ ⊆ scheduleSpace ℓ :=
  Set.iUnion_mono (fun a => hdaConeH_subset_hdaCone ℓ a)

theorem isOpen_scheduleSpaceH [Finite A] (ℓ : EdgeLabelling K A) : IsOpen (scheduleSpaceH ℓ) :=
  isOpen_iUnion (fun a => isOpen_hdaConeH ℓ a)

theorem scheduleSpaceH_eq_maximal_cover (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) :
    scheduleSpaceH ℓ = ⋃ b ∈ {b : ChainCat.Obj K | IsMaxChain b}, hdaConeH ℓ b := by
  refine subset_antisymm (fun t ht => ?_)
    (Set.iUnion₂_subset (fun b _ => Set.subset_iUnion (fun a => hdaConeH ℓ a) b))
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
  obtain ⟨b, hbmax, ⟨f⟩⟩ := hasMaxCoarsening K a
  exact Set.mem_iUnion₂.mpr ⟨b, hbmax, hdaConeH_mono_run ℓ hrun f ha⟩

/-- The horizon cones are a good cover of `scheduleSpaceH`: the maximal ones cover it, and every
finite intersection is open and convex, hence empty or contractible. -/
theorem maximalChains_goodCoverH [Finite A] (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) :
    (scheduleSpaceH ℓ = ⋃ b ∈ {b : ChainCat.Obj K | IsMaxChain b}, hdaConeH ℓ b)
      ∧ (∀ I : Finset (ChainCat.Obj K),
          IsOpen (⋂ b ∈ I, hdaConeH ℓ b) ∧ Convex ℝ (⋂ b ∈ I, hdaConeH ℓ b)) :=
  ⟨scheduleSpaceH_eq_maximal_cover ℓ hrun, fun _ =>
    ⟨isOpen_biInter_finset (fun b _ => isOpen_hdaConeH ℓ b),
      convex_iInter₂ (fun b _ => convex_hdaConeH ℓ b)⟩⟩

end FinalBraid
