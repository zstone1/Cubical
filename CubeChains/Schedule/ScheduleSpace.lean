import CubeChains.Schedule.ChainCone
import CubeChains.Chains.ChainSkeletal
import Mathlib.Order.GaloisConnection.Basic

/-!
# Schedule/ScheduleSpace — the schedule space, its cover, and the Galois connection (Phase 3)

Phase 3 of the *timing geometry* program.  Phase 2 (`ChainCone.lean`) sent each cube chain to the
**open convex cone** `hdaCone ℓ a` of schedules that realise it.  Phase 3 assembles the cones into
the **schedule space** and studies its combinatorics:

## 1 — the schedule space (assumption-free)

`scheduleSpace ℓ = ⋃ a, hdaCone ℓ a`, the union over *all* chains of their cones.  It is **open**
(`isOpen_scheduleSpace`) as a union of opens — needing nothing but the labelling.  The cube version
`scheduleSpaceCube n = ⋃ a, chainCone a` and its openness are recorded too.

## 2 — the Galois connection (the centerpiece, assumption-free)

Between subsets of chains (`Set (ChainCat.Obj K)`, `⊆`) and subsets of the schedule space
(`Set (A → ℝ)`, `⊆`):

* `coneUnion ℓ I = ⋃ a ∈ I, hdaCone ℓ a` — the left adjoint `L`;
* `chainsIn ℓ W = {a | hdaCone ℓ a ⊆ W}` — the right adjoint `R`;
* `gc_coneUnion_chainsIn : GaloisConnection (coneUnion ℓ) (chainsIn ℓ)` — pure order theory,
  `⋃_{a∈I} O_a ⊆ W ↔ ∀ a ∈ I, O_a ⊆ W ↔ I ⊆ {a | O_a ⊆ W}`.  **Assumption-free.**

The induced closure/coreflection are then free from mathlib's `GaloisConnection` API.  The
*optional* down-set fact `chainsIn_refine_closed` (a refinement of a chain in `chainsIn W` is again
in it) is the only Part-2 statement that consumes a hypothesis — now just `RunInjective` (via the
unconditional cone inclusion of Part 3) — kept separate so the core `GaloisConnection` stays
assumption-free.

## 3 — the maximal-chain cover (UNCONDITIONAL, from `RunInjective` alone)

`scheduleSpace_eq_maximal_cover` proves `scheduleSpace ℓ = ⋃_{b maximal} hdaCone ℓ b` from **only**
`RunInjective ℓ`.  The two inputs that were once taken as hypotheses are now theorems:

* **Cone inclusion** `hdaCone_mono_run` along a coarsening `a ⟶ b` needs `eventMap f` surjective;
  that follows from `RunInjective` + the *per-refinement* event-count equality
  `card_eventObj_eq_of_hom` (Deliverable A), which is `dimSum a = dimSum b` — proved
  **unconditionally** from the serial wedge's *own* altitude (`serialWedge_dimSum_eq`, `ChainCone`).
  The global `ConstEventCount K` (all chains equal count) is **NOT used** — indeed it is *false* for
  a disconnected `Ch(K)` (see the `ConstEventCount` docstring); only the per-refinement version is
  needed, and it needs no altitude.
* **Finiteness** `hasMaxCoarsening K` (Deliverable B): every chain coarsens to a maximal one, by
  strong induction on the bead count — a proper coarsening strictly drops `dims.length`
  (`ChainCat.lt_dims_length_of_not_isIso`, from `blockIdx` surjectivity + serial-wedge rigidity).

**Neither `NonSelfLinked` nor `AdmitsAltitude` appears anywhere.**

## 4 — the nerve equivalence (target, NOT proved)

`IsGoodConeCover`/`hdaCone_isGoodCover` prove the cones form a good cover (open, convex), and
`maximalChains_goodCover` (Deliverable C headline) packages the maximal-chain good cover: it covers
`scheduleSpace ℓ`, each cone is open+convex, and finite intersections are open+convex.  The
conjecture `|N(Ch K)| ≃ scheduleSpace ℓ` (Ziemiański's directed path space `P⃗(K)`) is the nerve
lemma applied to this good cover; there is no nerve lemma / homotopy colimit in current mathlib, so
it is recorded in prose only, not proved (no `sorry`).  Cite Ziemiański, "Spaces of directed paths
on pre-cubical sets" (arXiv:1901.05206).

-/

open CategoryTheory Opposite Set

namespace FinalBraid

open HDA

/-! ## Part 1 — the schedule space -/

section ScheduleSpace

variable {K : BPSet} {A : Type}

/-- **The schedule space of an HDA.**  In the common timing space `A → ℝ`, the union over *all* cube
chains of their realisable-schedule cones: a schedule is realisable iff it realises *some* chain. -/
noncomputable def scheduleSpace (ℓ : EdgeLabelling K A) : Set (A → ℝ) :=
  ⋃ a : ChainCat.Obj K, hdaCone ℓ a

/-- **The schedule space is open — assumption-free.**  A union of the open cones `hdaCone ℓ a`
(`isOpen_hdaCone`); needs nothing beyond the labelling. -/
theorem isOpen_scheduleSpace (ℓ : EdgeLabelling K A) : IsOpen (scheduleSpace ℓ) :=
  isOpen_iUnion (fun a => isOpen_hdaCone ℓ a)

/-- **The cube schedule space** `U = ⋃ a, chainCone a` in `Fin n → ℝ`, the union of the cube-chain
star cones.  Needs no labelling. -/
noncomputable def scheduleSpaceCube (n : ℕ) : Set (Fin n → ℝ) :=
  ⋃ a : ChainCat.Obj (BPSet.cube n), chainCone a

/-- **The cube schedule space is open** — a union of the open cones `chainCone a`. -/
theorem isOpen_scheduleSpaceCube (n : ℕ) : IsOpen (scheduleSpaceCube n) :=
  isOpen_iUnion (fun a => isOpen_chainCone a)

end ScheduleSpace

/-! ## Part 2 — the Galois connection -/

section Galois

variable {K : BPSet} {A : Type}

/-- **Left adjoint `L`.**  The union of the cones of a *set* `I` of chains. -/
noncomputable def coneUnion (ℓ : EdgeLabelling K A) (I : Set (ChainCat.Obj K)) : Set (A → ℝ) :=
  ⋃ a ∈ I, hdaCone ℓ a

/-- **Right adjoint `R`.**  The chains whose cone is contained in a schedule set `W`. -/
def chainsIn (ℓ : EdgeLabelling K A) (W : Set (A → ℝ)) : Set (ChainCat.Obj K) :=
  {a | hdaCone ℓ a ⊆ W}

/-- The schedule space is the left adjoint applied to *all* chains. -/
theorem scheduleSpace_eq_coneUnion_univ (ℓ : EdgeLabelling K A) :
    scheduleSpace ℓ = coneUnion ℓ Set.univ := by
  ext t; simp only [scheduleSpace, coneUnion, Set.mem_iUnion, Set.mem_univ, exists_prop, true_and]

/-- **The Galois connection (the centerpiece) — assumption-free.**  `coneUnion ℓ ⊣ chainsIn ℓ`:
`coneUnion ℓ I ⊆ W ↔ I ⊆ chainsIn ℓ W`.  Pure order theory (`Set.iUnion₂_subset_iff`); needs
nothing on `K`, `A`, or `ℓ`. -/
theorem gc_coneUnion_chainsIn (ℓ : EdgeLabelling K A) :
    GaloisConnection (coneUnion ℓ) (chainsIn ℓ) := fun I W => by
  change coneUnion ℓ I ⊆ W ↔ I ⊆ chainsIn ℓ W
  rw [coneUnion, Set.iUnion₂_subset_iff]
  exact Iff.rfl

/-- **The induced closure operator** `chainsIn ∘ coneUnion` is monotone, inflationary and idempotent
(from `gc_coneUnion_chainsIn`).  Recorded via mathlib's `GaloisConnection.closureOperator`. -/
noncomputable def coneClosure (ℓ : EdgeLabelling K A) :
    ClosureOperator (Set (ChainCat.Obj K)) :=
  (gc_coneUnion_chainsIn ℓ).closureOperator

end Galois

/-! ## Part 3 — the maximal-chain cover (assumption mapping) -/

section MaximalCover

variable {K : BPSet} {A : Type}

/-- **`chainsIn W` is refinement-closed (down-set) — costs only `RunInjective`.**  If `a`'s cone
lies in `W` and `g : b ⟶ a` refines `a` (`b` finer), then `b`'s cone (`⊆ hdaCone ℓ a ⊆ W`) also lies
in `W`.  Now unconditional via `hdaCone_mono_run` (Deliverable A); isolated so the core Galois
connection stays assumption-free. -/
theorem chainsIn_refine_closed (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    {W : Set (A → ℝ)} {a b : ChainCat.Obj K} (g : b ⟶ a)
    (ha : a ∈ chainsIn ℓ W) : b ∈ chainsIn ℓ W :=
  subset_trans (hdaCone_mono_run ℓ hrun g) ha

/-- **A maximal (coarsest) chain**: one admitting no *proper* coarsening — every refinement `b ⟶ c`
out of it is an isomorphism.  (`Ch(K)` is unconditionally skeletal, `ChainCat.eq_of_hom_hom`, so
this is genuine maximality in the coarsening order.) -/
def IsMaxChain (b : ChainCat.Obj K) : Prop :=
  ∀ ⦃c : ChainCat.Obj K⦄ (g : b ⟶ c), IsIso g

/-- **Finiteness input: every chain coarsens up to a maximal one.**  A proper coarsening strictly
drops the bead count `dims.length`, so iterating terminates at a maximal chain. -/
def HasMaxCoarsening (K : BPSet) : Prop :=
  ∀ a : ChainCat.Obj K, ∃ b : ChainCat.Obj K, IsMaxChain b ∧ Nonempty (a ⟶ b)

/-- **Deliverable B — `HasMaxCoarsening` holds unconditionally.**  Strong induction on the bead
count `a.dims.length`: if `a` is not maximal it admits a *proper* coarsening `g : a ⟶ c` (a
non-isomorphism), which strictly drops the bead count (`ChainCat.lt_dims_length_of_not_isIso`, from
`blockIdx` surjectivity + serial-wedge rigidity — **no `AdmitsAltitude`, no `NonSelfLinked`**); the
induction hypothesis on `c` supplies a maximal coarsening, reached from `a` through `g`. -/
theorem hasMaxCoarsening (K : BPSet) : HasMaxCoarsening K := by
  have key : ∀ n, ∀ a : ChainCat.Obj K, a.dims.length = n →
      ∃ b : ChainCat.Obj K, IsMaxChain b ∧ Nonempty (a ⟶ b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro a hn
      by_cases hmax : IsMaxChain a
      · exact ⟨a, hmax, ⟨𝟙 a⟩⟩
      · have hex : ∃ (c : ChainCat.Obj K) (g : a ⟶ c), ¬ IsIso g := by
          by_contra hcon
          simp only [not_exists, not_not] at hcon
          exact hmax fun c g => hcon c g
        obtain ⟨c, g, hg⟩ := hex
        have hlt : c.dims.length < n := hn ▸ ChainCat.lt_dims_length_of_not_isIso g hg
        obtain ⟨m, hm, ⟨fcm⟩⟩ := IH c.dims.length hlt c rfl
        exact ⟨m, hm, ⟨g ≫ fcm⟩⟩
  exact fun a => key a.dims.length a rfl

/-- **Every maximal cone sits inside the schedule space — assumption-free.**  Trivial: a maximal
chain is a chain, so its cone is one of the union's members. -/
theorem maximalCover_subset_scheduleSpace (ℓ : EdgeLabelling K A) :
    ⋃ b ∈ {b : ChainCat.Obj K | IsMaxChain b}, hdaCone ℓ b ⊆ scheduleSpace ℓ :=
  Set.iUnion₂_subset (fun b _ => Set.subset_iUnion (fun a => hdaCone ℓ a) b)

/-- **The maximal-chain cover — Deliverable C, needing only `RunInjective`.**
`scheduleSpace ℓ = ⋃_{b maximal} hdaCone ℓ b`.

The two former hypotheses are now discharged internally and unconditionally:
* the cone inclusion `hdaCone_mono_run` (from `card_eventObj_eq_of_hom` = Deliverable A) replaces
  the `ConstEventCount`-based `hdaCone_mono_const` — no altitude;
* `hasMaxCoarsening K` (Deliverable B) supplies a maximal coarsening of each chain — no altitude.

The proof uses only the *reachability* half of `hasMaxCoarsening` (a morphism `a ⟶ b`), not the
maximality predicate itself; `IsMaxChain` fixes the intended index set of the cover.
**Neither `NonSelfLinked` nor `AdmitsAltitude` is used.** -/
theorem scheduleSpace_eq_maximal_cover (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) :
    scheduleSpace ℓ = ⋃ b ∈ {b : ChainCat.Obj K | IsMaxChain b}, hdaCone ℓ b := by
  apply subset_antisymm
  · intro t ht
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
    obtain ⟨b, hbmax, ⟨f⟩⟩ := hasMaxCoarsening K a
    exact Set.mem_iUnion₂.mpr ⟨b, hbmax, hdaCone_mono_run ℓ hrun f ha⟩
  · exact maximalCover_subset_scheduleSpace ℓ

end MaximalCover

/-! ## Part 4 — the nerve equivalence (target, NOT proved)

**Conjecture (Ziemiański, arXiv:1901.05206).**  For an HDA `(K, ℓ)` there is a homotopy equivalence
`|N(Ch K)| ≃ scheduleSpace ℓ`, and the right-hand side is Ziemiański's space of directed paths
`P⃗(K)`.  The proof is the **nerve lemma** for the cover `{hdaCone ℓ a}`: it is a *good cover*
(every cone is open and convex — `hdaCone_isGoodCover` below — hence every finite intersection is
open and convex, so empty or contractible), and the nerve of the cover is the poset `Ch(K)`.

There is no nerve lemma / homotopy colimit / geometric realization of a category in current mathlib,
so this conjecture is recorded here in prose only — **not** stated as a `theorem` and **not**
`sorry`-ed.  Only the formalizable hypothesis (good-cover-ness) is proved. -/

section Nerve

variable {K : BPSet} {A : Type}

/-- **Good-cover property.**  Every chain cone is open and convex — the checkable hypothesis of the
nerve lemma that would yield the (unformalizable) equivalence `|N(Ch K)| ≃ scheduleSpace ℓ`. -/
def IsGoodConeCover (ℓ : EdgeLabelling K A) : Prop :=
  ∀ a : ChainCat.Obj K, IsOpen (hdaCone ℓ a) ∧ Convex ℝ (hdaCone ℓ a)

/-- **The chain cones form a good cover — assumption-free.**  `isOpen_hdaCone` + `convex_hdaCone`.
This is the sole formalizable input to the nerve-equivalence conjecture above. -/
theorem hdaCone_isGoodCover (ℓ : EdgeLabelling K A) : IsGoodConeCover ℓ :=
  fun a => ⟨isOpen_hdaCone ℓ a, convex_hdaCone ℓ a⟩

/-- **Deliverable C (headline) — the maximal chains give a good cover of the schedule space, from
`RunInjective` alone.**  For a run-injective HDA `(K, ℓ)` the cones of the *maximal* cube chains

1. **cover** the schedule space: `scheduleSpace ℓ = ⋃_{b maximal} hdaCone ℓ b`
   (`scheduleSpace_eq_maximal_cover`, using Deliverables A + B);
2. are each **open and convex** (`hdaCone_isGoodCover`);
3. have every **finite intersection open and convex** (`isOpen_biInter_finset`, `convex_iInter₂`) —
   hence empty or contractible, the good-cover / nerve hypothesis.

No `ConstEventCount`, no `HasMaxCoarsening` hypothesis, **no `NonSelfLinked`, no `AdmitsAltitude`**;
only the labelling's run-injectivity.

**Deliverable D (note).**  The nerve of this good cover is the poset `Ch(K)`, and the nerve lemma
would give a homotopy equivalence `|N(Ch K)| ≃ scheduleSpace ℓ`, identifying the schedule space with
**Ziemiański's space of directed paths `P⃗(K)`** (arXiv:1901.05206, "Spaces of directed paths on
pre-cubical sets").  Current mathlib has no nerve lemma / homotopy colimit / geometric realization
of a category, so that final equivalence is a citation, not a formalizable statement here. -/
theorem maximalChains_goodCover (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) :
    (scheduleSpace ℓ = ⋃ b ∈ {b : ChainCat.Obj K | IsMaxChain b}, hdaCone ℓ b)
      ∧ (∀ b : ChainCat.Obj K, IsMaxChain b →
          IsOpen (hdaCone ℓ b) ∧ Convex ℝ (hdaCone ℓ b))
      ∧ (∀ I : Finset (ChainCat.Obj K),
          IsOpen (⋂ b ∈ I, hdaCone ℓ b) ∧ Convex ℝ (⋂ b ∈ I, hdaCone ℓ b)) := by
  refine ⟨scheduleSpace_eq_maximal_cover ℓ hrun, fun b _ => hdaCone_isGoodCover ℓ b, fun I => ?_⟩
  exact ⟨isOpen_biInter_finset (fun b _ => isOpen_hdaCone ℓ b),
    convex_iInter₂ (fun b _ => convex_hdaCone ℓ b)⟩

end Nerve

end FinalBraid
