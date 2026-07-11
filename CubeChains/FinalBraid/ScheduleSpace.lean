import CubeChains.FinalBraid.ChainCone
import CubeChains.FinalBraid.ChainSkeletal
import Mathlib.Order.GaloisConnection.Basic

/-!
# FinalBraid/ScheduleSpace — the schedule space, its cover, and the Galois connection (Phase 3)

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
in it) is the only Part-2 statement that consumes hypotheses (`RunInjective` + `AdmitsAltitude`, via
the cone inclusion of Part 3) — kept separate so the core `GaloisConnection` stays assumption-free.

## 3 — the maximal-chain cover (where altitude first bites)

`scheduleSpace_eq_maximal_cover` proves `scheduleSpace ℓ = ⋃_{b maximal} hdaCone ℓ b` from **three**
explicit inputs, deliberately factored to expose exactly what each costs:

* `RunInjective ℓ` and `ConstEventCount K` — needed for the **cone inclusion** `hdaCone_mono_const`
  along a coarsening `a ⟶ b`.  `hdaCone_mono_of_card` (Phase 2) needs `eventMap f` surjective; the
  only *formalized* discharge is bijectivity from `RunInjective` + equal event counts, i.e.
  `ConstEventCount K : ∀ a b, card (EventObj a) = card (EventObj b)` — the *minimal actual*
  hypothesis the proof consumes, so it is taken abstractly.  **`ConstEventCount` is discharged by
  `K.AdmitsAltitude`** through `EventInduction.chainDimSum_eq` (`dimSum ≡ alt final − alt init`,
  chain-independent) + `eventObj_card`; that file **cannot be co-imported here** — it re-declares
  the `eventObjFintype` instance that `ChainCone → EventLocalSystem` already provides (the branch
  split `ChainCone` documents), so the altitude discharge is recorded, not wired in.  Mathematically
  the count equality along a *single* refinement is even a local `dimSum`-invariance, altitude-free,
  but no local version is formalized.  **`NonSelfLinked` is never used.**
* `HasMaxCoarsening K` — the **finiteness** input: every chain coarsens up to a maximal one.  This
  is a well-foundedness fact (a proper coarsening strictly drops the bead count `dims.length`,
  bounded below by `1`; `Ch(K)` is unconditionally skeletal by `ChainCat.eq_of_hom_hom`),
  *plausibly altitude-free*, but is **not** formalized here — it is taken as a hypothesis so the
  residual gap is named precisely.  The cover proof uses only reachability, not maximality.

## 4 — the nerve equivalence (target, NOT proved)

`IsGoodConeCover` records (and `hdaCone_isGoodCover` proves) that the cones form a good cover — all
open, all convex.  The conjecture `|N(Ch K)| ≃ scheduleSpace ℓ` (Ziemiański's directed path space
`P⃗(K)`) is the nerve lemma applied to this good cover; there is no nerve lemma / homotopy colimit
in current mathlib, so it is recorded in prose only, not proved (no `sorry`).  Cite Ziemiański,
"Spaces of directed paths on pre-cubical sets" (arXiv:1901.05206).

**Layer:** FinalBraid.  Not part of the default `CubeChains` target.
**Build:** `lake build CubeChains.FinalBraid.ScheduleSpace`.
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

/-- **Chains all carry the same number of events** (the minimal actual input to the cone inclusion).
`hdaCone_mono_of_card` needs `card (EventObj a) = card (EventObj b)`; this is exactly that,
uniformly.  **Discharged by `K.AdmitsAltitude`** (`EventInduction.chainDimSum_eq` +
`eventObj_card` — `dimSum` is the chain-independent altitude span), which cannot be co-imported here
(it re-declares `eventObjFintype`), so we take the count equality itself as the hypothesis. -/
def ConstEventCount (K : BPSet) : Prop :=
  ∀ a b : ChainCat.Obj K, Fintype.card (EventObj a) = Fintype.card (EventObj b)

/-- **Cone inclusion along a coarsening — costs `RunInjective` + `ConstEventCount`.**  For any
refinement `f : a ⟶ b` (`a` finer), `hdaCone ℓ a ⊆ hdaCone ℓ b`.  Discharges the surjectivity
hypothesis of `hdaCone_mono_of_card` via the uniform event-count equality. -/
theorem hdaCone_mono_const (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    (hcount : ConstEventCount K) {a b : ChainCat.Obj K} (f : a ⟶ b) :
    hdaCone ℓ a ⊆ hdaCone ℓ b :=
  hdaCone_mono_of_card ℓ hrun f (hcount a b)

/-- **`chainsIn W` is refinement-closed (down-set) — costs `RunInjective` + `ConstEventCount`.**  If
`a`'s cone lies in `W` and `g : b ⟶ a` refines `a` (`b` finer), then `b`'s cone
(`⊆ hdaCone ℓ a ⊆ W`) also lies in `W`.  Optional; isolated so the core Galois connection stays
assumption-free. -/
theorem chainsIn_refine_closed (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    (hcount : ConstEventCount K) {W : Set (A → ℝ)} {a b : ChainCat.Obj K} (g : b ⟶ a)
    (ha : a ∈ chainsIn ℓ W) : b ∈ chainsIn ℓ W :=
  subset_trans (hdaCone_mono_const ℓ hrun hcount g) ha

/-- **A maximal (coarsest) chain**: one admitting no *proper* coarsening — every refinement `b ⟶ c`
out of it is an isomorphism.  (`Ch(K)` is unconditionally skeletal, `ChainCat.eq_of_hom_hom`, so
this is genuine maximality in the coarsening order.) -/
def IsMaxChain (b : ChainCat.Obj K) : Prop :=
  ∀ ⦃c : ChainCat.Obj K⦄ (g : b ⟶ c), IsIso g

/-- **Finiteness input: every chain coarsens up to a maximal one.**  A proper coarsening strictly
drops the bead count `dims.length` (bounded below by `1`), so iterating terminates at a maximal
chain.  This well-foundedness is *plausibly altitude-free* but is **not** formalized here — it is
the lone finiteness hypothesis, taken abstractly so the residual gap is named exactly. -/
def HasMaxCoarsening (K : BPSet) : Prop :=
  ∀ a : ChainCat.Obj K, ∃ b : ChainCat.Obj K, IsMaxChain b ∧ Nonempty (a ⟶ b)

/-- **Every maximal cone sits inside the schedule space — assumption-free.**  Trivial: a maximal
chain is a chain, so its cone is one of the union's members. -/
theorem maximalCover_subset_scheduleSpace (ℓ : EdgeLabelling K A) :
    ⋃ b ∈ {b : ChainCat.Obj K | IsMaxChain b}, hdaCone ℓ b ⊆ scheduleSpace ℓ :=
  Set.iUnion₂_subset (fun b _ => Set.subset_iUnion (fun a => hdaCone ℓ a) b)

/-- **The maximal-chain cover.**  `scheduleSpace ℓ = ⋃_{b maximal} hdaCone ℓ b`.

Assumption cost (the Phase-3 deliverable): the equality consumes exactly
* `RunInjective ℓ` **and** `ConstEventCount K` — for the cone inclusion `hdaCone_mono_const` along
  the coarsening.  `ConstEventCount` is the *first* load-bearing consequence of altitude: it is
  discharged by `K.AdmitsAltitude` (`EventInduction.chainDimSum_eq`), recorded on `ConstEventCount`
  since that file cannot be co-imported (the `eventObjFintype` clash).
* `HasMaxCoarsening K` — the finiteness that every chain reaches a maximal one.

The proof uses only the *reachability* half of `HasMaxCoarsening` (a morphism `a ⟶ b`), not the
maximality predicate itself; `IsMaxChain` fixes the intended index set of the cover.
**`NonSelfLinked` is not used anywhere.** -/
theorem scheduleSpace_eq_maximal_cover (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    (hcount : ConstEventCount K) (hmax : HasMaxCoarsening K) :
    scheduleSpace ℓ = ⋃ b ∈ {b : ChainCat.Obj K | IsMaxChain b}, hdaCone ℓ b := by
  apply subset_antisymm
  · intro t ht
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
    obtain ⟨b, hbmax, ⟨f⟩⟩ := hmax a
    exact Set.mem_iUnion₂.mpr ⟨b, hbmax, hdaCone_mono_const ℓ hrun hcount f ha⟩
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

end Nerve

end FinalBraid
