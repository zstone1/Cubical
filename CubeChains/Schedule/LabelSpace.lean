import CubeChains.Schedule.ChainCone
import CubeChains.Chains.ChainSkeletal
import Mathlib.Order.GaloisConnection.Basic

/-!
# Schedule/LabelSpace — the label-chart image, its cover, and the Galois connection (Phase 3)

**What this file is (and is not).**  `labelSpace ℓ = ⋃ a, labelCone ℓ a` lives in the *label*
ambient `A → ℝ`: it is the **image of the schedule atlas under the label chart**, not the schedule
space.
The schedule space is `Sched K` (`Schedule/Space.lean`), an atlas of braid cones; the label chart
`labelTime` (`Schedule/LabelChart.lean`) maps it into `A → ℝ` and **folds** — schedules of distinct
chains can share a label time.  So `labelSpace` is a lossy image, and it provably has the *wrong
homotopy type* in general (`Testing/TwoSquares.lean`: for a branching `K` the two squares' cones
already contain each other's label times, so `labelSpace ℓ` collapses `S¹` to something
contractible).  It is kept because it is cheap and computable, and because everything below is true
*of the image* — but it is **not** the schedule space, and the nerve target of Part 4 is **false as
stated for branching `K`**.

Phase 3 of the *timing geometry* program.  Phase 2 (`ChainCone.lean`) sent each cube chain to the
**open convex cone** `labelCone ℓ a` of label times that realise it.  Phase 3 assembles the cones:

## 1 — the label space (assumption-free)

`labelSpace ℓ = ⋃ a, labelCone ℓ a`, the union over *all* chains of their cones.  It is **open**
(`isOpen_labelSpace`) as a union of opens — needing nothing but the labelling.  The cube version
`labelSpaceCube n = ⋃ a, chainCone a` and its openness are recorded too.

## 2 — the Galois connection (the centerpiece, assumption-free)

Between subsets of chains (`Set (Ch K)`, `⊆`) and subsets of the label space
(`Set (A → ℝ)`, `⊆`):

* `coneUnion ℓ I = ⋃ a ∈ I, labelCone ℓ a` — the left adjoint `L`;
* `chainsIn ℓ W = {a | labelCone ℓ a ⊆ W}` — the right adjoint `R`;
* `gc_coneUnion_chainsIn : GaloisConnection (coneUnion ℓ) (chainsIn ℓ)` — pure order theory,
  `⋃_{a∈I} O_a ⊆ W ↔ ∀ a ∈ I, O_a ⊆ W ↔ I ⊆ {a | O_a ⊆ W}`.  **Assumption-free.**

The induced closure/coreflection are then free from mathlib's `GaloisConnection` API.  The
*optional* down-set fact `chainsIn_refine_closed` (a refinement of a chain in `chainsIn W` is again
in it) is the only Part-2 statement that consumes a hypothesis — now just `RunInjective` (via the
unconditional cone inclusion of Part 3) — kept separate so the core `GaloisConnection` stays
assumption-free.

## 3 — the coarsest-chain cover (UNCONDITIONAL, from `RunInjective` alone)

`labelSpace_eq_coarsest_cover` proves `labelSpace ℓ = ⋃_{b coarsest} labelCone ℓ b` from **only**
`RunInjective ℓ`.  The two inputs that were once taken as hypotheses are now theorems:

* **Cone inclusion** `labelCone_mono_run` along a coarsening `a ⟶ b` needs `eventMap f` surjective;
  that follows from `RunInjective` + the *per-refinement* event-count equality
  `card_eventObj_eq_of_hom` (Deliverable A), which is `dimSum a = dimSum b` — proved
  **unconditionally** from the serial wedge's *own* altitude (`serialWedge_dimSum_eq`, `ChainCone`).
  The global `ConstEventCount K` (all chains equal count) is **NOT used** — indeed it is *false* for
  a disconnected `Ch(K)` (see the `ConstEventCount` docstring); only the per-refinement version is
  needed, and it needs no altitude.
* **Finiteness** `hasCoarsening K` (Deliverable B): every chain coarsens to a coarsest one, by
  strong induction on the bead count — a proper coarsening strictly drops `dims.length`
  (`ChainCat.lt_dims_length_of_not_isIso`, from `blockIdx` surjectivity + serial-wedge rigidity).

**Neither `NonSelfLinked` nor `AdmitsAltitude` appears anywhere.**

## 4 — the nerve equivalence (target, NOT proved — and FALSE as stated for branching `K`)

`IsGoodConeCover`/`labelCone_isGoodCover` prove the cones form a good cover (open, convex), and
`coarsestChains_goodCover` (Deliverable C headline) packages the coarsest-chain good cover: it
covers `labelSpace ℓ`, each cone is open+convex, and finite intersections are open+convex.  The old
target `|N(Ch K)| ≃ labelSpace ℓ` (Ziemiański's directed path space `P⃗(K)`) is the nerve lemma
applied to this good cover — but the nerve of the *label* cover is not `Ch(K)` once the chart
folds, so the
target is **false for branching `K`** (`Testing/TwoSquares.lean`); the honest ambient is the atlas
`Sched K`.  Independently, there is no nerve lemma / homotopy colimit in current mathlib, so nothing
here is stated as a theorem (no `sorry`).  Cite Ziemiański, "Spaces of directed paths on pre-cubical
sets" (arXiv:1901.05206).

-/

open CategoryTheory Opposite Set

namespace CubeChains

open HDA

/-! ## Part 1 — the label space -/

section LabelSpace

variable {K : BPSet} {A : Type}

/-- **The label-chart image of an HDA's schedules.**  In the common *label* timing space `A → ℝ`,
the union over *all* cube chains of their realisable-label cones: a label time lies in it iff it
realises *some* chain.  (This is **not** the schedule space — that is `Sched K`, in
`Schedule/Space.lean` — but its lossy image under the label chart; see the module docstring.) -/
noncomputable def labelSpace (ℓ : EdgeLabelling K A) : Set (A → ℝ) :=
  ⋃ a : Ch K, labelCone ℓ a

/-- **The label space is open — assumption-free.**  A union of the open cones `labelCone ℓ a`
(`isOpen_labelCone`); needs nothing beyond the labelling. -/
theorem isOpen_labelSpace (ℓ : EdgeLabelling K A) : IsOpen (labelSpace ℓ) :=
  isOpen_iUnion (fun a => isOpen_labelCone ℓ a)

/-- **The cube label space** `U = ⋃ a, chainCone a` in `Fin n → ℝ`, the union of the cube-chain
star cones.  Needs no labelling. -/
noncomputable def labelSpaceCube (n : ℕ) : Set (Fin n → ℝ) :=
  ⋃ a : Ch (□n), chainCone a

/-- **The cube label space is open** — a union of the open cones `chainCone a`. -/
theorem isOpen_labelSpaceCube (n : ℕ) : IsOpen (labelSpaceCube n) :=
  isOpen_iUnion (fun a => isOpen_chainCone a)

end LabelSpace

/-! ## Part 2 — the Galois connection -/

section Galois

variable {K : BPSet} {A : Type}

/-- **Left adjoint `L`.**  The union of the cones of a *set* `I` of chains. -/
noncomputable def coneUnion (ℓ : EdgeLabelling K A) (I : Set (Ch K)) : Set (A → ℝ) :=
  ⋃ a ∈ I, labelCone ℓ a

/-- **Right adjoint `R`.**  The chains whose cone is contained in a set `W` of label times. -/
def chainsIn (ℓ : EdgeLabelling K A) (W : Set (A → ℝ)) : Set (Ch K) :=
  {a | labelCone ℓ a ⊆ W}

/-- The label space is the left adjoint applied to *all* chains. -/
theorem labelSpace_eq_coneUnion_univ (ℓ : EdgeLabelling K A) :
    labelSpace ℓ = coneUnion ℓ Set.univ := by
  ext t; simp only [labelSpace, coneUnion, Set.mem_iUnion, Set.mem_univ, exists_prop, true_and]

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
    ClosureOperator (Set (Ch K)) :=
  (gc_coneUnion_chainsIn ℓ).closureOperator

end Galois

/-! ## Part 3 — the coarsest-chain cover (assumption mapping) -/

section CoarsestCover

variable {K : BPSet} {A : Type}

/-- **`chainsIn W` is refinement-closed (down-set) — costs only `RunInjective`.**  If `a`'s cone
lies in `W` and `g : b ⟶ a` refines `a` (`b` finer), then `b`'s cone (`⊆ labelCone ℓ a ⊆ W`) also
lies in `W`.  Now unconditional via `labelCone_mono_run` (Deliverable A); isolated so the core
Galois connection stays assumption-free. -/
theorem chainsIn_refine_closed (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ)
    {W : Set (A → ℝ)} {a b : Ch K} (g : b ⟶ a)
    (ha : a ∈ chainsIn ℓ W) : b ∈ chainsIn ℓ W :=
  subset_trans (labelCone_mono_run ℓ hrun g) ha

/-- **A coarsest chain**: one admitting no *proper* coarsening — every refinement `b ⟶ c` out of it
is an isomorphism.  So it has the *fewest* beads, not the most: it is a maximal element of the
coarsening order, which points the other way from chain length.  (`Ch(K)` is unconditionally
skeletal, `ChainCat.eq_of_hom_hom`, so this is genuine maximality in the coarsening order.) -/
def IsCoarsest (b : Ch K) : Prop :=
  ∀ ⦃c : Ch K⦄ (g : b ⟶ c), IsIso g

/-- **Finiteness input: every chain coarsens up to a coarsest one.**  A proper coarsening strictly
drops the bead count `dims.length`, so iterating terminates at a coarsest chain. -/
def HasCoarsening (K : BPSet) : Prop :=
  ∀ a : Ch K, ∃ b : Ch K, IsCoarsest b ∧ Nonempty (a ⟶ b)

/-- **Deliverable B — `HasCoarsening` holds unconditionally.**  Strong induction on the bead
count `a.dims.length`: if `a` is not coarsest it admits a *proper* coarsening `g : a ⟶ c` (a
non-isomorphism), which strictly drops the bead count (`ChainCat.lt_dims_length_of_not_isIso`, from
`blockIdx` surjectivity + serial-wedge rigidity — **no `AdmitsAltitude`, no `NonSelfLinked`**); the
induction hypothesis on `c` supplies a coarsest coarsening, reached from `a` through `g`. -/
theorem hasCoarsening (K : BPSet) : HasCoarsening K := by
  have key : ∀ n, ∀ a : Ch K, a.dims.length = n →
      ∃ b : Ch K, IsCoarsest b ∧ Nonempty (a ⟶ b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro a hn
      by_cases hmax : IsCoarsest a
      · exact ⟨a, hmax, ⟨𝟙 a⟩⟩
      · have hex : ∃ (c : Ch K) (g : a ⟶ c), ¬ IsIso g := by
          by_contra hcon
          simp only [not_exists, not_not] at hcon
          exact hmax fun c g => hcon c g
        obtain ⟨c, g, hg⟩ := hex
        have hlt : c.dims.length < n := hn ▸ ChainCat.lt_dims_length_of_not_isIso g hg
        obtain ⟨m, hm, ⟨fcm⟩⟩ := IH c.dims.length hlt c rfl
        exact ⟨m, hm, ⟨g ≫ fcm⟩⟩
  exact fun a => key a.dims.length a rfl

/-- **Every coarsest cone sits inside the label space — assumption-free.**  Trivial: a coarsest
chain is a chain, so its cone is one of the union's members. -/
theorem coarsestCover_subset_labelSpace (ℓ : EdgeLabelling K A) :
    ⋃ b ∈ {b : Ch K | IsCoarsest b}, labelCone ℓ b ⊆ labelSpace ℓ :=
  Set.iUnion₂_subset (fun b _ => Set.subset_iUnion (fun a => labelCone ℓ a) b)

/-- **The coarsest-chain cover — Deliverable C, needing only `RunInjective`.**
`labelSpace ℓ = ⋃_{b coarsest} labelCone ℓ b`.

The two former hypotheses are now discharged internally and unconditionally:
* the cone inclusion `labelCone_mono_run` (from `card_eventObj_eq_of_hom` = Deliverable A) replaces
  the `ConstEventCount`-based `labelCone_mono_const` — no altitude;
* `hasCoarsening K` (Deliverable B) supplies a coarsest coarsening of each chain — no altitude.

The proof uses only the *reachability* half of `hasCoarsening` (a morphism `a ⟶ b`), not the
coarsest-ness predicate itself; `IsCoarsest` fixes the intended index set of the cover.
**Neither `NonSelfLinked` nor `AdmitsAltitude` is used.** -/
theorem labelSpace_eq_coarsest_cover (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) :
    labelSpace ℓ = ⋃ b ∈ {b : Ch K | IsCoarsest b}, labelCone ℓ b := by
  apply subset_antisymm
  · intro t ht
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp ht
    obtain ⟨b, hbmax, ⟨f⟩⟩ := hasCoarsening K a
    exact Set.mem_iUnion₂.mpr ⟨b, hbmax, labelCone_mono_run ℓ hrun f ha⟩
  · exact coarsestCover_subset_labelSpace ℓ

end CoarsestCover

/-! ## Part 4 — the nerve equivalence (target, NOT proved; FALSE as stated for branching `K`)

**Old target (Ziemiański, arXiv:1901.05206).**  For an HDA `(K, ℓ)` one would like a homotopy
equivalence `|N(Ch K)| ≃ labelSpace ℓ`, with the right-hand side Ziemiański's space of directed
paths `P⃗(K)`.  The intended proof is the **nerve lemma** for the cover `{labelCone ℓ a}`: it is a
*good cover* (every cone is open and convex — `labelCone_isGoodCover` below — hence every finite
intersection is open and convex, so empty or contractible), and one hoped the nerve of the cover
was the poset `Ch(K)`.

That last step **fails for branching `K`**: the label chart folds distinct chains onto overlapping
cones (`Testing/TwoSquares.lean`), so the nerve of the label cover is not `Ch(K)` and `labelSpace ℓ`
has the wrong homotopy type.  The honest ambient is the schedule atlas `Sched K`
(`Schedule/Space.lean`).  Independently, there is no nerve lemma / homotopy colimit / geometric
realization of a category in current mathlib, so nothing here is stated as a `theorem` and nothing
is `sorry`-ed.  Only the checkable hypothesis (good-cover-ness of the label cones) is proved. -/

section Nerve

variable {K : BPSet} {A : Type}

/-- **Good-cover property.**  Every chain cone is open and convex — the checkable hypothesis of the
nerve lemma (whose conclusion `|N(Ch K)| ≃ labelSpace ℓ` is, as stated, false for branching `K`; see
the section docstring). -/
def IsGoodConeCover (ℓ : EdgeLabelling K A) : Prop :=
  ∀ a : Ch K, IsOpen (labelCone ℓ a) ∧ Convex ℝ (labelCone ℓ a)

/-- **The chain cones form a good cover — assumption-free.**  `isOpen_labelCone` +
`convex_labelCone`.  This is the sole formalizable input to the nerve-equivalence target above. -/
theorem labelCone_isGoodCover (ℓ : EdgeLabelling K A) : IsGoodConeCover ℓ :=
  fun a => ⟨isOpen_labelCone ℓ a, convex_labelCone ℓ a⟩

/-- **Deliverable C (headline) — the coarsest chains give a good cover of the label space, from
`RunInjective` alone.**  For a run-injective HDA `(K, ℓ)` the cones of the *coarsest* cube chains

1. **cover** the label space: `labelSpace ℓ = ⋃_{b coarsest} labelCone ℓ b`
   (`labelSpace_eq_coarsest_cover`, using Deliverables A + B);
2. are each **open and convex** (`labelCone_isGoodCover`);
3. have every **finite intersection open and convex** (`isOpen_biInter_finset`, `convex_iInter₂`) —
   hence empty or contractible, the good-cover / nerve hypothesis.

No `ConstEventCount`, no `HasCoarsening` hypothesis, **no `NonSelfLinked`, no `AdmitsAltitude`**;
only the labelling's run-injectivity.

**Deliverable D (note).**  One hoped the nerve of this good cover was the poset `Ch(K)`, so that the
nerve lemma would give `|N(Ch K)| ≃ labelSpace ℓ` and identify the label space with **Ziemiański's
space of directed paths `P⃗(K)`** (arXiv:1901.05206, "Spaces of directed paths on pre-cubical
sets").  It does not: the label chart folds (`Testing/TwoSquares.lean`), so that conclusion is false
for branching `K` — the atlas `Sched K` is the honest ambient.  (Current mathlib has no nerve lemma
/ homotopy colimit / geometric realization of a category either.) -/
theorem coarsestChains_goodCover (ℓ : EdgeLabelling K A) (hrun : RunInjective ℓ) :
    (labelSpace ℓ = ⋃ b ∈ {b : Ch K | IsCoarsest b}, labelCone ℓ b)
      ∧ (∀ b : Ch K, IsCoarsest b →
          IsOpen (labelCone ℓ b) ∧ Convex ℝ (labelCone ℓ b))
      ∧ (∀ I : Finset (Ch K),
          IsOpen (⋂ b ∈ I, labelCone ℓ b) ∧ Convex ℝ (⋂ b ∈ I, labelCone ℓ b)) := by
  refine ⟨labelSpace_eq_coarsest_cover ℓ hrun, fun b _ => labelCone_isGoodCover ℓ b, fun I => ?_⟩
  exact ⟨isOpen_biInter_finset (fun b _ => isOpen_labelCone ℓ b),
    convex_iInter₂ (fun b _ => convex_labelCone ℓ b)⟩

end Nerve

end CubeChains
