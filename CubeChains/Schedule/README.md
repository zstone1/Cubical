# Schedule — the schedule space of a precubical set

`Sched K` is the space of **timed cube chains**: a chain together with one strictly-increasing time
per bead. It is built as an **atlas of braid cones indexed by `Ch K`** — not inside a global
coordinate ambient. Design doc: **`DESIGN.md`** (read it first; it carries the diagrams, the
hypothesis budget, and the refuted claims).

## The one idea

    Sched K = Σ c : Ch K, Stratum c        Stratum c = strictly increasing bead times
    Chart a = Σ c, (c ⟶ a) × Stratum c     chartCoord a : Chart a ↪ ℝ^(EventObj a)  (onto the cone)

`Sched K` carries the final topology of all the charts. A chart is the open convex cone
`schedCone a`; the strata inside it are the chains refining `a`. **No `EdgeLabelling` is needed** —
schedules exist for every precubical set, not just HDAs.

## Headline results

- `Space.lean` — `Sched K`, `Stratum`, `Chart`, `spread`, the topology; `spread_mem_cone`.
- `Atlas.lean` — **`isAtlas K : IsAtlas K` for every `K`, unconditionally**: `chartCoord a` is a
  bijection onto the cone `schedCone a` (the tie-block decomposition). Injectivity is
  `bfSgnN_beadOf` (a refinement is determined by its bead map — **thinness is not needed**; it is
  `ChartsFaithful`, which forgets the refinement, that needs it); surjectivity builds the chain of an
  ordered partition (`pchain`/`prefine`) out of `SalBraidChain`'s `blockStar` cells.
- `Cover.lean` — `star a`; `fibre_isPrincipal` (**the load-bearing one**: `{a | x ∈ star a}` is the
  principal up-set `↑x.chain` — the hypothesis of the homotopy-colimit lemma); `star_coarsest_cover`;
  `isOpen_star` (needs `IsAtlas` only, *not* thinness — and `IsAtlas` is now a theorem).
- `Orientation.lean` — `orChar : Ch K ⥤ SingleObj ℤˣ` and
  `orientable_of_hasGlobalEventNaming : HasGlobalEventNaming K → Orientable K` — a coherent naming of
  the events trivialises `w₁(Sched K)`. The character `orSign` itself is `Events/OrdSign.lean`.
- `LocalCOM.lean` — `localCOM x = braidDirectSum x.chain.dims`; `localCOM_isEmpty_iff`: the ground set
  is empty exactly at generic schedules. **The local COM measures concurrency.**
- `COMSheaf.lean` — **chart-independence**: `localAt_refineCovector` — for `f : c ⟶ a`, localizing
  the chart's COM at the point's covector *is* the finer chain's COM, transported along
  `zeroSetEquiv f` (the zero set of `refineCovector f` = the within-bead pairs of `c`). So
  `localCOM` is an invariant of the point (`localAt_eq_localCOM`), and refining **deletes** walls:
  the chart's covectors restrict onto the local ones (`covectors_comap_image`) — a COM minor.
  `COM.map` transports a COM along a ground-set equivalence.
- `Salvetti/SalLocal.lean` — `Sal (localCOM x) ≌ Int(Lines(⋁x.chain.dims))`; its faces are the strata
  of `x`'s open star.
- `Arrangements/BraidCone.lean` — **realizability**: the braid arrangement restricted to a chain's
  cone realizes exactly the covectors of `braidDirectSum dims`.
- `Arrangements/COMLocal.lean` — `COM.localAt L X`, the local COM at a covector (an OM).

## Hypothesis budget: one

`Ch K` **thin** (⟸ `NonSelfLinked`), and only to stop a chart folding onto itself. `RunInjective`,
`AdmitsAltitude`, `ConstEventCount`, `Sculpture` and `Finite A` are **not needed** — nor are the
extended reals / horizon / ω-coordinate / box topology, all of which were artifacts of the global
chart. `EventObj a` is finite for every chain, loops included.

## The label picture is a chart, and it folds

`LabelChart.lean` records an `EdgeLabelling` as `labelTime : Sched K → (A → ℝ)`, landing in
`labelCone ℓ x.chain`. It is **not injective**, and no side condition repairs that:
`Testing/TwoSquares.lean` machine-verifies a `K` — two 2-cubes with the same boundary — that is
non-self-linked, altitude-graded and run-injective, whose refinement order is `K_{2,2}` (so
`|N(Ch K)| ≃ S¹`), and whose two squares carry identical labels. The label cones coincide, and
`labelSpace ℓ` collapses to something contractible.

So `LabelSpace.lean`'s nerve target is **false as stated for branching `K`**, and `Horizon.lean`'s
repair (separating chains by label set) is necessary but **not** sufficient. Both are kept as the
*global-chart* layer — useful for computation, not foundations.

## Legacy layer (the labelling / global chart)

- `HDA.lean` — `EdgeLabelling` (opposite-equal concurrency axiom), `RunInjective`.
- `Cone.lean` — `schedCone a`, the cone in `ℝ^(EventObj a)`. This *is* the chart.
- `ChainCone.lean`, `LabelSpace.lean`, `Horizon.lean` — the label ambient `A → ℝ` and its cones,
  the Galois connection, the (folding) cover.
- `Sculpture.lean` — retained; not needed by the atlas (it was compensating for the wrong ambient).
