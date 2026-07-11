# Schedule — HDA event naming and the schedule space of `Ch(K)`

The timing-geometry study of `Ch(K)`: name the events of cube chains (as HDA action labels),
send each chain to an open convex cone of schedules, and assemble the cones into the schedule
space `U` with a Galois connection to the ideals of `Ch(K)`.

## Headline theorems
- `ScheduleSpace.gc_coneUnion_chainsIn` — the Galois connection between ideals of `Ch(K)` and open
  subsets of `U` (`coneUnion ⊣ chainsIn`). Assumption-free.
- `ScheduleSpace.maximalChains_goodCover` — the cones of the maximal chains form a good cover of
  `U` (open, convex, with contractible-or-empty intersections). Needs `RunInjective ℓ` only.
- Target (citation, not formalized): `|N(Ch K)| ≃ U ≃ P⃗(K)` — the directed path space
  (Ziemiański, arXiv:1901.05206). mathlib has no nerve / homotopy-colimit lemma, so this is a
  target, not a theorem (and uses no `sorry`).

## Layers (each prior to the next — no vector space before the naming)
- `EventNaming.lean` — events of a chain (`EventObj`, `eventMap`); the universal naming
  `canonicalName` with `hasGlobalEventNaming_iff` (coherence is free, the content is "no folding").
- `EventLocalSystem.lean` — functoriality of `eventMap`; the cube base case.
- `HDA.lean` — the HDA edge labelling `EdgeLabelling` (opposite-equal concurrency axiom).
  `hasGlobalEventNaming_of_labelling : RunInjective ℓ → HasGlobalEventNaming K` — coherence from
  the axiom (no monodromy), fibre-injectivity from run-injectivity.
- `ChainCone.lean` — chain ↦ open convex cone (cube case assumption-free; general HDA via
  `RunInjective`).
- `ScheduleSpace.lean` — the schedule space, the Galois connection, the good cover.

## Why the labelling is input data
`NonSelfLinked K ∧ AdmitsAltitude K ⟹ HasGlobalEventNaming K` is **false** — machine-checked in
`Testing/EventNamingCounterexample.lean` (the "trinity": three squares filling `a → d`, all six
edges in one self-crossing hyperplane, so the events of the line `a→b→d` fold). The fix is to take
the action labelling as HDA data instead of reconstructing it from the local `eventMap` system.
Consequently `NonSelfLinked` and `AdmitsAltitude` are used nowhere here: the whole cone / cover /
adjunction apparatus rests on `RunInjective` alone.
