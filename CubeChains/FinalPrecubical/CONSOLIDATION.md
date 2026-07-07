# FinalPrecubical — consolidation ledger

Goal: dramatically reduce the size of the FinalPrecubical proof by routing its
re-derived plumbing through the existing `Chains/` API (`equivWedgeCat`,
`wedgeToRefineMap`, `WedgeMap`, `Basic`) and by de-duplicating the shared
block-decomposition arithmetic. Scoped to `FinalPrecubical/` for now (shared
helpers may relocate to `Foundations/` later).

## Baseline (2026-07-07, commit 70af1ed)

| Module | Lines |
|---|---|
| QuotientCat | 291 |
| MainFunctor | 605 |
| NerveQuot | 699 |
| Salvetti | 834 |
| Ev | 1799 |
| **Total** | **4228** |

## Two shared substrates (the reduction thesis)

- **A. Block/prefix-sum arithmetic on `List ℕ+`** — pure `Fin`/`Nat`/`List`. Three
  encodings today: Salvetti `blockOf`/`psum`/`blockOf_iff_psum` (ℕ); Ev
  `dimSum`/`globalEquiv` (`finSigmaFinEquiv`); Correspondence `dimPrefixSum` (ℤ, altitude).
  `dimSum` is literally duplicated Ev↔Salvetti (Salvetti's `private abbrev` is a
  name-clash dodge). Mostly de-dup / DRY; modest raw line savings.
- **B. Standard-cube sign-vector geometry** — `nones`/star embeddings, `app`, the
  interval `[vertex₀,vertex₁]`/cumulative-OR corners. The irreducible ~900-line
  owner-rule + realization content; reusable pieces (`nones_app`, `app_val`,
  `toStar_vertex_*`) "belong in `Representable.lean`". Hoist ⇒ owner rule reads thin.

## Consolidation targets (measured as completed)

| # | Target | Approach | Est. Δ | Status |
|---|---|---|---|---|
| C1 | `Ev.blockIdx_monotone` (was 517–644, ~127 ln incl. docs) | inherit `wedgeToRefineMap.refinementMono` over `K:=serialWedge B` | −60..−90 | ✅ **DONE** (Ev −86; see log) |
| C2 | Substrate A dedup (`dimSum`/`blockOf`/`psum`/`globalEquiv`) | one shared module in FinalPrecubical + rewire Salvetti/Ev | −40..−80 net; kills name-clash | ⏳ |
| C3 | `Ev.isCubeChain_ofFn` (1606, ~20 ln) | reuse `Basic.isCubeChain_aux` on `List.ofFn` | −20 | ⏳ |
| C4 | Ev Step-2 block Skolemization (178–312) | rebuild `blockIdx`/`blockMor`/`blockFace_spec` on `wedgeMap_block` | −40..−80 | ⏳ |
| C5 | Substrate B hoist (`nones_app`/`app_val`/`toStar_vertex_*`) | relocate to `Representable.lean` | dedup, ~0 net in-folder | ⏳ |

## Results log

- **C1 — `blockIdx_monotone` inherited from `refinementMono`** (2026-07-07, uncommitted):
  `Ev.lean` **1799 → 1713 (−86)**. Enabler: new reusable lemma
  `wedgeToRefineMap_refinement_spec` in `Chains/Correspondence.lean` (**+25**, one-time),
  which exposes the tactic-buried `refinement` field as a block membership. Net across
  both files **−61**; folder-only **−86**. The old ~110-line altitude/prefix-sum
  bracketing is now a single call to `refinementMono` + a 2-line block identification
  (`wedgeToRefineMap_refinement_spec` + `blockIdx_eq_of`). Whole FinalPrecubical folder
  still green & sorry-free. **Unlocks C4:** the same `refinement`-identification can now
  reroute more of Ev's Step-2 block machinery through `wedgeToRefineMap`.

- **C6 — Step 1 `dimSum_eq` routed through altitude machinery** (2026-07-07, uncommitted):
  `Ev.lean` **1713 → 1643 (−70)**. Deleted the bespoke `isAltitude_comp` + `cube_alt_final`
  + `serialWedge_alt_final` recursion; `dimSum_eq` now observes that over the ambient
  `serialWedge B` both `⟨A,g⟩` and `⟨B,𝟙⟩` are `init→final` chains, whose altitude gap =
  total dimension. Enabler: new reusable lemma `isCubeChain_alt_final` in
  `Chains/Correspondence.lean` (**+20**, vertex-level companion to `isCubeChain_alt_get`).
  **No altitude pullback needed** (the old proof pulled `altB` back along `g`; the ambient
  reframing removes it). Folder still green & sorry-free.

**Running total (Ev.lean): 1799 → 1643 = −156** across C1 + C6; `Chains/Correspondence.lean`
+45 (two reusable altitude/refinement lemmas). Both are the same pattern — expose a small
reusable Correspondence lemma, collapse the Ev re-derivation onto it.

_(append one row per landed consolidation with actual before→after line counts + commit)_
