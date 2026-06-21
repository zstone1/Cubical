# CLEANUP.md — major cleanup pass (tracker + plan)

Status board for the repo-wide cleanup. **This is the execution tracker**: each item
has a checkbox; mark `[x]` as it lands and record the build target that verified it.
Future agents: read this + `ARCHITECTURE.md` (built in Phase 5) + the one module you
touch — never the whole tree.

Branch: `cleanup-pass` (off `main`). Build is ground truth (`lake build CubeChains.<Module>`),
not the IDE. `sorry` only ever allowed in `Research/Conjectures.lean`.

> **STATUS — ✅ COMPLETE.** Phases 0–5 + the folder reorg (4b) are done; full `lake build CubeChains`
> green (1264 jobs), Testing green, sorry-free outside `Research/Conjectures.lean`. Both headline
> results (`equivWedgeCat`, `cylToPointedR`) intact. The tree went **37 files / 11,413 lines → 33 files
> / 9,531 lines = −1,882 (~16%)** into a layered structure (Foundations / Chains / Cylinder / Research /
> Testing). Gross deletions were ~2,100+ lines of dead/duplicate code; the net is smaller because the
> pass also added module docstrings (all 33 files), the reusable `glue0_*`/`RefineConcat` extractions,
> generalization wrappers, and split headers. **Phase 6 (build-speed) is deferred** by owner. Map:
> `ARCHITECTURE.md`. (NB `Research/Scratch/` is owner work, outside this cleanup.)

## Owner decisions (locked)

- **Scaffolding disposition = DELETE everything unused.** The weak-equivalence tower
  (`Homotopical → Span → Deformation → WeakEquiv → GroupoidTarget`) and the superseded
  ChP-based cylinder track are deleted outright, not attic'd. Git history is the recovery
  path if a direction is revived.
- **Priority results = FULL restructure.** Split `CylinderRefine` into modules, extract a
  reusable concat kernel, adopt `Quiver.IsThin`, generalize `BPSet → PrecubicalSet`, bundle
  the altitude axiom. All build-verified at each step.

## The two results to protect (never regress)

1. `RefineObj ⇔ Ch` naturality: `equivWedgeCat : RefineObj K ≌ ChainCat.Obj K`
   (`Chains/Correspondence.lean`) + the `Refine.pushforward` keystone (`Chains/RefineFunctor.lean`).
2. `CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)`: `cylToPointedR`
   (`Operations/CylinderRefine.lean`).

Both are currently green/sorry-free. Every phase ends with these two modules building.

---

## Baseline (current)

- 37 `.lean` files, ~11,413 lines. Biggest: `CylinderRefine` 2295, `Segal` 968,
  `Correspondence` 854, `Cylinder` 796, `WedgeMap` 614.
- Projected reduction: **~2,500–3,000 lines (~22–26%)** from deletions + dedup, before
  the reorg (which is line-neutral but flattens the dependency tree).

---

## Target architecture (end state)

Layered so future agents get a shallow dependency tree. `→` = "imported by".

REALIZED structure (after Phase 4 + 4b). `→` = import direction (down = upstream).

```
CubeChains/Foundations/                   Layer 0 — stable math fundamentals
  PrecubicalConstructions/{Basic,StandardCube}   concrete graded model
  Box            Box cat + PrecubicalSet := Boxᵒᵖ ⥤ Type
  Representable  cube Yoneda + trueCount/canonicalMap combinatorics + coface
  Bipointed      BPSet + vertex API + faceMap/cubeMap + IsAltitude predicate
  Wedge          cube, wedge2, vertexMap (:= cubeMap), serialWedge
  Shift          box shift endofunctor, PathOb, snocFree/snocFix, ⊗□¹⊣PathOb
  Altitude       NonSelfLinked / AdmitsAltitude / Accessible (PrecubicalSet-level)

CubeChains/Chains/                        Layer 2 — cube chains
  Basic        CubeChain (dead accessors trimmed)
  WedgeMap     wedge-map decomposition (+ glue0_* presheaf cores, mono infra)
  Refine       ChainRefine, RefineObj
  RefineConcat (NEW) RefineObj.append + appendLeft whiskering kernel
  Category     ChainCat, Ch, liftToCh
  Correspondence  equivWedgeCat  [RESULT 1]  (Quiver.IsThin)
  RefineFunctor   Refine.pushforward  (imports Correspondence)
  Lifting      refineAut := via Refine.pushforward  (imports RefineFunctor)
  Slice        Ch ↪ Over K, fully faithful  (mathlib-reuse exemplar)
  Segal (+ SegalAltitude)  monoidality  (IsThin; dead island deleted)

CubeChains/Cylinder/                      Layer 3 — cylinder ⇒ pointed-functor (was Operations/)
  PointedFunctor       PointedEndofunctor + groupoid API (mathlib FreeGroupoid)
  Cylinder             prism core: cylTranspose, CylMap, prism, …
  CylinderRefineCore   geometry: DPathGrpdR, CylMapR, blockQ, refine*G, bridges
  CylinderSweep        the sweepR fence-staircase
  CylinderRefine       cylToPointedR  [RESULT 2]  (thin deliverable)

CubeChains/Research/                      Layer 4 — conjectures + counterexamples
  Conjectures (refuted lowering removed), Unrealizable, Examples

CubeChains/Testing/                       decoupled computable FinBPSet harness
  Model, Lowering, Examples, CylinderObstruction, CylinderTwoBlock, WedgeMapDivergence

DELETED: Chains/Endpoints; Operations/{Homotopical,Span,Deformation,WeakEquiv,
  GroupoidTarget,Precubical}; dead halves of Cylinder & CylinderRefine; Segal dead island;
  exists_lower_orientationPreserving (refuted).
```

---

## Phase 0 — Setup & safety net

- [x] Branch `cleanup-pass` created off `main`.
- [x] Green-baseline `lake build CubeChains` recorded — 1278 jobs, only the 8 expected
      `Conjectures.lean` sorries. Starting point compiles.
- [ ] Track `Testing/CylinderTwoBlock.lean` (untracked but already cited by committed
      `CylinderRefine.lean`). `git add` only — no commit until owner asks.
- [ ] This tracker committed as the first cleanup commit (when owner authorizes commits).

## Phase 1 — Dead-code deletion  (low risk; biggest win; ~1,200+ lines)

Delete, then `lake build` the dependents, then remove the import from root `CubeChains.lean`.

- [x] **`Chains/Endpoints.lean`** — fully orphaned (no importer). Deleted; full `lake build
      CubeChains` still green (1278 jobs). *(−112)*
- [x] **Weak-equivalence tower** — DONE in Phase 4: `PointedFunctor` only needed mathlib
      `FreeGroupoid` (the GroupoidTarget edge was just the dead `transportTransf`); `Cylinder` needed
      zero `Precubical` symbols. Deleted `Operations/{Homotopical,Span,Deformation,WeakEquiv,
      GroupoidTarget,Precubical}.lean` + 6 root imports. **−745 lines.** Full build 1272→1261 jobs.
- [x] **`Segal.lean` dead island** — removed 12 dead symbols (`wedge2HomPsh*`, `homOfPsh`,
      `isoOfPshIso*`, `wedge2Cube0Iso`, `wedge2Assoc`, `wedge2Cube0IsoBP`); kept the live
      `wedge2_initVertex/finalVertex`, `cube0_*_eq_id`, `wedge2_cube0_inr_isIso`, `app_*_eq_of_*Vertex`.
      Was interleaved, deleted surgically. *(−160)*
- [x] **`Conjectures.lean`** — deleted `exists_lower_orientationPreserving` +
      `lower_orientationPreserving`, replaced with a REFUTED comment block; fixed "open"→"refuted"
      prose. One fewer sorry (8→7). *(−15)*
- [x] **`Chains/Basic.lean`** — deleted dead accessors `dimSeq`/`dimSeq_eq`/`dims_length`/`length`/
      `cube`/`link`/`init_eq_final_of_nil` (kept live `dims`). *(−31)*
- [x] **`Cylinder.lean` dead parts** — removed box-tensor adjunction, dead wedge2 copies,
      `WedgeDescP`, dead CylMap legs/groupoids, chain helpers, all `singleBlock*`/`emptyBlock*`
      θ-components, stale roadmap prose, 5 unused imports. Kept the prism core + live legs
      (`cylTranspose_naturality`/`leftLeg`/`rightLeg` are live — feed `prism_precomp`/`coface_prism`).
      **796 → 278 (−518).** Build green. *(−518)*
- [x] **`CylinderRefine.lean` dead prototypes** — removed the basepoint §6 family,
      `singleBlockSweepRG`, single-cube layer, `sweepR_twoBlock`/`sweepR_threeBlock`, and the
      ENTIRELY-DEAD `appendRight` functor block (grep-confirmed zero callers); compressed §9 prose.
      **2295 → 1739 (−556).** Build green. *(−556)*

Build targets after Phase 1: full `CubeChains` green at **1272 jobs** (was 1278).
**Phase 1 net ≈ −1,390 lines.** Weak-equiv tower deletion deferred to Phase 4 (import-gated).

## Phase 2 — Duplication → shared lemmas  (low–med risk; ~300 lines + reuse)

- [ ] **Centralize wedge2 API** (`wedge2Assoc`, `wedge2Cube0Iso`, `cube0_*_eq_id`,
      `serialWedge_singleton_ι_isIso`, `wedge2_initVertex/finalVertex`) → `Chains/WedgeMap.lean`
      (or `Wedge.lean`). Delete the verbatim copies in **both** `Cylinder` and `Segal`
      (Segal's "we copy rather than import" comment goes). *(~150)*
- [x] **Hoist vertex lemmas** — `vertex₀/₁_yonedaEquiv`, `vertex₀/₁_eq`, `map_vertex₀/₁` (general
      `PrecubicalSet` forms) hoisted to `Bipointed.lean`; deleted the 6 duplicates across
      WedgeMap/Cylinder/RefineFunctor/Correspondence/CylinderRefine and repointed callers. Build green.
      (`cubeMap`=`vertexMap` unification folded into Phase 4 when `cubeMap` moves to Bipointed.) *(dedup)*
- [x] **Reverse `Lifting`↔`RefineFunctor`** — `RefineFunctor` now imports `Correspondence` (never
      used a Lifting symbol); `Lifting` imports `RefineFunctor` and defines `refineAut` via
      `Refine.pushforward` + a local endpoint-rebase, dropping the thinness hypotheses. Deleted
      `mapCube`/`get_mapCube`/`isCubeChain_map`/`refineAutObj`/`refineAutMap`. Lifting 223→157. *(−66)*
- [x] **Misc dedup** — `chainLe`→`chLe` (Testing; also fixed `CylinderTwoBlock`), `hpush`→
      `inducedCubeList_map_descent` helper (Correspondence), `incl_index_eq` promoted to public
      `ChainRefine.incl_index_eq` + reused in CylinderRefine (`incl_heq_of_index_eq` left — genuinely
      different statement). Build green. *(dedup)*

## Phase 3 — Generalization  (med risk; line-light, reuse-heavy)

- [x] **`Quiver.IsThin`** — used mathlib `Quiver.IsThin` + `iso_of_both_ways`; registered the
      thin instances (global for `Obj (cube 0)` in Segal; local `haveI` in Correspondence since
      thinness is conditional on the altitude data `h₁ h₂`). Simplified `refineToWedge`/`wedgeToRefine`/
      `counitObjIso`/`equivWedgeCat` coherence to bare `Subsingleton.elim`. Green; idiomatic but
      ~line-neutral (conditional thinness ⇒ no free global instance). *(idiom)*
- [x] **`BPSet → PrecubicalSet` (altitude)** — `alt_map_eq`/`alt_vertex₀/₁`/`alt_cubeMap` moved to
      `namespace PrecubicalSet` over `X`; `NonSelfLinked` is now a `PrecubicalSet` predicate with a thin
      `BPSet` alias; `descent_alt_ge`/`descent_app_inj`/`isCubeChain_alt_get` take `IsAltitude`. Green.
- [x] **Bundle the altitude axiom** — added `PrecubicalSet.IsAltitude X alt`; `AdmitsAltitude`
      rewritten through it (defeq, no SegalAltitude churn). `descent_mono`/`hom_subsingleton` keep the
      `AdmitsAltitude` signature (consumed widely) but destructure to `IsAltitude` internally. Green.
- [x] **`BPSet → PrecubicalSet` (WedgeMap)** — added presheaf-level `glue0_*` cores (over arbitrary
      `□⁰ ⟶ A`/`□⁰ ⟶ B` maps) for `wedge2_isPushout_app`/`cell_cases`/`isPullback_app`/`inl,inr_app_injective`/
      `inl_ne_inr`; `wedge2_*` are now one-line `BPSet` wrappers. Merged the twin vertex-injectivity
      lemmas into `vertexMap_app_injective`. Green. (WedgeMap +38: the reusable cores.)

## Phase 4 — Reorganization (the layering)  (med risk; line-neutral; flattens deps)

- [x] Move `trueCount`/`canonicalMap_*` combinatorics: `Altitude` → `Representable`. Altitude 264→133.
- [x] Move `coface`/`faceMap`/`cubeMap`: `Altitude` → `Representable`(coface)/`Bipointed`(faceMap,cubeMap);
      unified `Wedge.vertexMap := cubeMap`. (Also removed a duplicate `canonicalMap_topCell` in Shift.)
- [~] Move chain-altitude arithmetic: `Correspondence` → `Altitude` — **SKIPPED**: `isCubeChain_alt_get`/
      `descent_alt_ge` reference `IsCubeChain` from `Chains/*` (downstream of Altitude) ⇒ would cycle.
      The 3 cycle-free helpers (`dimPrefixSum*`) aren't worth relocating alone. Left in Correspondence.
- [x] Move adhesive/mono infra (`vertexMap_mono`, `wedge2_*_mono`): `Segal` → `WedgeMap`.
- [x] Move `Shift.lean`: `Operations/Shift.lean` → `CubeChains/Shift.lean` (foundation). Importers updated.
- [x] `PointedFunctor` repointed to mathlib `FreeGroupoidOfCategory`, `GroupoidTarget` deleted, dead
      `pointedOfTransf`/`transportTransf` dropped. (Kept filename `PointedFunctor.lean`; rename deferred.)
- [x] `Operations/Precubical.lean` deleted (Cylinder needed zero ChP symbols).
- [x] Extracted `Chains/RefineConcat.lean` (584) — the generic `RefineObj.append` + `appendLeft`
      whiskering kernel, imports `Chains.RefineFunctor` + `Cylinder.Cylinder` (`isCubeChain_append`).
- [x] Split `CylinderRefine` (1741) → `RefineConcat` (584) + `Cylinder/CylinderRefineCore` (428) +
      `Cylinder/CylinderSweep` (710) + `Cylinder/CylinderRefine` (90, thin deliverable). Public name
      stable. Full 4-way split, green (1264 jobs).

## Phase 4b — Folder reorganization (by area)  ✅ DONE

Per owner: regroup the scattered top-level files into area folders ("Layer folders" layout).
`git mv` (history preserved) + anchored rewrite of every `import CubeChains.<path>` line; namespaces
left untouched (they're independent of file location). Both targets green: core **1264 jobs**,
Testing **2947 jobs**.

- [x] `Foundations/` ← PrecubicalConstructions/, Box, Representable, Bipointed, Wedge, Shift, Altitude
- [x] `Chains/` (unchanged location)
- [x] `Cylinder/` ← renamed from `Operations/` (PointedFunctor, Cylinder, CylinderRefineCore,
      CylinderSweep, CylinderRefine; the stale `CylinderPlan.md` rode along — assess in Phase 5)
- [x] `Research/` ← Conjectures, Unrealizable, Examples
- [x] `Testing/` (unchanged)
- [x] Doc/skill references to old paths fixed (DESIGN.md, orient skill, MEMORY, README) — Phase 5.

## Phase 5 — Docs · progressive disclosure · skills  ✅ DONE

- [x] **Refreshed `DESIGN.md`** — removed the stale Representable-"deferred"-sorry claim, the never-built
      `PrecubicalSet ≌ PrecubicalConstructions` equivalence, and the "temporary placeholder" pushout framing;
      updated all paths to the new folders; added a "Current structure" pointer to ARCHITECTURE/CLEANUP.
- [x] **Wrote `ARCHITECTURE.md`** — the canonical layer map + "where do I find X?" index + the two results.
- [x] **Module docstrings** on all 32 files (Foundations/Chains/Cylinder/Research/Testing) — layer + owns
      + deps, consistent with ARCHITECTURE.md. Build stayed green.
- [x] **Rewrote the `orient` skill** — folder map, build targets, status (results 1+2 done; refuted lowering
      removed), off-the-shelf catalogue de-staled; points to ARCHITECTURE.md as the single source of truth.
- [x] **Refreshed `MEMORY.md`** + memory files: rewrote `cubechains-operations-layer` (tower deleted),
      `cubechains-cylinder-roadmap` (compact, new paths), added `cubechains-cleanup-pass`; fixed paths/hooks.
- [x] Trimmed stale prose (the "since-removed wedge-map approach" narration; `CylinderObstruction`'s
      reference to the deleted `CylinderCh.lean`); deleted the superseded `CylinderPlan.md`; refreshed README.

---

## Phase 6 — Build-speed pass  ⏸ DEFERRED (owner: "deal with slowness later")

Not started. Recon left for whoever picks it up: the only two `set_option maxHeartbeats` bumps in
the whole project are in `Chains/Correspondence.lean` — `800000` at ~line 145 and `1600000` at ~line
174, each guarding a slow declaration. Those (and `Correspondence`'s ~45s build) are the targets.

- [ ] Profile the two bumped declarations (`count_heartbeats in` / `set_option profiler true in`);
      lower or remove the bumps if the cleanup made them unnecessary; speed the declarations with
      targeted `simp only`/rewrites where a broad `simp`/`erw` is searching.
- [ ] Re-time full `lake build CubeChains` before/after; record the delta.

## Execution discipline (how to do this without whole-repo context)

The cleanup is itself designed to be context-cheap — that was an explicit requirement:

1. **One cluster per work session.** Phases are ordered so each touches a bounded file set.
   A session loads only that cluster + direct deps (the import graph in `ARCHITECTURE.md`),
   never the whole repo.
2. **Build per module, not per repo.** Verify with `lake build CubeChains.<Module>` for the
   edited module + its direct dependents; run full `lake build CubeChains` only at phase ends.
3. **Delete before generalize before split.** Smaller surface first makes the later, riskier
   structural moves cheaper and easier to verify.
4. **Two results stay green every phase.** After any phase, `lake build CubeChains.Chains.Correspondence`
   and `lake build CubeChains.Operations.CylinderRefine` must pass.
5. **Tick this tracker** as items land (with the verifying build target) so a fresh agent can
   resume from the checkboxes without re-deriving state.
6. **Parallel-safe phases** (independent file clusters) can be farmed to worktree-isolated
   sub-agents; dependency-ordered phases (2→3→4) run in sequence.

## Goal traceability (owner's 5 asks → phases)

| Owner goal | Where it's addressed |
|---|---|
| 1. Reduce size (repeated logic, off-the-shelf, poor statements, comments) | Phases 1–2 (deletions+dedup), Phase 3 (IsThin, off-the-shelf), Phase 5 (comments) |
| 2. Generalize (BPSet→PrecubicalSet; use Mono/repr not the whole functor) | Phase 3 |
| 3. Isolate fundamentals from researchy bits | Phase 4 (layering: Foundations / Chains / Operations) |
| 4. Progressive-disclosure structure per area | Phase 5 (`ARCHITECTURE.md` + module docstrings + this tracker) |
| 5. orient / skills for future agents | Phase 5 (orient rewrite, MEMORY refresh) |
