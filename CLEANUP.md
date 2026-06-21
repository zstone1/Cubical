# CLEANUP.md — major cleanup pass (tracker + plan)

Status board for the repo-wide cleanup. **This is the execution tracker**: each item
has a checkbox; mark `[x]` as it lands and record the build target that verified it.
Future agents: read this + `ARCHITECTURE.md` (built in Phase 5) + the one module you
touch — never the whole tree.

Branch: `cleanup-pass` (off `main`). Build is ground truth (`lake build CubeChains.<Module>`),
not the IDE. `sorry` only ever allowed in `Conjectures.lean`.

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

```
Layer 0  FOUNDATIONS (stable math fundamentals)
  PrecubicalConstructions/{Basic,StandardCube}   concrete graded model
  Box                                            Box cat + PrecubicalSet := Boxᵒᵖ ⥤ Type
  Representable        cube Yoneda  (+ absorbs trueCount/canonicalMap combinatorics)
  Bipointed           BPSet + vertex API (+ absorbs coface/faceMap/cubeMap, vertex lemmas)
  Wedge               cube, wedge2, vertexMap, serialWedge
  Shift   (MOVED from Operations/)  box shift endofunctor, PathOb, snocFree/snocFix, ⊗□¹⊣PathOb

Layer 1  SIDE CONDITIONS
  Altitude            NonSelfLinked / AdmitsAltitude / Accessible + alt_* lemmas
                      (generalized to PrecubicalSet; hax bundled as AltitudeData)

Layer 2  CHAINS
  Chains/Basic        CubeChain (dead accessors trimmed)
  Chains/WedgeMap     wedge-map decomposition (+ centralized wedge2 API, mono infra; off BPSet)
  Chains/Refine       ChainRefine, RefineObj
  Chains/RefineConcat (NEW) RefineObj.append + whiskering kernel (extracted from CylinderRefine)
  Chains/Category     ChainCat, Ch, liftToCh
  Chains/Correspondence  equivWedgeCat  [RESULT 1]  (IsThin; chain-altitude moved to Altitude)
  Chains/RefineFunctor   Refine.pushforward  (imports Refine+Correspondence only)
  Chains/Lifting      refineAut := via Refine.pushforward  (imports RefineFunctor; dedup'd)
  Chains/Slice        Ch ↪ Over K, fully faithful  (reuse exemplar — leave as is)
  Chains/Segal(+Altitude)  monoidality  (IsThin; dead island deleted; infra hoisted)

Layer 3  OPERATIONS / CYLINDER
  Operations/PointedEndofunctor (renamed from PointedFunctor) PointedEndofunctor + groupoid API
                                 (imports mathlib FreeGroupoid directly)
  Operations/CylinderCore  (from Cylinder.lean) prism core: cylTranspose, CylMap, prism, …
  Operations/CylinderSweep (from CylinderRefine) the sweepR staircase
  Operations/CylinderRefine  cylToPointedR  [RESULT 2]  (thin deliverable)

Layer 4  RESEARCH TAIL
  Conjectures   (exists_lower_orientationPreserving removed/restated)
  Unrealizable, Examples
  Testing/*     (decoupled harness; CylinderTwoBlock tracked; probes trimmed)

DELETED: Chains/Endpoints; Operations/{Homotopical,Span,Deformation,WeakEquiv,
  GroupoidTarget,Precubical}; dead halves of Cylinder & CylinderRefine; Segal dead island.
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
- [ ] **Weak-equivalence tower** — `Operations/{Homotopical,Span,Deformation,WeakEquiv,GroupoidTarget}.lean`.
      NB their *symbols* are dead but the *files* are transitively imported by the live
      `PointedFunctor` (`PointedFunctor → GroupoidTarget → Deformation → Span → Homotopical`) and by
      `Precubical → {WeakEquiv,GroupoidTarget}`. So **file deletion is gated on Phase 4**: first
      re-point `PointedEndofunctor` to mathlib `FreeGroupoid` (kills the GroupoidTarget edge) and
      remove `Precubical` (kills the WeakEquiv edge); then the whole tower deletes cleanly. *(~600)*
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

- [ ] Move `trueCount`/`canonicalMap_*` combinatorics: `Altitude` → `Representable`/`StandardCube`. *(~115)*
- [ ] Move `coface`/`faceMap`/`cubeMap` foundations: `Altitude` → `Bipointed`. *(~16)*
- [ ] Move chain-altitude arithmetic (`dimPrefixSum*`): `Correspondence` → `Altitude`. *(~50)*
- [ ] Move adhesive/mono infra (`vertexMap_mono`, `wedge2_*_mono`): `Segal` → `WedgeMap`. *(~30)*
- [ ] Move `Shift.lean`: `Operations/` → foundations (`CubeChains/Shift.lean`); it's box-category
      infra, not an operation. Update importers.
- [ ] Extract `Operations/PointedEndofunctor.lean` (rename `PointedFunctor`): re-point to mathlib
      `FreeGroupoidOfCategory` directly, drop the `GroupoidTarget` dependency, **then delete
      `GroupoidTarget.lean`**. Drop dead `pointedOfTransf`/`transportTransf`.
- [ ] Extract `Chains/RefineConcat.lean` — the generic `RefineObj.append` + whiskering kernel
      (~330 lines) lifted out of `CylinderRefine`; belongs next to `Chains/Refine`.
- [ ] Split `CylinderRefine` → `Operations/CylinderCore` (prism core, from `Cylinder`) +
      `Operations/CylinderSweep` (sweepR staircase) + `Operations/CylinderRefine` (thin
      `cylToPointedR`). Keep the public name `CylinderRefine` stable so the root import is unchanged.
- [ ] Delete `Operations/Precubical.lean` once `Cylinder`'s ChP consumers are gone (verify by build).

## Phase 5 — Docs · progressive disclosure · skills

- [ ] **Refresh `DESIGN.md`** — remove stale claims (Representable "remaining" sorry; the never-built
      `PrecubicalSet ≌ PrecubicalConstructions` equivalence; "temporary placeholder" pushouts).
- [ ] **Write `ARCHITECTURE.md`** — the layer map above as the top-level disclosure entry point,
      with a "where do I find X?" index (per concept → file).
- [ ] **Module docstrings** — every file gets a 2–4 line `/-! -/` header: its layer, what it
      owns, what it depends on. This is the per-module disclosure unit agents grep first.
- [ ] **Update the `orient` skill** — current module map is stale (no `Operations/`, no `Segal`,
      no Cylinder program). Rewrite the map + build targets + status to match the end state.
- [ ] **Refresh `MEMORY.md`** + memory files touched by deletions (cylinder roadmap, operations
      layer, deferred-sorries).
- [ ] Trim stale prose throughout (the "since-removed wedge-map approach" narration, the
      `Testing/CylinderObstruction.lean` reference to deleted `CylinderCh.lean`, long findings essays).

---

## Phase 6 — Build-speed pass  (after the tree is clean)

- [ ] Profile the slowest modules (`Correspondence` is the known ~45s one; baseline showed a
      `maxHeartbeats 1600000` bump somewhere). Use `count_heartbeats`/`-Dprofiler=true` /
      `set_option profiler true` to find the worst declarations.
- [ ] Attack the offenders: replace expensive `simp`/`erw`/`decide` chains with targeted rewrites;
      drop unnecessarily-large simp sets; remove `maxHeartbeats` bumps that the cleanup made
      unnecessary; trim heavy imports.
- [ ] Re-time full `lake build CubeChains` before/after; record the delta here.
      (Fewer files + smaller proofs from Phases 1–4 should already help.)

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
