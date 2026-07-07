# FinalPrecubical — status & restart guide

Goal (from `BRAID_CHAINS_README.md`):
```
Main   :  Ch(Z)_n  ≌  (Sal₀Br n // Perm (Fin n))ᵒᵖ        (iso of categories)
Nerve  :  nerve (Ch(Z)_n) ≅ (nerve ((Sal₀Br n)ᵒᵖ)) / Perm (Fin n)
Support:  N (P // G) ≅ (N P) / G                          (order-free actions on posets)
```
`Z` = the **terminal** BPSet (constant-at-a-point presheaf — NOT `cube 0`).

## Status — ✅ MAIN THEOREM COMPLETE, ENTIRE FOLDER SORRY-FREE (reconfirmed green 2026-07-07)

`#print axioms PhiEquiv` = `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
The last open sorry — `Ev.evValid_exists` (the realization / fullness half of the event bijection) —
was **closed** via the cumulative-OR corner construction; `MainFunctor` and `NerveQuot` build green on
top of it. There are **no sorries left anywhere in the folder**.

Build per-module (still **withheld from `CubeChains.lean`** — see "Next direction" below):
```
lake build CubeChains.FinalPrecubical.{QuotientCat|Salvetti|Ev|MainFunctor|NerveQuot}
```

| Module | State | Delivers |
|---|---|---|
| `QuotientCat` | ✅ sorry-free | `OrderFreeAction`, `QuotCat P G` (+`Category`), `align`, `homEquivUpSet` |
| `Salvetti` | ✅ sorry-free | `BrFace`/`Sal₀Br` posets, `MulAction`+`OrderFreeAction (Perm (Fin n))`, `stdPair`/`stdPairAt`, `orbit_rep_unique`, `levelSizes_*` |
| `Ev` | ✅ sorry-free | `evPerm`, `ev_comp`, `ev_reconstruct`, `ev_bijective`, `IsEvValid` (+`Monotone bm`), `ev_valid`, `faceStar_val_mono` (owner rule, fwd), `evValid_exists` (realization, rev) |
| `MainFunctor` | ✅ sorry-free | **`PhiEquiv : ChZ n ≌ (QC n)ᵒᵖ`** (MAIN THEOREM), terminal `Z`, `ChZ n`, `Φ`, Full/Faithful/EssSurj, `objEquiv`/`Ψ`, `PhiCatIso` (staged) |
| `NerveQuot` | ✅ sorry-free | `nerveQuot`, `nerveQuotIso : (NP)/G ≅ N(P//G)` (STRICT), `opQuotCatIso`, `nerve_chZ_iso` (documented one-liner) |

## ▶▶ BRAID2 REBUILD — IN PROGRESS (2026-07-07, the ACTIVE work)

A genuinely different, Segal-route proof (see `BRAID2_PLAN.md`). Landed green & sorry-free
(all `#print axioms` = `[propext, Classical.choice, Quot.sound]`), NEW files only, no existing
file rewritten:

| New file | commit | Delivers |
|---|---|---|
| `CubeChainPoset` | `3de23a6` | `cube_nonSelfLinked`; **`Ch(□ᵐ) ≌ OSPcat m`** (ordered-partition poset); `refineObjEquivOSP` |
| `SerialNSL` | `745efe8` | `serialWedge_nonSelfLinked B` |
| `CompositionSalvetti` | `672e4d3` | **`Sal₀Br n ≃ Composition n × Perm`**, `salOrbitEquiv` (QC-objs ≃ `Composition n`), `paris_le_iff` |
| `HomAnalysis` (partial) | `d8cba4e` | `blockMap`(+monotone), `blockMap_spec`, `fibreShape` — wedge-map classification data |

**In flight:** object-level Segal decomposition (`blockChainObj`/`blockOwnerData` in `HomAnalysis`) —
the R2 crux; then `MainFunctor2` (`Φ'`, Paris↔OSP-refinement, `PhiEquiv`).

### ⚠ HONEST FINDING (2026-07-07) — the fork the user must steer
The rebuild's *elegance* win is real and mostly landed (Composition foundation kills Salvetti's
`blockOf`/`psum` arithmetic; OSP poset; Equiv-based). But the *size* premise softened:
1. **`CubeChainPoset` imports `Ev`** — the single-cube owner rule (~900 ln: `chainCoordMono`,
   `chainFace_eq_owner`, `cornerChain`, `chainStarSet_cover`, `isCubeChain_junction`) is irreducible
   and lives *in* Ev. Deleting Ev ⇒ first **move** those ~900 ln to a clean file.
2. The Segal decomposition (block-`j` sub-chain init→final) is ~300–400 ln of irreducible content
   Ev owns (welded to `evCell`/`faceStar`/`ev`); re-deriving it independently hinges on a
   "shared vertex between two blocks ⟹ junction" lemma (foundation: `glue0_inl_ne_inr`).
3. **Net line reduction ≈ modest (~200–400), not dramatic** — the two irreducible contents move or
   get re-derived; we also *add* `CompositionSalvetti`+`CubeChainPoset` packaging.

**Two endgames (user picks):**
- **A — delete Ev fully (stated goal):** re-derive Segal decomposition + extract single-cube core
  → Ev gone. ~700–1000 ln new/moved, higher risk, modest net size win, max elegance.
- **B — elegant top over preserved core:** build `MainFunctor2` on `CompositionSalvetti`+OSP reading
  per-block data via existing machinery; delete only old `MainFunctor` + Ev's permutation tower.
  Fast, low-risk, keeps most elegance, Ev slims but stays.
Currently building the object-level Segal decomposition — the **least-wasted** next brick under
BOTH A and B — so progress continues while the user steers.

## ▶ NEXT DIRECTION (2026-07-07): dramatically shrink FinalPrecubical

The proof is complete but **too large** (`Ev.lean` alone ≈ 1800 lines). We believe a **more elegant
proof exists**. Leads and constraints:

- **The redundancy (architecture finding #3):** `Ev` re-derives, at the presheaf level, the
  chain↔wedge correspondence that `equivWedgeCat` (RESULT 1, `Chains/Correspondence.lean`) already
  proves sorry-free. Much of the 1800 lines is presheaf plumbing that duplicates `WedgeMap`/`Refine`
  bookkeeping — that is the target for reuse.
- **HARD CAVEAT (proven 2026-07-06, do not re-try the naive version):** a "thin adapter over
  `equivWedgeCat`" does **not** work. `equivWedgeCat`'s thinness is about morphisms between *fixed*
  objects; it does **not** supply the **owner rule** (a face's fixed 0/1 values are forced by star
  positions + the chain/junction condition). `ev f` is a permutation that *discards* fixed values,
  so `ev_reconstruct`/`evValid_exists` carry real content. A rebuild that assumed this regressed Ev
  from 2 sorries to 7 and was reverted. **The elegant path must fold the owner-rule content through
  RESULT 1's *object* correspondence (`RefineObj`/`WedgeMap`), not just its thinness.**
- **The idea is already elegant; the size is in the plumbing.** The winning model is: faces =
  intervals `[vertex₀, vertex₁]`; a face is fixed by its two corners; along a chain
  `vertex₁(faceᵢ) = vertex₀(faceᵢ₊₁)` is literally `IsCubeChain` (`vtxCanon`); corners = cumulative OR
  of stars; the owner rule = one-step junction telescoping. Shrinking means expressing this against
  the existing `WedgeMap`/`serialWedge` API instead of re-proving cell-level lemmas locally.

## Remaining (non-sorry) polish — optional, low priority given the shrink plan

- **`MainFunctor.PhiCatIso`** — strict category-iso form. `PhiEquiv` (equivalence) is the delivered
  theorem and the nerve theorem is fine up to homotopy from it, so this is optional. Open bits: the
  two `h_map` legs (`Φ.map_injective` + `Functor.map_preimage` chase — `simp` set was incomplete)
  and disambiguating the overloaded `CategoryTheory.Functor.ext` (`_root_`-qualify or `open`-scope).
- **`NerveQuot.nerve_chZ_iso`** — documented one-liner `nerveQuotIso_of_catIso (ChZ n) Φiso`; needs
  the strict `PhiCatIso` (or restate homotopically via `PhiEquiv`) + `import ...MainFunctor`.
- **`Tests.lean`** (n=2 direction tables); **`dimSum` consolidation** (Salvetti's copy is `private`
  to dodge a name clash with Ev's byte-identical one — hoist one shared def); **registration in
  `CubeChains.lean`** (the folder is now eligible — hold until after the shrink to avoid churn).

## Architecture findings (kept — they inform the shrink)

1. **`nerveQuot` visibly "nerve P / G".** Mathlib `SingleObj.Types.colimitEquivQuotient`
   (`.../Limits/Shapes/SingleObj.lean`) gives `colimit J ≃ orbitRel.Quotient G (J.obj star)`. There
   is **no** dedicated presheaf/SSet quotient-by-action, so the colimit form would need gluing
   levelwise isos. Optional elegance refactor; the current hand-rolled def is correct.
2. **No off-the-shelf orbit category.** `CategoryTheory.Quotient` quotients *morphisms* (keeps
   objects); `ActionCategory`/`SingleObj G ⥤ Cat` colimit give the *action groupoid* (objects =
   elements), not orbits. No orbit-category constructor + no free-action alignment support ⇒
   hand-rolling `QuotCat P G` is justified.
3. See NEXT DIRECTION — `Ev` duplicates RESULT 1's correspondence; that's where the size is.

## History — how the last two sorries were closed (2026-07-06)

- **LINCHPIN:** `WedgeMap.lean`'s block-inclusion injectivity (`vertexMap_app_injective`,
  `glue0_inl/inr_app_injective`, `wedge2_inl/inr_app_injective`, `serialWedge_ι_app_injective`)
  **generalized from `1 ≤ m` to all `m`** (`□⁰.cells m` is a `Subsingleton` at every level). This is
  the vertex-non-folding fact the whole owner rule needs — direct dim-0 injectivity, NOT NSL.
- **`faceStar_val_mono`** (owner rule, forward): interval/corner model + one-step junction
  telescoping — `app_val`, `toStar_vertex₀/₁_val`, `blockFace_junction_val`, `evCell_junction`,
  `faceStar_step`/`faceStar_step_v`, iterated over a block via `blockIdx_monotone`.
- **`evValid_exists`** (realization, reverse): cumulative-OR corner construction
  (`starCoord`, `realFaceVal`/`realFace`, `blockCell`, `realBm_surj`, `blockCell_vertex_junction`),
  cross-block junction reusing `evCell_junction` on `𝟙 (serialWedge B)`, descent via `wedgeDesc`.
  `IsEvValid` was strengthened with `Monotone bm` — the old form was **FALSE** (`A=B=[1,1]`,
  `σ=swap` passed the old clauses but is unrealizable, since `g(e₀)` starts at `init`).
