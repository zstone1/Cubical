# FinalPrecubical — status & restart guide

Goal (from `BRAID_CHAINS_README.md`):
```
Main   :  Ch(Z)_n  ≌  (Sal₀Br n // Perm (Fin n))ᵒᵖ        (iso of categories)
Nerve  :  nerve (Ch(Z)_n) ≅ (nerve ((Sal₀Br n)ᵒᵖ)) / Perm (Fin n)
Support:  N (P // G) ≅ (N P) / G                          (order-free actions on posets)
```
`Z` = the **terminal** BPSet (constant-at-a-point presheaf — NOT `cube 0`).

## Build
Per-module only (do NOT add to `CubeChains.lean` yet — 3 sorries remain, and the repo
invariant is "sorry only in `Research/Conjectures.lean`"):
```
lake build CubeChains.FinalPrecubical.{QuotientCat|Salvetti|Ev|MainFunctor|NerveQuot}
```
All five build **green** as of this checkpoint.

## Module status

| Module | State | Delivers |
|---|---|---|
| `QuotientCat` | ✅ sorry-free | `OrderFreeAction`, `QuotCat P G` (+`Category`), `align`, `homEquivUpSet` |
| `Salvetti` | ✅ sorry-free | `BrFace`/`Sal₀Br` posets, `MulAction`+`OrderFreeAction (Perm (Fin n))`, `stdPair`/`stdPairAt`, `orbit_rep_unique`, `levelSizes_*` |
| `Ev` | ✅ green · **2 sorries** | `evPerm`, `ev_comp`, `ev_reconstruct`, `ev_strictMonoOn`, `ev_blocks`, `blockIdx_monotone` (proved), `IsEvValid`, `ev_valid`, `evValid_exists` |
| `MainFunctor` | ✅ green · 0 own | **`PhiEquiv : ChZ n ≌ (QC n)ᵒᵖ`** (MAIN THEOREM), terminal `Z`, `ChZ n`, `Φ`, Full/Faithful/EssSurj, `objEquiv`/`Ψ` (built), `PhiCatIso` (staged) |
| `NerveQuot` | ✅ green · **1 sorry** | `nerveQuot`, **`nerveQuotIso : (NP)/G ≅ N(P//G)`** (STRICT, sorry-free), `nerveQuotIso_of_catIso`, `opQuotCatIso` (sorry), `nerve_chZ_iso` (documented one-liner) |

## The 3 remaining sorries + how to close each

### 1+2. `Ev.faceStar_val_mono` (@675) & `Ev.evValid_exists` (@952) — CLOSE BY REFACTOR
These are the forward/reverse halves of the event bijection, currently built from scratch at
the presheaf level (~800 lines). **A read-only probe verified they both vanish** by rebuilding
`ev` as a THIN ADAPTER over the repo's flagship `equivWedgeCat` machinery, applied to
`K := serialWedge B`. Verdict: **feasible, sorry-free, needs only `serialWedge_admitsAltitude`
(already proven in `SegalAltitude.lean:224`) — NOT `serialWedge_nonSelfLinked`.**

Exact reuse (all in `Chains/`):
- `refineToWedgeObj` (Correspondence.lean:321, **unconditional**) — build a wedge map from a
  cube chain ⇒ **`evValid_exists`** (package σ's block/face data as a `RefineObj` of
  `serialWedge B`, then descend).
- `chainOfWedge_injective` (Correspondence.lean:63) + `bpset_hom_ext_of_wedgeToCubes`
  (Correspondence.lean:40), **unconditional** — a wedge map is determined by its cube list ⇒
  **`ev_reconstruct`** (injectivity is the wedge *colimit* property; `faceStar_val_mono`
  is NOT needed — delete it and `starSet_disjoint`).
- `wedgeToRefineMap` (Correspondence.lean:640, **needs only `AdmitsAltitude`**) — extracts the
  monotone block map + ordered per-block face `incl`; its `refinementMono` is literally the
  current `blockIdx_monotone` (already ported).
- `RefineObj`/`ChainRefine` (Refine.lean:42) carry `refinement`, `refinementMono`, `incl`.

Recommended restart move: rewrite `Ev.lean` as ~100-line adapter (define `evPerm` off
`(wedgeToRefine ⟨A,g⟩).incl` free-positions; get reconstruct/exists from the above), **preserving
the public surface** MainFunctor imports (`evPerm`, `ev_comp`, `ev_reconstruct`,
`ev_strictMonoOn`, `ev_blocks`, `blockIdx_monotone`, `IsEvValid`, `ev_valid`, `evValid_exists`,
`dimSum`, `globalEquiv`, `blockIdx`). Then MainFunctor rebuilds unchanged and both sorries are gone.

### 3. `NerveQuot.opQuotCatIso` (@482) — routine categorical
`Cat.of ((QuotCat P G)ᵒᵖ) ≅ Cat.of (QuotCat (OrderDual P) G)` (op commutes with the quotient).
The span-swap helpers `swapToDual`/`swapToOp` are written just above it (STAGED in a comment) —
they only need the `OrderDual` ≤-direction fixed (`toDual_le_toDual`/`ofDual_le_ofDual` expect
the *reversed* inequality), then define the two functors by `Quotient.map` of the swap and prove
the round-trips (the swap is involutive). No math depth.

## Staged, not-yet-finished (no sorries; just needs tactic repair)

- **`MainFunctor.PhiCatIso`** (strict category iso — the only remaining loose end near EOF).
  `stdObj_injective`, `objEquiv` (the object bijection) and the on-the-nose inverse functor `Ψ`
  are all **written and green** now. What's left: assemble `PhiCatIso : Cat.of (ChZ n) ≅
  Cat.of ((QC n)ᵒᵖ)` from the two round-trip equalities `Φ ⋙ Ψ = 𝟭` / `Ψ ⋙ Φ = 𝟭`. The `h_obj`
  legs discharge by `Equiv.symm_apply_apply`/`apply_symm_apply`; the open bits are (a) the `h_map`
  legs (finish the `Φ.map_injective` + `Functor.map_preimage` chase — the `simp` set was
  incomplete) and (b) `CategoryTheory.Functor.ext` is *overloaded* in this context, so
  disambiguate (a fully-qualified `_root_.CategoryTheory.Functor.ext` or `open`-scoping).
  OPTIONAL polish: `PhiEquiv` (equivalence) is the delivered main theorem and the nerve theorem
  is fine up to homotopy from it, so the strict form is not required.
- **`NerveQuot.nerve_chZ_iso`** — the final ChZ statement is a documented one-liner
  (`nerveQuotIso_of_catIso (ChZ n) Φiso`). To wire: `import CubeChains.FinalPrecubical.MainFunctor`,
  then add the def using `PhiCatIso` (needs the strict iso; if staying homotopical, restate via
  `PhiEquiv`). `nerveQuot (Perm (Fin n)) (OrderDual (Sal₀Br n))` is *by definition*
  `(nerve ((Sal₀Br n)ᵒᵖ)) / Perm (Fin n)`.

## Not started
- `Tests.lean` (working-agreement: n=2 direction tables etc.).
- Registration in `CubeChains.lean` (do only once sorry-free).
- Interface cleanup (see below).

## Architecture findings (answers to the review complaints)

1. **`nerveQuot` should visibly be "nerve P / G".** Mathlib has
   `SingleObj.Types.colimitEquivQuotient` (`.../Limits/Shapes/SingleObj.lean:104`):
   `colimit J ≃ orbitRel.Quotient G (J.obj star)` for `J : SingleObj G ⥤ Type`. So `(NP)/G`
   *can* be defined as `colimit` of the action functor `SingleObj G ⥤ SSet` (levelwise = the orbit
   quotient we hand-rolled). Mathlib has **no** dedicated "presheaf/SSet quotient by group action",
   so the colimit form needs gluing levelwise isos. Optional elegance refactor; current def is correct.
2. **Off-the-shelf quotient category?** **No.** `CategoryTheory.Quotient` quotients *morphisms*
   (keeps objects); `ActionCategory`/`SingleObj G ⥤ Cat` colimit give the *action groupoid*
   (objects = elements), not orbits. There is **no orbit-category constructor** and no support for
   the free-action *alignment* machinery — so hand-rolling `QuotCat P G` is justified.
3. **Why was `Ev` 800 lines + sorries?** It re-derived, at the presheaf level, the chain↔wedge
   correspondence that `equivWedgeCat` (RESULT 1) already proves sorry-free. **No new mathematical
   content** — redundant bookkeeping. Fix = the thin adapter in §1+2 above.

## One spec gap encountered
`Ev` and `Salvetti` both declared top-level `FinalPrecubical.dimSum` (byte-identical) — a hard
name-clash on import. Currently resolved by making Salvetti's `dimSum`/`dimSum_nil`/`dimSum_cons`
**`private`**. Cleanup: hoist one shared `dimSum` into a small common module.

## Suggested restart order
1. Rewrite `Ev` as the thin adapter over `equivWedgeCat` (§1+2) → kills both Ev sorries; keep the
   public surface so `MainFunctor` is unaffected.
2. Fix `NerveQuot.opQuotCatIso` (§3) → NerveQuot sorry-free.
3. (Optional) repair `MainFunctor.PhiCatIso` tactic lines → strict iso.
4. Wire `NerveQuot.nerve_chZ_iso` (import MainFunctor).
5. `Tests.lean`; consolidate `dimSum`; then register in `CubeChains.lean`.
