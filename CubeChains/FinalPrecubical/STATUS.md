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

## Module status — ✅ MAIN THEOREM COMPLETE, ENTIRE FOLDER SORRY-FREE (2026-07-06)

`#print axioms PhiEquiv` = `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).

| Module | State | Delivers |
|---|---|---|
| `QuotientCat` | ✅ sorry-free | `OrderFreeAction`, `QuotCat P G` (+`Category`), `align`, `homEquivUpSet` |
| `Salvetti` | ✅ sorry-free | `BrFace`/`Sal₀Br` posets, `MulAction`+`OrderFreeAction (Perm (Fin n))`, `stdPair`/`stdPairAt`, `orbit_rep_unique`, `levelSizes_*` |
| `Ev` | ✅ **SORRY-FREE** | `evPerm`, `ev_comp`, `ev_reconstruct`, `ev_strictMonoOn`, `ev_blocks`, `blockIdx_monotone`, `IsEvValid` (now +`Monotone bm`), `ev_valid`, **`faceStar_val_mono`** (owner rule, closed via interval/corner model), **`evValid_exists`** (realization, cumulative-OR construction) |
| `MainFunctor` | ✅ sorry-free | **`PhiEquiv : ChZ n ≌ (QC n)ᵒᵖ`** (MAIN THEOREM, sorry-free), terminal `Z`, `ChZ n`, `Φ`, Full/Faithful/EssSurj, `objEquiv`/`Ψ`, `PhiCatIso` (staged) |
| `NerveQuot` | ✅ sorry-free | `nerveQuot`, **`nerveQuotIso : (NP)/G ≅ N(P//G)`** (STRICT), `nerveQuotIso_of_catIso`, `opQuotCatIso`, `nerve_chZ_iso` (documented one-liner) |

Remaining (non-sorry) polish: `PhiCatIso` (strict cat-iso form; `PhiEquiv` is the delivered theorem),
`nerve_chZ_iso` wiring, `Tests.lean`, and registration in `CubeChains.lean`.

## The 3 remaining sorries + how to close each

### ⚠ CORRECTION (2026-07-06): the old "thin-adapter over `equivWedgeCat`" plan below §1+2 was WRONG
`equivWedgeCat`'s thinness is about morphisms between *fixed* objects; it does **not** give the
"owner rule" (a face's fixed 0/1 values are forced by star positions + the chain/junction
condition). `ev f` is a permutation that *discards* fixed values, so `ev_reconstruct` /
`evValid_exists` genuinely need that content — reuse alone cannot kill them. (The old rebuild that
assumed this regressed Ev to 7 sorries; it was reverted.)

### 1+2. `Ev.faceStar_val_mono` (@670) & `Ev.evValid_exists` (@950) — the "owner rule" (irreducible)
These are the forward/reverse halves of the event bijection — PZ Def 6.11. The current file
isolates them cleanly: everything downstream of `faceStar_val_mono` (`starSet_disjoint`,
`evCell_determined`, `ev_reconstruct`, `ev_bijective`) is **already proven on top of it**.

**ELEGANT MODEL (validated 2026-07-06): faces = intervals `[vertex₀, vertex₁]`.**
A face is determined by its two corner vertices; along a chain `vertex₁(faceᵢ) = vertex₀(faceᵢ₊₁)`
*by definition of `IsCubeChain`* (`vtxCanon` API, `Chains/Basic.lean:107-164`). So the corners are
the cumulative OR of the stars, and the owner rule is a one-step junction telescoping, not a
geometric lemma. Concretely:

- **`faceStar_val_mono`**: the one-step junction gives
  `getD true (faceStarⱼ.val c) = getD false (faceStarⱼ₊₁.val c)` for consecutive same-block `j,j+1`
  (via `map_vertex₀/₁` + `IsCubeChain` junction + **block inclusions injective at dim 0**), so
  `≠ some false` at `j` ⟺ `= some true` at `j+1`; iterate over `[i,i']` (all same block by the
  proven `blockIdx_monotone`).
- **`evValid_exists`**: build corners by cumulative OR of `σ`'s stars, faces `= [wᵢ,wᵢ₊₁]`; the
  chain condition is automatic; descend via `wedgeDesc`/`equivWedgeHom`. **NSL-free.**

**LINCHPIN — DONE (2026-07-06):** the dim-0 (vertex-level) case of block-inclusion injectivity.
`WedgeMap.lean`'s `vertexMap_app_injective`, `glue0_inl/inr_app_injective`,
`wedge2_inl/inr_app_injective`, `serialWedge_ι_app_injective` were **generalized to all `m`**
(dropped `1 ≤ m`) — `□⁰.cells m` is a `Subsingleton` at every level, so one proof-term swap does it.
This is the vertex-non-folding fact the whole owner rule needs (the rebuild *assumed* it via NSL
but never proved it; it is not NSL-via-thinness, it is direct dim-0 injectivity). Builds green.

**DONE (2026-07-06): `faceStar_val_mono` CLOSED** (sorry #1 gone), and with it all its
downstream (`ev_reconstruct` = faithfulness, `ev_bijective`, `starSet_disjoint`). The elegant
model landed as, in `Ev.lean`:
- `app_val` — value form of `noneSet_app`: `(app w v).val c` = `w`'s fixed value, or `v`'s value
  at the matching free slot (strong induction, reuses the `nones_app` theory);
- `toStar_vertex₀/₁_val` — sign-vector↔corner bridge (`ev_comp` + `app_unique` + `app_val`);
- `blockFace_junction_val` — equal readings from a shared junction (dim-0 `serialWedge_ι_app_injective`);
- `evCell_junction` — `vertex₁(evCell g j) = vertex₀(evCell g (j+1))` (`vtxCanon`);
- `faceStar_step` / `faceStar_step_v` — one junction step; `faceStar_val_mono` iterates it over the
  block (value-parametrised coordinate so all `Fin`/cube casts collapse; `blockIdx_monotone` squeeze).

**REMAINING: `evValid_exists` (sorry #2, realization/fullness) — IN PROGRESS.**

**IsEvValid was STRENGTHENED (bug fix):** added `Monotone bm`. It was FALSE as previously stated —
`A=B=[1,1]`, `σ=swap` satisfies the old clauses but is unrealizable (`g(e₀)` starts at `init`, forcing
`g(e₀)=e₀`). `ev_valid` now supplies `blockIdx_monotone g`; `MainFunctor.Phi_full_interface` supplies
the monotone merge `hm_mono` from `BrFace.le`. Whole stack rebuilt green.

**DONE (green, ~200 lines of realization infrastructure in `Ev.lean`):**
`starCoord` (p-th star coord) + `globalEquiv_starCoord`; `realOwner`; `realFaceVal` (owner-rule
sign vector) + `realFaceVal_none_iff`; `realOwner_starCoord`, `starCoord_inj`; **`realFace_card`**
(noneSet = image of star embedding, card = A.get i) + `realFace` (the cell); `blockCell`
(`canonicalMap`) + `toStar_blockCell`; `cellFace` (`ι`-embedded); `realBm_surj` (bm surjective from
covering); `toStar_injective`, `toStar_canonicalMap`; **`blockCell_vertex_junction`** (same-block
junction via `toStar_injective` + the corner bridge; block index carried as a variable so the cube
cast `subst`s away).

**STILL TODO (the geometric assembly, ~250 lines, one API gap):**
1. same-block value-match feeding `blockCell_vertex_junction` (owner trichotomy: both corners =
   `true` iff owner ≤ i);
2. **cross-block junction** — the wedge junction `ι_r(1̄)=ι_{r+1}(0̄)` is NOT a real gap: it equals
   `vertex₁(evCell (𝟙 (serialWedge B)) r) = vertex₀(evCell 𝟙 (r+1))`, i.e. **reuse `evCell_junction`
   applied to `𝟙 (serialWedge B)`** (whose block cells `evCell 𝟙 r = yonedaEquiv (ι B r)` are the
   `ι`-images; `vertex₁ = ι.app(final)` via `vertex₁_yonedaEquiv`/`map_vertex₁`). Plus boundary
   conditions `vertex₁(blockCell i)=1̄` (all `owner ≤ i`) / `vertex₀(blockCell(i+1))=0̄` — from
   `hcover`+`hbm_mono`: `bm(owner c)=bm i`, so `owner c > i ⇒ bm(owner c)≥bm(i+1)>bm i`, contra; plus
   `bm(i+1)=bm i+1` (monotone+`realBm_surj` ⇒ no skips);
3. `cellFace_junction` assembling 1+2; then `IsCubeChain` (endpoints `init`/`final` + junctions);
4. descent via `wedgeDesc`/`wedgeDescHom` (+ bipointedness); readback `evPerm g = σ` via
   `ι_comp_wedgeDesc`/`wedgeToCubes_wedgeDesc` ⇒ `blockIdx g = bm`, `faceStar g = realFace`,
   `nones (realFace i) = starCoord i`.

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
