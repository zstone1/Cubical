---
name: orient
description: Orient a fresh session on the Cubical (Lean 4) repo — what it is, the module map, build commands, conventions/gotchas, and the current proof status. Invoke at the START of any work on this repo to get up to speed and optimize context before reading code.
---

# Orienting on the Cubical repo

Lean 4 + mathlib formalization of **Ziemiański's cube-chain category `Ch(K)`** and
the relationship between automorphisms of a bi-pointed precubical set `K` and of
`Ch(K)` (the **lifting** and **lowering** lemmas). Lean `v4.30.0`, mathlib pinned to
`v4.30.0`.

**`ARCHITECTURE.md` is the canonical file map** (layers + a "where do I find X?" index).
Read it to pick the one file you need, then open just that file + its docstring.

## Do this first (context discipline)

1. **`MEMORY.md` is auto-loaded** — the live status board, linking the per-topic memory files.
   Treat it + `ARCHITECTURE.md` as the freshest truth.
2. **Read only the module you're touching** plus its direct deps. **Never read `.lake/`**
   (mathlib/deps) except to confirm a specific lemma signature; use `grep`/`rg` for that. Use
   the **Explore** agent for broad searches instead of opening many files.
3. **Build to verify, don't trust the IDE.** Cross-file IDE diagnostics are **stale** here —
   `lake build` is ground truth.
4. For deep detail on a subsystem, jump to the relevant memory file or `DESIGN.md` entry.
5. **Off-the-shelf first — try fairly hard to reuse a mathlib construction before building your
   own.** Almost every categorical gadget here (over/comma categories, full subcategories, Kan
   extensions, adjunctions, free groupoids, thin categories, adhesive/pushout API, limit/colimit
   preservation) already exists in mathlib with its typeclasses. A 3-line `def X := <mathlib thing>`
   that inherits instances beats a 40-line bespoke structure. `Chains/Slice.lean` is the in-repo
   exemplar. See **Off-the-shelf mathlib APIs** below.
6. **Read Lean/mathlib docs as needed.** When unsure of an API's exact name/signature, consult the
   source under `.lake/packages/mathlib/Mathlib/...` (grep first) or the web docs
   (`leanprover-community.github.io/mathlib4_docs`) — don't guess names, don't reinvent.

## Build / check

- Whole project: `lake build CubeChains`
- One module: `lake build CubeChains.Chains.Category` (`Chains.Correspondence` is the slow one,
  ~45s; bump nothing, just wait)
- Property-testing harness (decoupled): `lake build CubeChains.Testing.Examples`
- If oleans are missing: `lake exe cache get` (mathlib prebuilt cache)
- `.claude/settings.json` allows `lake/timeout/grep/rg/find/cat/sed/ls/head/tail/echo/cd/wc`.
  Permission match is a **prefix on the command string**, so start commands with an allowed binary
  and use absolute paths (avoid `cd X && …`; cwd persists across calls).

## Module map — folders = areas (full per-file map: `ARCHITECTURE.md`)

**Two models of precubical sets coexist — know which you're in:** concrete/computable
(`Foundations/PrecubicalConstructions/`, graded cells + face maps) and topos
(`PrecubicalSet := Boxᵒᵖ ⥤ Type`). Wedges are generic pushouts, so `serialWedge`/`Ch`/`liftToCh`
are **noncomputable** (forced, not spurious). The two are bridged by the cube Yoneda lemma
(`Foundations/Representable.lean`). Topos is the default downstream.

- **`Foundations/`** — `PrecubicalConstructions/{Basic,StandardCube}` (concrete model); `Box`
  (box cat + `PrecubicalSet`, `HasPushouts` free); `Representable` (cube Yoneda `cubeRepr`,
  `trueCount`, `coface`); `Bipointed` (`BPSet`, `vertex₀/₁`, `cubeMap`/`faceMap`, `IsAltitude`);
  `Wedge` (`cube`, `wedge2`, `serialWedge`); `Shift` (box shift, `PathOb`, `⊗□¹⊣PathOb`);
  `Altitude` (`NonSelfLinked`, `AdmitsAltitude`, `Accessible` — all `PrecubicalSet`-level).
- **`Chains/`** — `Basic` (`CubeChain`, `IsCubeChain`); `WedgeMap` (wedge↔cube-list decomposition
  + reusable `glue0_*` pushout cores + mono infra); `Refine` (`ChainRefine`, `RefineObj`);
  `RefineConcat` (generic `RefineObj.append`/`appendLeft` kernel); `Category` (`Ch`, **`liftToCh`**);
  **`Correspondence`** (`equivWedgeCat` — **RESULT 1**, `Quiver.IsThin`); `RefineFunctor`
  (`Refine.pushforward`); `Lifting` (`refineAut := pushforward σ.hom`); `Slice` (`Ch ↪ Over K` ff);
  `Segal`(+`SegalAltitude`) (`Ch(X∨Y) ≌ Ch X × Ch Y`, faithful via adhesive).
- **`Cylinder/`** (was `Operations/`) — `PointedFunctor` (`PointedEndofunctor` + groupoid API,
  mathlib `FreeGroupoid`); `Cylinder` (prism core: `cylTranspose`, `CylMap`, `prism`);
  `CylinderRefineCore` (geometry); `CylinderSweep` (the `sweepR` staircase); **`CylinderRefine`**
  (`cylToPointedR` — **RESULT 2**, thin deliverable).
- **`Arrangements/`, `Salvetti/`, `Schedule/`** — the braid/COM/Salvetti fundamentals, the
  `Sal(braidCOM n) ≌ Int(Lines)` comparison, and the HDA schedule-space study of `Ch(K)`
  (each folder has a `README.md`).
- **`Testing/`** (decoupled, NOT built by `lake build CubeChains`) — computable `FinBPSet`
  surrogate for `Ch K` to `#eval`/`native_decide` conjectures on small finite `K`. See
  `[[cubechains-property-testing]]`.

## Current status / sorry frontier (verify against `MEMORY.md`)

- Project is **entirely sorry-free**.
- **RESULT 1** (`equivWedgeCat : RefineObj K ≌ ChainCat.Obj K`) and **RESULT 2** (`cylToPointedR`)
  are both proved, sorry-free.
- **Lifting** + **orientation-preservation of the lift** are proved, unconditionally.
- **Uniqueness/faithfulness** of the lift is proved modulo a clean geometric input
  (`ChainsJointlySurjective K`, an accessibility hypothesis; `Chains/Category.lean`).
- **Lowering EXISTENCE is FALSE** in this symmetry-free setting — `□²` is the minimal
  counterexample (found via the testing harness). The old `exists_lower_orientationPreserving`
  conjecture was **refuted and removed** (don't re-add it). The induced cube map is coherent but
  need not be **precubical** — that naturality failure is the obstruction. See
  `[[cubechains-lowering-refuted]]`.

## Off-the-shelf mathlib APIs (reuse before building — see principle 5)

Prefer `def Foo := <mathlib thing>` + inherited instances over bespoke structures. When a
name/signature is uncertain, **read the source/docs** — don't guess.

- **Over / comma categories** (`CategoryTheory.Comma.Over.Basic`): `Over X` — used for `CylMap`
  (= `Over (PathOb K)`). `Under`, `StructuredArrow`, `CostructuredArrow` analogously.
- **Full subcategories** (`CategoryTheory.ObjectProperty.FullSubcategory`) — cut out a subcategory
  by an object predicate; inherits the category + `ι`.
- **Thin categories** (`CategoryTheory.Thin`): `Quiver.IsThin C := ∀ X Y, Subsingleton (X ⟶ Y)`;
  `iso_of_both_ways` builds isos with no coherence obligations. Used in `Correspondence`/`Segal`.
- **Adhesive / pushouts** (`CategoryTheory.Adhesive`, `IsPushout`, `IsPullback`): monos are stable
  under pushout — `Adhesive.mono_of_isPushout_of_mono_*`. Used for the wedge monos / Segal faithful.
- **Kan extensions** (`CategoryTheory.Functor.KanExtension.Adjunction`): `F.lan` + `F.lanAdjunction`.
  Used in `Slice` (blind Kan extension). The box-tensor `⊗□¹ ⊣ PathOb` is obtainable this way.
- **Adjunction ⇒ (co)continuity** (`CategoryTheory.Adjunction.Limits`):
  `adj.leftAdjoint_preservesColimits` (+ duals) — get pushout/colimit preservation for free.
- **Free groupoid** (`CategoryTheory.Groupoid.FreeGroupoidOfCategory`): `FreeGroupoid C`,
  `FreeGroupoid.of/map/lift/liftNatIso`. The target `DPathGrpdR K := FreeGroupoid (RefineObj K)`.
- **Cube Yoneda** (project-local `Foundations/Representable.lean`): `cubeRepr`/`yonedaEquiv` give
  `(□ⁿ ⟶ K) ≃ K_n` — the cheap way to compute on representables.

## Conventions & gotchas (the time-savers)

- **Symmetry-free precubical**: morphisms preserve face *index* — no axis swaps, no connections.
  So `Aut(□ⁿ) = {id}` (rigid). Central to the lowering story.
- **`face ε i`**: `ε = false` is the source (`d⁰`) face, `true` the target (`d¹`).
- **`erw`, not `rw`**, for `PrecubicalSet` (functor-category) compositions and `yonedaEquiv_comp`
  etc. — `rw`/`simp` fail on an instance mismatch (`Functor.category.toCategoryStruct` vs
  `Category.toCategoryStruct`).
- **Rewriting under `yonedaEquiv`** fails the motive → convert to a plain morphism equation first
  (`Equiv.apply_eq_iff_eq_symm_apply`), or cancel a mono (`rw [← cancel_mono b.map.hom]`).
- **Dot notation on `K.toPsh`** (a raw `Boxᵒᵖ ⥤ Type`) doesn't resolve project lemmas — use the
  fully-qualified `PrecubicalSet.foo K.toPsh …` form.
- `List.get_map` doesn't exist (use `getElem_map`/`by simp`); `Fin (l.map g).length` is *not* defeq
  `Fin l.length` (use `Fin.cast (by rw [List.length_map])`).
- The repo is **sorry-free**.
- Dimensions are `ℕ+`; coerce to `ℕ` only inside `cube`.

## Source docs and memories

- `ARCHITECTURE.md` — the canonical file map + "where do I find X" index (read this first).
- `DESIGN.md` — conventions/decisions log (with PZ/Z paper references).
- Per-area `README.md` in `Arrangements/`, `Salvetti/`, `Schedule/`.
- Memory files (linked from `MEMORY.md`): `[[cubechains-deferred-sorries]]`,
  `[[correspondence-nonselflinked]]`, `[[unrealizable-counterexample]]`,
  `[[cubechains-lowering-refuted]]`, `[[cubechains-property-testing]]`, `[[cubechains-cylinder-roadmap]]`.
- Papers: PZ = arXiv:2103.05336 (Lemma 2.11 = poset structure of `Ch(K)`),
  Z = arXiv:1901.05206 (defines `Ch(K)`). NB: the lowering lemma is **not** a cited theorem — a
  project-original conjecture whose existence half is refuted.
