---
name: orient
description: Orient a fresh session on the Cubical (Lean 4) repo — what it is, the module map, build commands, conventions/gotchas, and the current proof status. Invoke at the START of any work on this repo to get up to speed and optimize context before reading code.
---

# Orienting on the Cubical repo

Lean 4 + mathlib formalization of **Ziemiański's cube-chain category `Ch(K)`** and
the relationship between automorphisms of a bi-pointed precubical set `K` and of
`Ch(K)` (the **lifting** and **lowering** lemmas). Lean `v4.30.0`, mathlib pinned to
`v4.30.0`.

## Do this first (context discipline)

1. **`MEMORY.md` is auto-loaded** — it is the live status board and links the
   per-topic memory files. Treat it as the freshest source of truth; this skill is
   the stable map.
2. **Read only the module you're touching** (see the map below) plus its direct
   deps. **Never read `.lake/`** (mathlib/deps) except to confirm a specific lemma
   signature; use `grep`/`rg` for that. Use the **Explore** agent for broad
   searches instead of opening many files.
3. **Build to verify, don't trust the IDE.** Cross-file IDE diagnostics are
   **stale** here — `lake build` is ground truth.
4. For deep detail on a subsystem, jump to the relevant memory file or `DESIGN.md`
   entry rather than re-deriving it.
5. **Off-the-shelf first — try fairly hard to reuse a mathlib construction before
   building your own.** Almost every categorical gadget here (over/comma categories,
   full subcategories, Kan extensions, adjunctions, localizations, free groupoids,
   limit/colimit preservation) already exists in mathlib with its typeclasses and
   API. Before hand-rolling a structure, category instance, functor, or adjunction,
   `grep` mathlib (or **read its docs** — see below) for the existing one and inherit
   it. A 3-line `def X := <mathlib thing>` that inherits instances beats a 40-line
   bespoke structure. See **Off-the-shelf mathlib APIs** below for the catalogue.
6. **Read Lean/mathlib docs as needed.** When unsure of an API's exact name,
   signature, or instance requirements, consult the source under
   `.lake/packages/mathlib/Mathlib/...` (grep first) or the web docs
   (`leanprover-community.github.io/mathlib4_docs`) via WebFetch/WebSearch — don't
   guess names from memory, and don't reinvent what you can look up.

## Build / check

- Whole project: `lake build CubeChains`
- One module: `lake build CubeChains.Chains.Category` (Correspondence is the slow
  one, ~45s; bump nothing, just wait)
- Property-testing harness: `lake build CubeChains.Testing.Examples`
- If oleans are missing: `lake exe cache get` (mathlib prebuilt cache)
- `.claude/settings.json` allows `lake/timeout/grep/rg/find/cat/sed/ls/head/tail/echo/cd/wc`.
  Permission match is a **prefix on the command string**, so start commands with an
  allowed binary and use absolute paths (avoid `cd X && …`; cwd persists across calls).

## Module map (dependency order)

**Two models of precubical sets coexist — know which you're in:**
- **Concrete / computable**: `PrecubicalConstructions` (graded cells + face maps).
- **Topos / "the real one"**: `PrecubicalSet := Boxᵒᵖ ⥤ Type`. Wedges are *generic
  pushouts* (`Classical.choice`), so `serialWedge`/`Ch`/`liftToCh` are
  **noncomputable** — this is forced, not spurious. The two are bridged by the cube
  Yoneda lemma (`Representable.lean`).

Foundations:
- `PrecubicalConstructions/Basic.lean` — concrete precubical sets; `face ε i`,
  `vertex₀/₁`, category instance.
- `PrecubicalConstructions/StandardCube.lean` — `□ⁿ` concretely (cells = sign
  vectors `{*,0,1}ⁿ`); `face`, `topCell`, `constVertex`, `freeMin`, `trueCount`.
- `Box.lean` — the box category `Box` and `PrecubicalSet := Boxᵒᵖ ⥤ Type` (topos,
  `HasPushouts` for free).
- `Representable.lean` — **cube Yoneda lemma**: `StdCube.canonicalMap`,
  `cubeRepr : (□ⁿ ⟶ K) ≃ K.cells n`. PROVED, sorry-free; everything downstream
  leans on it.
- `Bipointed.lean` — `BPSet` (bi-pointed precubical set) + `Hom` + category;
  `cells`, `vertex₀/₁`, `initVertexMap`/`finalVertexMap`. `Aut K = Iso K K`.
- `Wedge.lean` — `cube n` (representable), `wedge2` (pushout), `serialWedge`,
  `serialWedge.ι`.

Side conditions (`Altitude.lean`):
- `coface`, `faceMap`, `cubeMap`; the predicates `NonSelfLinked`, `AdmitsAltitude`,
  `Reach`/`Accessible`; and the altitude-of-pulled-back-cell theory
  (`trueCount`, `alt_map_eq`, `alt_vertex₀/₁`, `alt_cubeMap`).

Chains:
- `Chains/Basic.lean` — `CubeChain` (junction-vertex rep), `IsCubeChain`, `dims`,
  `ofIsCubeChain`, `vtxCanon`.
- `Chains/WedgeMap.lean` — wedge-map side: `wedgeDesc`, `wedgeToCubes`, serial-wedge
  cell-decomposition (`serialWedge_block_unique`, `wedge2_*`), `wedgeMap_block`.
  Big reusable-lemma library.
- `Chains/Refine.lean` — `ChainRefine`, `RefineObj`, the refinement category.
- `Chains/Category.lean` — `ChainCat.Obj`/`Hom`, `Ch : BPSet ⥤ Cat`,
  **`Aut.liftToCh`** (lifting), `OrientationPreserving`,
  `Aut.liftToCh_orientationPreserving` (proved, unconditional), and faithfulness:
  `ChainsJointlySurjective` + `Aut.liftToCh_injective_of_jointlySurjective`.
- `Chains/Correspondence.lean` — **`equivWedgeCat : RefineObj ≌ ChainCat.Obj K`**
  (under `NonSelfLinked` + `AdmitsAltitude`); thinness, `descent_mono`, both
  functors. SORRY-FREE.

Conjectures + counterexample:
- `Conjectures.lean` — **the only file with `sorry`** (by policy). Open statements:
  `chainsJointlySurjective_of_accessible`, `exists_lower_orientationPreserving`
  (existence half of lowering), plus the poset conjectures
  (`hom_subsingleton`/`chain_ext_of_altitude`/`hom_iff_facewise`).
  `liftToCh_injective` and the *uniqueness* half of `lower_orientationPreserving`
  are proved here modulo those inputs.
- `Unrealizable.lean` — the four-square-loop counterexample showing
  orientation-preservation is **necessary** for lowering.
- `Examples.lean` — type-level sanity checks.

Testing harness (decoupled — NOT imported by `CubeChains.lean` root):
- `Testing/{Model,Lowering,Examples}.lean` — a **computable** `FinBPSet` surrogate
  for `Ch K` (avoids the noncomputable topos machinery) to `#eval`/`native_decide`
  property-test conjectures on small finite `K`. See `[[cubechains-property-testing]]`.

## Current status / sorry frontier (verify against `MEMORY.md`)

- Project is **sorry-free except `Conjectures.lean`**.
- **Lifting** + **orientation-preservation of the lift** are proved, unconditionally.
- **Uniqueness/faithfulness** of the lift is proved modulo a clean geometric input
  (joint surjectivity ⟸ accessibility).
- **Lowering EXISTENCE is FALSE** in this symmetry-free setting — `□²` is the
  minimal counterexample (found via the testing harness). Don't try to prove
  `exists_lower_orientationPreserving`. The induced cube map is well-defined
  (coherent) but need not be **precubical**; that naturality failure is the real
  obstruction. See `[[cubechains-lowering-refuted]]`.

## Off-the-shelf mathlib APIs (reuse before building — see principle 5)

The catalogue of mathlib constructions this project leans on (or should). Prefer
`def Foo := <mathlib thing>` + inherited instances over bespoke structures. When a
name/signature is uncertain, **read the source/docs** (principle 6) — don't guess.

- **Over / comma categories** (`CategoryTheory.Comma.Over.Basic`): `Over X` objects are
  `{left, hom : left ⟶ X}`, morphisms are the commuting triangles — use this for any
  "object-with-a-map-to-`X`" category (e.g. cylinder maps `src ⟶ PathOb K`) instead of a
  hand-rolled structure + `Category` instance. `Under`, `StructuredArrow`,
  `CostructuredArrow` analogously.
- **Full subcategories** (`CategoryTheory.ObjectProperty.FullSubcategory`): `P.FullSubcategory`
  for `P : ObjectProperty C` (a predicate on objects) inherits the category and gives the
  `ι` forgetful functor — use to cut out a subcategory by a side condition.
- **Kan extensions** (`CategoryTheory.Functor.KanExtension.Adjunction`): `F.lan` (left Kan
  extension functor) and `F.lanAdjunction H : F.lan ⊣ (whiskeringLeft …).obj F`. A
  precomposition functor `(whiskeringLeft …).obj F` *always* has `F.lan` as left adjoint
  (instances auto-resolve for `Type`-valued presheaves on a small cat). This is how
  `PathOb`'s left adjoint (the box tensor) is obtained for free.
- **Adjunction ⇒ (co)continuity** (`CategoryTheory.Adjunction.Limits`):
  `adj.leftAdjoint_preservesColimits : PreservesColimitsOfSize F` (and the right-adjoint /
  limits dual). Use to get `F` preserves pushouts/colimits (e.g. the box tensor preserves
  the `serialWedge` pushouts) instead of constructing the comparison by hand.
- **Free groupoid / localization** (`CategoryTheory.Groupoid.FreeGroupoidOfCategory`,
  `CategoryTheory.Localization.*`): `FreeGroupoid C`, `FreeGroupoid.of/map/lift/liftNatIso`,
  `(of C).IsLocalization ⊤`. Morphisms of `FreeGroupoid C` are the zigzags of `C`.
- **Calculus of fractions** (`CategoryTheory.Localization.CalculusOfFractions`): if a
  `MorphismProperty` has a left/right calculus of fractions, localization morphisms are
  *single* spans/cospans (not arbitrary zigzags). NB: **not** available for `⊤` on a
  general category — needs an Ore-type condition; check before relying on it.
- **Reflective subcategories / adjunction builders** (`CategoryTheory.Adjunction.Reflective`,
  `Adjunction.mkOfHomEquiv`/`leftAdjointOfEquiv`): a fully-faithful right adjoint = a
  `Reflective` localization; use the framework for unit/counit/idempotency API.
- **`MorphismProperty` algebra** (`CategoryTheory.MorphismProperty.*`): multiplicative
  classes, 2-out-of-3, `IsInvertedBy`, `Localization` — already used for the `Weq` tower.
- **Cube Yoneda** (project-local `Representable.lean`): `cubeRepr`/`yonedaEquiv` give
  `(□ⁿ ⟶ K) ≃ K_n` — the cheap way to compute on representables (cheaper than a Kan-extension
  colimit). Pair it with the abstract adjunction rather than replacing it.

## Conventions & gotchas (the time-savers)

- **Symmetry-free precubical**: morphisms preserve face *index* — no axis swaps,
  no connections. So `Aut(□ⁿ) = {id}` (rigid). This is central to the lowering story.
- **`face ε i`**: `ε = false` is the source (`d⁰`) face, `true` the target (`d¹`).
- **`erw`, not `rw`**, for `PrecubicalSet` (= functor-category) compositions and for
  `yonedaEquiv_comp`/`ι_comp_wedgeDesc` etc. — `rw`/`simp` fail on an instance
  mismatch (`Functor.category.toCategoryStruct` vs `Category.toCategoryStruct`).
- **Rewriting under `yonedaEquiv`** fails the motive → convert to a plain morphism
  equation first (`Equiv.apply_eq_iff_eq_symm_apply`), or cancel a mono
  (`rw [← cancel_mono b.map.hom]`).
- `List.get_map` doesn't exist (use `getElem_map`/`by simp`); `Fin (l.map g).length`
  is *not* defeq `Fin l.length` (use `Fin.cast (by rw [List.length_map])`).
- `sorry` is allowed **only** in `Conjectures.lean`.
- Dimensions are `ℕ+`; coerce to `ℕ` only inside `cube`.

## Source docs and memories

- `DESIGN.md` — the conventions/decisions log (every non-obvious choice, with the PZ/Z
  paper references). `ClaudeSetup.md` — the original spec (§-numbered).
  `Unrealizable.md` — the counterexample writeup.
- Memory files (linked from `MEMORY.md`): `[[cubechains-deferred-sorries]]`,
  `[[correspondence-nonselflinked]]`, `[[unrealizable-counterexample]]`,
  `[[cubechains-lowering-refuted]]`, `[[cubechains-property-testing]]`.
- Papers: PZ = arXiv:2103.05336 (Lemma 2.11 = the poset structure of `Ch(K)`),
  Z = arXiv:1901.05206 (defines `Ch(K)`). NB: the lowering lemma is **not** a cited
  theorem — it is a project-original conjecture (and its existence half is refuted).
