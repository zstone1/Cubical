---
name: orient
description: Orient a fresh session on the Cubical (Lean 4) repo — build commands, the mathlib-reuse table, and the conventions/gotchas that cost time to rediscover. Invoke at the START of any work on this repo, before reading code.
---

# Orienting on the Cubical repo

Lean 4 + mathlib, both pinned to `v4.30.0`. Formalizes the **concurrency braid groupoid** of a
precubical set: the executions of a cube chain `Ch(K)` made into a groupoid, and the theorem that
for the standard cube it is the pure braid group (for the terminal set, the full braid group).

This skill carries only what lives nowhere else: build, mathlib reuse, gotchas. The file map
is `ARCHITECTURE.md`, the board is `bd`, the conventions log is `DESIGN.md`.

## Build / check

- Whole project: `lake build CubeChains`. One module: `lake build CubeChains.Chains.Category`.
  `Chains.Correspondence` is the slow one (~45s) — let it run.
- Testing harness, decoupled (not reached by `lake build CubeChains`):
  `lake build CubeChains.Testing.SalvettiSpotCheck` (or any `Testing/` module).
- Missing oleans: `lake exe cache get`.
- **Trust `lake build`, not the IDE.** Cross-file IDE diagnostics are stale here.
- **Never read `.lake/`.** To confirm a mathlib name or signature, `grep`/`rg` the source under
  `.lake/packages/mathlib/Mathlib/`, or read `leanprover-community.github.io/mathlib4_docs` —
  don't guess names. For broad searches use the **Explore** agent, not many `Read`s.

## Off-the-shelf mathlib first

Try fairly hard to reuse a mathlib construction before building your own: a 3-line
`def X := <mathlib thing>` that inherits instances beats a 40-line bespoke structure.
`Salvetti/Elements.lean` (reusing `CategoryTheory.Elements` + thinness) is an in-repo exemplar.

| need | mathlib |
|---|---|
| category of elements / Grothendieck | `CategoryTheory.Elements`: `F.Elements`, `π`, `mapEquivalence` (see `Salvetti/Elements.lean`) |
| slices, over/under, comma | `CategoryTheory.Comma.Over.Basic`: `Over X`; likewise `Under`, `StructuredArrow`, `CostructuredArrow` |
| subcategory cut out by a predicate on objects | `CategoryTheory.ObjectProperty.FullSubcategory` — inherits the category and `ι` |
| thin categories | `CategoryTheory.Thin`: `Quiver.IsThin C := ∀ X Y, Subsingleton (X ⟶ Y)`, and `iso_of_both_ways` — isos with no coherence obligations |
| monos stable under pushout | `CategoryTheory.Adhesive`: `Adhesive.mono_of_isPushout_of_mono_left` / `…_right` |
| Kan extensions | `CategoryTheory.Functor.KanExtension.Adjunction`: `F.lan`, `F.lanAdjunction` |
| colimit preservation for free | `CategoryTheory.Adjunction.Limits`: `adj.leftAdjoint_preservesColimits` (+ duals) |
| free groupoid on a category | `CategoryTheory.Groupoid.FreeGroupoidOfCategory`: `FreeGroupoid`, `.of` / `.map` / `.lift` / `.liftNatIso` |
| computing on representables | project-local `Foundations/Representable.lean`: cube Yoneda `cubeRepr : (□ⁿ ⟶ K) ≃ K.cells n` |

## Gotchas

- **Symmetry-free precubical**: morphisms preserve the face *index* — no axis swaps, no
  connections. Hence `Aut(□ⁿ) = {id}`, the cubes are rigid. This is why `(BPSet, ⊗)` has no swap and
  the braiding is *created* by the passage to executions, not inherited.
- **`erw`, not `rw`**, for `PrecubicalSet` (functor-category) compositions and `yonedaEquiv_comp`:
  `rw`/`simp` fail on an instance mismatch — `Functor.category.toCategoryStruct` vs
  `Category.toCategoryStruct`.
- **Rewriting under `yonedaEquiv`** fails the motive. Convert to a plain morphism equation first
  (`Equiv.apply_eq_iff_eq_symm_apply`), or cancel a mono (`rw [← cancel_mono …]`).
- **Dot notation on `K.toPsh`** (a raw `Boxᵒᵖ ⥤ Type`) does not resolve project lemmas — write
  `PrecubicalSet.foo K.toPsh …` fully qualified.
- `List.get_map` does not exist (use `getElem_map` / `by simp`), and `Fin (l.map g).length` is
  *not* defeq to `Fin l.length` (use `Fin.cast (by rw [List.length_map])`).
- Wedges are generic pushouts, so `serialWedge` / `Ch` / `liftToCh` are `noncomputable` — forced,
  not a defect to route around.
- No `sorry`, no `admit`.

## Then

Run `bd ready` for what is open, and read `ARCHITECTURE.md` for the file map and its
"where do I find…?" index. Open the one module you need, plus its direct deps.
