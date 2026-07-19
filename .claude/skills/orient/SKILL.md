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
  Nothing is slow — the whole tree builds in ~30s and no file sets `maxHeartbeats`. If you find
  yourself wanting one, you have hit a spelling mismatch (see Gotchas), not a hard proof.
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
- **If you reach for `erw`, you have hit a _spelling mismatch_ — not an instance mismatch.** (The
  old "`Functor.category.toCategoryStruct` vs `Category.toCategoryStruct`" advice was **false**:
  traced with `pp.explicit`, both `≫` use the identical instance, and plain `rw [yonedaEquiv_comp]`
  works fine.) The real gap is `CategoryStruct.comp`'s **object argument**: the outer `≫` may carry
  `Y := (X ∨ Y).toPsh` while the inner carries `Z := Glue.gluePsh X.finalVertex Y.initVertex`.
  `rfl`-equal, not syntactically equal — and `rw`'s `kabstract` matches at `.instances`
  transparency, so it will not unfold a plain `def` (`wedge2`) to reach `Glue.gluePsh`. Hence
  `Category.assoc` can fail on a goal that *prints as* `(f ≫ g) ≫ h`. Same shape: `⋁(n::da)` vs
  `□n ∨ ⋁da`; `(K.repoint a b).toPsh` vs `K.toPsh` (a type ascription does **not** fix that one).
  **Cures, in order:** unify the spelling with a reducible wrapper typed the way callers see it
  (`wedgeInl`/`wedgeInr`/`wedge2Desc` in `Foundations/WedgeMonoidal.lean` are the worked example);
  or use `exact`/`.trans`, since elaboration unifies at default transparency where `kabstract`
  will not. Only 7 `erw` survive repo-wide, each with a comment naming its load-bearing defeq.
- **Foundational machinery proves the strongest `BPSet`-level statement available.** Never weaken a
  def or lemma to the presheaf level (`.toPsh ⟶ .toPsh`) to make a tactic fire — callers project
  with `.hom`. `BPSet.Hom` bundles `app_init`/`app_final`, so `BPSet`-level statements carry the
  endpoint conditions for free and keep `⊗`/`▷`/`◁`/`α_`/`λ_`/`ρ_` and `monoidal` usable. To track
  endpoint data beside a map, **re-point the target** (`BPSet.repoint`) instead of pairing value
  with proof by hand.
- **Rewriting under `yonedaEquiv`** fails the motive. Convert to a plain morphism equation first
  (`Equiv.apply_eq_iff_eq_symm_apply`), or cancel a mono (`rw [← cancel_mono …]`).
- **Dot notation on `K.toPsh`** (a raw `Boxᵒᵖ ⥤ Type`) does not resolve project lemmas — write
  `PrecubicalSet.foo K.toPsh …` fully qualified.
- `List.get_map` does not exist (use `getElem_map` / `by simp`), and `Fin (l.map g).length` is
  *not* defeq to `Fin l.length` (use `Fin.cast (by rw [List.length_map])`).
- Wedges are **computable**: `wedge2` is built on the bespoke `Glue.gluePsh` (a pointwise `Quot`),
  deliberately *not* mathlib's `Classical.choice`-opaque `pushout`, so `serialWedge` / `Ch` /
  `liftToCh` compute. Keep it that way — do not "simplify" `Glue` into `Limits.pushout`.
- No `sorry`, no `admit`.

## Then

Run `bd ready` for what is open, and read `ARCHITECTURE.md` for the file map and its
"where do I find…?" index. Open the one module you need, plus its direct deps.
