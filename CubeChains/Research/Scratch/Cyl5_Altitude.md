# Cyl5 — Simplifications under `NonSelfLinked` + `AdmitsAltitude`

**Topic (user item 6).** Under the two side conditions `BPSet.NonSelfLinked K` and
`BPSet.AdmitsAltitude K` — exactly the regime where
`Correspondence.equivWedgeCat : RefineObj K.init K.final ≌ ChainCat.Obj K` holds and the
refinement category is **thin** — does the cylinder ⟹ pointed-functor construction
(`cylToPointedR : CylMapWeqR K ⥤ PointedEndofunctor (DPathGrpdR K)`) get easier?

Lean: `CubeChains/Research/Scratch/Cyl5_Altitude.lean`. **Sorry-free; green** under
`lake build CubeChains.Research.Scratch.Cyl5_Altitude`.

The construction recap (from the README):
`DPathGrpdR K = FreeGroupoid (RefineObj K.init K.final)`;
`cylToPointedObj c = pointedOfPaths F₀ η` with `F₀ x = Rgrpd (Lgrpd⁻¹ x)` and
`η x = counit.inv ≫ sweepR …`; the morphism map is forced because the base is a groupoid.

---

## Headline answer to item 1 — does thinness force `η` to be canonical?

**No — thinness of the BASE `RefineObj …` does NOT force `η` to be canonical.** The path
`η x : (of C).obj x ⟶ F₀ x` lives in the free **groupoid** `FreeGroupoid C`, whose hom-sets
are torsors over the fundamental group of the base, generally nontrivial even for a thin
(poset-like) base. The precise governing condition is thinness of the **free groupoid**, not of
`C`:

- **PROVEN `pointedOfPaths_eq_of_thin`** — if `Quiver.IsThin (FreeGroupoid C)` then
  `pointedOfPaths F₀ η = pointedOfPaths F₀ η'` (the construction is independent of `η`, depending
  only on `F₀`). This is the cleanest "canonicity" payoff.
- **PROVEN `pointedOfPaths_pt_app`** (the converse machinery) — `(pointedOfPaths F₀ η).pt.app
  (of x) = η x`: the chosen path is **fully recoverable** from the pointed endofunctor. No side
  conditions needed.
- **PROVEN `pointedOfPaths_eq_iff`** — combining the two:
  `pointedOfPaths F₀ η = pointedOfPaths F₀ η'  ↔  ∀ x, η x = η' x`.
  So `η` is canonical (forced by `F₀`) **exactly** when each path-hom `of x ⟶ F₀ x` is a
  subsingleton, i.e. exactly when `FreeGroupoid C` is thin. The base's thinness is *neither used
  nor sufficient*.

Net: the regime makes the BASE thin (`refineObj_isThin`, `chainCat_isThin`) but that buys
nothing for `η`'s canonicity; the real lever is `π₁` of the chain complex.

## Headline answer to item 2 — classification / surjectivity

**The TARGET is a preorder, unconditionally.**
`PointedEndofunctor (DPathGrpdR K)` is **thin** (`dpath_target_isThin`,
`pointedEndofunctor_isThin`): for any groupoid base the point axiom forces the unique
comparison `pointedHomOfGroupoid`. Hence:

- all the content of `cylToPointedR` is in its **object map** `cylToPointedObj`; the morphism map
  carries no information (`hom_eq_pointedHomOfGroupoid`, `cylToPointedObj_thin`).
- A "classification" of the image is therefore a classification of *objects* up to the preorder.
  This is the codiscreteness already flagged in the cylinder roadmap, now pinned in Lean.

So under (or without) the side conditions, surjectivity/classification questions reduce to the
object map `c ↦ (F₀, [η])` modulo the preorder — the morphism direction is degenerate.

## Headline answer to item 3 — leverage `equivWedgeCat`

**PROVEN transport across the equivalence.** Under the side conditions:

- `freeGroupoidEquiv` — the free groupoid of any equivalence `C ≌ D` is an equivalence
  `FreeGroupoid C ≌ FreeGroupoid D` (built from `FreeGroupoid.map` + `freeMapNatIso` + the strict
  `map_comp`/`map_id` laws via `Equivalence.mk`).
- `dpathEquivChain` — applying it to `equivWedgeCat`:
  `DPathGrpdR K = FreeGroupoid (RefineObj …) ≌ FreeGroupoid (ChainCat.Obj K)`.
- `pointedTransport` — pointed endofunctors transport along any equivalence (`F ↦ e⁻¹ ⋙ F ⋙ e`).
- `cylToPointedChain` — the cylinder's pointed endofunctor moved onto the wedge-map model:
  `CylMapWeqR K → PointedEndofunctor (FreeGroupoid (ChainCat.Obj K))`.

So the pointed-endofunctor target may equivalently be computed on `ChainCat.Obj K` ("the
construction commutes with the equivalence").

---

## Status table

### PROVEN (sorry-free Lean lemmas)

| Lemma | Statement |
|---|---|
| `refineObj_isThin` / `chainCat_isThin` | side conditions ⟹ base categories thin (repackaging `Correspondence`) |
| `conjFunctor_eq_of_thin` | thin free groupoid ⟹ conjugation functor independent of `η` |
| **`pointedOfPaths_eq_of_thin`** | **thin free groupoid ⟹ `pointedOfPaths` independent of `η` (KEY)** |
| `pointedOfPaths_pt_app` | `(pointedOfPaths F₀ η).pt.app (of x) = η x` (η recoverable) |
| `pointedOfPaths_eq_iff` | `pointedOfPaths F₀ η = pointedOfPaths F₀ η' ↔ ∀ x, η x = η' x` |
| `pointedEndofunctor_hom_subsingleton`, `pointedEndofunctor_isThin` | pointed endofunctors of a groupoid form a **preorder** |
| `hom_eq_pointedHomOfGroupoid` | every target morphism is the forced comparison |
| `freeMapNatIso`, `freeGroupoidEquiv` | `FreeGroupoid` of an equivalence is an equivalence |
| `dpathEquivChain` | `DPathGrpdR K ≌ FreeGroupoid (ChainCat.Obj K)` under the side conditions |
| `pointedTransport`, `cylToPointedChain` | transport of pointed endofunctors / the cylinder one |
| `dpath_target_isThin`, `cylToPointedObj_thin` | the live target `PointedEndofunctor (DPathGrpdR K)` is thin |

### CONJECTURED / OPEN (clearly marked, not in Lean)

- **`Quiver.IsThin C` ⇏ `Quiver.IsThin (FreeGroupoid C)`** (the negative half of item 1).
  Standard: the free groupoid on a thin category is the fundamental groupoid of its order
  complex. The 4-element poset whose Hasse diagram is a 4-cycle (the `□¹ ∨ □¹`-style boundary)
  has order complex `≃ S¹`, so `End x ≅ ℤ` in its free groupoid — *not* thin. Witnessing
  `End x ≅ ℤ` in Lean is a genuine `π₁`-computation, deliberately out of scope for this scratch.
  Consequence: for generic `K`, `cylToPointedObj`'s `η` is a real homotopy-class choice, **not**
  forced by `F₀`.
- **Exact identification of `Quiver.IsThin (DPathGrpdR K)`** with a `K`-level condition (e.g. the
  chain complex being simply connected). Conjecturally `DPathGrpdR K` is thin iff the order
  complex of `RefineObj K.init K.final` is simply connected; then and only then is the whole
  cylinder construction canonical (`pointedOfPaths_eq_of_thin` applies). Open.
- **Surjectivity / image classification of `cylToPointedR`** beyond "preorder on objects". With
  the morphism map degenerate (item 2), this is purely an object-image question; a finite-`K`
  characterization could be probed with the `Testing/` harness. Not attempted here.

---

## Bottom line

The side conditions make the *base* categories thin and give the clean transport
`DPathGrpdR K ≌ FreeGroupoid (ChainCat.Obj K)`, but they **do not** simplify the central
`η`-canonicity question: that is governed by `π₁` of the chain complex (thinness of the *free
groupoid*), which the side conditions do not control. The construction's only genuine
degeneracy — proven here unconditionally — is on the **morphism side**: the target is a
preorder, so `cylToPointedR` is determined by its object map up to forced comparisons.

**Best open question:** identify a `K`-level condition equivalent to
`Quiver.IsThin (DPathGrpdR K)` (conjecturally: simple-connectivity of the chain order complex).
Under it, `pointedOfPaths_eq_of_thin` makes the entire cylinder construction canonical
(object-only); without it, `η` is an essential homotopy-class choice.
