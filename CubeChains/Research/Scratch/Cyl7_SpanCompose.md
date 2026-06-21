# Cyl7_SpanCompose — span composition of cylinders, the length-2 cocylinder `K^{I₂}`, and the reparametrization obstruction

Scratch findings for the cylinder ⟹ pointed-functor program (RESULT 2). Companion to
`Cyl7_SpanCompose.lean` (decoupled from the green build; `lake build
CubeChains.Research.Scratch.Cyl7_SpanCompose`, **sorry-free and green**, no warnings).

## VERDICT (lead)

**Yes — the homotopies line up, and span composition works.** Two cylinders, viewed as spans
`K ⟵ᴸ src ⟶ᴿ K`, compose via the pullback `P = E₁ ×_K E₂` (precubical sets have all pullbacks, off
the shelf). The two classifying maps `cyl₁∘π₁` and `cyl₂∘π₂` **glue** to a single map
`P ⟶ PathOb K ×_K PathOb K`, with composite legs `L₁∘π₁` (left) and `R₂∘π₂` (right). This is
**PROVEN** (sorry-free).

The composite lands over the **length-2** interval `I₂ = □¹ ∨ □¹`, i.e. in the length-2 cocylinder
`K^{I₂} = PathOb K ×_K PathOb K`. Collapsing it back to a strict `□¹`-cylinder requires a precubical
**fold** `□¹ → I₂` covering both segments, which **does not exist** — **PROVEN** (`no_fold_edge`,
sorry-free). Therefore:

> **The strict `□¹`-cylinder image is NOT `·`-closed: it is off by exactly one reparametrization.**
> The composite is honestly length-2 and there is no precubical map to renormalise it back to
> length-1. The fix is **Moore cylinders** (homotopies over any `Iₙ`), whose image IS `·`-closed
> (composing `Iₘ`- and `Iₙ`-cylinders gives an `Iₘ₊ₙ`-cylinder, no fold needed) and on which
> `cylToPointed` is a monoid homomorphism.

This sharpens, and gives the precise *geometric* mechanism behind, Cyl6's pinned obstruction
("no `PathOb` multiplication, because precubical sets lack degeneracies"): the missing
multiplication `PathOb K ×_K PathOb K → PathOb K` is exactly the (non-existent) reparametrization
fold `□¹ → I₂`. The pullback `PathOb K ×_K PathOb K` itself exists and the composite lands in it;
what fails is *only* the length-2 → length-1 collapse.

---

## 1. POSITIVE — span composition via the pullback `E₁ ×_K E₂` — **PROVEN**

A cylinder `c : CylMap K = Over (PathOb K)` is the span `K ⟵ leftLeg src rightLeg ⟶ K` with
`leftLeg = cyl ≫ endpoint false`, `rightLeg = cyl ≫ endpoint true` (from `Cylinder/Cylinder.lean`).

| Def / theorem | Statement | Status |
|---|---|---|
| `spanPullback c₁ c₂` | `P = pullback c₁.rightLeg c₂.leftLeg` (the span-pullback over `K`) | **PROVEN** (def) |
| `spanπ₁`, `spanπ₂` | the two projections `P ⟶ c₁.src`, `P ⟶ c₂.src` | **PROVEN** (def) |
| `span_condition` | `π₁ ≫ rightLeg₁ = π₂ ≫ leftLeg₂` (pullback condition) | **PROVEN** |
| `spanCompose c₁ c₂` | the glued map `P ⟶ pathOb2 K = PathOb K ×_K PathOb K` | **PROVEN** |
| `spanCompose_fst/snd` | `spanCompose ≫ fst = π₁ ≫ cyl₁`, `… ≫ snd = π₂ ≫ cyl₂` | **PROVEN** (`@[simp]`) |
| `spanCompose_leftLeg` | `spanCompose ≫ leftEnd = π₁ ≫ leftLeg₁` (composite left leg `= L₁∘π₁`) | **PROVEN** |
| `spanCompose_rightLeg` | `spanCompose ≫ rightEnd = π₂ ≫ rightLeg₂` (composite right leg `= R₂∘π₂`) | **PROVEN** |

**The gluing is the heart.** `spanCompose` is built by `pullback.lift (π₁ ≫ cyl₁) (π₂ ≫ cyl₂) h`,
where `h` is the obligation that the two homotopies' *inner* ends agree:
`(π₁ ≫ cyl₁) ≫ endpoint true = (π₂ ≫ cyl₂) ≫ endpoint false`. After reassociating, this is exactly
`π₁ ≫ rightLeg₁ = π₂ ≫ leftLeg₂` = the span-pullback condition. **So "the homotopies line up" is
literally the pullback's universal property** — no extra hypothesis. The composite legs come out as
genuine span composition `(L₁∘π₁, R₂∘π₂)`.

No matching hypothesis (`c₁.rightLeg = c₂.leftLeg`) is needed or even well-typed (the two legs have
different domains `c₁.src`, `c₂.src`); the matching happens *over `K`* inside the pullback, which is
the correct categorical formulation of span composition.

---

## 2. IDENTIFICATION — `PathOb K ×_K PathOb K` as the length-2 cocylinder `K^{I₂}`

| Def / theorem | Statement | Status |
|---|---|---|
| `pathOb2 K` | `PathOb K ×_K PathOb K = pullback (endpoint true) (endpoint false)` | **PROVEN** (concrete object) |
| `pathOb2.fst/snd` | the two projections `K^{I₂} ⟶ PathOb K` | **PROVEN** (def) |
| `pathOb2.leftEnd/rightEnd` | the two *outer* endpoints `K^{I₂} ⟶ K` (start of first, end of second) | **PROVEN** (def) |
| `pathOb2.condition` | inner ends match: `fst ≫ endpoint true = snd ≫ endpoint false` | **PROVEN** |
| `I₂` | the 2-segment interval `serialWedge [1,1] = □¹ ∨ □¹` | **PROVEN** (def) |
| `I₂_eq`, `Iv_two` | `I₂ = wedge2 (cube 1) (serialWedge [1])`, `Iv 2 = I₂` | **PROVEN** (`rfl`) |
| `pathOb2 K ≅ (I₂ ⟹ K)` | the **cocylinder** identification (full exponential iso) | **CONJECTURED** |

**What is concrete and PROVEN.** The pullback object `pathOb2 K` is built with both projections and
both outer endpoint maps, and the span composite already lands in it (§1). A point of `pathOb2 K` is
a pair of homotopy-cubes glued at the matched end — exactly a homotopy over the 2-segment interval.

**What is conjectured (`CocylinderConjecture`).** The *full exponential iso*
`pathOb2 K ≅ (I₂ ⟹ K)` (presheaf internal hom). Geometrically this is the continuity of `(-) ⟹ K`:
it sends the pushout `I₂ = □¹ ∨_{□⁰} □¹` to the pullback `K^{□¹} ×_{K^{□⁰}} K^{□¹}`, and
`PathOb = K^{□¹}` on the box-tensor adjunction. Formalising the iso needs the box tensor
`(-) ⊗ I₂` (Day convolution), which `Foundations/Shift.lean` provides only on representables. We
deliberately keep `pathOb2 K` as the concrete stand-in and label the iso a clearly-marked
conjecture. The `CocylinderConjecture` def in the file is a typed placeholder (it cannot state the
real iso without first constructing `(I₂ ⟹ K)`); the genuine statement is in its docstring.

---

## 3. NEGATIVE — the reparametrization obstruction (no fold `□¹ → I₂`) — **PROVEN, decisive**

This is the crisp, sorry-free, `K`-independent obstruction.

### Statement (`no_fold_edge`, PROVEN)

> There is **no** `1`-cell `z` of `I₂ = □¹ ∨ □¹` with `vertex₀ z = I₂.init` and
> `vertex₁ z = I₂.final`.

By the cube Yoneda lemma a precubical map `□¹ ⟶ I₂` *is* a `1`-cell of `I₂`, and "covering both
segments" forces its single edge to run from the global start `I₂.init` to the global end
`I₂.final`. So `no_fold_edge` says: **the only maps `K^{I₂} → K^{□¹}` are the two half-projections
`pathOb2.fst/snd`; there is no concatenation/fold.** The strict `□¹`-cylinder cannot be
renormalised from a length-2 homotopy.

### Proof (the geometry)

Every positive cell of a wedge lies in a **single block** — the structural lemma
`wedge_cell_xor` (a direct corollary of mathlib-backed `wedge2_cell_cases` + `wedge2_inl_ne_inr`
from `Chains/WedgeMap.lean`): a `1`-cell is either `inl x` or `inr y`, never both. Then:

* If `z = inl x` (left block): its target vertex is `inl(vertex₁ x)` (naturality `map_vertex₁`),
  while `I₂.final = inr(W.final)` (the `wedge2` `final`-field, `W = serialWedge [1]`). The two block
  images overlap *only* at the junction (`wedge_vertex_overlap`, extracted from the dimension-0
  pullback square `wedge2_isPullback_app` via `Types.exists_of_isPullback`), forcing `W.final =
  W.init` — impossible (`W_init_ne_final`, ultimately `cube1_init_ne_final` via `trueCount` `0 ≠ 1`).
* If `z = inr y` (right block): dual, at `vertex₀`. Its source vertex is `inr(vertex₀ y)` while
  `I₂.init = inl(cube1.init)`; the overlap forces `cube1.init = cube1.final` — impossible.

### Supporting lemmas (all PROVEN, sorry-free)

| Lemma | Content |
|---|---|
| `wedge_cell_xor` | every positive wedge cell is in exactly one block (`inl` xor `inr`) |
| `vertexMap_app_self` | a vertex map `□⁰ ⟶ Z` returns its selected vertex on the (unique) `0`-cell |
| `wedge_vertex_overlap` | `inl a = inr b` at dim 0 ⟹ `a = X.final ∧ b = Y.init` (the junction) |
| `cube1_init_ne_final` | `(cube 1).init ≠ (cube 1).final` (via `trueCount`, `0 ≠ 1`) |
| `W_init_ne_final` | `(serialWedge [1]).init ≠ (serialWedge [1]).final` |
| `no_fold_edge` | **the decisive non-existence** |

**Reuse note.** The block decomposition (`wedge2_cell_cases`, `wedge2_inl_ne_inr`,
`wedge2_isPullback_app`) and vertex naturality (`map_vertex₀/₁`) are all pre-existing main-library
API; the only new geometric inputs are the dim-0 overlap extraction and the `trueCount`
distinctness. No `native_decide` / finite-model fallback was needed — the abstract proof tracks the
real `PrecubicalSet`/wedge development directly.

---

## 4. SYNTHESIS — strict not `·`-closed; the Moore fix

| Def / theorem | Statement | Status |
|---|---|---|
| `Iv n` | the serial `n`-interval `Iₙ = □¹ ∨ ⋯ ∨ □¹` (`Iv 0 = □⁰`, `Iv 1 = □¹`, `Iv 2 = I₂`) | **PROVEN** (def) |
| `MooreCyl K` | scaffold of a length-`n` Moore cylinder (homotopy over `Iₙ`) | **SCAFFOLD** |
| `MooreCyl.ofStrict` | strict `□¹`-cylinders embed as the `len = 1` Moore cylinders | **PROVEN** (def) |
| `strict_image_not_closed_witness` | `= no_fold_edge`: the decisive witness that strict is not `·`-closed | **PROVEN** |
| `MooreSpanComposeConjecture` | `Iₘ`- ∘ `Iₙ`- cylinder ⟹ `Iₘ₊ₙ`-cylinder (Moore image `·`-closed) | **CONJECTURED** |

### The conclusion (sharp)

* **Strict `□¹`-cylinder image is NOT a submonoid.** It contains `1` (Cyl6 `taut_eq_one`), but is
  **not `·`-closed**: the span composite of two strict cylinders is genuinely length-2
  (`spanCompose`, in `K^{I₂}`), and `no_fold_edge` shows there is no precubical renormalization back
  to length 1. This is exactly Cyl6's "no `PathOb` multiplication" obstruction, now with its precise
  mechanism: the missing `PathOb K ×_K PathOb K → PathOb K` *is* the non-existent fold `□¹ → I₂`.
  The gap is *one reparametrization*, no more — the homotopies do line up; only the collapse fails.

* **Moore cylinders fix it (CONJECTURE, scaffolded).** Enlarge to homotopies over any `Iₙ`. Span
  composition then *adds lengths* (`Iₘ ∘ Iₙ ⟶ Iₘ₊ₙ`) with **no fold required** — §1's
  `spanCompose`/`spanCompose_leftLeg/rightLeg` already deliver the object-level composite and its
  legs; only the length-additivity `K^{Iₘ} ×_K K^{Iₙ} ≅ K^{I (m+n)}` (the iterate of
  `CocylinderConjecture`) is left open, pending the box-tensor exponential. On the Moore image,
  span-pullback composition realises the Cyl6 monoid product `mul_pointedOfPaths`, so
  `cylToPointed` becomes a monoid hom there (the Cyl6 `cylSubmonoid` hypotheses are then met).

### What is owed (CONJECTURE / future work)

1. `CocylinderConjecture`: the exponential iso `pathOb2 K ≅ (I₂ ⟹ K)` (needs box tensor `(-) ⊗ I₂`).
2. `MooreSpanComposeConjecture`: length-additivity of Moore span composition (iterate of (1)).
3. Connect `MooreCyl`'s `cyl` to the genuine target `src ⟶ K^{Iₙ}` (currently a placeholder field)
   and show `cylToPointed` is a monoid hom on the Moore image (realising `mul_pointedOfPaths`).

These are exactly the box-tensor / exponential inputs the broader program already owes; the
*combinatorial obstruction* (no strict renormalization) is fully settled here.

---

## Summary table

| Item | Statement | Status |
|---|---|---|
| Span pullback object + projections | `spanPullback`, `spanπ₁/₂`, `span_condition` | **PROVEN** |
| Homotopies glue / span composite | `spanCompose` into `K^{I₂}` | **PROVEN** |
| Composite legs `= (L₁∘π₁, R₂∘π₂)` | `spanCompose_leftLeg/rightLeg` | **PROVEN** |
| Length-2 cocylinder object | `pathOb2 K = PathOb K ×_K PathOb K` (+ ends, condition) | **PROVEN** (concrete) |
| 2-segment interval | `I₂ = serialWedge [1,1]` | **PROVEN** |
| Cocylinder iso `pathOb2 K ≅ K^{I₂}` | full exponential | **CONJECTURED** |
| Every wedge edge in one block | `wedge_cell_xor` | **PROVEN** |
| Block overlap = junction (dim 0) | `wedge_vertex_overlap` | **PROVEN** |
| `(cube 1).init ≠ (cube 1).final` | `cube1_init_ne_final` | **PROVEN** |
| **No fold `□¹ → I₂`** | `no_fold_edge` | **PROVEN (decisive)** |
| Moore-cylinder scaffold | `Iv`, `MooreCyl`, `ofStrict` | **SCAFFOLD / PROVEN defs** |
| Moore length-additivity | `MooreSpanComposeConjecture` | **CONJECTURED** |
| **Strict image not `·`-closed** | off by one reparametrization; Moore closes it | **PROVEN (witness) + CONJECTURED (fix)** |
