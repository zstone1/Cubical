# Cyl3 — worked examples & pathologies for `cylToPointedR`

**Topic (user item 2):** worked small examples of the cylinder ⟹ pointed-functor
construction `cylToPointedObj`/`cylToPointedR`, plus pathologies, in the spirit of
`Research/Unrealizable.lean`.

**Lean:** `CubeChains/Research/Scratch/Cyl3_Examples.lean` — **green, sorry-free** under
`lake build CubeChains.Research.Scratch.Cyl3_Examples` (3005 jobs, no sorries).
Status tags below: **PROVEN** = sorry-free Lean (topos-level proof or `native_decide` on the
`FinBPSet` surrogate), **CONJECTURED** = argued but not in Lean, **OPEN**.

---

## The construction, recalled

`cylToPointedObj (c : CylMapWeqR K) : PointedEndofunctor (DPathGrpdR K)` where
`DPathGrpdR K = FreeGroupoid (RefineObj K.init K.final)`, built by `pointedOfPaths`:

* object map `F₀ x = Rgrpd (Lgrpd⁻¹ x)`  (transport `Rgrpd` along the equivalence `Lgrpd`);
* per-object point `η x = counit.inv ≫ sweepR (Lgrpd⁻¹ x)`  (the cylinder homotopy).

Because the base is a **groupoid**, the morphism map is forced (`pointedFunctorOfObj`).

---

## Part 1 — the tautological cylinder induces the identity (PROVEN, topos-level)

The pipeline always ends in `pointedOfPaths F₀ η`. The **tautological / both-legs-equal**
object-data is `(F₀, η) = (of, 𝟙)`.

| Lemma (in `Cyl3_Examples.lean`) | Statement | Status |
|---|---|---|
| `conjFunctor_taut` | `conjFunctor of of 𝟙 = of` | PROVEN |
| `lift_of_eq_id` | `lift (of C) = 𝟭` | PROVEN |
| `pointedOfPaths_id_F` / `taut_F_eq_id` | the taut pointed endofunctor's underlying `F` is **literally `𝟭`** | PROVEN |
| `taut_iso_id` | the taut pointed endofunctor `≅ idPointed` (uniquely) | PROVEN |

**The tautological cylinder induces the identity pointed endofunctor `𝟭`** (on the nose for
`F`, uniquely up to iso for the whole object). This anchors everything.

### Part 1b — the degeneracy mechanism (the central structural finding, PROVEN)

| Lemma | Statement | Status |
|---|---|---|
| `pointedEndo_thin` | `PointedEndofunctor 𝒢` is **thin** for a groupoid `𝒢` (≤ 1 morphism between objects) | PROVEN |
| `pointed_determined_by_F_pt` | a pointed endofunctor of a groupoid is determined by `(F, pt)` | PROVEN |
| `pointedUniqueIso` | between any two pointed endofunctors of a groupoid there is a **unique iso** | PROVEN |

So `PointedEndofunctor (DPathGrpdR K)` is **codiscrete on objects**: the only invariant of
`cylToPointedObj c` is its π₀-object-map `Rgrpd ∘ Lgrpd⁻¹ : π₀ → π₀`. The homotopy datum
`η = counit ≫ sweepR` only witnesses that `of x` and `F₀ x` lie in the *same component*; its
actual path is washed out. **This is the "codiscrete ⟹ identity-deformation" degeneracy,
proven.**

---

## Part 2 — worked small bases (`FinBPSet` surrogate, `native_decide`)

`RefineObj`/`DPathGrpdR`/`cylToPointedObj` are `noncomputable` (wedges = generic pushouts), so
examples use the `Testing` surrogate. Dictionary: `chains` = objects of `RefineObj`,
`dimSeq` = shape, `chLe` = `RefineObj` order, `chainsConnected`/`chConnected` = π₀ test.

| Base `K` | `RefineObj` / d-paths (`chains`) | shapes | `DPathGrpdR K` (π₀) | induced `(F₀, η)` for a natural cylinder | status |
|---|---|---|---|---|---|
| `□¹` interval | `[[e]]` — 1 d-path | `[1]` | terminal (1 obj) | `F₀ = id`, `η = 𝟙` ⇒ **`𝟭`** | PROVEN |
| `□²` square | `[[e0_,e_1], [e_0,e1_], [sq]]` — 3 d-paths | `[1,1],[1,1],[2]` | **connected**, 1 π₀ class (both staircases refine `[sq]`) | any cylinder ⇒ `≅ 𝟭` | PROVEN |
| `□¹∨□¹` wedge (`pathWedge`) | `[[eA,eB]]` — 1 d-path | `[1,1]` | terminal (Segal: `Ch(X∨Y)≌Ch X×Ch Y`) | `≅ 𝟭` | PROVEN |
| `2×1` grid (`grid2`) | 5 d-paths | mixed | **connected**, 1 π₀ class | any cylinder ⇒ `≅ 𝟭` | PROVEN |
| self-linked square (`cylSquare`) | `[b0e],[pSq],[b1e]` (+ self-loop pads) | `[1],[2],[1]` | **connected** (`b0e,b1e` both refine `[pSq]`) | the *genuine* cylinder ⇒ `≅ 𝟭` — **info loss** | PROVEN |
| two-block (`twoBlock`) | `la,m1,bridge,m2,ra` | mixed | **connected** via junction-bridge staircase | the *genuine* cylinder ⇒ `≅ 𝟭` | PROVEN |
| `fourPaths` 1-skeleton | 4 incomparable d-paths | all `[1,1,1]` | **DISCONNECTED**, 4 π₀ classes | only base where `F₀` can be `≠ id` on π₀ | PROVEN |

Each row's `chains`/`chConnected`/`chLe` facts are pinned by `native_decide` in the Lean file.

---

## Part 3 — pathologies (the realizability-style findings)

### Pathology A — π₀-only invariant ⇒ connected base collapses every cylinder to `𝟭` (PROVEN)

By Part 1, `cylToPointedObj c` is determined up to unique iso by π₀-object-map. When
`DPathGrpdR K` is **connected** (`chConnected = true`), that map is forced to the identity, so
**`cylToPointedObj c ≅ 𝟭` for *every* cylinder `c`** — the geometric homotopy `sweepR` is
invisible to the output. This is the cylinder analogue of `Unrealizable`: there bare
functoriality fails to pin a cube map; here the *target algebra is too coarse to record the
homotopy*.

Crucially this hits the bases the program **actually needs**: a rel-interface cylinder forces
basepoint self-loops, and the smallest such base `cylSquare` has connected `DPathGrpdR`
(`b0e, b1e` distinct legs, both refining the prism cube `[pSq]`). `native_decide`:
`cylSquare.chLe [b0e] [b1e] = false`, `cylSquare.chLe [b1e] [b0e] = false`,
`cylSquare.chainsConnected [[b0e],[pSq],[b1e]] = true`. Same for `twoBlock`. **The construction
runs (it is `cylToPointedR`, green), but on these bases its output is `≅ 𝟭` regardless of the
cylinder — total information loss.**

### Pathology B — the only non-degenerate regime needs a disconnected `DPathGrpdR K` (PROVEN)

For `cylToPointedObj c ≇ 𝟭`, `F₀ = Rgrpd∘Lgrpd⁻¹` must permute π₀ nontrivially ⇒ `DPathGrpdR K`
needs ≥ 2 components. Minimal witness: `fourPaths` (`chConnected = false`, 4 incomparable
d-paths). But a cylinder map's left leg must be a groupoid **equivalence** (`CylMapWeqR`),
pinning `π₀(src) ≅ π₀(K)`; the induced permutation is then the π₀-action of an automorphism of
`K`. So the construction sees **only** the π₀-action of `Aut K` — the same coarse invariant the
lowering refutation isolated. `native_decide`: `fourPaths.autK.length = 4` (`V₄`),
`fourPaths.opAutCh.length = 24` (`S₄`).

### Pathology C — a pointed endofunctor induced by no cylinder (the `Unrealizable` analogue)

Over `fourPaths` the discrete groupoid `DPathGrpdR` admits all `S₄` π₀-permutations as pointed
endofunctors, but the 20 outside `V₄` are induced by **no cylinder** (whose legs are precubical
maps): a transposition of two d-paths fixes a shared edge yet must send it two different ways.
`native_decide`: `fourPaths.firstIncoherence = some ([1,0,2,3], d1, d2, d1)` — the swap sends
the shared edge `d1` to both `d1` and `d2`; `fourPaths.coherentAll = false`. This is exactly
the cylinder analogue of `Unrealizable.ρ_not_realizable`.

---

## Cause, in one sentence

The target `PointedEndofunctor (FreeGroupoid (RefineObj …))` is **codiscrete on objects**
(Part 1, PROVEN), so the construction is a **π₀-invariant**; it is degenerate (collapses to
`𝟭`) exactly when `Ch K` is connected — which is the generic case *and* the case the
rel-interface program requires (`cylSquare`, `twoBlock`). The information the cylinder carries
(its homotopy `sweepR`) is real but the target cannot see it.

---

## Open questions

1. **(Best open question.)** Replace the codiscrete target with one that records the homotopy:
   build `cylToPointed` into the **geometric** adjunction `⊗□¹ ⊣ PathOb` (`Foundations/Shift`),
   whose pointed endofunctor `PathOb`-side is *not* codiscrete, so two cylinders with the same
   π₀ but different `sweepR` become distinguishable. Is `Hom(K,K) ↪ {cylinders}` (program
   step 3) faithful for *that* target? OPEN.
2. Over a **disconnected** `DPathGrpdR K`, characterize the image of `cylToPointedR`: is it
   exactly the π₀-action of `Aut K` (Pathology B suggests yes), so that the "unrealized" pointed
   endofunctors are precisely the lowering-refuted chain automorphisms? CONJECTURED.
3. A non-weak-equivalence cylinder (`CylMapR \ CylMapWeqR`): `Lgrpd⁻¹` does not exist, so
   `cylToPointedObj` is undefined. What is the natural extension (lax/relative pointed
   endofunctor) and does it retain more than π₀? OPEN.
