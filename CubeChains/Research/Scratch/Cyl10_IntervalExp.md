# Cyl10_IntervalExp — the interval exponential `Iₙ ⟹ -` as an iterated pullback of `PathOb`

**Files:** `Cyl10_IntervalExp.lean` (green & sorry-free) and this writeup.
**Build:** `lake build CubeChains.Research.Scratch.Cyl10_IntervalExp`.
**Decoupled:** owns only this file + its `.md`; `Cyl7`/`Cyl9`/`Wedge`/`Shift` are read-only imports.

The brief: construct the interval exponential `Iₙ ⟹ -` for the geometric box-tensor as the
**iterated pullback of `PathOb`**, and discharge the two deferred conjectures
(`CocylinderConjecture`, `MooreSpanComposeConjecture`) — *without* building a general tensor or a
`MonoidalCategory Box` instance.

---

## TL;DR / verdict (lead)

- **`cyl2 ⊣ pathOb2Functor` landed — PROVEN, sorry-free** (`cyl2Adj`).  The I₂-cylinder functor
  `cyl2 = (-) ⊗ I₂` (the **pushout** of two `□¹`-cylinders glued at the junction) is left adjoint to
  the I₂-cocylinder functor `pathOb2Functor = PathOb ×_{(-)} PathOb` (the **pullback** of the two
  endpoints).  Built exactly per the route — *"hom out of a pushout is a pullback"* + the off-the-shelf
  `cylinderAdj` hom-equivalence — with **no general tensor and no `MonoidalCategory Box`**.

- **`CocylinderConjecture` — DISCHARGED** (in its meaningful form, `cocylinder_isInternalHom`).
  Cyl7's concrete `pathOb2 K = PathOb K ×_K PathOb K` is isomorphic to `pathOb2Functor.obj K`, the
  value of the *genuine right adjoint* of the I₂-cylinder.  So `pathOb2 K ≅ (I₂ ⟹ K)` with the
  internal hom realised by an honest adjoint — not a placeholder.  The literal Cyl7 placeholder
  `CocylinderConjecture` (a tautology) is also closed (`cocylinderConjecture`).

- **`MooreSpanComposeConjecture` — DISCHARGED** (Cyl7's existence form, `mooreSpanComposeConjecture`).
  Backed by the recursive cocylinder `cocylN n` (the length-`n` interval cocylinder, built by gluing
  one `□¹` at a time) and span composition `cocylGlue`.  The base/definitional length-additivity
  (`cocylN (n+2) = cocylGlue cocyl1 (cocylN (n+1))`) is PROVEN, and `cocylN 2`'s cocylinder is
  *definitionally* `pathOb2Functor` (`cocylN_two_cocyl`), anchoring the tower at the proven I₂ adjunction.

- **Strengthenings, precisely reduced (no longer to the geometric tensor).**  The *functor-iso* form
  of length-additivity (`MooreSpanComposeIso`) reduces to **pullback associativity** (`pullbackAssoc`)
  + the proven interval-additivity (`Cyl9.mooreSpanCompose_interval_additive`); the general n-ary
  adjunction (`CylNAdjunction`) reduces to a **parametrised re-run of §2–3** (the generic
  "glue a `□¹` onto an adjunction" step).  Both are populated/proven at `n = 0,1,2`.

---

## The route taken (and why it avoids the general tensor)

Everything is built on two off-the-shelf facts from `Cyl9`:
`cylinder := Box.shift.op.lan` and `cylinderAdj : cylinder ⊣ PathOb` (`= shift.op.lanAdjunction`).
The strict cylinder/cocylinder adjunction is the *only* adjunction consumed; the higher intervals are
assembled by **(co)limit gluing** in the functor category, never by a binary tensor.

### 1. Cofaces `𝟭 ⟹ cylinder` (§1)
`coUnit ε : 𝟭 ⟹ cylinder` is the **mate** of `endpoint ε : PathOb ⟶ 𝟭` under `cylinder ⊣ PathOb`
and `𝟭 ⊣ 𝟭` (`mateEquiv`).  The two load-bearing identities are PROVEN:
- `unit_endpoint`: `unit X ≫ endpoint ε (cylinder X) = coUnit ε X` (from `unit_mateEquiv_symm`);
- `coUnit_comp`: `coUnit ε X ≫ a = (homEquiv a) ≫ endpoint ε`  — **the dictionary** turning a
  pushout-of-cofaces matching condition into a pullback-of-endpoints matching condition.

### 2. The two functors as functor-category (co)limits (§2)
- `cyl2 := Limits.pushout (coUnit true) (coUnit false)` in `PrecubicalSet ⥤ PrecubicalSet`.
- `pathOb2Functor := Limits.pullback (endpoint true) (endpoint false)`.

Evaluation at `X`/`K` preserves these (functor-category (co)limits are pointwise), giving the
**pointwise** witnesses `cyl2.isPushout X : IsPushout …` and `pathOb2Functor.isPullback K :
IsPullback …` (via `IsPushout.map`/`IsPullback.map` along `(evaluation _ _).obj _`).

### 3. The adjunction `cyl2 ⊣ pathOb2Functor` (§3)
`Adjunction.mkOfHomEquiv` with hom-equivalence `homEquiv2 X K : (cyl2 X ⟶ K) ≃ (X ⟶ pathOb2Functor K)`:
- **forward** `homEquivToFun`: split `g` into legs `inl ≫ g`, `inr ≫ g`; transport by
  `cylinderAdj.homEquiv`; the pushout square `w` becomes the pullback condition via `coUnit_comp`;
  `IsPullback.lift`.
- **backward** `homEquivInvFun`: project `h` by `fst`/`snd`; transport by `homEquiv.symm`;
  `coUnit_comp` again; `IsPushout.desc`.
- `left_inv`/`right_inv` by `IsPushout.hom_ext`/`IsPullback.hom_ext` + the computation lemmas.
- the two `mkOfHomEquiv` naturalities reduce (via leg-naturality of `inl`/`inr`/`fst`/`snd` and
  `cylinderAdj`'s own `homEquiv` naturalities) to `cylinderAdj`'s naturality — PROVEN.

### 4. Cocylinder identification (§4)
`pathOb2Functor.obj K ≅ Cyl7.pathOb2 K` (`pathOb2Functor_obj_iso`, via `IsPullback.isoIsPullback` —
both are the same pullback), with matching projections.  Hence `cocylinder_isInternalHom`.

### 5. Iteration (§5)
`IntervalCocyl` bundles a cocylinder functor with its two outer endpoints.  `cocyl1` (= `PathOb`),
`cocylCons` (prepend one `□¹` = pullback over the junction), and `cocylN n` (length-`n` interval
cocylinder).  `cocylGlue` = span composition.  Proven: `cocylCons_eq_glue` (prepend = glue with
`cocyl1`), `glue_cocyl1_cocylN`, and the n=2 consistency `cocylN_two_cocyl : (cocylN 2).cocyl =
pathOb2Functor` (definitional).

---

## PROVEN (sorry-free)

| Name | Statement |
|---|---|
| `coUnit ε` | `𝟭 ⟹ cylinder`, the `ε`-coface, mate of `endpoint ε`. |
| `unit_endpoint`, `coUnit_comp` | the unit-level mate identity and the coface/endpoint dictionary. |
| `cyl2`, `pathOb2Functor` | the I₂-cylinder (pushout of cofaces) and I₂-cocylinder (pullback of endpoints) functors. |
| `cyl2.isPushout`, `pathOb2Functor.isPullback` | pointwise (co)limit squares (evaluation preserves). |
| `homEquiv2` | `(cyl2 X ⟶ K) ≃ (X ⟶ pathOb2Functor K)`. |
| **`cyl2Adj`** | **`cyl2 ⊣ pathOb2Functor`** — the I₂-cylinder/cocylinder adjunction. |
| `PreservesColimitsOfSize cyl2`, `PreservesLimitsOfSize pathOb2Functor` | left/right adjoint (co)continuity. |
| `pathOb2Functor_obj_iso` | `pathOb2Functor.obj K ≅ Cyl7.pathOb2 K`, projections matching. |
| **`cocylinder_isInternalHom`** | **`Cyl7.pathOb2 K ≅` (the genuine I₂-internal-hom `pathOb2Functor K`)** — `CocylinderConjecture` content. |
| `cocylinderConjecture` | Cyl7's literal `CocylinderConjecture` placeholder (closed). |
| `IntervalCocyl`, `cocyl1`, `cocylCons`, `cocylN`, `cocylGlue` | recursive interval cocylinders + span composition. |
| `cocylN_two_cocyl` | `(cocylN 2).cocyl = pathOb2Functor` (definitional). |
| `cocylCons_eq_glue`, `glue_cocyl1_cocylN` | prepend = span-compose with `cocyl1`; base length-additivity. |
| **`mooreSpanComposeConjecture`** | **Cyl7's `MooreSpanComposeConjecture`** (existence form). |
| `cylNAdjunction_two` | the `CylNAdjunction` interface populated at `n = 2` by `cyl2Adj`. |

## CONJECTURED / REDUCED (precise, no longer gated on the geometric tensor)

- **`MooreSpanComposeIso`** (functor-iso length-additivity):
  `(cocylGlue (cocylN (m+1)) (cocylN (n+1))).cocyl ≅ (cocylN (m+1+(n+1))).cocyl`.  Reduces to
  **pullback associativity** (`pullbackAssoc`, matching the three endpoint maps) + the PROVEN
  interval-additivity `Cyl9.mooreSpanCompose_interval_additive`.  Base `m=1` is definitional; `n=2`
  anchor proven (`mooreSpanComposeIso_two`).  Routine, not yet formalised.
- **`CylNAdjunction`** (the n-ary adjunction `cylN n ⊣ (cocylN n).cocyl`):  reduces to a
  **parametrised re-run of §2–3** — the generic "glue a `□¹`-cylinder onto an adjunction `Fn ⊣ Gn`
  with a chosen left endpoint" step (every §2–3 lemma used only *left adjoint + chosen coface*,
  nothing specific to the second factor being `cylinder`).  Proven at `n = 0,1,2`.

## OPEN (the precise residue)

1. **Pullback-associativity glue** for `MooreSpanComposeIso` — assemble `pullbackAssoc` with the
   `IntervalCocyl` endpoint maps.  Routine; effort = moderate (three-way endpoint bookkeeping).
2. **The generic gluing-of-adjunctions step** for `CylNAdjunction` (all `n`) — re-run §2–3 with an
   abstract `Fn ⊣ Gn` in place of the second `cylinder`.  Effort = moderate (parametrise the existing
   proofs; no new ideas).

Neither is gated on the geometric tensor or `MonoidalCategory Box` — the whole point of the `lan` +
(co)limit-gluing route is that those never appear.

---

## What this closes for the Moore submonoid result (Cyl7/Cyl8, step 5)

Cyl8's `SpanComposeRealisesProductConjecture` is gated (in Cyl8) on `Cyl7.CocylinderConjecture`, with
its **algebraic half already PROVEN** there (`spanComposeRealisesProduct_algebraic`,
`mul_eq_mooreToPointed_pair`: every product is a genuine length-2 Moore staircase).  The thing that
was owed was the *geometric* meaning of "`pathOb2 K = K^{I₂}`": that a map `P → pathOb2 K` is a bona
fide homotopy over the length-2 interval.

`cocylinder_isInternalHom` supplies exactly that: `pathOb2 K` is now **proven** to be the right
adjoint value `(I₂ ⟹ K)` of the genuine I₂-cylinder `cyl2 = (-) ⊗ I₂` (`cyl2Adj`).  So Cyl7's
`spanCompose : P ⟶ pathOb2 K` is a map into the genuine I₂-cocylinder — an honest homotopy over `I₂`,
not a stand-in.  Combined with Cyl7's `no_fold_edge` (no renormalisation to length 1), this confirms
the verdict: the **strict `□¹`-cylinder image is not `·`-closed; the Moore enlargement is**, and the
Moore composite lives over `I₂` (and, iterating, `Iₙ`) — exactly where `cocylN`/`cocylGlue` put it.

The remaining step-5 gap (identifying Cyl8's algebraic length-2 list with the *single* geometric
`spanCompose` object) is a Cyl8-side bookkeeping task: it now has a real target (`pathOb2Functor`,
proven to be the I₂-cocylinder) rather than a placeholder.  We do not edit Cyl8 (read-only here).
