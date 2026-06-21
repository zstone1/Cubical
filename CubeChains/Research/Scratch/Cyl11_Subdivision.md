# Cyl11_Subdivision — hetero-cylinders, the pointed-over-`G` target algebra, and base subdivision

Design + scaffold for **generalizing the cylinder construction to support subdividing the base `K`**.
Companion to `Cyl11_Subdivision.lean` (decoupled from the green build; `lake build
CubeChains.Research.Scratch.Cyl11_Subdivision`, **green and genuinely sorry-free** — every label
`PROVEN` is a real sorry-free Lean def/theorem; every `DESIGN`/`OPEN` claim is a typechecking
`Prop`-level `…Conjecture` def or a structure signature, never presented as proven).

This is an *exploratory design pass* (like Cyl1–Cyl10): the goal is a coherent, type-checking Lean
skeleton + this self-contained writeup, not full proofs. Where a real proof is out of scope it is
stated as a labelled `Prop`.

---

## 0. Lead / verdict

> **The cylinder construction generalizes from a *monoid of endo-cylinders* (Cyl6) to a *bicategory
> of hetero-cylinders*** `K ⟵ᴸ src ⟶ᴿ K'`, whose induced action is a **functor**
> `Φ : DPathGrpdR K ⥤ DPathGrpdR K'` *pointed over a reference* `G : DPathGrpdR K ⥤ DPathGrpdR K'`
> (a comparison 2-cell `G ⟹ Φ`). The reference is exactly `FreeGroupoid.map (Refine.pushforwardBP
> f)` of a strict comparison `f : K → K'`, so **a hetero-cylinder is the homotopy refinement of a
> strict comparison map**. Subdivision is the special case `K' = Sd K` with `f` the subdivision map.

The right target algebra is **pointed-over-`G` functors** `PointedOverFunctor 𝒞 𝒟 G`, which at
`𝒟 = 𝒞`, `G = 𝟭` is *literally* `PointedEndofunctor 𝒞`. The whole groupoid-conjugation engine of the
endo deliverable (`conjFunctor`/`conjNatIso`/`pointedFunctorOfObj`) transports **verbatim** to a
fixed reference `j`.

On **`Sd K`** for precubical sets: a literal endofunctor `Sd : PSet ⥤ PSet` exists only as a heavy
left Kan extension over the cube-grid subdivisions and is *not* the recommended formalization.
Base-subdivision is better expressed entirely through the **chain-refinement layer we already have**
(`RefineObj` + `Refine.pushforwardBP`), with the interval case already settled (`Iₙ = serialWedge
(replicate n 1)`, Cyl7 `Iv`, Cyl10 `Iₙ ⟹ K = pathObₙ K`). The single most promising next theorem is
**"subdivision cylinders realize the refinement comparison"** at the 1-dimensional witness `□¹ → I₂`.

---

## 1. The generalized target algebra — `PointedOverFunctor 𝒞 𝒟 G` — **PROVEN scaffold**

The endo target is `PointedEndofunctor 𝒞` = (endofunctor `F : 𝒞 ⥤ 𝒞`) + (point `𝟭 ⟹ F`). Fixing
categories `𝒞`, `𝒟` and a **reference functor** `G : 𝒞 ⥤ 𝒟`:

```
structure PointedOverFunctor (G : 𝒞 ⥤ 𝒟) where
  Φ  : 𝒞 ⥤ 𝒟          -- the comparison functor
  pt : G ⟶ Φ           -- the comparison 2-cell ("point", relative to G)
```

| Item | Statement | Status |
|---|---|---|
| `PointedOverFunctor 𝒞 𝒟 G` + `Hom` + `Category` instance | the generalized target category | **PROVEN** |
| `toEndo` / `ofEndo` (+ round-trips `rfl`) | `PointedOverFunctor 𝒞 𝒞 (𝟭) ≅ PointedEndofunctor 𝒞` on objects | **PROVEN** |
| `pt_isIso` (groupoid target) | every point is a natural iso when `𝒟` is a groupoid | **PROVEN** |
| `pointedHomOfGroupoid` + `_id`/`_comp` | the forced point-determined morphism `A.pt⁻¹ ≫ B.pt` | **PROVEN** |
| `pointedFunctorOfObj` | object family ⟹ functor (forced-morphism assembly) | **PROVEN** |
| `pointedOverOfPaths j F₀ η` | object-data ⟹ pointed-over-`j` functor, no naturality chase | **PROVEN** |

**Why this is the right generalization.** The endo morphism map of `cylToPointedR` is *forced* (the
base is a groupoid). The exact same forcing holds when only the **target** `𝒟` is a groupoid: each
`pt : G ⟹ Φ` is a natural iso, so `A.pt ≫ τ = B.pt` determines `τ = A.pt⁻¹ ≫ B.pt`. Hence
`pointedHomOfGroupoid`/`pointedFunctorOfObj` are copied with one symbol changed (`𝒢`-endo ↦
`𝒟`-target groupoid), and the assembly of per-cylinder actions into a *functor of cylinders* is
inherited for free.

**Reuse of the conjugation core.** `Operations.conjFunctor`/`conjNatIso` (in
`Cylinder/PointedFunctor.lean`) already take an **arbitrary** `j : C ⥤ G` into a groupoid — they were
never specialized to `of`. So `pointedOverOfPaths j F₀ η := ⟨conjFunctor j F₀ η, (conjNatIso …).hom⟩`
is a one-liner reuse. The endo `pointedOfPaths` differs only by post-composing with
`FreeGroupoid.lift` (because an *endo*functor of `FreeGroupoid C` is wanted, not a functor out of the
generators); precisely:
`(Operations.pointedOfPaths F₀ η).F = FreeGroupoid.lift ((pointedOverOfPaths (of C) F₀ η).Φ)`, by
`FreeGroupoid.lift_spec`. So Cyl11 genuinely *contains* the endo target as the `j = of`, lift-it case.

---

## 2. The reference comparison from a bi-pointed map — **PROVEN (def); functoriality = DESIGN**

A strict comparison `f : K → K'` (`BPSet` map) induces a strict functor on d-path groupoids:

```
refComparison f : DPathGrpdR K ⥤ DPathGrpdR K'  :=  FreeGroupoid.map (Refine.pushforwardBP f)
```

This is **PROVEN by definition** and is *literally the leg-functor construction* `CylMapR.Lgrpd`/
`Rgrpd` (`Cylinder/CylinderRefineCore.lean`) read off a single map instead of a cylinder's two legs.
It reuses `Refine.pushforwardBP` (`Cylinder/CylinderRefineCore.lean`, which wraps
`Chains/RefineFunctor.lean`'s `Refine.pushforward` — the proof that `RefineObj` is functorial in `K`)
and `FreeGroupoid.map`.

| Item | Statement | Status |
|---|---|---|
| `refComparison f = FreeGroupoid.map (Refine.pushforwardBP f)` | the strict reference functor | **PROVEN** (def) |
| `refComparison_id_Conjecture` | `refComparison (𝟙) = 𝟭` | **DESIGN** (`Prop`) |
| `refComparison_comp_Conjecture` | `refComparison (f ≫ g) = refComparison f ⋙ refComparison g` | **DESIGN** (`Prop`) |

The functoriality conjectures reduce to (a) `Refine.pushforwardBP` respecting `𝟙`/`∘` — true
cube-wise because `mapCubeHom` does, but with an endpoint-transport (`app_init`/`app_final`) chase
that is fiddly — composed with (b) mathlib's already-PROVEN `FreeGroupoid.map_id`/`map_comp`. They
are stated as `Prop`s rather than proved because the transport chase is genuine engineering, out of
scope for a design pass. **Design slogan:** *a hetero-cylinder is the homotopy refinement of the
strict `refComparison f`* — it fills the strict comparison in up to its point `G ⟹ Φ`.

---

## 3. The hetero-cylinder — **PROVEN structure + leg-functors; action modulo a hetero-sweep**

```
structure HeteroCylR (K K' : BPSet) where
  ref      : K ⟶ K'                              -- the strict comparison to be refined
  src      : BPSet
  leftLeg  : src ⟶ K                             -- left leg into the COARSE target K
  rightLeg : src ⟶ K'                            -- right leg into the FINE target K'
  cyl      : src.toPsh ⟶ PathOb.obj K'.toPsh     -- homotopy living in K'
  hleft    : cyl ≫ endpoint false = (leftLeg ≫ ref).hom   -- false-end = f∘leftLeg
  hright   : cyl ≫ endpoint true  = rightLeg.hom          -- true-end  = rightLeg
```

The design choice (one of two natural ones — see §3.1) is: **the homotopy lives in the fine target
`K'`, between the comparison-image `f ∘ leftLeg` of the left leg and the right leg**. This keeps a
*single* `PathOb` (no cospan/`PathOb` of a comparison object needed), and degenerates cleanly:

| Item | Statement | Status |
|---|---|---|
| `HeteroCylR K K'` | the hetero-cylinder structure | **PROVEN** |
| `HeteroCylR.ofEndo : CylMapR K → HeteroCylR K K` | endo ↪ hetero (over `ref = 𝟙`) | **PROVEN** |
| `HeteroCylR.Lgrpd` / `Rgrpd` | leg-functors `DPathGrpdR src ⥤ DPathGrpdR K` / `K'` | **PROVEN** |
| `HeteroCylR.leftWeq` | predicate "left leg is a groupoid weak equivalence" | **PROVEN** |
| `HeteroCylR.comparison c hc = Lgrpd⁻¹ ⋙ Rgrpd` | the comparison functor `DPathGrpdR K ⥤ DPathGrpdR K'` | **PROVEN** |
| `HeteroSweepSig c hc` | type of the per-object homotopy `(refComparison ref).obj x ⟶ (comparison).obj x` | **PROVEN** (type) |
| `HeteroCylR.toPointedOver c hc η` | the action as a `PointedOverFunctor … (refComparison ref)`, via `pointedOverOfPaths` | **PROVEN modulo `η`** |
| `HeteroSweepConjecture` | every weq hetero-cylinder admits a hetero-sweep | **OPEN** (`Prop`) |

**The action recovers the endo deliverable.** With `ref = 𝟙`, `refComparison 𝟙 = 𝟭` (mod §2
conjecture), `comparison = Lgrpd⁻¹ ⋙ Rgrpd` is the endo object map, and the hetero-sweep `η x :
(refComparison 𝟙).obj x → (comparison).obj x` is exactly the endo `counit.inv ≫ sweepR` (the input to
`cylToPointedObj`). So `toPointedOver` *is* `cylToPointedObj`, transported across `toEndo`/`ofEndo`.

**The only genuinely new geometric work** is the **hetero-sweep** `η` — the staircase bridging the
comparison image of a chain to the right-leg transport of its left-leg preimage. In the endo case this
is the fully-built `sweepR` (`Cylinder/CylinderSweep.lean`); the hetero version is the same
junction-bridge staircase relative to `f`, and is left as `HeteroSweepConjecture`. Everything *around*
it (assembly into a pointed-over-`G` functor, naturality, the forced functor of cylinders) is PROVEN.

### 3.1 Alternative design (recorded, not chosen)

The fully symmetric hetero-cylinder is a homotopy over a **cospan** `K ←u W →v K'` (a "comparison
object" `W`): `cyl : src → PathOb W` with legs `leftLeg = cyl·e₀` into `K` via `u` and `rightLeg =
cyl·e₁` into `K'` via `v`. This is more symmetric but needs a `PathOb` of a *bridge* `W` and an
explicit `u`,`v`; it is strictly more general and the chosen "fix `ref : K → K'`, homotope inside
`K'`" version is its special case `W = K'`, `v = 𝟙`, `u = ref`. We chose the special case because (a)
it reuses a single `PathOb K'` (so the existing prism/`sweepR` geometry transports with `ref`
prepended), and (b) it makes the endo recovery and the subdivision application immediate. The cospan
version is the right thing to scaffold next if a genuinely two-sided comparison is needed.

---

## 4. Composition = bicategory, not monoid — **PROVEN leg level; coherence inherits Cyl7's obstruction**

Endo-cylinders of a fixed `K` form Cyl6's **monoid**. Hetero-cylinders compose with **leg-matching**
`K → K' → K''`, so:

* **objects** `BiObj = BPSet`;
* **1-cells** `OneCell K K' = HeteroCylR K K'` (restrict to `leftWeq` for the action to exist);
* **horizontal composition** = span composition (Cyl7 `spanCompose`), matched over the middle `K'`;
* **endo-hom** `OneCell K K` recovers Cyl6's monoid.

| Item | Statement | Status |
|---|---|---|
| `OneCell.compSrc c d = pullback c.rightLeg d.leftLeg` | the composite source `src_c ×_{K'} src_d` | **PROVEN** (def) |
| leg-level composite | left leg `= leftLeg_c ∘ π₁`, right leg `= rightLeg_d ∘ π₂`, homotopy via `spanCompose` | **PROVEN** (Cyl7) |
| `HorizontalCompConjecture c d` | ∃ composite 1-cell with source `compSrc c d` | **OPEN/DESIGN** (`Prop`) |
| `endoHom_isMonoid` | every endo-cylinder gives an endo-hom 1-cell (= `ofEndo`) | **PROVEN** |

**Where `spanCompose` is the horizontal composition.** A hetero-cylinder forgets `cyl` to a span
`K ⟵ leftLeg src rightLeg ⟶ K'`. Two composable hetero-cylinders pull back over the middle `K'`
(`compSrc`), and Cyl7's `spanCompose`/`spanCompose_leftLeg`/`spanCompose_rightLeg` already deliver the
composite legs and the glued homotopy — *into the length-2 cocylinder* `pathOb2 K''`. So the
leg-level horizontal composite is **PROVEN** (it is exactly Cyl7's positive result).

**Why a bicategory, and why the coherence is owed.** Collapsing the length-2 composite back to a
strict `□¹`-classifying map requires a fold `□¹ → I₂`, which **does not exist** (Cyl7 `no_fold_edge`,
PROVEN). So the strict `□¹`-bicategory's horizontal composition is *off by one reparametrization* —
exactly Cyl6's pinned obstruction (no `PathOb` multiplication, from precubical degeneracy-freeness).
The honest structure is therefore a **Moore-enriched bicategory** (1-cells = homotopies over any
`Iₙ`), where composition *adds lengths* (`Iₘ ∘ Iₙ ⟹ Iₘ₊ₙ`) with no fold. `HorizontalCompConjecture`
is the strict-collapse statement (OPEN, obstructed); the Moore version is the recommended remedy and
matches Cyl7's `MooreCyl`/`MooreSpanComposeConjecture`. The **endo-hom recovers Cyl6's monoid**
(`endoHom_isMonoid` PROVEN: `ofEndo` includes endo-cylinders into `OneCell K K`; on the image,
horizontal composition restricts to Cyl6's `·`).

---

## 5. What is `Sd K`? — **DESIGN verdict**

A `k`-cube `□ᵏ` subdivides into a **grid** of `2ᵏ` (or `nᵏ`) sub-cubes. The repo already realizes the
1-dimensional case as the **serial interval** `Iₙ = serialWedge (replicate n 1) = □¹ ∨ ⋯ ∨ □¹`
(`Foundations/Wedge.lean`'s `serialWedge`/`cube`; Cyl7 `Iv`; Cyl10 proved `Iₙ ⟹ K = pathObₙ K`).
Re-exported here as `SdInterval n := Cyl7.Iv n` (**PROVEN**, def).

**Verdict: do *not* build a literal `Sd : PSet ⥤ PSet` endofunctor.**

* A genuine endofunctor on the topos `PrecubicalSet = Boxᵒᵖ ⥤ Type` would be a **left Kan extension**
  of a functor `Box ⥤ PSet` sending each representable `□ᵏ` to its grid subdivision (an iterated
  `serialWedge`/`cube`). The `Lan` exists (mathlib `Functor.lan`), but its *combinatorics* — matching
  the grid gluings across the cube category's face maps — is heavy and not needed for the cylinder
  program. Recorded as `SdEndofunctorConjecture` (a deliberately weak placeholder: the *intended* `Sd`
  is a *specific* `Lan`, whose construction needs the grid-indexing functor `Box ⥤ PSet`).

* **Recommended formalization: keep base-subdivision in the chain-refinement layer.** `RefineObj
  K.init K.final` *is* the poset of subdivisions of d-paths (PZ Lemma 2.11(c)), and
  `Refine.pushforwardBP` makes it functorial in `K`. A subdivision need never be an `Sd`-endofunctor:
  per `K`, take a *finer* `BPSet` `K'` and a comparison map `f : K → K'`; then `refComparison f :
  DPathGrpdR K ⥤ DPathGrpdR K'` *is* the strict subdivision functor, and a **subdivision cylinder** is
  a weak-equivalence hetero-cylinder refining it. This reuses everything already built and sidesteps
  the Day-convolution/`Lan` machinery entirely.

| Item | Statement | Status |
|---|---|---|
| `SdInterval n = Cyl7.Iv n` | the 1-dim subdivision witness (interval into `n` pieces) | **PROVEN** (def) |
| `SdEndofunctorConjecture` | a literal `Sd : PSet ⥤ PSet` (intended: a grid `Lan`) | **DESIGN/OPEN** (`Prop`) |
| `SubdivisionRealizationConjecture f` | subdivision cylinders realize `refComparison f` (`Φ ≅ refComparison f`) | **OPEN — the key theorem** (`Prop`) |

**The key conjecture** `SubdivisionRealizationConjecture f`: for a subdivision comparison `f : K → K'`
there is a weak-equivalence hetero-cylinder `c` with `c.ref = f` and a hetero-sweep `η` such that the
induced `Φ = (c.toPointedOver hc η).Φ` is naturally isomorphic to `refComparison f`. I.e. **subdivision
is a homotopy-trivial cylinder**: the cylinder's homotopy refinement of the strict comparison is, up
to iso, the strict comparison itself — the subdivision adds no homotopy, it only refines.

---

## 6. Reuse map (what plugs into what)

| Existing infra | Reused for | Where in Cyl11 |
|---|---|---|
| `Operations.conjFunctor` / `conjNatIso` | builder for the pointed-over-`G` functor (no naturality chase) | `pointedOverOfPaths` |
| `Operations.pointedFunctorOfObj` skeleton | forced morphism map (groupoid *target*) | `pointedHomOfGroupoid`, `pointedFunctorOfObj` |
| `Operations.pointedOfPaths` (endo) | recovered at `j = of` + `lift` | §1 recovery note |
| `Refine.pushforwardBP` (`CylinderRefineCore`) → `Refine.pushforward` (`RefineFunctor`) | the reference comparison + leg-functors | `refComparison`, `HeteroCylR.Lgrpd/Rgrpd` |
| `FreeGroupoid.map` + `map_id`/`map_comp` | functoriality of the reference comparison | `refComparison`, §2 conjectures |
| `CylMapR` + `sweepR` (`CylinderSweep`) | the endo special case + the hetero-sweep to generalize | `ofEndo`, `HeteroSweepSig/Conjecture` |
| Cyl7 `spanPullback`/`spanCompose`/`pathOb2` | horizontal composition (leg level PROVEN) | `OneCell.compSrc`, `HorizontalCompConjecture` |
| Cyl7 `no_fold_edge` + `Iv` + `MooreCyl` | the bicategory obstruction + Moore fix; the `Sd`-interval | §4, `SdInterval` |
| Cyl10 `Iₙ ⟹ K = pathObₙ K` | the settled 1-dim subdivision exponential | §5 narrative |

---

## 7. Status table (all of Cyl11)

| Item | Status |
|---|---|
| `PointedOverFunctor` + `Category` + `toEndo`/`ofEndo` | **PROVEN** |
| groupoid-target forced morphisms (`pointedHomOfGroupoid`, `pointedFunctorOfObj`) | **PROVEN** |
| `pointedOverOfPaths` (conjugation over a reference) | **PROVEN** |
| `refComparison f` | **PROVEN** (def) |
| `refComparison_id/comp_Conjecture` | **DESIGN** (`Prop`) |
| `HeteroCylR` + `ofEndo` + `Lgrpd`/`Rgrpd` + `comparison` | **PROVEN** |
| `HeteroCylR.toPointedOver` (action) | **PROVEN modulo hetero-sweep `η`** |
| `HeteroSweepConjecture` | **OPEN** (`Prop`) |
| `OneCell.compSrc` (composite span source) | **PROVEN** (def) |
| `endoHom_isMonoid` | **PROVEN** |
| `HorizontalCompConjecture` | **OPEN/obstructed** (`Prop`; Moore fix) |
| `SdInterval = Cyl7.Iv` | **PROVEN** (def) |
| `SdEndofunctorConjecture` | **DESIGN/OPEN** (`Prop`) |
| `SubdivisionRealizationConjecture` | **OPEN — recommended first theorem** (`Prop`) |

---

## 8. Recommended first concrete theorem

**Prove `SubdivisionRealizationConjecture` for the 1-dimensional subdivision `f : □¹ → I₂`**
(`I₂ = SdInterval 2 = Cyl7.Iv 2`):

1. Build the explicit hetero-cylinder `c : HeteroCylR (cube 1) I₂` with `ref = f` and `src = □¹`,
   whose homotopy fills `f` (the two halves of `I₂` are the two sub-edges).
2. Check `c.Lgrpd` is an equivalence (the left leg `□¹ → □¹` is the identity — trivially a weq).
3. Build the single-rung **hetero-sweep** `η` (here `Cyl7.spanCompose` of the two halves is the rung;
   the staircase has length 1, so no recursion is needed).
4. Conclude `Φ ≅ refComparison f` — both send the generating chain to its subdivision, and `η`
   exhibits the iso.

This is the **first genuine *base*-subdivision cylinder**, and it is the minimal case where every
gadget in this file is exercised end-to-end. It is sized like the existing `Testing/CylinderTwoBlock`
confirmation and should be reachable with the same `native_decide`/explicit-staircase tooling.
