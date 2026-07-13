# The schedule space of a precubical set — target architecture

## 0. Thesis

**Do not globalize coordinates.** The schedule space is *locally* a braid cone, glued along
refinements. Written that way:

* no `EdgeLabelling` is needed to **define** schedules — a labelling is a *chart*, not a hypothesis;
* `RunInjective`, `AdmitsAltitude`, `Sculpture`, `ConstEventCount`, `Finite A` all disappear;
* the extended reals / horizon / ω-coordinate / box-topology problems disappear (they were all
  symptoms of a global chart);
* exactly **one** structural hypothesis survives: `Ch(K)` is **thin** — and it is *already proved*
  from `NonSelfLinked + AdmitsAltitude` (`chainCat_hom_subsingleton`).  It is consumed only where a
  chart must not *fold*: `ChartsFaithful` (geometry) and `Over.forget` being full (categories).
  `IsAtlas` itself is **unconditional** (`Schedule/Atlas.lean`).

The obstruction to a global event naming (the trinity: monodromy of the event local system) is real
and is *irrelevant*, because nothing in the theory needs a global naming. It obstructs a global
chart, not the space.

**Slogan.** `Sched(K)` is a manifold modelled on braid cones. `Ch(K)` is its atlas. A wedge map
`W ⟶ K` (i.e. a cube chain) *is* a chart. `Sched(W)` is the local model.

---

## 1. Definitions

Fix a precubical set `K` (bipointed). No labelling.

| object | definition |
|---|---|
| `E a` | `EventObj a` — the events `(bead i, direction δ)` of a chain `a`. Finite. |
| `bead : E a → Fin (a.dims.length)` | the bead index of an event |
| `C a` | `{t : E a → ℝ ∣ bead e < bead e' → t e < t e'}` — the **chain cone**. Open, convex, nonempty in `ℝ^(E a)`. (This is today's `schedCone`.) |
| `Δ° c` | `{τ : Fin (nbeads c) → ℝ ∣ StrictMono τ}` — the **stratum** of `c`: one time per bead, strictly increasing. |
| `Sched K` | `Σ c : Ch K, Δ° c` — a **valid schedule** is a cube chain with strictly increasing bead times. Topologized by the charts below. |
| `f : Sched K → Ch K` | `π₁`. |

**`f` is the projection, not a construction.** `StrictMono τ` *is* the statement that no two beads
are tied, so the chain component of a schedule already is its tie-block decomposition. `f` proves
nothing; it names the stratification. All the content lives in the chart.

**The charts (this is the theorem).** For each chain `a`,

```
chart a :  C a  ≃  Σ (c, g) : (Ch K / a),  Δ° c
```

sending `t` to its **tie-blocks**: the cross-bead constraints force every tie-block of `t` inside a
single bead of `a`, so the tie-blocks form an ordered partition of each bead's directions — i.e. a
refinement `g : c ⟶ a` — and the block times are strictly increasing. The inverse spreads a bead's
time to all its events. Bijectivity is **L5**.

`Sched K` carries the topology **coinduced** by the charts. Then `C a = f⁻¹(refinements of a)` — the
open star of `a`'s stratum — and `f` is continuous for the **Alexandrov topology** on `Ch(K)ᵒᵖ`.

**Dual setup, same work.** One may instead define `Sched K := colim_{Ch K} C` along the open
embeddings `C c ↪ C a`. Then the topology is free and `f` becomes a real construction (tie-blocks,
`IsLeast {b ∣ t ∈ C b} (f t)`, well-definedness on overlaps). The two are the same space and the
same total content, redistributed. We take the Σ-type: carrier explicit, work in the charts.

**Honesty about the nerve.** Because `Sched K` is *defined* from `Ch K`, the statement
`|N(Ch K)| ≃ Sched K` is close to definitional. It is not the headline. The substance of this
architecture is (i) the **local structure** — `C a` is an open convex cone cut by the braid
arrangement, so its combinatorics is the realizable COM `braidDirectSum a.dims` (§2b) — and (ii) the
**comparison** `Sched K ≃ P⃗(K)` (Ziemiański), which is what earns `Sched` its name and which we
cannot formalize (mathlib has no d-path space).

## 1a. The topology, precisely

* **Carrier**: `⨆_c Δ°(c)`.
* **Topology**: the final topology of `⨆_a C(a) → Sched K`. Equivalently `colim_{Ch K} C` in `Top`.
* **Gluing locus**: `C a ∩ C b = ⋃ { C c | c a common refinement of a and b }` — open in both,
  **possibly disconnected**.
* **Transitions**: the event bijection `E a ≅ E c ≅ E b`, determined pointwise by the point's own
  finest chain. A locally constant coordinate permutation — possibly a *different* permutation on
  different components of the overlap. That is where the event-local-system monodromy lives, and it
  is harmless (transitions need only be continuous).
* **Local model**: `C a` is an open convex cone in `ℝ^(E a)`, so `Sched K` is locally `ℝⁿ`,
  `n = dimSum` (locally constant), with affine transitions.
* **NOT Hausdorff.** Let `K` be two 2-cubes `S`, `S′` with the *same boundary*. `Ch K` has
  `[S]`, `[S′]`, `[x][y]`, `[y][x]`, with both edge paths refining both squares. `C[S] ≅ C[S′] ≅ ℝ²`
  share everything off the diagonal, and the two diagonal strata are distinct points:

  > `Sched K` = the plane with a doubled diagonal line.

  This is *correct*: `N(Ch K) = K_{2,2} ≃ S¹`, the doubled plane is the homotopy pushout
  `pt ← (2 contractible) → pt ≃ S¹`, and `P⃗(K) ≃ S¹`. Non-Hausdorffness **is** the branching of `K`
  and it carries the homotopy type. `Sched K` is an étale space; those are routinely non-Hausdorff.

## 1b. Why no global chart can ever work

The two-squares `K` above satisfies **`RunInjective`, `NonSelfLinked`, and thinness** — every side
condition we have ever assumed. `S` and `S′` have the same edges, hence the same labels, so in the
label ambient `ℝ^A`:

```
labelCone ℓ [S]  =  labelCone ℓ [S′]  =  ℝ²
```

The union is contractible; the truth is `S¹`. **The horizon repair (`Horizon.lean`) is necessary but
not sufficient**: it separates chains with different *label sets*, and these two have the same one.
No formulation with a global coordinate ambient can work under any side conditions, because distinct
cubes with the same boundary are invisible to it. This is the decisive argument for the atlas.

Times are only ever compared, never measured: `C a` is invariant under `t ↦ λt + c·1` (`λ > 0`). No
horizon, no basepoint, no sign convention. Those were global-chart artifacts.

**Loops are free.** `E a` is finite for every chain, *including* chains that traverse a loop many
times. The `ℝ^ω` and the box topology only ever arose from the global occurrence ambient
`ℝ^(A × ℕ)`. There is no global ambient here.

---

## 2. The master diagram

Everything is the same triangle, repeated at every chain `a`. Write `W a := serialWedge a.dims` (the
abstract serial wedge of cubes — the *shape* of `a`, forgetting `K`).

### 2a. Locality (the square)

```
              chart a
      C a  ─────────────────≅──────────────>  Sched (W a)
       │                                          │
     f │  (stratification)                        │  f_W
       v                                          v
   (Ch K / a)ᵒᵖ ─────────≅──────────────────>  Ch (W a)ᵒᵖ
                     sliceEquiv
```

*The star of a stratum in `Sched K` is the whole schedule space of its shape.* Left column: global,
`K`-dependent. Right column: a wedge of cubes — pure combinatorics, no `K`. This is what "local
behaviour of schedules ↔ slices of `Ch K`" means, precisely.

### 2b. Three names for one poset (the triangle)

```
                          Ch(K)/a   ≅   Ch(W a)
                            ▲                ▲
        f  (finest chain)   │                │   serialSalBaseEquiv
                            │                │
        strata of  C a  ────┴──── σ ─────────┴──  Face (braidDirectSum a.dims)
                              (covector)
```

* **left**: chains refining `a` — combinatorics;
* **middle**: strata of the cone `C a` — geometry;
* **right**: faces of the local COM — algebra.

`σ t` = the sign vector of `t` under the braid arrangement on `E a` (`braidCovectorR`). Its zero set
is the tie relation, so `σ` *is* `f` read in COM language: **the finest chain of a schedule is the
covector of its timing.** Combined with §2a, the local COM is

```
localCOM t  :=  braid arrangement on E(f t), localized at σ t   ≅  braidDirectSum (f t).dims
```

which is *exactly* the COM `salFunctorSlice` is already stated about. Realizability is the
Bandelt–Chepoi–Knauer picture on the nose: **(braid arrangement on `E a`) ∩ (open convex cone `C a`)
is a COM, and it is `braidDirectSum a.dims`.**

### 2c. The Salvetti layer (already proved)

```
   Face (braidDirectSum a.dims) ──── salFunctor ────> Type
            ≅ │ serialSalBaseEquiv                    ║  salFunctorSlice
              v                                       ║
      (Ch K / a)ᵒᵖ ─────────── Lines K ─────────────> Type
```

So the bonus (goal 3) is *already done* — it just needed the left column to be geometry rather than
an unmotivated algebraic gadget. §2b supplies that.

### 2c′. Localization: the local Salvetti is a **full subcategory** of the global one

`Lines K` sends a chain to `∏ᵢ Chamber(dᵢ)` — one chamber per bead — which is exactly the set of
**topes** of `braidDirectSum a.dims`.  So an object of `Sal (localCOM x)` is a pair (covector, tope
above it) = (a chain `c` refining `x.chain`, a line of `c`) = an object of `∫Lines K` over the star
of `x`.  Formally:

```
Sal (localCOM x)  ≌  ∫ ( (Over.forget x.chain)ᵒᵖ ⋙ Lines K )     -- slice explicit
                  ≌  (Over x.chain)ᵒᵖ  ×_{(Ch K)ᵒᵖ}  Int(Lines K) -- slice as a BASE CHANGE
```

The second line is because `∫(Lines K) → (Ch K)ᵒᵖ` is a **discrete fibration**, so restricting the
presheaf = pulling back the elements category.  The comparison functor is
`CategoryOfElements.pre (Lines K) ((Over.forget a).op)`.

**`pre P G` is fully faithful when `G` is.  `Over.forget a` is always faithful, and it is FULL
exactly when `Ch K` is thin** (given `g : c ⟶ c'`, both `g ≫ f'` and `f` are morphisms `c ⟶ a`, so
thinness commutes the triangle).  Hence:

> If `Ch K` is thin, `Sal (localCOM x)` is a **full subcategory** of `Int(Lines K)` — the full
> subcategory on the `(c, L)` with `c` refining `x.chain`.  These cover (every `(c,L)` lies in the
> piece at `c` itself), so `Int(Lines K)` is glued from local Salvetti complexes.

The two glueings are indexed by the *same* poset, which is the shared local structure of `Ch(K)` and
`Sched(K)`:

```
Sched K       =  ⋃_a  star a                  open cover, spaces
Int(Lines K)  =  ⋃_a  Sal (localCOM_a)        full subcategories, categories
```

And note the consistency: **thinness is what makes the geometric charts embeddings *and* the
categorical charts full.**  One hypothesis, both sides.  (At a generic `x` every bead is
1-dimensional, `Chamber 1` is a singleton, and the local piece is the single object
`(x.chain, its unique line)` — no walls, as it should be.)

### 2d. Globally

```
        C  :  Ch(K)ᵒᵖ  ⟶  Open (Sched K)        a ↦ C a
   chainsIn :  Open (Sched K)  ⟶  Ch(K)ᵒᵖ       U ↦ {a | C a ⊆ U}
```

`C ⊣ chainsIn` — this is the Galois connection **already in `LabelSpace.lean`** (`coneUnion` /
`chainsIn`), now with the right domain. `C` is injective on objects, preserves meets (§3, L6), and
its image is a basis closed under nonempty intersection. That is the whole "relationship between
schedules and wedge maps": **not** a sheaf and **not** an adjunction to `K` — a *stratification*,
whose formal shadow is this Galois connection.

A sheaf does appear, but only downstream: an `EdgeLabelling ℓ : K → A` induces
`Sched K → ℝ^(A×ℕ)` (time each occurrence of each action). This map is **étale**, and `Sched K` is
the étale space of the sheaf of runs over timing space. It is *injective* iff `K` is
run-deterministic. **The old hypotheses (`RunInjective`, `NSL`, `Sculpture`) are exactly conditions
for this chart to be faithful — they were never prerequisites for the theory.** Demote them to a
chapter titled "when is the global chart an embedding".

---

## 3. Key lemmas, with their real hypotheses

| # | statement | hypotheses | status |
|---|---|---|---|
| L1 | `eventMap f : E a ≃ E b` is a **bijection** | none | ✅ `EventMapBij.lean` |
| L2 | `dimSum` constant along refinements | none | ✅ `dimSum_eq_of_hom` |
| L3 | bead order monotone along refinements | none | ✅ `serialWedge_blockIdx_monotone` |
| L4 | `C a` open, convex, nonempty | none | ✅ `Cone.lean` |
| L4′ | `spread f τ ∈ C a` — the chart lands in the cone | none | ✅ `spread_mem_cone` (`Space.lean`) |
| L5 | **the chart**: `C a ≃ Σ (c,g) : Ch(K)/a, Δ° c` (tie-blocks) | **none** (thin *not* needed — see below) | ✅ `Atlas.lean` (`isAtlas`) |
| L6 | **fibre posets are principal**: `{a ∣ x ∈ star a} = ↑(x.chain)` | none | ✅ `Cover.lean` |
| L7 | ~~**meet**: `C a ∩ C b = C (a ∧ b)`~~ | — | ❌ **FALSE** — see below |
| L8 | `IsOpen (star a)` | `IsAtlas` only (**not** thin) | ✅ `Cover.lean` |
| L8′ | stars of the coarsest chains cover `Sched K` | none | ✅ `Cover.lean` |
| L9 | `Sched K = colim C ≃ hocolim C ≃ \|N(Ch K)\|` | `Ch K` thin | 🚧 — *near-definitional, see §1* |
| **R** | **realizability**: `beadCovector '' beadCone = (braidDirectSum dims).covectors` | none | ✅ `BraidCone.lean` |
| **M** | `COM.localAt L X` is a COM (indeed an OM) | none | ✅ `COMLocal.lean` |
| **C** | local COM trivial ⟺ every bead is 1-dim (**it measures concurrency**) | none | ✅ `LocalCOM.lean` |
| **S** | `Sal (localCOM x) ≌ Int(Lines(⋁x.chain.dims))`; its faces = the star's strata | none | ✅ `SalLocal.lean` |
| **X** | two-squares sphere: passes NSL + altitude + run-injectivity, still folds | — | ✅ `Testing/TwoSquares.lean` |

**L5 needs no thinness** (correcting the prediction below). A chart point is a refinement *plus* its
bead times, and a refinement is **determined by its bead map** (`Atlas.lean`'s `bfSgnN_beadOf`: the
block faces are forced — a coordinate is free at its own bead, already `1` before it, still `0`
after). So two distinct refinements `c ⟶ a` (a self-linked cube) have distinct bead maps and hence
distinct chart *coordinates*; they name the same *schedule*. Thinness is therefore what
`ChartsFaithful` — the chart map that **forgets** the refinement — needs, not `IsAtlas`.

**L7 is false.** For the two-squares `K` of §1a, `C[S] ∩ C[S′]` is a union of **two disjoint**
half-planes: `[S]` and `[S′]` have two incomparable minimal common refinements and no meet.
Consequences:

* the cone family is **not** closed under intersection, and intersections may be disconnected;
* the cover is **not** good in the Čech sense;
* "nerve of the cover = order complex of `Ch K`" is **FALSE** — the Čech nerve of that example
  acquires the chord `{[S],[S′]}` and two filled triangles, giving a contractible complex instead of
  `S¹`.

The correct machinery is the **homotopy colimit / projection lemma**, not the Čech nerve lemma: every
`C a` is contractible (convex), and by L6 the fibre poset `{a ∣ x ∈ C a}` is a principal up-set for
every `x`, hence contractible. So `colim ≃ hocolim ≃ |N(Ch K)|`. **L6 is the load-bearing lemma** —
the finest-chain map earns its keep as the hypothesis of the hocolim theorem, not as `IsLeast`.
| L10 | `Ch(K)/a ≌ Ch(W a)` | none | ✅ `sliceEquiv` |
| L11 | `Face(braidDirectSum a.dims) ≌ Ch(W a)ᵒᵖ` | none | ✅ `serialSalBaseEquiv` |
| L12 | `salFunctor (braidDirectSum a.dims) ≅ slice(a) ⋙ Lines K` | none | ✅ `salFunctorSlice` |
| L13 | `Ch K` thin, i.e. `Quiver.IsThin (Ch K)` | `NonSelfLinked` + `AdmitsAltitude` | ✅ `chainCat_hom_subsingleton` (`Correspondence.lean`) — already existed |
| **F** | `Sal (localCOM x)` is a **full subcategory** of `Int(Lines K)`, image = the star of `x`; the stars cover | thin (fullness only) | ✅ `SalLocal.lean` (`localToGlobal`, `salLocalFullyFaithful`, `localToGlobal_essImage`, `mem_localToGlobal_self`) |

**The entire hypothesis budget is L8: `Ch(K)` is thin.** It is needed for exactly one thing — that a
chart doesn't fold onto itself — and it is precisely what `NonSelfLinked` was always buying (a
self-linked cube gives two distinct refinements `c ⟶ a`, so two points of `C a` name one schedule).
State it as `[Quiver.IsThin (ChainCat.Obj K)]`, not as `NonSelfLinked`: it is weaker, it is the
honest hypothesis, and it is *automatic for every local model* (`W a` is a wedge of cubes). Slogan:
**local models are always thin; thinness is only needed to glue them.**

L7 is the lemma that makes the good cover *sharp*: nonempty intersections of cones are themselves
cones, so the cover is closed under intersection and the nerve is the order complex on the nose — no
"contractible-or-empty" hand-waving, and no Čech subtleties.

---

## 4. Module layout

```
Arrangements/
  BraidCone.lean         beadCovector '' beadCone = braidDirectSum covectors   (realizability)
  COMLocal.lean          COM.localAt L X : the local COM at a covector (an OM)

Schedule/
  Cone.lean              C a = schedCone a : open convex cone in ℝ^(EventObj a)   ✅
  Space.lean             Sched K, Stratum, Chart, spread, the topology             ✅
  Cover.lean             star a, cover by coarsest chains, principal fibre posets
  Atlas.lean             IsAtlas: chartCoord ≃ the cone (tie-blocks, via blockStar)     ✅
  LocalCOM.lean          localCOM x = braidDirectSum (x.chain).dims; = localAt of any chart
  LabelChart.lean        EdgeLabelling ⟹ labelTime : Sched K → (A → ℝ); folds       ✅

Salvetti/
  SalLocal.lean          salFunctorSlice restated at a point of Sched K
```

Demoted (kept, but as *charts*, not foundations): `ChainCone.lean`'s `labelCone`,
`LabelSpace.lean`'s `labelSpace`, `Horizon.lean`.  `LabelChart.lean` explains what they are —
the image of the atlas under the labelling — and why they fold.

## 5. Notation

Global, and it prints, so goals read as the maths does:

| notation | means |
|---|---|
| `□n` | `BPSet.cube n` |
| `⋁d` | `BPSet.serialWedge d` |
| `Ch K` | `ChainCat.Obj K` |

(The cube-chain *functor* `BPSet ⥤ Cat` is now `chFunctor`, freeing `Ch`.  This also removes a real
ambiguity: `chFunctor.obj K` is a bundled `Cat`, `Ch K` is the object type.)

**Retired to `Chart.lean` as *characterizations*, not hypotheses:** `RunInjective`,
`AdmitsAltitude`, `ConstEventCount`, `Sculpture`, `Finite A`, the horizon/occurrence-sign layer
(`Horizon.lean`), the label ambient `A → ℝ` (`ChainCone.lean`'s `labelCone`), `labelSpace`.

**Deleted claims.** `LabelSpace.lean`'s nerve claim ("the nerve of `{labelCone ℓ a}` is `Ch K`") is
false for branching `K` — the diamond (`a→x→b`, `a→y→b`, no squares) has two cones that spuriously
meet. It is false because `labelCone` is the *image* of `C a` under the global chart, not `C a`. In
the architecture above the statement is true by construction.
