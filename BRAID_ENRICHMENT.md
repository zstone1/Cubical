# Braid enrichment — the result

The mathematics. **This is not a work plan** — the cleanup, the landmines, and the open questions are
in beads (`bd ready`; the landmines and the two refuted claims are pinned at `Cubical-hic`). This
file is the paper skeleton.

Everything marked ✅ is proved in Lean, sorry-free, and — this is the surprise — **with no side
conditions anywhere**: no `NonSelfLinked`, no `AdmitsAltitude`, no `Quiver.IsThin`, no `Sculpture`,
no `RunInjective`. Machine-checked:

```
hasGlobalEventNaming_iff_braidPure : ∀ (K : BPSet), HasGlobalEventNaming K ↔ BraidPure K
axioms: [propext, Classical.choice, Quot.sound]
```

**One thing is assumed, and only for interpretation** — see §2.4. Read that before believing anything
about "braids".

---

## 1. The result

### The constructions

| | |
|---|---|
| **`Fund K`** | the fundamental 2-category. 0-cells = vertices; 1-cells = **chains**; 2-cells = zigzags of refinements. Hom-object `FreeGroupoid ((Ch (K;u,v))ᵒᵖ)`. |
| **`CFund K`** | the *complexified* one. 0-cells = vertices; 1-cells = **executions** (= chain **+ line**); 2-cells = **braids**. Hom-object `ConcGrpd (K.repoint u v)`. |
| **`CFund ↠ Fund`** | forget the line. §3 says exactly what this quotient is. |

Both are `Cat`-enriched, hence strict 2-categories (§4), and the projection is an `EnrichedFunctor`.

### The invariants

| | |
|---|---|
| | `K` is an **HDA** ⟺ every **loop** of `CFund K` gives a **pure** braid |
| | `salWind` = the **writhe** (exponent sum) of the braid |
| | `w₁(Sched K)` = the **sign** of the braid's underlying permutation (up to an explicit coboundary) |
| | the closure of a loop has `n` components ⟺ the braid is pure |
| | **forgetting the line loses only *pure* braids** — a loop of executions whose *chain*-zigzag is trivial has a braid with trivial permutation (`Braid/Purity.lean`) |

That last row is the sharp form of "what is the line for", and it is worth stating twice. The `Sₙ`-shadow
of the braid functor is a **chain** invariant — it *is* the event monodromy, and `Ch K` already
determines it completely. The line buys exactly the lift `Sₙ → Bₙ`, and the entire discrepancy is
confined to `Pₙ`.

⚠ **Do not say `ker Φ` is "the branching / dihomotopy ambiguity".** What is proved is about the kernel
of the *projection* `CFund ↠ Fund`, not of `Φ`; and `Φ` does **not** factor through that projection —
`Φ` is injective on exactly the part the projection kills.

---

## 2. The proof structure

### 2.1 The objects

```
Lines K : (Ch K)ᵒᵖ ⥤ Type          a chain ↦ ∏ᵢ (a chamber = a total order of bead i's directions)
ConcCat K := (Lines K).Elements     objects = (chain a, line L)   ← THE 1-CELLS OF CFund
ConcGrpd K := FreeGroupoid (ConcCat K)                            ← THE 2-CELLS OF CFund
```

**The line is the complexification.** A chain is a *face* of the local braid arrangement (which events
are simultaneous); a line is a *tope above it* (in which order the simultaneous ones are taken). That
pair is exactly a **Salvetti cell**. Dropping the line collapses to the real picture and the braids
vanish (§3). This is Salvetti's theorem lifted from arrangements to precubical sets, and it is the one
sentence to lead the paper with.

### 2.2 The braid functor — the heart, and it is short

**`Salvetti/BraidFunctor.lean`.** ✅ `braidFunctor K n : ConcGrpdN K n ⥤ BraidGrpd n`.

**The key move: `FreeGroupoid`'s universal property.** `FreeGroupoid.lift` turns a functor
`ConcCat K ⥤ G` (`G` a groupoid) into `FreeGroupoid (ConcCat K) ⥤ G`. So **no presentation theorem is
needed** — no "half-twists generate with braid relations", no CW/`π₁` bridge, no topology. **Only one
functor out of the un-groupoidified category.**

```
Ψ on objects.   (a, L)  ↦  a Salvetti cell of braidCOM n   (n = dimSum a)
                  face  =  braidSign (bead index)     -- sign(bead e − bead e'); 0 iff same bead
                  tope  =  braidSign (evKey rank)     -- the total order: bead first, then L within bead
                face ⊑ tope is IMMEDIATE (evKey sorts by bead first, so cross-bead signs agree)

Ψ on morphisms. evPerm f = eventMap read through the two evKey frames — a Perm (Fin n).
                THIS is the monodromy ρ. It forces the target to be the Sₙ-EXTENSION,
                i.e. B_n and not P_n.

Φ := FreeGroupoid.lift Ψ.
```

**The functor is forced, not chosen.** There is no design freedom in `Ψ`: a `(chain, line)` pair
*determines* those two sign vectors.

### 2.3 Why functoriality is easy — the slice observation

`Ψ` reads **only** the dims, the block data (`blockIdx`/`blockFace`, which come from the wedge map `φ`
alone), and the lines. The condition `φ ≫ a.map = c.map` — the only place `K` appears in a chain
morphism — is **never consulted**. And every morphism *and every composable pair* lies in a single slice
(`z` refines `y` refines `x`). **So functoriality is a statement about `⋁a.dims`, never about `K`.**

It reduces to three unconditional facts:

1. `fineBead_le` — `evKey` is lex (bead first), so beads increase along the frame;
2. **`serialWedge_blockIdx_monotone`** (`Chains/ChainSkeletal.lean`) — **a refinement never reorders
   beads**. This gives the *face* half.
3. `evKey_eventMap_lt` — `linesRestrict` is definitionally `Chamber.restrict` along
   `faceEmb (blockFace …)`, so the coarse chamber restricts to the fine one. This gives the *tope* half.

Cross-bead pairs are trivial: there `y`'s own face is nonzero, so it wins in `⊙`. **~70 lines total.**

### 2.4 ⚠ What is assumed, and where

**The construction of `Φ` does not use Salvetti's theorem at all.** It is elementary and unconditional.

Salvetti's theorem — `|N(Sal(braidCOM n))| ≃ F(ℂ,n)`, hence `π₁ = P_n` — is used **only to justify
calling the target "braids"**. In Lean it is not even stated: `Salvetti/ConcGroupoid.lean` *defines*
`PureBraid n := Aut (FreeGroupoid (Sal (braidCOM n)))` and records the identification in a docstring.

**Keep this separation explicit in the paper.** Construction: unconditional, elementary. Interpretation:
one classical theorem. It is the cleanest way to present it and it is honest — it is what makes the
result a genuine *lift* rather than a transport.

`braidSalEquiv n : Sal (braidCOM n) ≌ Int(Lines(□n))` (`Salvetti/BraidIso.lean`) and
`braidSerialSalEquiv` (`Salvetti/SalWedge.lean`) are the bridges that make the identification apply.
They are **not inputs to `braidFunctor`** — they are what let you *read* it.

---

## 3. `CFund ↠ Fund` — what exactly is the quotient?

**It is literally "forget the line", and it is a projection.**

```
CategoryOfElements.π (Lines K) : ConcCat K ⥤ (Ch K)ᵒᵖ
FreeGroupoid.map (…)           : ConcGrpd K ⥤ FreeGroupoid ((Ch K)ᵒᵖ)  =  Π₁(P⃗ K)   [Gabriel–Zisman]
```

- **Surjective on 1-cells**: every chain has at least one line.
- **Full on 2-cells**: ✅ `linesRestrict_surjective` + `exists_conc_zigzag` (`Salvetti/PurityHDA.lean`).
  Every zigzag of chains lifts to a zigzag of executions.
- **Kernel** = the local pure braid groups.

So `Fund K` = `CFund K` **modulo the braid groups** — a full surjection of `Grpd`-enriched categories,
identity on 0-cells. That is the precise sense in which this generalizes the existing directed-topology
work: **`Fund` is the real picture, `CFund` is its complexification, and the braid content is exactly
what the projection destroys.**

Three tiers, each the quotient of the last:

```
1-cells = (chain, line)   2-cells = braids           ConcGrpd K       ← CFund
1-cells = chains          2-cells = dihomotopies     Π₁(P⃗ K)          ← Fund
1-cells = trace classes   2-cells = trivial          →π₁(K)           ← the classical fundamental category
```

---

## 4. The enrichment question

### It is a `Cat`-enrichment, and that *is* the strict 2-category

`EnrichedCategory Cat (CFund K)` — three data fields (`Hom`, `id`, `comp`) and three laws. mathlib's
`CatEnriched` then derives the 1-category, the hom-categories, whiskerings, associator, unitors,
**pentagon, triangle and the five whisker laws**, and finally `Bicategory.Strict`. There is no separate
"strict 2-category" class to instantiate: a strict 2-category **is** `Bicategory` + `Bicategory.Strict`,
and the enrichment is its cheapest generator. Hand-rolling `Bicategory` means paying for coherence you
would otherwise get for free.

Not `Grpd`: mathlib gives `Grpd` no monoidal structure. The hom-objects are still the groupoids
`ConcGrpd`; "every 2-cell is invertible" is a *property* coming from `FreeGroupoid`, not structure the
base must carry. Not the slice `Cat/𝔅`: that is the same data as (`Cat`-enrichment + a strict 2-functor
to the delooping), and its mere *existence* is vacuous — the trivial lift sending every 2-cell to the
identity braid is a valid `Cat/𝔅`-enrichment on the same 2-category.

### You cannot enrich over the braid category — and it is a degeneracy, not an accident

Enrichment over `V` needs hom-*objects* in `V`. The hom-objects here are groupoids whose **objects are
the 1-cells**; `𝔅`'s objects are strand counts. So they cannot live in `𝔅`.

The sharper statement is that a `𝔅`-enriched category carries **no information beyond its set of
objects**. `𝟙_𝔅 = 0`, `⊗ = +`, and `𝔅` has morphisms only `n ⟶ n`. The unit forces `ℓ(x,x) = 0`;
composition forces `ℓ(x,y) + ℓ(y,z) = ℓ(x,z)`; put `z := x` and use `ℓ ≥ 0` in `ℕ` to get `ℓ ≡ 0`. Every
hom-object is `0`, and `𝔅(0,0) = B₀` is trivial. So the "enrichment" is a set. Nothing to do with `K`.

### What is true

`CFund K` is a `Cat`-enriched (hence strict 2-) category carrying a **braid grading**

    braidGrading K : Int(Lines K) ⥤ 𝔅     an execution  ↦ the object naming its EVENT COUNT
                                          a refinement ↦ ofPerm (evPerm f)

`𝔅` is the **germ** braid category (`Braid/Germ.lean`) and is already a groupoid — braids are
invertible — so `braidGrpd` is a bare `FreeGroupoid.lift`, with no `Localization.uniq` anywhere.

The remaining statement, *1-cell composition ↦ the braid tensor* (concatenating executions **adds**
strand counts), needs the delooping as an `EnrichedCategory Cat` on one object with hom-object
`Braids`. `Salvetti/BraidDeloop`'s version cannot serve: its composition goes through
`freeGroupoidProdEquiv = Localization.uniq`, so it is pinned only up to natural iso and can never
satisfy an equality-of-functors `assoc`.

### ⚠ Two sentences that were here and are false

> ~~`CFund K ≃ →π₁(K)` with every hom-set replaced by a braid group.~~

False twice over. Hom-objects are **groupoids**, not groups. And their vertex groups are **pure and
reducible**: a single `n`-cube gives `Pₙ` (`concCubeEquiv` + Salvetti), a serial wedge gives
`∏ᵢ P_{dᵢ}` — the block-diagonal pure subgroup of `Bₙ`. The full braid group is never the vertex group
of a cube; non-pure braids arise **only** from event monodromy, which is global. The sentence reads as
true only because "concurrency braid group" is *defined* to be the vertex group, making it circular.

> ~~`CFund K` is a `Grpd`-enriched category.~~

It is `Cat`-enriched. See above for why `Grpd` is not available.

---

## 5. Key lemmas, and where they live

| lemma | file | why it matters |
|---|---|---|
| `eventMap_bijective` | `Events/EventMapBij.lean` | the event local system is a local system of *bijections*. Everything about `ρ` rests on this. |
| `serialWedge_blockIdx_monotone` | `Chains/ChainSkeletal.lean` | **a refinement never reorders beads** — the face half of functoriality |
| `evKey` / `keyEquiv` | `Salvetti/Normalize.lean` | the total order on events induced by a line. The *frame*. |
| `concGrpdRunEquiv` | `Salvetti/Normalize.lean` | every 1-cell is 2-iso to a **run**. The normalization. |
| `evPerm_smul_le` | `Salvetti/BraidFunctor.lean` | **functoriality of `Ψ`** — the theorem |
| `braidSalEquiv`, `braidSerialSalEquiv` | `Salvetti/BraidIso.lean`, `SalWedge.lean` | the *interpretation* bridges (§2.4) |
| `ChainCat.sliceEquiv`, `salFunctorSlice` | `Chains/ChainSlice.lean`, `Salvetti/SerialSalLines.lean` | **the slice is a wedge** — why functoriality is local |
| `freeGroupoidProdEquiv` | `Salvetti/FreeGroupoidProd.lean` | `FreeGroupoid (C × D) ≌ FreeGroupoid C × FreeGroupoid D`. Used **three** times (enrichment, delooping, local model). Comes free from mathlib's `Localization/Prod.lean` — do not hand-roll it. |
| `salCross_add`, `salWind` | `Salvetti/Braiding.lean` | the winding character, for **any** finite-ground COM |
| `linesRestrict_surjective`, `exists_conc_zigzag` | `Salvetti/PurityHDA.lean` | fullness of `CFund ↠ Fund` |
| `hasGlobalEventNaming_iff_braidPure` | `Salvetti/PurityHDA.lean` | **the headline** |

`Events/OrdSign.lean`'s **`ordSign`** compares **two explicit linear orders** (not instances) on
one finite type, with the cocycle identity `ordSign_trans` through **any** middle order. That is the
right tool whenever two frames must be compared; it was reused for the `w₁` coboundary.

---

## 6. Two places the naive statement is false

Both are one line away from a false paper.

1. **"`evPerm f = 1` for every morphism ⟺ `K` is an HDA" is FALSE**, machine-checked
   (`forall_isRun_of_evPerm_one`). That condition forces **every chain to be a run** — i.e. `K` has *no
   concurrency at all*. Witness: `□²` has a global naming **and** a non-run chain.
   **Purity is a statement about LOOPS.** Quantifying over all morphisms accidentally says "`K` is a
   graph".

2. **Lifting a chain loop does NOT give an execution loop.** A lifted `Ch K` loop at `a` is a path
   `(a, L₀) ⇝ (a, M)` — same chain, *different line*. You must **shift the line back**, and the shift is
   free precisely because runs have unique lines (`exists_lineShift`). **Lines must be shifted, not just
   lifted.**

---

## 7. The diagram

```
                      Salvetti's theorem  (ASSUMED — interpretation only, §2.4)
                                  |
        braidSalEquiv  /  braidSerialSalEquiv        [PROVED — the bridges]
                                  |
   ┌──────────────────────────────┴──────────────────────────────┐
   │                                                             │
   │   THE CONSTRUCTION (elementary, unconditional, no Salvetti) │
   │                                                             │
   │   (chain, line)  ──Ψ──▶  Salvetti cell of braidCOM n        │
   │        │                   face = bead covector             │
   │        │                   tope = evKey rank                │
   │        │                                                    │
   │   functoriality = evPerm_smul_le                            │
   │        ▲                                                    │
   │        └── LOCAL: Ψ never reads K, only the wedge           │
   │            (slice: every morphism + composable pair         │
   │             lies over one chain)                            │
   │        │                                                    │
   │   Φ := FreeGroupoid.lift Ψ    ← universal property;         │
   │                                 NO presentation theorem     │
   └─────────────────────────────────────────────────────────────┘
                                  |
                    ┌─────────────┴─────────────┐
                    ▼                           ▼
        CFund ↠ Fund  (forget the line)   CFund ⟶ B𝔅raid  (compose ↦ tensor)
        full: linesRestrict_surjective    braidDeloopComp
        kernel: the braid groups
                                            |
                    ┌───────────────────────┼───────────────────────┐
                    ▼                       ▼                       ▼
            HDA ⟺ pure              salWind = writhe         closure components
       hasGlobalEventNaming_          salIncl ⋙ writhe        = cycles of ρ
         iff_braidPure                 = salWind              = n ⟺ pure
```

---

## 8. The one thing I could not settle

**`salWind` in terms of bead sizes.** What *is* proved: the writhe of a refinement equals the
**inversion number** of its event permutation (`writhe_braidPsi`). A chain `a` has `Σᵢ C(dᵢ, 2)` walls
available (pairs within each bead), which bounds the per-step winding. There is **no** clean formula
relating the writhe of a *loop* to the bead sizes, and I did not find one. **Do not assume there is
one.**
