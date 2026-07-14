# Braid Enrichment — cleanup brief

**Purpose.** The braid-enrichment result is finished and (we believe) publishable and original. It is
currently scattered across a repo that also contains a lot of unrelated material. This document says
what the result *is*, what its proof structure *is*, which lemmas are load-bearing, and what the
cleanup should do.

**Status of the mathematics.** Everything marked ✅ below is proved in Lean, sorry-free, axiom-clean
(`propext, Classical.choice, Quot.sound` only), and — this is the surprise — **with no side conditions
anywhere**: no `NonSelfLinked`, no `AdmitsAltitude`, no `Quiver.IsThin`, no `Sculpture`.

**One thing is assumed, and only for interpretation** — see §2.4. Read that before believing anything
about "braids".

---

## 1. The result, as a paper

### Part 1 — the constructions

| | |
|---|---|
| **`Fund K`** | the enriched fundamental category. 0-cells = vertices; 1-cells = **chains**; 2-cells = dihomotopies. No new mathematics. |
| **`CFund K`** | the *complexified* one. 0-cells = vertices; 1-cells = **complexified chains** (= chain **+ line**); 2-cells = **braids**. |
| **`CFund ↠ Fund`** | forget the line. §3 says exactly what this quotient is. |

### Part 2 — the invariants

| | |
|---|---|
| ✅ | `K` is an **HDA** ⟺ every **loop** of `CFund K` gives a **pure** braid |
| ✅ | `salWind` = the **writhe** (exponent sum) of the braid |
| ✅ | `w₁(Sched K)` = the **sign** of the braid's underlying permutation (up to an explicit coboundary) |
| ✅ | the closure of a loop has `n` components ⟺ the braid is pure (so: **`K` fails to be an HDA exactly when some loop's closure has fewer than `n` components**) |
| ✅ | `ker Φ` = the branching / dihomotopy ambiguity |

---

## 2. The proof structure

### 2.1 The objects (all in `Salvetti/`)

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

### 2.2 The braid functor — **this is the heart, and it is short**

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

### 2.3 Why functoriality is easy — **the slice observation**

`Ψ` reads **only** the dims, the block data (`blockIdx`/`blockFace`, which come from the wedge map `φ`
alone), and the lines. The condition `φ ≫ a.map = c.map` — the only place `K` appears in a chain
morphism — is **never consulted**. And every morphism *and every composable pair* lies in a single slice
(`z` refines `y` refines `x`). **So functoriality is a statement about `⋁a.dims`, never about `K`.**

It reduced to three already-unconditional facts:

1. `fineBead_le` — `evKey` is lex (bead first), so beads increase along the frame;
2. **`serialWedge_blockIdx_monotone`** (`Chains/ChainSkeletal.lean`) — **a refinement never reorders
   beads**. This gives the *face* half.
3. `evKey_eventMap_lt` — `linesRestrict` is definitionally `Chamber.restrict` along
   `faceEmb (blockFace …)`, so the coarse chamber restricts to the fine one. This gives the *tope* half.

Cross-bead pairs are trivial: there `y`'s own face is nonzero, so it wins in `⊙`. **~70 lines total.**

### 2.4 ⚠ What is ASSUMED, and where

**The construction of `Φ` does not use Salvetti's theorem at all.** It is elementary and unconditional.

Salvetti's theorem — `|N(Sal(braidCOM n))| ≃ F(ℂ,n)`, hence `π₁ = P_n` — is used **only to justify
calling the target "braids"**. In Lean it is not even stated: `Salvetti/ConcGroupoid.lean` *defines*
`PureBraid n := Aut (FreeGroupoid (Sal (braidCOM n)))` and records the identification in a docstring.

**Keep this separation explicit in the paper.** Construction: unconditional, elementary. Interpretation:
one classical theorem. It is the cleanest way to present it and it is honest.

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
- **Full on 2-cells**: ✅ this is `linesRestrict_surjective` + `exists_conc_zigzag`
  (`Salvetti/PurityHDA.lean`). Every zigzag of chains lifts to a zigzag of executions.
- **Kernel** = the local pure braid groups.

So `Fund K` = `CFund K` **modulo the braid groups** — a full surjection of `Grpd`-enriched categories,
identity on 0-cells. That is the precise sense in which this generalizes the existing directed-topology
work: **`Fund` is the real picture, `CFund` is its complexification, and the braid content is exactly
what the projection destroys.**

Three-tier picture, each the quotient of the last:

```
1-cells = (chain, line)   2-cells = braids           ConcGrpd K       ← CFund
1-cells = chains          2-cells = dihomotopies     Π₁(P⃗ K)          ← Fund
1-cells = trace classes   2-cells = trivial          →π₁(K)           ← the classical fundamental category
```

---

## 4. The enrichment question — read this before choosing

**You cannot literally enrich over the braid category.** Enrichment over `V` needs hom-*objects* in `V`
and composition `Hom(u,v) ⊗ Hom(v,w) → Hom(u,w)` in `V`. The hom-objects here must be **groupoids** —
their *objects are the 1-cells*. The braid category's objects are strand counts. So hom-objects cannot
live in `𝔅raid`.

**What is true, and is the flashy statement:**

> `CFund K` is a **`Grpd`-enriched category** equipped with a **monoidal 2-functor to the delooped braid
> category**, under which **1-cell composition maps to the braid TENSOR** (concatenating executions adds
> strand counts).

✅ Both halves exist: `Flow/Flow.lean` (`flowHom`, `flowComp`) and `Salvetti/BraidDeloop.lean`
(`braidDeloopComp`, where composition really is `n ⊗ m = n + m`).

Equivalently, and this is the sentence for the abstract:

> **`CFund K ≃ →π₁(K)` with every hom-set replaced by a braid group.** (Hom-groupoid `π₀` = the trace
> classes; vertex groups = the concurrency braid groups. From `concGrpdRunEquiv` + skeletality.)

### ⚠ Two hard facts about the Lean packaging

1. **mathlib has no monoidal structure on `Grpd`.** `Cat` has `CartesianMonoidalCategory`
   (`Monoidal/Cartesian/Cat.lean`); `Grpd` has only `Grpd.has_pi`. So `EnrichedCategory Grpd` is **not
   available off the shelf**. `Flow K` is currently bare defs.
2. **Strictness cannot pass through `freeGroupoidProdEquiv`** — it is `Localization.uniq`, characterised
   only up to natural iso.
   **THE FIX (do this):** enrich in **`Cat`** with hom-objects `Cat.of (ConcCat (K;u,v))`, building
   composition via **`FreeGroupoid.lift`**, whose universal property *is* strict (`lift_spec` is an
   equality). `EnrichedCategory Cat` = a genuine strict 2-category, and it is reachable. The only
   missing input is `chambersConcat` associativity/unitality — a `HEq` induction over
   `List.append_assoc`, ~60 lines.

---

## 5. Key lemmas, and where they live

**The load-bearing ones. If you move nothing else, keep these findable.**

| lemma | file | why it matters |
|---|---|---|
| `eventMap_bijective` | `Schedule/EventMapBij.lean` | **unconditional**; the event local system is a local system of *bijections*. Everything about `ρ` rests on this. |
| `serialWedge_blockIdx_monotone` | `Chains/ChainSkeletal.lean` | **a refinement never reorders beads** — the face half of functoriality |
| `evKey` / `keyEquiv` | `Salvetti/Normalize.lean` | the total order on events induced by a line. The *frame*. |
| `concGrpdRunEquiv` | `Salvetti/Normalize.lean` | every 1-cell is 2-iso to a **run**. The normalization. |
| `evPerm_smul_le` | `Salvetti/BraidFunctor.lean` | **functoriality of `Ψ`** — the theorem |
| `braidSalEquiv`, `braidSerialSalEquiv` | `Salvetti/BraidIso.lean`, `SalWedge.lean` | the *interpretation* bridges (§2.4) |
| `ChainCat.sliceEquiv`, `salFunctorSlice` | `Chains/`, `Salvetti/SerialSalLines.lean` | **the slice is a wedge, unconditionally** — why functoriality is local |
| `freeGroupoidProdEquiv` | `Salvetti/FreeGroupoidProd.lean` | `FreeGroupoid (C × D) ≌ FreeGroupoid C × FreeGroupoid D`. Used **three** times (enrichment, delooping, local model). Quiet workhorse. Comes free from mathlib's `Localization/Prod.lean` — **do not hand-roll it.** |
| `salCross_add`, `salWind` | `Salvetti/Braiding.lean` | the winding character, for **any** finite-ground COM |
| `linesRestrict_surjective`, `exists_conc_zigzag` | `Salvetti/PurityHDA.lean` | fullness of `CFund ↠ Fund` |
| `hasGlobalEventNaming_iff_braidPure` | `Salvetti/PurityHDA.lean` | **the headline** |

### The `Fin`/order machinery worth reusing

`Schedule/Orientation.lean`'s `ordSign` compares **two explicit linear orders** (not instances) on one
finite type, with the cocycle identity `ordSign_trans` through **any** middle order. That is the right
tool whenever two frames must be compared; it was reused for the `w₁` coboundary.

---

## 6. ⚠ Landmines (each of these cost real time)

1. **`equivWedgeCat` and `refineToWedge` CARRY `NonSelfLinked` + `AdmitsAltitude`.** Routing through
   them silently imports both while the statement *looks* unconditional. This bit two agents.
   **Never route through the `RefineObj ⟷ Ch` bridge when the point is to have no side conditions.**
   (`RefineConcat.append` is unusable for the same reason. `Chains/Segal.lean`'s `chConcat` /
   `wedgeInclL/R` are the unconditional replacements.)
2. **`(n :: A) ++ B` vs `n :: (A ++ B)`** are defeq but not syntactically equal, and they sit inside
   `serialWedge`/`pushout` **type** arguments. `rw`/`simp`/`reassoc`/even `Category.comp_id` silently
   fail to match. Use `erw` with **fully explicit** arguments (bare `erw` triggers a whnf blow-up through
   `pushout`/`colimit`).
3. **`Type`'s morphisms are bundled `TypeCat.Hom`**; `comp_apply`/`types_comp_apply` do **not** fire in
   `simp` (the `ConcreteCategory` `outParam`s wreck the discrimination keys). Use `exact`/defeq.
4. `Functor.map_id`/`map_comp` unqualified resolve to the **monad** `Functor` under
   `open CategoryTheory`. Write `CategoryTheory.Functor.map_id`.

---

## 7. Two claims of mine that were REFUTED — do not resurrect them

1. **"`evPerm f = 1` for every morphism ⟺ `K` is an HDA" is FALSE**, machine-checked
   (`forall_isRun_of_evPerm_one`). That condition forces **every chain to be a run** — i.e. `K` has *no
   concurrency at all*. Witness: `□²` has a global naming **and** a non-run chain.
   **Purity is a statement about LOOPS.** Quantifying over all morphisms accidentally says "`K` is a
   graph".
2. **Lifting a chain loop does NOT give an execution loop.** A lifted `Ch K` loop at `a` is a path
   `(a, L₀) ⇝ (a, M)` — same chain, *different line*. You must **shift the line back**, and the shift is
   free precisely because runs have unique lines (`exists_lineShift`). **Lines must be shifted, not just
   lifted.**

Both are recorded because they are the two places the naive statement is wrong, and both are one line
away from a false paper.

---

## 8. What the cleanup should do

### 8.1 Separate the thread

The braid result depends on: `Foundations/`, `Chains/`, `Arrangements/`, `Salvetti/`, plus **two files
from `Schedule/`** (`EventNaming.lean`, `EventMapBij.lean`) and **one** (`Orientation.lean`, for the
`ordSign` machinery and `w₁`).

Everything else in `Schedule/` (the schedule space, the atlas, cones, charts, `MORSE.md`), all of
`Cylinder/`, and all of `Testing/` is **not** on the critical path. Move the needed `Schedule` files
into the braid thread (or a shared `Events/` layer) and quarantine the rest.

### 8.2 De-bipoint

`BPSet` is bipointed, and most of the development does not need it. `Flow/ChainConcat.lean`'s
**`BPSet.repoint K u v`** shows the way — and note `K.repoint K.init K.final = K` is **`rfl`** (structure
eta). Either (a) generalize `Ch`/`Lines`/`ConcCat` to take endpoints, or (b) keep `repoint` as the
official idiom and delete the bipointing from everything that does not use it. **Decide once.**

### 8.3 Revisit the proofs with hindsight

Several things are almost certainly now shorter than they were when first written:

- `WallCrossing.lean` was built as an ingredient of `braidSalEquiv` and is stated **for cubes only** —
  not because cubes are needed. It is a special case of `evPerm_smul_le`. Probably deletable.
- `linesRestrict_surjective` came out **far** cheaper than planned: no interleaving construction is
  needed, because `eventEquiv` *already is* the statement that a coarse bead's directions **are** the
  fine events inside it. Look for the same shortcut elsewhere.
- `salSumEquiv` is **not** reusable for the braid tensor (`COM.directSum`'s ground set is only the
  *within*-block pairs; the extension-by-block-order is the whole content). Do not try again.
- The `Sₙ`-action on `braidCOM n` (`BraidFunctor.lean`) and the reindexing `salReindex`
  (`BraidDeloop.lean`) are the same construction at different generality. Unify.

### 8.4 The diagram to draw for the paper

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

### 8.5 One thing I could not settle

**`salWind` in terms of bead sizes.** What *is* proved: the writhe of a refinement equals the
**inversion number** of its event permutation (`writhe_braidPsi`). A chain `a` has `Σᵢ C(dᵢ, 2)` walls
available (pairs within each bead), which bounds the per-step winding. I have **no** clean formula
relating the writhe of a *loop* to the bead sizes, and I did not find one. Do not assume there is one.

---

## 9. Housekeeping

Untracked scratch files the sandbox would not let me delete — `git clean` them:
`AxCheck.lean`, `CubeChains/Testing/{Scratch5,AxCheckRev,Cube5Tmp,SqTmp,T1}.lean`.

---
## 10: parting wisdom

The braid-enrichment result is finished and we believe it is publishable and original. hasGlobalEventNaming_iff_braidPure — K is an HDA iff every loop of the flow category gives a pure braid — is proved, unconditional, axiom-clean. The repo, however, is massive and scattered, and the thread is hard to follow.
The next major chunk of work will be to execute on the cleanup work:
1. Separate the thread (§8.1). Isolate what the braid result actually depends on; quarantine Schedule/ (except EventNaming, EventMapBij, Orientation), Cylinder/, and Testing/.
2. Decide the enrichment (§4). Enriching over Groupoid would be nice, but mathlib support is limited. Enriching over Cat works, but we know something far nicer. It might be nice encrich over the category of braids, which I think is just salvetti's theorem + what we already have. That is, objects are natural numbers, and all morphisms are from n to n. Each morphism is a braid word on n strands.
3. Build Fund and CFund and the projection between them (§3) — the quotient is literally "forget the line", and its fullness is already proved.
4. De-bipoint (§8.2) and K.repoint shows the way and K.initK.final = K is rfl.
5. Revisit the proofs with hindsight. WallCrossing.lean is probably deletable.
Do not attempt to shorten the braid functor itself; it is already ~70 lines and its proof is already the "right one".

The construction never uses Salvetti's theorem. Φ is elementary and unconditional; Salvettarget is a braid group. Keeping that separation explicit is, I think, the cleanest way to present the paper — and it is what makes the result feel like a genuine lift rather than a transport.
The functoriality is local, and that's the whole trick. Ψ never reads K — only the dims, the block data, and the lines — and every composable pair lies in one slice. So the theorem is a statement about a wedge.