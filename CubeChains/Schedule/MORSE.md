# Morse theory and the cube-chain complex

*Companion to `DESIGN.md`.  `DESIGN.md` says what `Sched K` **is** (a manifold charted by
braid cones, atlas `Ch K`).  This says what it is **for**.*

> **⚠ Read this first — two conjectures in here were machine-refuted (`Testing/`).**
> 1. **§4(a):** a *time function* does NOT glue the local Morse matchings.  It orders **beads**; the
>    matching must order **events inside a bead**.  `fourSquare` is the witness.  Corrected in place.
> 2. **The "curvature = causality" thesis is FALSE.**  `∂²` (the signed 2-path count on the
>    vertex/altitude complex) does not detect causality: `threeSquare` has causality with `∂² = 0`
>    (parallel 2-paths cancel), and the trinity has none with `∂² ≠ 0` — and there the sign system is
>    *inconsistent*, which is exactly the non-orientability of `Sched T`.
>    **Causality does not linearize.**  It lives in the non-invertibility of the fundamental
>    *category*; concurrency lives in homology.  The two are separated by **localization**
>    (`ConcCat K ⟶ ConcGrpd K` destroys causality and creates the braiding), not by two homologies.
>    See `Salvetti/BRAID.md` and the `concurrency-vs-causality` memory.
>
> What DID survive: the cube-chain complex and its duality (§2–2a); `w₁` = the event-naming
> monodromy; the discrete-Morse payoff (`□ⁿ` collapses to one critical cell, `541 → 1` at `n = 5`);
> and the exactness of the vertex/altitude complex on cubes (it is the Koszul complex).

## 0. The one-sentence answer to both questions

`Sched K` is a stratified space whose strata are the cells of an arrangement, graded by
**bead count**.  That grading is a Morse function; its Morse complex is the **cube-chain
complex**

> `C_k(K) = ℤ[ chains with k beads ]`,  `∂[c] = Σⱼ (−1)ʲ Σ_{D fuses beads j,j+1} [c ⋯ D ⋯]`

and it computes the (Borel–Moore, time-oriented) homology of `Sched K`, hence — by duality —
the cohomology of the directed path space `P⃗(K)`.  A **Morse function on `K`** (a strictly
increasing real function on vertices) is exactly the global datum needed to (i) pick a point in
every stratum and (ii) glue the *local* Salvetti/COM matchings into a *global* discrete-Morse
matching, which shrinks that complex.  So the two questions are one question.

---

## 1. The grading: `Sched K` is an arrangement, stratified by bead count

Fix a chain `a` with beads `d₁ … d_k`, `n = dimSum a = Σdᵢ`.

```
C a  =  { t : E a → ℝ | bead e < bead e' → t e < t e' }   ⊂  ℝ^(E a),   dim = n
```

The braid arrangement on `E a` cuts `C a` into strata; the stratum of a refinement `c ⟶ a` is
`Δ° c = {τ : Fin (nbeads c) → ℝ | StrictMono}`, and

| | |
|---|---|
| `dim (stratum c)` | `nbeads c` |
| deepest stratum of `C a` | `a` itself (all of a bead's events tied) |
| open chambers of `C a` | the **finest** chains — `nbeads = dimSum`, one event per bead: *linear executions* |
| closure order | `stratum a ⊆ closure (stratum c)  ⟺  c ⟶ a` (c refines a) |

So **`nbeads` is the cell dimension**, and `Ch(K)ᵒᵖ` is the face poset of a regular cell
structure on `Sched K` — locally the face poset of `braidDirectSum a.dims`
(`serialSalBaseEquiv`, L11), globally glued by the atlas.  Coarse = concurrent = deep; fine =
sequential = generic.

Two consequences, both purely local (i.e. checkable inside a single slice, where the slice is a
COM face poset ≅ ordered set partitions of the beads):

* **graded**: every cover `c ⋖ a` raises `nbeads` by exactly 1, and is a **merge of two adjacent
  beads** (blocks of an ordered set partition coarsen by merging adjacent blocks);
* **diamond**: every length-2 interval `[c, a]` has exactly **two** elements strictly between —
  the two cases are `(A|B|C) ⟶ (ABC)` (intermediates `A|BC`, `AB|C`) and two independent merges
  (intermediates: do one, do the other).

That is the whole input needed for a cellular chain complex.  *`∂² = 0` is a length-2 interval
condition, and every length-2 interval of `Ch K` lives in a single slice.*  **This is the
local-to-global mechanism** (question 2): the local COM does not need to be "assembled" — it
already governs every interval, and the only global conditions are of interval length ≤ 2.

## 2. The cube-chain complex

Beads `j, j+1` of `c` (dims `p`, `q`) are **fused** by a cube `D ∈ K_{p+q}` *together with a
bipartition* `S ⊔ Sᶜ = Fin (p+q)`, `|S| = p`: the face of `D` freeing `S` and zeroing `Sᶜ` is `cⱼ`,
and the face freeing `Sᶜ` and setting `S` to `1` is `c_{j+1}`.  **Every** bipartition counts, not
just the staircase `S = {0,…,p−1}` — a `d`-cube splits into two beads along any ordered
bipartition of its directions.  (Restricting to the staircase silently drops incidences and breaks
duality; verified.)

```
C_k(K) := ℤ[ {c : chains of K, nbeads c = k} ]
∂[c]   := Σ_{j=0}^{k-2} (−1)^j  Σ_{(D,S) fusing beads j,j+1}  [ merge j D c ]
```

`∂² = 0` — and, notably, **unconditionally**: the sum is over *all* fusing `(D,S)`, so branching
(several cubes with the same boundary) is handled, not excluded.  The cancellation is the diamond:

* *independent merges* `j`, `j'` (`j' ≥ j+2`): the two orders give `(−1)^j(−1)^{j'-1}` and
  `(−1)^{j'}(−1)^j` — cancel;
* *3-into-1*: a cube `D` fusing three consecutive beads determines **both** intermediates as
  *faces of `D`* (faces of a cube of `K` are cubes of `K`), so the two routes are in bijection and
  carry signs `(−1)^j(−1)^j` and `(−1)^{j+1}(−1)^j` — cancel.

The `(−1)^j` is forced, not chosen: `Δ° c` has canonical coordinates `τ₀ < ⋯ < τ_{k-1}`, and
`ι_ν(dτ₀∧⋯∧dτ_{k-1})` at the wall `τⱼ = τ_{j+1}` (`ν = ∂_{τⱼ} − ∂_{τ_{j+1}}`) is `(−1)^j` times the
merged cell's form.  The block *contents* never enter — so no shuffle sign.

**What it computes.** `C_•` is the cellular Borel–Moore complex of the stratification of `Sched K`.

## 2a. `Sched K` need not be orientable — and `w₁` is the event-naming monodromy

The charts of `Sched K` are `ℝ^(E a)`; the transitions are the **event bijections**, i.e. coordinate
*permutations*.  Their signs form an orientation local system `or`, and the cells' canonical
(bead-time) orientations do **not** glue: `Δ°[ef]` and `Δ°[fe]` induce opposite orientations of the
plane.  So

```
H_k(C_•)              ≅ H^{n−k}(P⃗ K ; or)      -- untwisted BM, incidence (−1)^j
H_k(C_• ⊗ or)         ≅ H^{n−k}(P⃗ K ; ℤ)       -- or-twisted BM
```

and the `or`-twist is implemented by weighting each incidence with the **shuffle sign**
`(−1)^{inv(S,Sᶜ)}` — that sign *is* the orientation cocycle.  It is a coboundary exactly when the
chain's events admit a coherent global order, via `ε(c) = sign of the permutation sorting c's
events`.  Hence:

> **global event naming ⟹ `Sched K` orientable**, and `w₁(Sched K)` is the sign character of the
> event-naming monodromy.

The machine-verified witness is the **trinity** (`Testing/EventNamingCounterexample.lean` — the
example with no global event naming).  `n = 2`, `N(Ch T) ≃ S¹`, and the odd cycle is the hexagon
`[am,md] → [t1] ← [ab,bd] → [Q] ← [ac,cd] → [t2] ← [am,md]` (three `−1`s).  There the untwisted BM
homology is **`0` in every degree** — the rank-1 nontrivial local system on `S¹` — while the twisted
one is `[0,1,1]`, dual to the nerve's `[1,1,0]`.  The refuted global-event-naming thread was not a
dead end: its obstruction is a real characteristic class.

Checks (all machine-verified, `Testing/CubeChainComplex.lean`; duality below is against the
*twisted* complex, which is the one dual to the untwisted nerve):

| `K` | `n` | `b(merge, twisted)` | `b(N(Ch K))` | orientable |
|---|---|---|---|---|
| `□²` | 2 | `[0,0,1]` | `[1,0,0]` (`pt`) | ✓ |
| `□³` | 3 | `[0,0,0,1]` | `[1,0,0,0]` | ✓ |
| two squares, same boundary | 2 | `[0,1,1]` | `[1,1,0]` (`S¹`) | ✓ |
| diamond (two edge-paths) | 2 | `[0,0,2]` | `[2,0,0]` | ✓ |
| four-square loop | 3 | `[0,0,1,1]` | `[1,1,0,0]` (`S¹`) | ✓ |
| **trinity** | 2 | `[0,1,1]` | `[1,1,0]` (`S¹`) | **✗** |

The branching that makes `Sched K` non-Hausdorff is what puts the entry `1+1` into `∂` for the two
squares; the complex *sees* it.  This is the chain complex that was hiding.

**Dual reading.** The transpose of `∂` is the **split** differential (refine a bead into two
ordered halves).  That is the cellular boundary of Ziemiański's CW structure on `P⃗(K)`: the cell
of a chain has dimension `dimSum − nbeads`, the cell of a single `d`-bead is the
`(d−1)`-**permutohedron** (its `2^d − 2` facets = the ordered bipartitions = the one-step
refinements), and a general cell is a product of permutohedra.  Merge-complex and split-complex
are transposes; the merge signs are trivial, so build that one.

## 3. Morse functions on `K`

**Definition.** A *time function* (= Morse/Lyapunov function) on `K` is
`f : K.cells 0 → ℝ` with `f (vertex₀ e) < f (vertex₁ e)` for every edge `e`.  Equivalently: a
positive 1-cochain that is exact.  `AdmitsAltitude` is the rigid ℤ-valued unit-step special case;
a time function is the flexible one, and it exists (for finite `K`) **iff `K` has no directed
cycle** — the Lyapunov criterion.

Three things it buys, all cheap:

1. **Finiteness.** time function ⇒ no cycles ⇒ `dimSum` bounded ⇒ `Ch K` finite (for finite `K`).
   That is what makes `C_•(K)` a finite complex at all.
2. **A section of the stratification.** A chain `c` has junction vertices `v₀ … v_k`; set
   `s_f(c) := (c, τ)` with `τⱼ = f(vⱼ)`.  Strict monotonicity of `f` along directed paths is
   exactly `StrictMono τ`, so `s_f(c) ∈ Δ° c`:

   ```
   s_f : Ch K ⟶ Sched K,   π ∘ s_f = id     (a canonical point of every stratum)
   ```

   *A Morse function on `K` is precisely a coherent choice of one schedule per stratum.*
3. **A global generic direction, without a global chart.**  This is the point.  The obstruction
   to globalizing the arrangement picture is the monodromy of the *event* naming (`TwoSquares`).
   But `f` lives on **vertices**, which *are* globally named, and it induces a coherent choice in
   every chart.  So `f` can play the role that a generic linear form/flag plays in the
   Salvetti–Settepanella theory — which is what the next section needs.

## 4. The flow category, honestly

Take the Morse function `nbeads` on `Sched K`.  Its "critical manifolds" are the strata; the
unstable manifold of `c` is `star c`; flow lines from a cell to a codim-1 face are unique.  So
the flow category has objects `Ch K` and *contractible* moduli spaces, and its classifying space
is `|N(Ch K)| ≃ Sched K` (L6/L9) — i.e. **the naive flow category is just `Ch K` again**, and its
Morse complex is §2.  That is a consistency check, not a new theorem; say so and move on.  The
genuinely new content is in the two refinements:

**(a) Discrete Morse theory — this is where the payoff is.**  An acyclic matching on the Hasse
diagram of `Ch K` collapses `C_•` to a **Morse complex on the critical chains**.  Each slice is the
face poset of `braidDirectSum a.dims` = ordered set partitions, for which explicit acyclic matchings
are classical (Salvetti–Settepanella; Delucchi; the COM case in the DDP paper).

**Machine-verified payoff** (`Testing/MorseReduction.lean`): `□ⁿ` collapses to **exactly one**
critical cell (n = 2,3,4 with the exact Morse complex; n = 5 for the matching).  Chain counts are the
Fubini numbers `1, 3, 13, 75, 541, …`, so the reduction is `541 → 1` at `n = 5`.  On every acyclic
example the Morse homology **equals** the full homology, for *both* the untwisted and the `or`-twisted
boundary; every acyclic case is in fact a **perfect** matching (criticals per degree = Betti numbers).

**⚠ The local matchings do NOT glue, and a time function does NOT fix it.**  On `fourSquare` the four
fine chains and four square-chains form an **8-cycle** in the Hasse diagram; the purely local rule
merges at every one of them, and every perfect matching of a cycle is cyclic.  Since
`H_*(P⃗ fourSquare) = H_*(S¹)`, *any* acyclic matching needs ≥ 2 criticals, so no always-merge rule
can work there.

A time function is the **wrong** tie-break, for a sharp reason: both staircases of a square start at
the *same vertex*, so a vertex-valued function carries no information about which to prefer.  A time
function orders **beads**; the matching must order **events within a bead**.  What Salvetti–
Settepanella actually need is a generic linear functional on the *events* — i.e. a global total order
on events.  `fourSquare` has none (its four squares fuse all eight edges into one parallelism class,
so it has **no global event naming**), and the cube-internal coordinate order winds around the loop.

> **(M, corrected)** Global event naming ⟹ the arrangement matching glues canonically, giving a
> canonical minimal model of `P⃗(K)`.  Without naming, an arbitrary global order on cells still works
> empirically (all 10 examples) but is a *choice*, not a construction — and is not `Aut(K)`-invariant.
>
> Caveat: the trinity has no global naming either yet *is* acyclic under the local rule.  So naming is
> not equivalent to acyclicity; it is what removes the guarantee, not what forces failure.

**This closes the loop with §2a.**  Event-naming monodromy now obstructs: a global chart (refuted,
two-squares); orientability (`w₁`, §2a); a multivariable Alexander polynomial; and a *canonical*
Morse matching.  One obstruction, four faces.

**(b) Complexification — the concurrency braid group.**  The Salvetti complex of an arrangement
models the *complexified* complement.  Locally that is `Sal(localCOM x) ≌ Int(Lines(⋁ x.chain.dims))`
(`SalLocal.lean`, **already proved**), and `SalLocal` also already proves the local pieces are
**full subcategories of `Int(Lines K)` covering it**.  So `Int(Lines K)` is the *global* Salvetti
complex, and

> `|N(Int(Lines K))|` = the complexified schedule space; `π₁` = a **concurrency braid groupoid**
> of `K`; for `K = □ⁿ` the local model is the braid arrangement complement, so this is the pure
> braid group `P_n`.

This is the flow category with the moduli spaces *not* collapsed: hom-data = `Lines` = which
chamber (= which total order of the concurrent events) the flow came in on.  The assembly is the
category of elements / hocolim, and the computational shadow is the stratification spectral
sequence

```
E₂ = H_*( Ch K ; H_*(Sal (local COM)) )  ⟹  H_*( |N (Int (Lines K))| ).
```

**That is the answer to "does the local COM data assemble globally":** yes — as a constructible
sheaf on `Sched K` (`Ch K` is its exit-path poset), whose stalks are the local Salvetti complexes,
and the assembly is hocolim, *not* Čech (there are no meets — `DESIGN.md` L7).

## 5. Build order

| # | file | content | depends on |
|---|---|---|---|
| 0 | `Testing/CubeChainComplex.lean` | computable `∂`, `∂²=0`, Betti numbers; validate §2's table and the duality against the order complex of `Ch K` | Testing harness only |
| 1 | `Chains/Grading.lean` | `nbeads`; covers = adjacent-bead merges; `nbeads` graded | `Chains/`, `Segal` |
| 2 | `Chains/Diamond.lean` | length-2 intervals have exactly 2 middles — transported from ordered set partitions via `sliceEquiv` + `serialSalBaseEquiv` | `Salvetti/`, `Arrangements/` |
| 3 | `Chains/CubeChainComplex.lean` | `C_•(K) : ChainComplex ℤ ℕ`, `∂² = 0` | 1, 2 |
| 4 | `Foundations/TimeFunction.lean` | time function; ⇒ `Fintype (Ch K)`; `s_f : Ch K → Sched K` a section | `Foundations/Altitude`, `Schedule/Space` |
| 5 | `Schedule/DiscreteMorse.lean` | the matching (M); critical chains; Morse complex ≃ `C_•` | 3, 4 |

Nothing above needs `RunInjective`, `Sculpture`, or a global chart.  Steps 1–3 need nothing but
the precubical axioms (the diamond can be proved directly from "faces of a cube are cubes"); the
COM layer is what *explains* them and what step 5 needs.
