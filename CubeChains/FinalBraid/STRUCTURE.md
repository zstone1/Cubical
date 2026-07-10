# The structure of `R(K) := Int(Lines K) = (Lines K).Elements`

Companion to `DESIGN.md`. What `R(K)` *is*, what its nerve looks like, and how it compares to
the nerve of `Ch(K)`.

---

## 0. Summary

> `Sal L` and `R(K)` are both `∫` of a **presheaf of maximal elements with retractions** on a
> face-like poset. `Sal L` gets that presheaf from `comp`; `R(K)` gets it from `faceEmb`.
> This is a structural analogy, **not** a claim that `Ch(K)ᵒᵖ` is the covector poset of a COM
> for general `K` — that holds for `K = □ⁿ` (it is `braidCOM n`) and is the whole content of the
> target theorem. See §6.
>
> `N(Ch K)ᵒᵖ` and `N(R K)` are both **permutohedral complexes**. They have the *same cells*
> — one product-of-permutohedra `∏ᵢ Π_{dᵢ−1}` per cube chain `a` — except that `N(R K)`
> carries **one copy of each cell per vertex of that cell**. The projection
> `π : R(K) ⥤ Ch(K)ᵒᵖ` folds the copies together.
>
> For `K = □ⁿ`: `N(Ch □ⁿ)` is a **single permutohedron `Π_{n−1}`** (contractible), while
> `N(R □ⁿ)` is **`n!` permutohedra glued along faces** = the Salvetti complex of the braid
> arrangement `≃ Conf_n(ℂ) = K(P_n, 1)`.

---

## 1. The dictionary (why `R(□ⁿ) ≅ Sal(braidCOM n)`)

Objects of `Ch(□ⁿ)` are cube chains; `SalBraidPartition.lean` shows each one is exactly an
**ordered set partition** `(B₁, …, B_ℓ)` of `Fin n` (`blockOf`/`blockIndex`, blocks disjoint and
covering, `Σ|Bᵢ| = n`). Morphisms `x ⟶ y` in `Ch` mean *`x` refines `y`*, so:

| cube-chain side | braid COM side |
| --- | --- |
| chain `a` with beads `d₁,…,d_ℓ` | covector `X` = ordered set partition, `ℓ` blocks |
| `a ⟶ b` in `Ch(K)` (`a` finer) | `X_b ⊑ X_a` (face order) |
| `Lines a = ∏ᵢ Chamber(dᵢ)` | topes `T ⊒ X` (linear orders refining the blocks) |
| `linesRestrict` | `comp X' T` (wall crossing) |
| `Ch(□ⁿ)ᵒᵖ` | face poset of `A_{n−1}` = face poset of `Π_{n−1}` |
| `R(□ⁿ) = ∫Lines` | `Sal(braidCOM n)` |

Two facts make the last line work:

- **`X ⊑ T` forces the blocks to be intervals of `T`.** If `i <_T j <_T k` with `i,k ∈ B` and
  `j ∉ B`, then `X` puts `B` before `j`'s block *and* after it. So a Salvetti cell `(X,T)` is
  literally "a linear order `T` of `Fin n` cut into consecutive blocks" = "a chain with a
  chamber".
- **`Sal L` is itself a Grothendieck construction.** `X ↦ {topes above X}` is a covariant
  functor on `(L.covectors, ⊑)` — functorial by `comp_comp_of_faceLE`, unital by
  `comp_eq_right_of_faceLE` — and `SalCell`'s `PartialOrder` is exactly `∫` of it. Same shape as
  `∫Lines`.

So the conjecture factors cleanly, and `Elements.lean` already has the two connectives:

1. `Ch(□ⁿ)ᵒᵖ ≌ (braidCovectors n, ⊑)` (ordered set partitions ↔ covectors), then
2. `Lines ≅ Topes ∘ (that equivalence)` (natural iso), then
3. `CategoryOfElements.preEquivalence` + `mapEquivalence` ⟹ `∫Lines ≌ Sal`.

**`Lines a` is intrinsically the set of finest chains refining `a`.** A maximal refinement of a
bead `□^d` is a maximal chain of `{0,1}^d` = a linear order on its `d` directions. Under thinness
this is a bijection. So `Lines` is the "topes above" presheaf with no braid input at all — the
COM is only needed to *name* it.

---

## 2. `R(K)` as a category

`Lines K : Ch(K)ᵒᵖ ⥤ Type`, so with `C := Ch(K)ᵒᵖ` (order: `a ≤ b` iff `b` refines `a`):

- **Objects** `(a, L)`: a chain plus a chamber per bead.
- **Morphisms** `(a,L) ⟶ (b,M)`: `b` refines `a` **and** `M = L|_b`. The second component is
  *determined*, so `π : R(K) ⥤ Ch(K)ᵒᵖ` is a **discrete opfibration** with fibre `Lines a`.
- **Thin** (`Functor.elements_isThin`), and antisymmetric whenever `Ch(K)` is — so a poset.

The one counterintuitive point: **the "line" is not preserved by morphisms.** Refining
`a = [2]` with chamber `x<y` into `b = [1,1]` along the *other* edge path yields `M` with
`y <_M x`. That is exactly Salvetti's `T' = comp X' T` — the wall crossing. There is no functor
`R(K) → {lines}`; only `π` to the chain.

**Wedge/Segal.** `linesWedgeEquiv` gives `R(X ∨ Y) ≌ R(X) × R(Y)`, matching COM direct sum
`Sal(L₁ ⊕ L₂) ≅ Sal L₁ × Sal L₂`. Serial wedge = direct sum.

### Same objects, different morphisms: where the information actually is

`Lines a ≅ {ℓ ∈ Fin(K) : ℓ ⟶ a}`, where `Fin(K)` = the finest (all-dims-`1`) chains, the "lines".
So the following two categories have **literally the same objects** — pairs `(a, ℓ)` with `ℓ`
refining `a`, of which there are `n!·2^{n−1}` for `□ⁿ`:

- `I(K)`, the **inclusion** version: `(a,ℓ) ⟶ (a',ℓ)` when `a` refines `a'`. This is `∫` of the
  covariant `a ↦ {lines refining a}` with the subset inclusions, i.e. the comma category
  `(Fin(K) ↓ Ch K) = ⨿_ℓ (ℓ ↓ Ch K)`. Each piece has an initial object, so
  `|N I(□ⁿ)| = n!` points.
- `R(K)`, the **retraction** version: `(a,ℓ) ⟶ (b, proj_b ℓ)` when `b` refines `a`.
  `|N R(□ⁿ)| ≃ K(P_n, 1)`.

The *only* difference is whether the line is carried along unchanged or pushed through the
retraction. That substitution alone turns `n!` contractible components into the pure braid group.
The projections are the entire content.

**The retraction is a degeneracy, not a precubical map.** A face inclusion `d : □ᵏ ↪ □ᵐ` fixes
coordinates; the retraction `r : □ᵐ → □ᵏ` forgets them, `r ∘ d = id`. In the cube category `r` is
a composite of degeneracy operators, and `Box` is degeneracy- and symmetry-free — so `r ∉ Box`.
But `Lines` only ever needs `r` **on the beads** (standard cubes), never on `K`. That is why
`Lines` is definable here at all, and why `linesRestrict` had to be built from `faceEmb` rather
than pulled from Yoneda. In sign vectors `r` is the **Tits projection** `T ↦ comp X T`;
`comp_eq_right_of_faceLE` says it is a retraction and `comp_comp_of_faceLE` says it is functorial.

---

## 3. The nerve of `R(K)`

**Simplices.** Because `π` is a discrete opfibration, a `k`-simplex is a base chain plus one
element of the fibre at its *initial* vertex:

```
N(R K)_k  ≅  Σ_{a₀ ≤ a₁ ≤ … ≤ a_k in Ch(K)ᵒᵖ}  Lines(a₀)
```

i.e. a flag of successive refinements together with a chamber on the coarsest one. The inner
`dᵢ` just drop `aᵢ`; only `d₀` does anything interesting — it restricts the chamber
(`Lines(a₀) → Lines(a₁)`), which is the wall crossing. Equivalently:

> `N(R K) → N(Ch K)ᵒᵖ` is the **left fibration classified by `Lines`** — discrete fibres,
> the simplicial-set unstraightening of the chamber presheaf.

It is **not** a covering: `linesRestrict` is not bijective (`Lines[2]` has 2 elements,
`Lines[1,1]` has 1).

**Cells.** `↑(a,L) = {(b,M) : b refines a}` — the chamber is forced — so

```
↑(a,L) ≅ (refinements of a) ≅ ∏ᵢ (ordered set partitions of bead i's dᵢ directions)
       = ∏ᵢ face poset of the permutohedron Π_{dᵢ−1}
```

So `R(K)` is the (opposite of the) face poset of a **regular CW complex whose closed cells are
products of permutohedra**, one cell per `(a, L)`, of dimension `Σᵢ(dᵢ − 1)`. Its nerve is the
order complex = the barycentric subdivision of that complex.

Note `#Lines(a) = ∏ᵢ dᵢ! = ` **the number of vertices of the cell `∏ᵢ Π_{dᵢ−1}`**.

**Homotopy type.** `|N(R K)| ≃ hocolim_{Ch(K)ᵒᵖ} Lines` (Thomason). All of it is monodromy of
`Lines`; the base contributes nothing.

---

## 4. Comparison with `N(Ch K)`

`Ch(K)ᵒᵖ` has the *same* cell structure with the chamber dropped: closed cell
`↑a ≅ ∏ᵢ Π_{dᵢ−1}`, one per chain. This is precisely **Ziemiański's permutohedral model of the
directed path space** `P⃗(K)(v₀,v₁)` — which is why `Ch` was defined in the first place.

Hence:

| | `N(Ch K)ᵒᵖ` | `N(R K)` |
| --- | --- | --- |
| cells | one `∏Π_{dᵢ−1}` per chain `a` | one per `(a, L ∈ Lines a)` |
| copies over `a` | 1 | `∏dᵢ!` = #vertices of the cell |
| meaning | d-path space of `K` | Salvetti complex of `K` |

`|Nπ|` is a cellular map, `∏dᵢ!`-to-one on the cell over `a`: bijective on vertex cells (finest
chains), `n!`-to-one on the top cell. That degree drop is the whole story.

### `K = □ⁿ`

`Ch(□ⁿ)` has a **terminal object** — the one-bead chain `⟨[n], 𝟙⟩` — since `a ⟶ ⟨[n],𝟙⟩` is
uniquely `a.map`. So:

- `|N(Ch □ⁿ)| = Π_{n−1}`, a single `(n−1)`-ball. Contractible. (The d-path space of `□ⁿ` from
  `0` to `1` is contractible ✓.)
- `|N(R □ⁿ)| = Sal(A_{n−1})` — `n!` permutohedra (one per chamber of `□ⁿ`) glued along faces
  `≃ Conf_n(ℂ) = K(P_n, 1)`.

`Ch(□ⁿ)ᵒᵖ` has an *initial* object, so `lim Lines = Lines([n]) = Chamber n`: there are `n!`
**sections** `s_c : Ch(□ⁿ)ᵒᵖ ⥤ R(□ⁿ)`, `a ↦ (a, c|_a)`, with `π ∘ s_c = id`. Their images are
exactly the `n!` closed top cells. So the permutohedron sits inside Salvetti `n!` times, and
folding them is `π`.

Failure of `Lines` to be representable *is* the braid monodromy: if it were, `∫Lines` would have
an initial object and be contractible. Instead it has `n!` minimal objects `([n], c)`.

### Counts (sanity)

`#Ob Ch(□ⁿ) = Fubini(n)`; `#Ob R(□ⁿ) = Σ_a ∏dᵢ! = n!·2^{n−1}`; cells of `R(□ⁿ)` in dimension `i`:
`n!·C(n−1, i)`.

- `n = 2`: `Ch` = 3 objects = face poset of a segment `Π₁`. `R` = 4 objects = 2 segments glued at
  both endpoints = `S¹ = K(ℤ,1) = K(P₂,1)`. ✓
- `n = 3`: `Ch` = 13 = `1 + 6 + 6` = face poset of the hexagon `Π₂`. `R` = 24 = `6` hexagons,
  `12` edges, `6` vertices — the classical Salvetti complex of `A₂`; `χ = 0`, Poincaré
  polynomial `(1+t)(1+2t)`, `π₁ = P₃ ≅ F₂ × ℤ`. ✓

---

## 5. Consequences for the Lean development

1. **`R` is a poset — and antisymmetry is FREE** (see §9). `Ch(K)` has only identity
   endomorphisms and is skeletal for *every* `K`, unconditionally. So `≃o` needs nothing beyond
   `chainCat_hom_subsingleton`, which we already have for `□ⁿ`. The only new input is
   `serialWedge_admitsAltitude` (the `trueCount` prefix-sum altitude on `serialWedge dims`).
2. **The tope witness.** `SalBraidPartition` gives `covectorHeight = blockIndex`, and
   `SalBraidChamberRank` gives `chamberRank`. The tope is the lexicographic height
   ```
   height p = n * blockIndex x p + chamberRank (L (blockIndex x p)) p
   ```
   (`0 ≤ chamberRank < dᵢ ≤ n`, so cross-block comparisons are dominated by the block index).
   It is injective, and `faceLE (braidSign covectorHeight) (braidSign height)` is immediate.
   The glue lemma: `Chamber (dᵢ)`'s `Fin dᵢ` matches `blockOf x i` through
   `nones (toStar (bead i))` — the same `orderEmbOfFin` that `faceEmb` uses.
3. **The two real lemmas**, in order of difficulty:
   - *(order)* `linesRestrict f L` corresponds to `comp X_b T_{a,L}` — the naturality square.
     This is the mathematical content; everything else is bookkeeping.
   - *(essential surjectivity)* an ordered set partition of `Fin n` builds a cube chain with
     `blockOf` giving it back.
4. **Structure to exploit:** `Sal L = ∫ (topes-above)` over `(L.covectors, ⊑)` on the nose. So
   prove the comparison as an iso of *presheaves over an iso of bases* and let
   `preEquivalence`/`mapEquivalence` do the rest, rather than matching cells by hand.

---

## 6. What is and is not general

"Tope" and "linear order on `Fin n`" are `□ⁿ`-only. A chamber *per bead* is always a linear order
on that bead's `Fin dᵢ`; what fails to generalise is the **assembly** of the tuple into one order,
which needs the beads' direction sets to partition a single `Fin n`. That is exactly what
`SalBraidPartition` establishes for `□ⁿ`, and it is where the braid arrangement enters.

For general `K` only this survives, and it is enough to define `∫`:

- `Lines a ≅ {ℓ ∈ Fin(K) : ℓ ⟶ a in Ch(K)}` — the maximal objects of `Ch(K)ᵒᵖ` above `a`.
  Injective because `Ch(K)` is thin (the morphism `ℓ ⟶ a` is unique), so distinct chamber tuples
  give distinct lines. No COM required.
- For `b` refining `a`: `Lines b ⊆ Lines a` as subsets of `Fin(K)`, and `linesRestrict` is a
  **retraction** onto that subset (identity on `Lines b`), functorially.

A family of subsets-with-retractions indexed by a face poset is precisely what a COM's covector
poset carries via `comp`. Whether `Ch(K)ᵒᵖ` genuinely *is* a COM covector poset for general `K`
is **not** automatic — see §8, where `∂□ⁿ` is a counterexample.

### `Σ Hom` gives the cells, but with the wrong variance

`Lines a ≅ Σ_{ℓ ∈ Fin(K)} Hom_{Ch K}(ℓ, a)` — a bi-pointed wedge map `∨(1,…,1) ⟶ ∨(a.dims)` is a
monotone edge path through the beads, hence a maximal chain in each bead. The `Σ` keeps distinct
`φ` distinct even when they induce the same `ℓ`, so this needs **no thinness and no NSL**
(surjectivity does use `blockIdx` monotonicity, free on the `RefineObj` side).

⚠ But `Σ_ℓ Hom(ℓ,−)` is **covariant** — post-composition fixes `ℓ`. It is the inclusion functor
`I(K)` of §2, not `Lines`. So this is an isomorphism of **objectwise sets only**, never of
presheaves. Usable for the object bijection in `ObjectBijection`; useless for `OrderCompat`.

Consequence worth stating: the *cells* of `R(K)` are determined by the category `Ch(K)` alone.
Only the retraction maps are extra data.

---

## 7. Citations for "`Sal` is a category of elements"

- **Dorpalen-Barry–Dugger–Proudfoot**, *Salvetti complexes for conditional oriented matroids*
  (arXiv:2507.06365) — the source of our `Sal`. Gives the poset and the order
  `(X,T) ⪯ (X',T') ⟺ X ≤ X' ∧ X'∘T = T'` combinatorially. **Does not** mention Grothendieck
  constructions, categories of elements, or any functorial description.
- **Delucchi**, *Diagram models for the covers of the Salvetti complex* (arXiv:math/0409036) —
  **this is the citation.** Builds a diagram of discrete spaces `D : F(A) ⟶ Top`,
  `D(F) = {chambers above F}`, structure maps by projection, and proves (Prop. 4.2) that the order
  complex of its *poset limit* is the Salvetti complex on the nose. "Poset limit" (Welker–Ziegler–
  Živaljević) is the Grothendieck construction of a poset-indexed diagram; their Simplicial Model
  Lemma gives `hocolim D ≃ ∆(Plim D)`. So: `Sal = ∫(chamber functor)` and `|Sal| ≃ hocolim`.
- **d'Antonio–Delucchi**, *A Salvetti complex for toric arrangements* (arXiv:1101.4111) — the
  categorified form. Their **Salvetti category** has objects the morphisms `F → C` of the face
  category with `C` a chamber, and a morphism `m₁ → m₂` over `n : F₂ → F₁` iff
  `π_{F₁}(m₁) = π_{F₁}(m₂)` — the discrete-opfibration condition, written by hand.

Neither Delucchi paper uses the words "category of elements"; the `∫` phrasing is ours.
⚠ Both were read via fetched renderings, not the PDFs — verify Prop. 4.2 before citing in print.

---

## 8. When is the `Lines` presheaf a COM? (and `∂□ⁿ` is not)

`∫` needs nothing: retraction + functoriality is all that `∫Lines` and its regular CW structure
use. COM-ness is what lets you *name* the topes by sign vectors.

**Knauer–Marc** (`READING.md` #3) is exactly about this presheaf: a graph is the tope graph of a
COM iff it is a **partial cube** in which every **antipodal subgraph is gated**; the faces are the
antipodal gated subgraphs, and **the gate map is `comp`**. Gatedness *is* our retraction. So:

> `Lines` is COM data iff the topes form a partial cube, `Lines(a)` are its antipodal gated
> subgraphs, and `linesRestrict` is the gate map.

Here the tope graph is the graph on `Fin(K)` (lines) with an edge per square flip (a 2-cube of
`K`). For `□ⁿ` that is the permutohedron graph — Cayley graph of `Sₙ` with adjacent
transpositions — a partial cube. ✓

### ⚠ `braidCOM n ∖ {0}` is NOT a COM — it fails SE

(Corrects an earlier claim that `∂□ⁿ = Sal(braidCOM n ∖ {0})`.) FS holds; SE fails for all `n ≥ 2`.

- `n = 2`: `sep(+,−) = {e}` and no remaining covector vanishes at `e`.
- `n = 3`, ground set `{a,b,c} = {(0,1),(0,2),(1,2)}`: take `X = (+,+,0)` (from `x = (1,0,0)`) and
  `Y = (−,−,0)` (from `x = (0,1,1)`). Then `sep(X,Y) = {a,b}`, and `c ∉ sep` with
  `comp X Y c = 0`. SE at `e = a` demands `Z a = 0` and `Z c = 0`, i.e. `x₀ = x₁ = x₂`, so
  `Z = 0` — deleted.

`∂□ⁿ` is still perfectly good `∫Lines`: `Ch(∂□ⁿ)` = ordered set partitions with `≥ 2` blocks (a
bead must be a cube *of* `K`, and the only face of `□ⁿ` running `v₀ → v₁` is the top cell), so
`R(∂□ⁿ) = Sal(braidCOM n)` minus its minimal cells = **the `(n−2)`-skeleton of the Salvetti
complex**. Checks: `n=2` → 0-skeleton, 2 points; `n=3` → 1-skeleton of `Sal(A₂)`, 6 vertices and
12 edges, a wedge of 7 circles, while `N(Ch ∂□³)` is the hexagon boundary `≃ S¹` — the known
d-path space of `∂□³`.

**Reading:** SE is a *cell-completeness* condition on `K`, not a condition on lines. It says every
wall separating two lines can be **un-resolved** — some chain has a bead containing both swapped
directions. Deleting the top cell deletes exactly the beads that do the un-resolving. Hence
COM-representability is about `K` having enough high-dimensional cubes, and the general tool is
BCK's amalgamation theorem: glue COMs along the cubes you do have.

### Toric

There is no accepted notion of a toric oriented matroid (Anderson–Knauer–Ziegler, `READING.md`
#7). The `∫` formulation answers the gap rather than dodging it: d'Antonio–Delucchi's toric
Salvetti is already `∫` of a tope functor on an acyclic **category** of faces (§7). Sign vectors
cannot survive a loop quotient — monodromy permutes the topes — but a functor `T : C ⥤ Set` with
retractions handles that without complaint.

So a "toric COM" should be: an acyclic category `C` of faces plus `T : C ⥤ Set` whose structure
maps are retractions onto gated subsets. See §9 for where that category actually comes from —
**not** from a looped `K` directly.

---

## 9. `Ch(K)` is always acyclic; toric ≠ a generalisation of classical

### Toric does not generalise classical

They are **siblings**, not a tower. Bibby's *abelian arrangements* fix a connected abelian Lie
group `G` and cut `Gⁿ` by characters: `G = ℂ` → linear/affine, `G = ℂ*` → toric, `G =` elliptic
curve → elliptic. None contains another; a finite hyperplane arrangement is not a toric one.

The real relation runs the other way. Lifting a toric arrangement through `ℂᵈ → (ℂ*)ᵈ` gives a
**ℤᵈ-periodic, locally finite, infinite affine arrangement**, and d'Antonio–Delucchi
(arXiv:1101.4111) prove: *the face category of a toric arrangement is the quotient of the face
category of the lifted affine arrangement by `ℤᵈ`.* So **toric is a quotient of an infinite
classical arrangement.** The rung between OM and toric is therefore the **finitary affine OM**
(Delucchi–Knauer, arXiv:2011.13348, `READING.md` #5) — not a "toric OM", which per
Anderson–Knauer–Ziegler is undefined.

### `Ch(K)` is an acyclic category for EVERY `K` — no loop-freeness needed

✅ **FORMALISED** (`FinalBraid/ChainSkeletal.lean`, green, sorry-free, `#print axioms` clean):
`serialWedge_bipointed_endo_id`, `ChainCat.endo_eq_id`, `ChainCat.eq_of_hom_hom`,
`ChainCat.le_antisymm`. Confirmed: the only altitude input is `BPSet.serialWedge_admitsAltitude`;
`AdmitsAltitude K`, `NonSelfLinked`, and thinness are never used.

**Lemma (unconditional).** Every endomorphism of `Ch(K)` is the identity, and `Ch(K)` is skeletal.

*Proof.* Let `φ : a ⟶ a`, i.e. `φ : ∨a.dims → ∨a.dims`. Each bead lands in a unique target bead
(`serialWedge_block_unique`, unconditional), giving `blockIdx` and `blockFace i : □^{dᵢ} ↪
□^{d_{blockIdx i}}`. `φ` is bi-pointed, and a `Box`-face carries `min ↦ min` of the face with
`trueCount` jumping by exactly `dᵢ`, so the wedge's **own** `trueCount` altitude of junction `i`
is the prefix sum `sᵢ`, before and after `φ`. With `j = blockIdx i`, bead `i`'s image face lies in
bead `j`, so `s_{i−1} ≥ s_{j−1}` and `sᵢ ≤ s_j`. Prefix sums strictly increase, so `i = j`. Then
`blockFace i` is a `Box`-endo of `□^{dᵢ}`, hence `𝟙` by rigidity, hence `φ = 𝟙`. For skeletality:
`φ : a ⟶ b`, `ψ : b ⟶ a` make `φ ≫ ψ`, `ψ ≫ φ` identities, so `φ` is a wedge iso; bead-counting
forces `a.dims = b.dims`; then `φ = 𝟙` by the same lemma, so `a.map = b.map` and `a = b`. ∎

Note this uses **only the serial wedge's** altitude, which always exists — `AdmitsAltitude K` is
not required. (`serialWedge_admitsAltitude` already existed in `Chains/SegalAltitude.lean`.)

Two corrections the formalisation forced on this sketch:
- **Box rigidity:** do not transport along `blockFace`. Take the raw factorisation witness
  `⟨r, incl, hincl⟩` from `wedgeMap_block`, prove `r = i`, then `subst r` — now `incl` is genuinely
  a `Box`-endo `□^{dᵢ} ⟶ □^{dᵢ}`, and `eq_topCell (ev incl)` + `cubeRepr.left_inv` +
  `canonicalMap_topCell` give `incl = 𝟙`.
- **"Bead-counting forces `a.dims = b.dims`"** is not immediate from a bijection of block indices.
  It needs monotonicity of `blockIdx` (free from the same prefix-sum bound) plus "a monotone
  bijection of `Fin` is the length cast", together with full-dimensionality of `blockFace` in both
  directions for the per-bead dimension equality.

**Consequence:** the `≃o` antisymmetry obligation of §5.1 is discharged for free. Thin + skeletal
= poset.

### So what do `K`'s loops cost?

Not acyclicity. `Ch(K)` is a category of directed **paths** `v₀ → v₁`; it is intrinsically
unrolled, so a loop in `K` yields infinitely many objects (one per winding number), never an
endomorphism.

| `K` | `Ch(K)` | arrangement side |
| --- | --- | --- |
| loop-free, NSL, altitude | finite acyclic **poset** | COM / classical Salvetti |
| loop-free, self-linked | acyclic, **non-thin** | parallel morphisms, no COM |
| looped | infinite acyclic, one object per winding | **finitary affine** (the periodic lift) |

The toric complex is `∫Lines` over the **quotient of `Ch(K)` by the `ℤᵈ` deck action**, matching
d'Antonio–Delucchi exactly. The loop is unavoidable somewhere — `π₁` of the ambient torus *is* the
toric data — but it never lives in `Ch(K)`, and one never leaves acyclic categories. **Model the
deck action, not the loop.**

⚠ Two cautions. The naive directed circle (one vertex, one loop edge) has `Ch(K)` discrete and
`R(K)` discrete: no 2-cells ⟹ no walls. And the `ℤᵈ` action on `Ch(K)` is a genuine design
question, not a given — shifting winding number is not obviously an endofunctor when `v₀ ≠ v₁`.
