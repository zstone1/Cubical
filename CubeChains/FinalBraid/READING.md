# COM operations — reading list

Background reading for the **COM ↔ precubical** program (`FinalBraid/`): making the
`Sal : COM → Poset` / `Int(Lines) : BPSet → Poset` correspondence functorial and understanding
how *operations* (direct sum, amalgam, minors, reorientation, quotients) behave at the COM level
before lifting them to precubical sets / toric OMs.

Organised around **operations**, not topology. Each item is tagged to the question in our program
it answers. Suggested pacing at the bottom.

---

## The spine — read first

### 1. Bandelt–Chepoi–Knauer, "COMs: Complexes of Oriented Matroids" (JCTA 2018)
<https://arxiv.org/pdf/1507.06111>

*The* source; everything we've discussed is here.
- **Composition closure** (FS + SE ⟹ `X∘Y ∈ L`) — this is the `comp_mem` lemma we deferred rather
  than stub; their proof is the real thing.
- **Minors** — deletion `L∖e`, contraction `L/e` (restrictions / hyperplanes).
- **The amalgamation theorem** — "every COM is built from its OM cells by amalgamation." This *is*
  our mono‑pushout‑along‑a‑cube = amalgam‑over‑`braidCOM n` story at the abstract level. **The single
  most relevant result.**
- Direct sum, reorientation, realizability; examples (lopsided sets, CAT(0) cube complexes, affine
  OMs) that pin the boundaries of the class.

### 2. Knauer, HDR: "Oriented matroids and beyond: complexes, partial cubes, and corners"
<https://www.ub.edu/comb/koljaknauer/HDR_new_final_revision.pdf>

Survey stitching COM operations, tope graphs, and partial cubes into one landscape. Good day‑1
orientation to read *alongside* BCK.

---

## The representation / kernel question

### 3. Knauer–Marc, "On tope graphs of complexes of oriented matroids" (DCG 2020)
<https://arxiv.org/pdf/1701.05525>

Our **essential‑image and kernel** thread made precise: which graphs/posets *are* tope graphs of
COMs — via **excluded partial‑cube minors** and "antipodal subgraphs are gated" — plus an intrinsic
characterization of *affine* OM tope graphs and polynomial‑time recognition. If "which precubical
sets are COM‑representable" has a clean combinatorial answer, it is here (excluded‑minor form).

---

## Salvetti ↔ operations (our functor)

### 4. Dorpalen‑Barry–Dugger–Proudfoot, "Salvetti complexes for conditional oriented matroids"
<https://pages.uoregon.edu/njp/salcom.pdf> (arXiv:2507.06365)

Our exact `Sal(COM)` (the definition `SalCOM`/`Sal.lean` is lifted verbatim from here). Read for how
the Salvetti construction sees minors/amalgams — i.e. how operations push through the functor.

---

## Forward pointers (skim later in the week)

### 5. Delucchi–Knauer, "Finitary affine oriented matroids"
<https://arxiv.org/pdf/2011.13348>

Affine‑OM operations (minors, reorientations, covector posets). The rung between COM and toric; the
abstract home of the "keep‑the‑hole" (loop) quotient.

### 6. d'Antonio–Delucchi, "A Salvetti complex for toric arrangements and its fundamental group"
<https://arxiv.org/abs/1101.4111>

The toric Salvetti as a **nerve of an acyclic category** — the shape `Int(Lines)` already has, and
the target of the loop‑quotient program. (Companion: "Minimality of toric arrangements",
<https://arxiv.org/abs/1112.5041>.)

### 7. Anderson–Knauer–Ziegler, "Oriented Matroids Today" (dynamic survey, 2024)
<https://www.combinatorics.org/files/Surveys/ds4/ds4v4-2024.pdf>

Current‑state reference for OM/COM/affine operations and open problems — including the explicitly
**missing notion of a "toric oriented matroid."**

---

## Background reference (dip in, don't read cover‑to‑cover)

**Björner–Las Vergnas–Sturmfels–White–Ziegler, "Oriented Matroids"** (Cambridge, 2nd ed. 1999).
Ch. 3 (minors, duality) and Ch. 7 (constructions — single‑element extensions, **amalgams/unions**)
are the OM‑level operations COMs generalize; the topological‑representation chapter for the Salvetti
side.

---

## Suggested pacing

- **Day 1–2** — BCK §1–4 + Knauer HDR: the axioms, composition, faces.
- **Day 2–3** — BCK minors + amalgamation + Knauer–Marc: the operations and the essential image.
- **Day 3–4** — DDP: operations through the Salvetti functor.
- **Later in the week** — the affine/toric trio (5–7) as light forward reading.

If only two results: **BCK's amalgamation theorem** (= our gluing) and **Knauer–Marc's
excluded‑minor characterization** (= our representable class).
