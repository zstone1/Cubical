# Directed Cobordisms of Precubical Sets — build & management prompt

You are a mathematician–Lean engineer working inside an **existing** Lean 4 + Mathlib
project that already formalizes precubical sets, several representations of directed
paths, and their category structures. Your job is to extend it with the theory of
**directed cobordisms** between precubical sets, culminating in the category `dCob`,
and to verify it is non-trivial *in the right way* (defined precisely in M6).

Treat this file as the standing spec. Keep it, `MAP.md`, and `SORRIES.md` up to date as
you work.

---

## 0. Orientation — do this before writing any new code

1. Read `lakefile`, `lean-toolchain`, and pin the Mathlib version. Run `lake build` and
   record the baseline (pre-existing errors / sorries) so you never blame yourself for
   inherited red.
2. **Inventory the repo and write `MAP.md`.** Do not assume names — discover them.
   Locate and note the exact definitions of:
   - the precubical set type (presheaf on the box category `□` without degeneracies, or a
     bespoke structure) and its face maps `δ_i^ε`;
   - dipaths / directed-path representations and the fundamental-category construction;
   - the geometric tensor `⊗` (Day convolution) and the interval `□¹`;
   - the **existing span / cylinder material** — this is the code we are deprecating.
   Reuse these throughout. Never re-derive what already exists.
3. Confirm whether Mathlib's `CategoryTheory.Adhesive` instance is available for your
   presheaf category (it controls pushouts of monos). If present, use it; if not, plan to
   prove the mono-pushout facts you need directly.

## Operating discipline

- **`lake build` stays green after every commit.** One concept per file; new namespace
  `Precubical.Cobordism`.
- `sorry` is allowed **only** as tracked scaffolding: tag with `-- TODO(dCob): <reason>`
  and log it in `SORRIES.md`. Prove leaf lemmas before the structures that depend on them.
  Aim for **zero sorries in M1–M4 and M6**; isolate any unavoidable scaffolding to M5.
- Mathlib idioms: bundle data in `structure`s, lean on `CategoryTheory.Limits` for
  pushouts/colimits (do not hand-roll them), give `@[ext]` and `@[simp]` lemmas, keep
  defeq-friendly definitions.
- **Do not delete the misguided span/cylinder code.** Move it to
  `Precubical/Deprecated/`, mark it `@[deprecated]`, and *salvage* the cylinder
  construction `K ⊗ □¹` as the identity collar (it is reused below).
- Commit per milestone; update `MAP.md` and `SORRIES.md` each time.

---

## Mathematical spec — use THESE definitions, adapted to the repo's representation

Conventions: `≤` is the reachability preorder on vertices (`v ≤ w` iff a dipath
`v ⇝ w`). For a cell `c`, write `ι c` for its initial vertex (iterated `δ⁰`) and `τ c`
for its terminal vertex (iterated `δ¹`).

- **Past-closed / sieve** `A ⊆ W`: `τ c ∈ A ⇒ c ∈ A`.
- **Future-closed / cosieve** `A ⊆ W`: `ι c ∈ A ⇒ c ∈ A`.
- **Collar**: a mono `X ⊗ □¹ ↪ W` restricting to a given leg on `X ⊗ {0}` (source collar)
  or on `Y ⊗ {1}` (sink collar).
- **Directed cobordism** `X ⇒ Y`: a cospan `X —i→ W ←j— Y` with
  - (C1) `i`, `j` mono and `i X ∩ j Y = ∅` (so `X ⊔ Y ↪ W`);
  - (C2) `i X` past-closed (sieve);  (C3) `j Y` future-closed (cosieve);
  - (C4) a source collar on `X` and a sink collar on `Y`;
  - flags, carried as separate predicates so they compose cleanly:
    `Closed` (minimal vertices `⊆ i X`, maximal `⊆ j Y`), `Spanning` (every cell lies on a
    dipath `X ⇝ · ⇝ Y`), `LoopConfined` (every nontrivial strongly-connected component
    is contained in `i X` or `j Y`).
- **Operations**: union `⊔` (componentwise); tensor `⊗` (Day; congruence holds only via
  one-sided substitution `W ⊗ Z`, **not** `W ⊗ V` — the product cobordism has the Leibniz
  boundary, so do not claim a cobordism between the tensors of boundaries); **composition
  = pushout** over the shared boundary; **identity = cylinder** `X ⊗ □¹`.
- **Equivalence**: rel-`∂` directed-homotopy equivalence of cobordisms with the same
  `X, Y`, as a `Setoid`. `dCob` has objects = precubical sets and
  `Hom X Y = Quotient` of `{cobordisms X ⇒ Y}` by this setoid.

---

## Milestones (each ends green; each lists the theorems that are the point)

**M1 — Collars & directed boundary.** Define `ι`, `τ`, sieve, cosieve, collar. Prove:
the two ends of `X ⊗ □¹` are a sieve and a cosieve respectively; the cylinder carries
canonical source/sink collars; the **loop-barrier lemmas** — *a directed loop meeting a
sieve `i X` lies entirely in `i X`*, dually for cosieves, and *no loop straddles `X` and
`Y`*. These barrier lemmas are real theorems (not scaffolding) and power M3.

**M2 — Cospans & pushout composition.** Cospan structure; pushout exists via presheaf
colimits; mono is preserved by the pushout of a mono (via `Adhesive` or a direct proof);
the two outer legs of a composite stay disjoint. No quotient yet.

**M3 — Loops.** Reachability, SCCs, the `LoopConfined` predicate. Prove **inheritance**:
`X, Y` loop-free ⇒ `W` loop-free. Prove **composition**: gluing creates no spurious
loops (the barrier lemmas), so a composite is loop-confined iff the shared boundary is
loop-free. Corollary: the full subcategory on loop-free objects is closed under
composition and entirely loop-free.

**M4 — Cobordisms & their algebra.** Bundle `DirectedCobordism X Y`. Prove: the cylinder
is a cobordism (the identity); `⊔` and `⊗` of cobordisms are cobordisms; the **pushout
composite is again a cobordism** (collars, sieve, cosieve, and the chosen flags survive
the pushout — this closure theorem is the technical heart); congruence of `⊔` and `⊗` for
the cobordant relation via one-sided substitution + chaining. State the consequence:
cobordism classes form a **commutative semiring** under `(⊔, ⊗)` — and note it is *not* a
ring (directedness makes the oriented cylinder an iso `X ≃ X`, not a nullbordism of
`X ⊔ X`), but you need not formalize the negative.

**M5 — `dCob`.** Define the rel-`∂` `Setoid`; `Hom = Quotient`; prove composition descends
to the quotient (well-defined). Assemble the `CategoryTheory.Category` instance. **Expect
the heavy proofs here**: unit and associativity hold only *up to* rel-`∂` equivalence
(collars genuinely add cells, so the cylinder is only a weak unit — this is why we
quotient, exactly as `M × I` is the identity cobordism only up to diffeomorphism).
Isolate any scaffolding sorries to this milestone and log them. Provide the symmetric
monoidal structure for `⊔` (data + the laws you can discharge).

**M6 — Non-triviality, the right way (the goal).** Prove a `NonTriviality.lean` with:
  - **(a) Not indiscrete at the bottom.** `Hom_dCob ∅ X = ∅` whenever `X` has a vertex:
    no cobordism from the empty precubical set to a nonempty one (the `Closed`/`Spanning`
    minimal-vertex condition forbids it). This is the one place the *relation* carries
    information.
  - **(b) Not a groupoid.** Exhibit a non-invertible cobordism: the **merge**
    `{a,b} ⇒ {*}` (two source vertices, collars, joining to one sink). Prove
    non-invertibility via a `π₀`-cardinality invariant: define `π₀` (vertex components
    under reachability), prove *an invertible cobordism induces a bijection on `π₀`*, then
    `|π₀ {a,b}| = 2 ≠ 1 = |π₀ {*}|`. You may define a predicate `IsEquivalenceCob W`
    directly (∃ `V` with both composites rel-`∂` equivalent to cylinders) and refute it
    for the merge, so M6 does **not** depend on M5's coherence proofs being fully closed.
  - **(c) Nontrivial identities.** The cylinder is the identity (unit, up to rel-`∂`), and
    is distinct from the merge.

  > **Explicit warning — do not chase the wrong theorem.** The bordism *existence
  > relation* is flabby by design: most nonempty connected precubical sets ARE mutually
  > cobordant (the square-funnel / directed-cone constructions collapse them), exactly as
  > in 2d TQFT `Cob₂` where every object is cobordant to every other. **Do not attempt to
  > prove that connected nonempty `X, Y` are non-cobordant.** If you find yourself trying,
  > stop — the target is the categorical content in (a)–(c): `dCob` is a genuine category,
  > neither indiscrete nor a groupoid.

---

## Out of scope — stub only, do not attempt proofs

Create `Future/` with statement-only theorems (sorry'd) and docstrings, no proof work:

- **Morse/handle decomposition** (`Future/Morse.lean`): the directed-time function is a
  canonical discrete Morse function; loop-confinement = acyclicity of the gradient
  matching; critical cells classify as cap/cup/saddle/cylinder. State, don't prove.
- **Profunctor** `Φ_W : π₁(X)ᵒᵖ × π₁(Y) → Set` and `dCob → Prof`. Stub.
- **TQFT / Frobenius presentation of `dCob_{≤2}`; Khovanov-type homology.** Docstring only.

## Deliverables

A compiling library with M1–M6, `MAP.md`, `SORRIES.md`, the deprecated code relocated,
and a short closing report distinguishing what is fully proven (target: all of M1–M4 and
M6) from what is scaffolded (confined to M5's coherence). Begin with step 0 and post the
`MAP.md` inventory before writing new definitions.
